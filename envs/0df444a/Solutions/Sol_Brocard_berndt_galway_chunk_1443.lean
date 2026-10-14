-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1443
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:01:08.129175+00:00
-- url     : https://prove2.me/submissions/826839e4-f517-40a0-ab1d-fe42315015d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 259352517 ≤ n < 259532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 259353767 1250 259352517 259352537
    0x1008040606060905030d1101140903041841090a0501150506190509060a0504051008060a06120902060d0902100809060c071104090825110d30 62
    0x6845160301000b00c078070040041281b494240015140e44000022400f40c55480324454100b00ca183c0b00c45501540c000b03002980d40e40d26005052200131424810100e2060802106010309402602c81006119002401c035820381000804a4a2103d1417101e000700740542001300a01c05101244042100380114024040091024100a640c6401d4018140c5c0604140451110401d000d1040644007089040441c54400042d000410507049912008006000040c00780300ba400c0c00c0c1203414084001c0c0c1045683e900309000015881c0c10140201000c2180c00132107084200074603000f841036240c004d0103c0340c1c1e944403200660301078902420103900a01c00f010380807100c40d00c9840c00500c650b203042d0190a540d03c0d45101032105501010082d90740040b1304030241d500ba0303554401e0101451051038060303079610020124041d81445240c40500c120501184100495031940150014000885000850041c0b0785031400b160304200c4000201c603580781407030148581e09001c2400c0e00d40416101c0150507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 259355017 1250 259353767 259353779
    0xc031b0b0705030a080403020f100c09150e01050306010219050309040b0108040302070e060f0303030f220f060c030213060305010303021204060c0b0903040914041202070b0703080a0b1008040606 85
    0x41c454104000c040e980104040d0301c21a2165000907000b40c406e1055405820f102800316203045002c60149071619a40c1c0030300d041050700001290000d05849000d1880c092a08002910b90a12400300906004001000407260f1384207000720384520000c5085140d42e00300d06d003000c039566040000000e0007240b40400c0070400f580581d20141c070482d4503a00030030001c0e00340341c00c9061010001d445541c010b4031541c117000c0c5503601030020710300c81c4c0f011110500702441c00c491320200803c540f0388000240a04c6142d038a01090306a060f007440e854000350085249400c0380c04c101c0c000e21030322800c5000741462103c041481c2d40d02d034100c14100c0e4001da003101c58540003602d5182c41489503105c1c020205440c0e140303050005420600c00303035010461310292400d19550785480d106841d92240a90035120004c0100802c20501081c0c10030b09011600c0182049810304d402c10b4450302c90000083c0610038543c8c000784280341c1641080140c1500a8442095045a16030241c03c201065a086030b00d98284000070800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 259356267 1250 259355017 259355039
    0x402040c0e031608122506060b030903090103060b04050114090a03051507080c030613090303090b10030c0f0e060d060609020a0c030e09060609010e1c0f140601240201090c031b 77
    0x2880300e103500200105002d100a9107850465046e08032105500c0300c8002030080d1929014511800b6007801071550340c0d0402e40010110391a5803c0045814814001889203076070001031004074950a0019075950380c00300c1d0004105c0301c80b42e8001005407245014441031907100c00b015601590b450348851580d80c480090001403400101d50351034215403140c6810280e040150001114180a818002000c0b8020380798508124070031100f843c0d015400190410810100c480490010400b0b0000700242c03508020210b06032090242c44c40780b00e840c12059000c18042294000401880c0c4010115a5015100d5000e04005051802034000c207010030a452014105459a140b09400090089180104400c019941c00f40318040c0140c001d000110012400c013080d550004049001d0700310004d4040c000e2601d00041c084651a00c801070708070380c004000110341602c044810b843c01001220362003000d520300700c2c010009010003411140b100100001400846040d902d0003140ca03040d00c5841d1a03d80c5002e1032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 259357517 1250 259356267 259356277
    0x1e0c100207083007020f0d0f1b051c0c05120f0f33040602030a06080a080403060b0d0302060f040212030a0801170a02030a0f211d01170402040c0e03160812 68
    0x240041b002d03000c45070980f410200358000184204402d0100785842d0302c0790804045040380a911201b1340c038106000c0f504d044040111419921442410880340513560207d030074040c0c0c4103842c0a580b181c0d05800908906001d510f0498a8903011200b040848000c966550107004407601840300d589134100801c4081902448031766610b0110f40020f40d196540c9580081d80020038501c00590384080104424030244a01542d060048105603140d50070350030321a08884000a59600c5591000f00c10400250082800e40e440400c05c1c7c4d22610a680741e001181614180000751070060200041001c1e5880e0400d8030300e410b07a414003503220000714086a82c00c1d50794031140c00185d8168810601c1c2800260500b510502040c4140101c3e912090002c44030900041804000f5010541e040b1a030359020060041c04a1011400d10b884840030000c5071080d500f40c140900301902454840520703246003402150400e08696020b011607114014070080303040c28400b140500380390390194115140c80040700e201a25 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 259358767 1250 259357517 259357519
    0x1608070e010507030807020c0d06060f0b07050d0e1906031a0102030f0909061306060903030e09161b1b080f07060522030c0b07051e0c10020708300702 66
    0x51810300580c07015581c64130010800740031807123088501c034500c2e29031802a03103a8500c00e1034007059050404800c414060415085900701c498280910000b040c40025283c1c86040076041c1161f4009418020404064202d11603840c107410400000034015890380c465860000300d00c0844104400310001240c8a00c144028104620000d000d1485149042180307250041001802c0e4110064140d00040030b80c1c1c155400b400115000200810515400030340c0c000800908450304816440d002e10214180e41041d4100340070045985200f42203841c0b4110102d0301d483d00100410022400c82490501d803502030b00622900303001d804d4403018040707000550b5406840c240d84550b82003c043c5020030000c1c000b0302006409620f0086400804945c91042a2000d840848030103640c030349460405a180c01040428088008070700c1d0001c000190001c19106c007010802c642c00c61459048100403464040150040c0b0014018024111944106003a9008810f102c4091800d0520140d010b1403d6a0042c3d00c400307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 259360017 1250 259358767 259358777
    0xb0a030b03010b0f210615010914011e0512040b01050f030105010e0705090a030b010b09041103040309140d060e0114060d030e040f110c070905130f0605040501090503031608070e01 79
    0x1c0c802c1440c0480d07400017a41e0400501c8140d00568004c0300e440c280082c5c3c2c260809544003203218126581c03116000000e03040384450683e45040d9140020405241032a0119010240c000c080f06002c1c800c00c11034840c4090301101da081c5003001c0c18620f4202d1801e1051a101f40d41001001c00d0505040c0180c5048441190300c802d150380c0c4640701911079502c80e510703069000c80102e0b80440000d0f024040c0c5400b80c20200102c0c0e8072826840107201c103e0f41550030030807050b80e0074410000000e921a1400054407030380da90a0708624005004107164040002c1c00400803818114003070b0999505500c000d01c10f040d60f0100c00c21984500042c4205014440c40c0500040c10410880c2a00d007020f800204200007251000205e0810100c8001c1440c0c2042501140c1c03504480c004101c00340143c080d05410464111155070806400e558524440c040d481303008207040c0e00d44000038180300080d440081007913080b0040e40e60364a4905078007240c0040c0300c400e407008680303c80003182d2524070070351412000701d0741a120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 259361267 1250 259360017 259360039
    0x3080904020a0c020d050c01020d08040b071101110a030504020a0f03080430030e0a210f05071d0906070c03270b0a0302041701020307170907030b010b0a030b03010b 72
    0x40c04040d40c030054030a01400004080c080c010b85414004c0000180a14050040b4420101c0024144660f43c0d0410040006005c00d003c0803518920b00d8035000b25141c1040171607203032400240750161144c0b0500611301503001c2603000c80301ea00360704002c0c46036102f1035124008a84030000f410303580c18980805000820203100501c4006415801c9185400d4120244080c02410542503104201d501c00c0403000594504e640c60b5003420014007000c040c2440561110180f40c2c1101034800001c0c1d6903a019001c80b001589110074031606000c9107000e0115200c02c1c0c401130b500741c1245641c1c5e0000349d450118500c1a1000034280500c40e4502c013000c1f55050781c883c00b502e02003c64202440414019140d0b20300407815002034a946240700401100520361000340e05d440c50007941207120b4141604d480c80c940d004008001180360701014030040040d00051103000c41c2c80d200e10340c61802c0100d070801400e4402e00700010880b40546030240190807482d0750217100c418006c2003803500380d59061491071341000c07207a00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 259362517 1250 259361267 259361269
    0xe1f06051908030403031404030c060c06050907060f1b0506010602010605120a05030d0203060f030706031b0e0a05060705030d11040906061b0209060d0b10141c150228020610030809 79
    0x30782c031b0041039080c00181010740ba0303150701c000c172b00156200c2808180518541c1b01040380030700070329038004001c00140032840d2a100c1c000d020443e2a4281000300509101c90001c000b81e007100810031143c000c42110625078440b00003034000e0903240240c41c80313154201c082c5005940b001540100c099848005507040032071340c1002e540a0b400240c0481d07481603d000390341d07229440803c01c6c940103051695022410b24500c010103540c0c034403072801c64010400c0122502c021a21400b801e101298000d40703440c0e50318001801c1c0241503004c3d40110704e1b400c074240101104031490780800303001994040d84040229554034407041d0340b039034040e09150785068050b140300005490858100c3d5442240906420140c00c5995500381034104200ca040a401c00b070302809111301c01e0072400a40031204250b400341c0c40c280b1005189840441c11402c0180929044801c10100b001e198040c3c070412080c40b402003105d9403004000d80440602c1a49820040c42910001824034094030028800c0301e0b0440002072500c10868 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 259363767 1250 259362517 259362527
    0x3050d140415050306040605040905061009020a05070b04020f0d051f061401110c0d0b1509010305150702010612051005061f0c0c051503090f0a020906040e1f0605190803040303 77
    0x8105c694410355480c0006070f40d4032903015285a0340d1082001e08414a0b018416800f01c0a06421003038910384188048044550804229514280c100180c40c45a540307501c00500003120b007205c8a90041c0311081d4107001c002c3d0000742915803000b22840441c0c0710000e1901030040307801c9845045446039156098a115500502055031400104c00503164100040740c00719031005081c040803182340384010208601041d0391100c1d0190100c0448501c181c40d491912496a1150210911034099030154040380183d0f0003540108020070442c41601c0c43c6900030704080f9140c0c4010190410124213007400191685032621110380b00001d107403403603c802c000040c0c01b10342c15806108203d0b00a090400042030780d5489180e0b017016558055400e60f078030715141140781c3c01c05440c100c08114503408030640d0740c0140d0390000059480903040d00c00049003c02d20741041c0c50001401605c0d50b506d40c03c4038050341d04c4140c580101054610a4510b921031180d900e90400c6222054403c0c6031343c80c2c109020510000c2d04c14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 259365017 1250 259363767 259363771
    0x2402270301090b0403080603160b0403060605040c08010303050f04081c200607051312110307060c11060d090b040803010617010803071103030f0d0510090b0f010807050d0603050d1404150503 83
    0x140458070800d21842c502c4000d40b40a400070302003014007040c03c100300080313800ec45015240a4800f404610100400a0600303001800000c050010118504966103c0c16007600d004120640840300100c00c00301084401010203442d101c0001c0c107614482200448240721421118a2400207049581d50850101c0b21a00b00c107440d103048415000c0002885001413030302c024290301030f140c41c202886441040600d095050b40c408001d000c800961000410b40c00ba2001400c0b05040e501c40d0740d95001595448010450000d00070942460b110901050000701c1d805181601c640b9160000c4103112145011103141c002d1280c0f031a91380c400c0245c0400140180f98901516101404981c01c0c848481c0308465160404918010b405581c0c008020307500b4451130801c4001d11a030141040900519004100710840801001c3d0502143c200450203041c881c104480491145170342c1001101d80364500306803103a0a42e01e00360005004034000e40a17900381c00080704c0480d4218001848482d502a13402d440c0742d080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 259366267 1250 259365017 259365019
    0x20c150601020a02121c1b030c0f0602031915051e0103090b090610090e15060f2e180909021903051024032402270301090b04030806 58
    0x5003141060050712603505405d00045880040c02401c5005a05960034540c4404074038108604000c0c019070304042038409507011909454071510040132401c11200c500e03408100144842e1000041000b2100da18140d52190340f0000c0301800141c0c1900401d400d10703001801107952008000c0030101641c0307101e440580c285036040c140440c19850588a0042805c403c4564913055042141041008840944820041c2c400c4890420811501d480c03480d50701c4405840410030460710f1030215040781d80e0445a06810b0070001c2800589034124a0617149050b948041e000030b20243c0341054003503c0c002c42ca031a803001c60040848045500d01030006014225044050380c100040c4250454210038154001c0084c600070742c010704031490004003903030484801610002c0ea2a0760441e0307528960800c11040f0301100d80003040000c1e403c15030007035042e401e0307a1a825182e88900c0082c0e409041100c03c05881e000c1040c0c4051006034042000c1030500b41ca08213003004254111006c009000240038401076508904 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 259367517 1250 259366267 259366273
    0xf0604081207174015180602030a030605030c010c022106071d01020c21010b06040f0501020d081509281505030f07050f0102150a0603060e01020c15060102 68
    0x2203000681c1410f544804160801015a03507400b050192204c02c01026050130314201000a041003064080040110700444080c44d9842e034920400921550924240c1085001c800701056a140b102a40d6540b10514600c0030905107403000a0f20319020414000107001a118412352508640c20420340c00f0152094803541c1c0c900c8941d140710044208180c1d0f01c0b520080e1200031321904071010802440105058960440d070181403a80c40c50b848440002001c01d2081d0550a0400324082041e0301400c01080c000c0d4101070003080014030f000c10b00c090142261802c0e02982c641c0c100101003211116400c940f9602d4621420b54070030380a04041c1d400981c000200500985030030000c58198403c41003680d2010282611842e82d1241c0040a02c00b000061104500902c00e00d1211050310780c84402520601c0c0c030502400c03540400d00d900a104c84034400480ca0f020500c45c0ca041c4c100500103011a00003500d88518001003803d035900c0510846094640207070017010402143c1c0341c0d0b603080c910002c0a850440c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 259368767 1250 259367517 259367543
    0x50c0f0102070303020909010b070228050d0606090e1c080c090918120c071415030c0c071502150a020408120306100201051b070305190c020f0604081207 67
    0x60081c805400094070a0740d01694030500e40041240000f0306030805000210100030745001a80c88004840d21071090a00060209400403030f1500140d026506c00f6030494492035401c2d081084540c40340b0180c43c03809004014800c2c1e6240c041d0398500c1c50803281e81009140e10041041c882c000c00c03003203601c8428080781030300c0c0510000c04107001d9842520f01803520044780c90980e000c0001070240b507600100241d111418081040729039a9105980d10030100f030355010013104801912810204018400301c4000c003541c0707043c2038114940c9907001c0e0700e602c3d01d2800b8160000c1f03004010a800c0440203600365006244c030060074002c8454600b400340070000c015508010020781100c041c070503213141004100c0c0003604c929010040c02020440511400d045915050411101c51641c04548a07080c0002c0201c0f034036000c2618080d5101e12441105802c2e06001d807411440c8158021601024184241c0e0400f1850f80134070300f400380b41d000390300404840390080c04d00050142c0010015190300ca004240c1d0344884 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 259370017 1250 259368767 259368793
    0x70504120501020d06090c1706060711062215080105090411010c060e07051809030a050a020f0303010e06241b160f0f0e0702070e060613150207061b03050c 68
    0x40d05c0b598004e160160300e90309410407640e041510700d049402c1d17503450507609182c6600003412612a46500421750444102e03100d6294480e0001c1d250348a030380490305260003419003840c480e25200ca110b4070000310b201d000b5054845200e404041d04941c80a0941d1080352150758a41014039588100581000301036480100890341034000c410b0000100c4004d084000e041101740201005010742065840c1e0140d01445207070080002200c5400800e4a04036459024140f0308078200003006055911901c0048004102e01c400c0030b030aa40210001c484c2c02009051503030300141a0806004084680c1e0000d110b1403d12072000d02c2864500310310003080c1c8208410071500030b13a159a09400400d40741c84181c009208641d8116941c038040c18840d10340981034038010f00c1c001d50324041c034010721140041550109019807242c10641d41e402e055501d50441407925041c504090400003940d190051081ca103000910b503019841b04c8400c1076810300501e810302203a031400d9a10707902c1680318802a11814040d8018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 259371267 1250 259370017 259370021
    0x41e05100213050906030a0803130b040809090a0b1008420a030b0411040204030204050f09010b01030207031407031e020c030c09060d060e030408030408010b090708070504120501020d 80
    0x80402808001a02e8648210001101c40c000383c1055009520750310a020065900140082ca49948001138035904c0d981e100c1c0003000546165402072100612109020070821414040c00d25400140c44401c4107903551010f00054816403d6031641089175900c00590741403141d8a4640d000c3c1030401c5800300e1540c01603c0d03030402c90360082018451018136580300c84428404050391141d1000b207852981450842d2504c00385813801900040240700314900e83e405a40300c07501942d0013141c004204010303a00e09502c2c45030803044111044046540707405070515a540c06403007507991854160392480a00d42801ea5021f5160740308500a50601c405040551b003401c00f290b402c3e0342185444c0d0702522503000400e0500d803610400c40f40d914866641041009034035118000d03620425908460045544280c00401754158411034001c00c1f440e000c000750101e83c40704150030039641c020050740c80d101103544bd0041240c2c0c001d8142d41480005a0070042004025203c0403151020b50150300014584039480070800c00b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 259372517 1250 259371267 259371283
    0xf04270c1805060a14100e040b1002031c15060c11030f0d0801050102011b0309020d0b1501080a0605010509090c12011202190b0406180906031b0801090b041e05 70
    0x1041c292101c0801c5260304021000d600100070b0009940072141450f00011300e10404d0544400811007800c500300c6441e559900580d08a8a024210854030030103484000d440e903128030082c0303180349a04050166000044e2203041580307000740301290a1307076051907802c0718401f41e505015903000500800710610780c0c0d001c0c031841003031101540007860b074030700c003000c0c0580f01030816031000e4196490b01190000080800760000d0311b08806180c00199070100344001a62840181f0f400340041100c00100305003401d0000344004512000d80341c8442a941d1021800199115405501c0c005103080c02100440e003448080345410182005405040110f9142c001071506000d0340301d580860303000d4000708294206000d850545031101c0c0c4034080c0090520b250311640b44180d1007071104000d02249580b441c1e04001024101604c0008818000305aaa003404400c030504940c103480f9008001034002a018014850900c1959200c807078411280d40c4c0340c40f00701c000c41800c070318000c940009840307990000e1018003406c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 259373767 1250 259372517 259372559
    0x20408010507090603020322020310290a0302030d08070c0f0305091c0b1b0706022701022107020d050604140106120c0902030705040f0b0403020f04270c 67
    0x11145481d05000f03084031032540c0140145481007007440000c13142031590802025440502445006007440401d2500e0b2404102600e078501d003d10781c84906001c417140c803142c01c00d4940d00041c071210401c20018030681610000f541903203c0c2c000a400030b4040c2c0c24443e400911380c24140d10b450b0140d20355941c40c01c0540801c800040000894000b180b800180f0410400000312800c00100d98a0303540342d80e21350018003401400586629070000354035152044a0b0115800081075445801c0701e0785021032200d580800d401d00102e001c3c2e00c950107500c0000d100600d581d448a0032100d601c12480890165071042e10300b40c0e0800181004140442c20070004039010f5841541041c00f070010303a801031400c640103600494014651485440c020032409401002568018900140d80c0c2d114540e060382c60388904d40c0800b54641c0b44100010700e6450314030141c000c1300d0095504aa1042e80f4904200440b04000e004002e89440c8040c1403120317450301045600120301c10b04509078440c0e12040c80705544140d1844c0c003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 259375017 1250 259373767 259373771
    0x241a040f09090203150411220f1401090912030905010906050c03180f0304050f0406120f0c080d050f0d0e012d02030606030c030703110a050703020c01080403050a0e010e0402040801 79
    0x40400c41c01c080000c80120401d1117030903030140c01c0c290340e41407400e48600c1ca01d5105080c0f002040d003111000c200e0340c11160842c404100000138982c42c1110142c211103981840c040c03400c1b00001492046130062246660344001a10f0b4017545941085e4028840d10302c00741c07031541d80c5010301c070005180740c414140a10302e011034840d10380c5445510303036000300f032400701d940040d03001416801402d100000648058500454211101408010214000745621751010403002d01503a1004140105201c0700414140624482d09105840e03248440d540c45c0b040d405200012000c11401c0e40e5084441b020b003503401120000443c001c94120701550a55808915014031300b4004452000d035081110300005180446030025400c600e007080005070b203030100501000111000000040d50a17120b640b02d40750300c1240c44c60b616101c140304800207110b5041100100d0141c802e10f07840c1c4000358021220b40c0e20560b03140c0e81e29458000300707039411241409800807107810f002880c50720349200d80d598005400074150103000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 259376267 1250 259375017 259375031
    0x40306020a0905030d02160b070303020c011503020306070518010804050102120c13051822060608060612060906070315080a05030919210213050f010306241a040f09 72
    0x10181001c1a4070145c10a650003a4903c607981c880000111048410788204541c5032282802c0580282c401c02c000303900503500e800000d81a441c55030510304240c074000d5081750801d80e1503c105680502c162540d141d01c1c0d080d4410f130b0000030741c4a010141d9000d88903400241c01c0416242e2903104211b4152a5074104200c081541c110050302107248200908085401000d20303401d01d090f0a441c8840034002c91240b58050360100141c90280003502c0d09558410b108000c1681d03101080c5440d01825900e181c850003aa2048289100000803401c0c0a02e030428080c10f60b03625240f000707800a1410542c8880e880ba400350f40040d40342014841d00c01e0190040c400786079151038410402401e140240c2e440c1d80c0c0200120710130702240382d2420240c4580f0350781405240c0100c00500018100000ca103440140302e500b070004200291091101c02412603108403014814100050072900414404107881c00c0c0c0c2c1425940304009866660000001d0b20300c40c84220b0340391986882c5280541003054100110b1682c40d010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 259377517 1250 259376267 259376269
    0x61a1c1803091503020f030a0b120604080901031505030c0d1110080f070f0c060f0207060c050c0c040209060a0513170a050f0c060d02092206180c020705090c040306020a0905 76
    0x12440c2e1800b0351454111b2170403980c00d002c03600c540009445007401c20b6407043d0348401901c6070750400710850045030403107100c0e240928205032550f0002d107050780000d003483c0445502c0300840c00c00906451008010300304485201050200d01c880206007a142680c0c0158580f2580d12200c50307000800d82e03503554052a0746441102ca0132104000384c41c0c0010070084450080c446588564601d5060764024008200c807140811408040d005d5000301809091400c00e8000301036130054010500d01065505594410003610100422405100b00680e0060402c200030b08132644a0300042c210440703122301c0400a940c6882095251645130086184540e000c2c60f4203105109041150100b095103400040091440800c04107856000f0a01503d44d6030b5000704544c52982e030b8030368103034400000305401400c285070380d4460103014103458403c4003030100d07140c21149034012443c0250000d2590340d03002082698030304002d11194410007030600d52061030a00011000440e0b500041007000c8103175486140c840d081030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 259378767 1250 259377517 259377539
    0x103110a2715030203060610050f0a0806130c020706140409110c10060305120307032913060b1207020f0303070c03090b0313060f2003010306061a1c180309 68
    0x42c0a000070201070100800040c0d800240a5a01034415150355040550348101511103000380c4400543d02113002c03407402081603014099920400c0d0403241030b2012000900301c441250f00740d003030800043c4c1005500748411806540c40700a00484580700700d01c1c10750f44400c040201c0c0e542146401007050001030303100980d40b080105544030090080700304425440c654485550b04880c040260101101200048256010f136000980c2d40d20700440c200ca0342c8802c2d0a64248450620b000f0750322640c032031440300340303400301a2251340141c50306a050785107026100d01c8a0b840c01e210040c00c0c00214480e00750070000301d0f00305102443c0602c0f52a25210180242e902d070160148026400c4440c41040034000c0090070071026500f00310464014200049a08082005401900070022a0040095461107140343d481c4010002c5040b00e01560041101c00d480e407030070040d940c403c008500a110404d000710000d1030340d10508030800c03000c00800001c0039900120300c4204202d4105007500810411001046034540390 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 259380017 1250 259378767 259378781
    0x30a0b0403031b120c0507050604030f020d1409060d11130305151e0406110a05210c0a031a1e010909180f0f0218090c040902090103110a27 61
    0x5100e442040c43c80620006200741c003a40e02000c00e142d140d5411040345070040e02198800c0307800c4801d440151915040c0641a807101180b00401441003800070400d9510031035441003079900309407200340b0380503031401080001d801c410050354410b80d88100c0d440d090091440200030100640303803240034681c40c60610320f05004546031403400c22312241042050700445c0080700c060013500503d41c0b044a407110308000c1c00400d10b102946802e00c000180c09000e49400501070100e0b01074080f031181c0a802180303820b13900e03054243c030a110384c014240180c07030440c1d0003500004038009441d40140d4038400c06100080003003c1c050b807081d07410130b810860b649039075a00c00c401d01c018100ea90028000d80b1b84280700070250910312000680068403500d0319504014801441e055007980051150041d101180d405188041003901c114602c4d210307000c46486141010300804020540040c00b15015a2a40c1c84810228a103000800d42c048005940480d922585044155100750040c40300c604603005400030b40d04035810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 259381267 1250 259380017 259380041
    0x712060b19050607050a022d0f010206060607050c04050a020d0e0109080f09030309090703150e01031203110c010c0e0a17071202060d061415031006050309030405030a0b040303 77
    0x1e4010724003080700c18440203070120303002030f201d00ba6210700c1da050507402c10500110017544144c5e4525081c84035591940545d0620081c48002141c42422078100280f031704040b0011405a00300e08006805494a2800780011038080c1090756843c0400a001400f2698111200d652465000c1a10000386c94140300321090784030544000c016130441512001340902401600040d11800029951032a490074803d27900c42400103481090300e800c10440c043c01030300d40109103021038408050700181c000001c03441e05040b250008007004007860717102c1045001e011665081301c180d05081002910104d401d20a0b400100e010755a001451503a040800c6040003455101d01601c03903030811080b1249502282c01c504550781c408542c64041e40c0e510204120340130b00300c00c00d41c041c1d1030301c81c001545021943d12264940c4040f181e609490700c4100d84080380b80000c1d240898120b00200741030051a00800055030041e00c02c00c1242c0c100790752140040d140907010b8104407480b0300d04909000405400d405654600e9013 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 259382517 1250 259381267 259381279
    0x7080f070225030606090219050703050702091803072d0309090203070e0901090e010c0c1a0c13080102040906080f190609060905010c020d0503091b0604080712060b 72
    0x100180025503403695100a50100882e00d10403840c40401582c840b0000c580c080f2042c0714140c0c1d26040103009401c10400001201c03010414003a00e20310940880b000030740d01d6240e881c1002102c2d0240110413034001c1842e0713104401100c842441c0701040000d0f01c0c4581c802c200c5418010340d4403040c216200c00ea03003552032a00c1c6010050800003500040c4280954039a030304010b07141c0d0f40d0080d04a4a41650715200c0303400415500011440d070f0f0081d08100c4145140100034031118840340d078200e80003500305001400c0c812401e00c8000c0c1a103004000e00d80c2240280080b507041c4000010920602c03902c0d0b911041c1c0580d80000c040000c060640102c00040c43c002c07020b840c03241c403905c41094590b80d1485030b0913240503605410700d00300801e0b58007154000e0b400640400c801241403030f241e402084440139540c00b612481008001030351198044900c22090078025041140010380e94140350208121041c0e40b1440c28000071943d2041040b00b01c000f000345101d1810441002d04251045803070540720326002d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 259383767 1250 259382517 259382521
    0x904050c030706031b0c17041508090c010525060507180e070918111206041d1e01020f070605012d0506030601021e0706030f0e0a060504031803080307080f 68
    0x54100405003800b50395041c00c80a02c2a6031030007d0403402c2c50a11111088008603022a88004402901199001c191a82441c0e62a102003c0755100211030340c01c1c0c0003950410048400003440940e091f420149190030800280c85607690345c003520422039a000000b9a1400c01c0b060790302820700e1034001040a040c01c0000b60401c04d4004040343e8181c0541e91a109200c4864400071a081e07019001c044900b40005446010603c1c4000802d10192502c1e4401c41c240b03000540b0f031014441c8201d55050752000100781109124088041e0790451071003c01d0b895600303100c40454084040b00030881c8078030814000480c0d41c180282d02610005902c0d203100c0c500c00302004000441d131016041d605645040310641e883e0780e61600100d2905d00ca03071101c10383c0080540640c241043d00001c0140c00c1e02c50948080c8030040342d482d008000c4a0b90940c844000340d0000e580f40d404200e00ba440720750403a00901e081005440d80000f01d50081406500803141c03850300204119030b4652208070300da00300140d00c9415001e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 259385017 1250 259383767 259383791
    0x130203040510090f0c030803011d07170c0f19030501170a031817010b04050c0f16030309020a0b040e132307080f071a0906040603020f090904050c03070603 68
    0x14030300741d00d00e8240302c0382d844044000b44082010240c42056000d0200460316441e85003d5030079400c20700c10074032020407034464040c0a60030458200e1080c0c1c1150780c0c2d0b02d0b4001c0920344400e21050080c14502c8a0740b010441c0c01501e69945000300380c4d02d907164820203651011403100034119007050b0702c008208101c0c8401c81003174075408558841503e0f05803420741000d00900034000300b41c00361940010068117002d0541000120190000c1100c00800c950030066583c8034600141c03640b1078841c154172440810424403144036203101c0910320140c00b0b840c0000b50005207a000c0341400c02c16400c241041d0102060070402808500402e552014000ba2a915191100d40c1e913060014842e06101448401d00240c014031090100001d8004002c003008803401400240b021030303290703040c0380200d050742507005015070700c0c2c940100c0031100010409000603203441c1c50300070110029000310302044500304081012541c10b41d5184411405140284080c01c80010300400301443e000559208a00b40b604100d008144 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 259386267 1250 259385017 259385023
    0x7230304060c0602180904031d0102030f04030b09070510081519050907141303020a0801061508070903050a0b0a0b041a060a0309050109080a1101150b0703020f070605091302030405 79
    0x7030a5400340f405a00c0c0c2c00c4549004503031311000740743c03103410003058001c000030f040e4029101509607080712607008101381c048004980b68482c1e48401e00b1009000c0204000043c1010840c80e4011144d405a4568a0716040010940e114034000400003c500105000402100c03a0400d059890308644101c115400d42000d0803801d4194032a652040c0a04c000207405140182c051407c20860391590381d5131060740a400031020f0125001c00d038007a0001010204510b1014819201525015101c0c2c060f40c1419a03800c5075018002041c40e02041125100000040d00820000c10b60f03c0c8641c0441103d8034010014008903203c0040880c4a541805402800800750011000555001b80c4d00150340d58180c00e8180c01620401c64002c0c1a5031034001315101b80007182000d040a8800c0703549081003042003e00007420b030784000d02684c41707010b1030010400010110700000c00c0c1840c480e005036044800c04464003801c04c3d480340d0002c00440c000140d03c031128545500385407420610950114150f0500c1c5c0c880c165 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 259387517 1250 259386267 259386287
    0xf030c05010302160b01091a15030a0903050f0301270b01090306020d09080f040905072a020a090c1e0215040602071a01080f0c1503040f03030b060723030406 69
    0x414950f0014180d0020010b20200741559500541804103650351070b481350004081c4000c91407001501005408110f00e8a0154014201035240c00641035803a0640803100414a480c0114207001c0b08110001c0e6a80b900b001442c02030249000d450307261810a022400f0020303a02800740c2c101032910101c1e02c46a80c000e503050302503c2e00028016201c4a002c803040b0010400110007428058012071203070001c8c003007400144103641e805034060105e602da003402907076010301205c10b01034100c2c0401050103040c092100401d2005c3d00043c990020f4030342c3d0702d21308400c40b841e501d201c000190001c10304803034415001c01c0d402c1c800003603803008003452450300b080f8092203400680010b0280d50005018018420700f40c1001c070040e099101e0f060702d0707035075a10a150f40c0c0324158140c0d800e4074001c2d00750000b55071410750508040e04405002040c915500c0b42e070b030142c160002100c110305150755401001c0c0140c031454090001c00e8403034014400c015030315101c03071000b40040f105002c0240e4002c200c14084c469104507042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 259388767 1250 259387517 259387519
    0x2070b030702061f0f03060207020a090608060109200c0d020d050a0f031508070e0403091d0415270b1501020309010c05011b05030f1005100f0c15150f030c05 69
    0x1000d50107032854807442c0c4032080c4e000c225170071410031011007401000da004040c0310f482105c1d904070b115600c1000d00d0aa070440d100e540d0098200b200100324604d06034002804503042e00203120004e011200a28013660420040110750f58442860f14070b0483d01040a80c0c41810745050144c103011114400400c03641701c6648640c1090b444154010220800e50320b120090080c40b020b803240f054441e80304210002c41100c007a00083c40003c07001811074101c203628001060100e15818465070b039500c3e680b0944454034a0000c219542d0110080c0301221110700180701c03030950240c01d51800160401e001d1048000e4034038400303013410304400d07015680c00004a07080200c081c03c0280c50540c031400c0642c010200800544071000c041c6090f0140c15a0000085100b0020740c40c40c00c82580390406c0e0001c880c00c0f01d01130582c018012008031340003a40240f803a07026007c0740345030101141c440365403800480000c1c0707031104625540f11240300800030f40610748400a05000300060220305c0c516161034001d500244581 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 259390017 1250 259388767 259388791
    0xf040c060e0d0203070b0c190503040506180409050304090f051512150906040314070506070503061c050c030606090405060a0203070504050d0510110a09030803090304080a060b0102070b03070206 85
    0x10009902c41079440700e6056002425a10510340d102094079840c0e00c001051902405003034a62000895440c4862820a400c40c0c010760a10341842c040c0945a40400c54940000d201d01c286140c540c2e81d00d00480c40e1262203280503540b07952414090b0360588070850001c0c026182804c08000c1211510100c25056080c100d941c08a01446070702c070b9a041075072a04000d01c0003000042045546440020501d00a43c0f296407811291094a01d104c003880c041c0040081032070300042c1c08516000c0c8500f000c1c54010300000c1a614402c12403240c0030404202644045940350400100301b4918034040c4502c43d4480026100c04490340b0b082d90783c00742c8a4038018483d00c60f0075404404206494402c0701910007409001c3e11000c030031200d9003816a950071240b881000380d00c0c1401c1030300b2640390100c4190750701c680c480d403102c2107034030b01b0350f5510445604000c01c90155440b0600c0005021001045007000e201d0069900040c5803140710002070402d40f29070030050348014200280700380741c0c2e400031f00b07994030140310004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 259391267 1250 259390017 259390037
    0xc010518100c210e180610140403060f0605040b0a1715070e0307090b240d051806070801030f0803061206181603050d260a0501050103050f040c06 64
    0x402d40311081c00ca800503100960600383c1c0800c081c8504451007107980f2545400d10011385030010041884505106100701c020f241c004140306041910f90702c41c12030a2828400f284200e402d441c50600e40081c0c0c01681ca05803075010222005002c0e10910000d403406450a002c41d180350004601d444020340316299500b00040c2c03e60900b010f0138000d030300030324141b00300b0000c03a4100000d000b00346100c4070114034824051540005114146031203480b40492000d0003139a00e015991140e90450f00f07040d0f2617070005980810181c0c26004040c440d95104d02c02c40c40c0d140e07040d0501c040c005441c2500c003c10102c18062401c0050021410410440c1181170384011459640d0b9580c802003520032a18030011001c0340310b000305002e9400e00340040b0110110310601110940005450320f400000d04600c005032440d080041121044c510518428200e00c8d404050020035250f25025518258012a854400c2d19a1140140403079031341801843d1b0490240c0783c0c0b00c0d01604260b20307000e841e814503120310800c2c0106036030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 259392517 1250 259391267 259391299
    0xa051206102c03010903050901110d0206010b0924030405190b01090914010608100b03010b0f060c070e070e1003050402130507120e0303060109051005040303140705010c0c050c010518 80
    0x5280d1003102d002a00038881c1088a01d00034041d5017040c01103a001c12106103000011140018004030600002c4e40100b00e940d00c3c1445040540d070000610b50342001c0c0300c0e418401058110140c40c01160144d8640c655203240c00e0505038145210039210310303e1a1281c96804001c2603108902c0c0781503030150300b80060702041038030300500005840007c658043d42840000280300d11301044121546502020030710803401414101800c840700642203a50114005401d80c480b810898041c0412524003411200403a13111614400c2200c411140030000800ca641c10b10300c90705020b4051040507520f414140240e00f800c2d80001e0004001400003900c6599600c001a221032141c00008410080071000708007521040c013005490f980215002404200503030b00c006241d06200f0030b64407900c10035985480c280750a40d034084540c0100840c04001d42041406040045030080c415240003420300d40782c1004403d441c1c0fa1050400341601200c0b41446000d0040700d00c40c0c0d4210031490005d00040381c001e181b02d40255 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 259393767 1250 259392517 259392587
    0x6040905010c03090c05030c0108010b03150312090a06031b030e031e091c1a15120f1b01020a080904140c04080f1c08060d080a05120610 60
    0x10102400540c2042607040072241c0644c4180340b110300aa450b001302c1605c41c0140340c0d80384600651107000418140c010066000e401014541050f80004406036820300a40024070b024003841d03c0b4000340720000f03156041d9213031809112005020b68101400500c000805944100f1242c0003410107054440503a0301d0300150070702c2250354220405c0f4200303400c7d080c0b100b00340c441a0070840c41d880c05600c892406010146445800502c0541c1c031100110490402820305c15401d4005082400000701001000305540e0300d400b0382810380f4910b07074002c105882c41c070b070309c0c0340c3c80c184695040b04500d1110b4047d020481e40c3c01b040c06114140c100300402d65403030560010034010301c5403010700b402c81c0d00c4c00403d000c2c3e9132025400800480345410201d8107810405030038542c940404262681502c0000651907804ea801046101c1d8071076002000b6142c6008a0380300c0c0c0180750b224032202000658001040603411040c0100550840c01c1903c080c18210719110002d01440d01300641824850803050110000780240c0f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 259395017 1250 259393767 259393781
    0x13080a02010608060c0a020f0703020d0f0f080d020307020606010903080a03090309120804030312052404021b10110309030d02030910090b06010e0609030c0f011209050f06010b040e0f0604 82
    0x6003228694540b1185e0160300c0c5c5c100c1d4503a00e0040c020b048440c0c0701c9800004080c070680e80c0080c1003032800140d980d651150031090300002c032101c180382c20008010821000107044480c10102001d43d5916000c0b0009040803002001c0318140300d2020720500100e6003940551380c040304941030009a50400d4281625000081e0b032050702080922110401000310540207002240d1003a25040014854080f00402f42ca0781243d55005031050910100d0035007400100c1034010031000b4000502d030400c8074072956110950303c1d81c0301559600100b07200400808510480e1010f8184200660843c248070a000b503d84c400c600d2400304003a00800414031011013032180c5100081da1150800a01e060f81c641007100d10301c00c840c8580460030000468000d42040d0041b02c02042d00180980280b8044108000500007420000ca040140c20200e10075030001e94031505128900810080c1311001d00140041d2500c034050b04180083d0800703010404c43c21000ca601140c100c144444d04031003e503184000b040080c024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 259396267 1250 259395017 259395029
    0xa11030307020136201e0a06050309100b060405030a06060509010f030203150916090516050711100e0604030c170109032c060712020705010516150e1204140102010513080a020106 78
    0x6041d0217440e078108031b1b689001c00325058072803490455480b0b400795040e00044544150a0300004400c841030955a8031010f4a60001054a4103141e140c0010030300e04890701030125929170fa1844140601e103031070340c0d060780105818114051810309540c0465295104e20200da0740c081c030b9010200307100c00402e200421120301001d0074910b03413580c1c440102000d0501908d0081104094038a000d0900d4801c1c412070310070300d03049804c410201e4280d20501039146080840502008046031010440340e50300e10003400154003500014103210708080c03020600c4006600160402e078907005480c00002c0c0c00480031082c0080c202c1c0c40e54400039400d4120103a1100006595500c01130004002041104017074041a6086256084800c80c54640300190382d0f6110301d4001c1505d44400c2c0e00c2240c00112140e140001c2c528014101003910303402180181c2c94085012010320b00100e0205080c0030b050110016418480b0382403000340080d0401401d4008485085440548000300004984015500035000700d0000c00c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 259397517 1250 259396267 259396279
    0x140a050a030306140a03030f030e070605040306060503030306090606160602070614060d20010c0f0b04020306070801052116090614040e0c01050a1103030702013620 72
    0x452421684840d809602100402d103030001c0815039548030441e02e000880058021540c180c1141c4041c0e5950386070503100c808142c2c4a8000700c0b0090303024440d90009244030b840b0191682e0852401100350781c841d0f04034500035030051040046594455500c00e4006605441c0d1954402d510550300003c4c09514030041d12040c00002c0c488100120340d4003002c2c918002c201c1105090300e0744020000650400000904640c84d45030718a100140d0b00c042080f440b5005040c8030241c640700307a94038011107008610540d8111801002c020a40c00e040c09282c1c4d000c505450154555070400d00060f2a100313481c5100101d41120f40c00e03107501d00307004108070780d50741c2502c0080c03415566542810002500d428000c282601010000b5a441030034240240400070718488058082181c0b02e01c01110a500a01c40000410021801100400c8028801580a800c8503070010598400842050040d10314100140400403c01d10042e146081c581001d03146056018901c04507030341413401201000c03d61914101c0c1c0c482 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 259398767 1250 259397517 259397533
    0x6020906071e02090a09021003020a021e0105010e091912140705010b030c060702030a0210021606030605040c17070e0f12011a0126040303020f040e07120509070504020714 75
    0x500700c1030002610343c400c0b0303840c611070303903540f001d0400382c50340000000e4002645c003040c2e8005a009030040c0c00032500503c115241101076485c107500c4160490040f5200780d554400502c034a00d0441000d940c001000300082101c0686130200c11030784030742440054882c400c50145a8003561041502481031030020341c0310754407019581071040c000d001c40089940b00344a90106417145080072400d4450380354004024003d81481034090003400002e850780c040450003a241c3c02c1100c3c10004c4004005082c60f96170005956082805000c11180da840c9210b080c0b11440510092203803505a02c10390000c002d107400341a01040c040032440b10b04a04800710b030f001c114032000d10740c80881540300a004090342c0940017103d44401005540c0c00480b903801040c811031201d003c2456011031038400350001c1c482e00d0700510b08041a032040d203441d002a04841100c4903040c3c2800341d5194040c15030405074844000411187c1440b16884ac3e48a25621a6a0007941c01180443c1800040031221115407042e105079030042c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 259400017 1250 259398767 259398803
    0x90c050409062607050a0905090109050109080c060606130b09030a0c080f070e090613050c0402280807081303030209120a140c0f0103020c03130602060702010f11070602090607 77
    0x12641c0150400042c55100802c00f0503000c0044c2ca2401c98001a082010b0700707080c80c00e030f0400b824009000b4111503488400c0032002980c00d20134460b44c00e018825040d110405000303035500f8090082c29040c81071406010040300301c5681d49840040700c81c225000c56507001e03214042410b00001c0c400292401c4440072001030316043c0415003143c090204400c0e14001501c0380401d03203840106072184640da42c88980000d04e01c031200b108040307010b405038003103030003180c0c1003030004050380e02180c11007580c21068203181003000c0d502910700e20721000505201403586040c0d040100310080c014614040d100c4007450200906000754110741034000c019200c02655a810403900d9035a0443c80002c41d07000c1d0060700a0f03095120f020650030b450103001071080c0c41c2600890b0044010b508914284866070000700300c070425200c000c020b03582c010b00d02500a0241440c0c06500642100c2c48a002c40742c10500300004020004028021160382c80da20036001a1240038184c045200d5002d00e443c000d0400038003401d40544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 259401267 1250 259400017 259400039
    0x10e0f0d2102190f02060913060b0909010608190c05071505070908030f030a090c05030a0b07080c0412021216080106030204180302150a0f02040e181501090c05040906 73
    0x801d048a80072200341050304040078400392021000a000c0742d0092868000601c0c26000500c100b042c01458440d000a49600380300480c2d070079034045440c80c2c00000300c00c0900c0c03c0502c0145e0040c074803410724503000d180c1400508400360990307410040c819079410307000e0f2450f03005d142a90201c42d0840340501e080b0394030100880c001c04d400d403281c0011a03056240081c00480000c100c640002103011f4042c01e68880e070740e000010f4103810104580b4013a8040001c40c40351801c020745002103000e10f00810b911309010300c0151400c0c4004e48101a03204007040144044404000340f140c09039410307600589214800c581150801100d144d03886020042040c0c0083c80c802c0540182040d02c0c0220760400146e00c0c0c1d0f511a1144c82c1d120f602c0200960024032110380c070b1481c14181180d000c141044049500722402c2801d80032030f4000d4114070b9414182400f88402845a101c48007074540c0c02c42e0007003001641c61100404280414450303000400d80f02c42040c4901d91069040c1d80c01004c00b20402d1225946031909064 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 259402517 1250 259401267 259401323
    0x190909091a010f060c110102010204030f060504020a0e0c07020f03010219020f0607091503051801110406030501080303041707030207030203070312020d0e01090902160206070b060a14010e0f0d 84
    0x4400440000070420f0060411010102e0380c1a0726540105440d41da00d501000c00d50040c52030665500f0301000002c170311041e00c40c816103803084000181030300c1c1c90b104000100e030841d04010054502d40e41007090054400c0d0072600d140b501252507410300034925001901a102c0c3d8203c060315210b48541a88955800040c580415410071050f124250345400342129a05c9940c410612554041c0c19560380b101c1c0a0740c06160082040c080040740c0c0302400b9146425150f0306114404a5034000804001c8a645482040d014000b420065403460a264031208849184418031295000c800503102017014002c1186000030355010301595849503480c100840050415001000980980051a8101e9214003600303040c20780141c444010050400405800a402c1010415000d00ca001300603005079840070040c080b814401c0c001c0101a14001060003040b424907800054240c00c0d0414441250383c2013803004a50301700c01d40d24980c03000850030000d20000f22000001c6c10004001d02d0f80c6540b02c241c41c070041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 259403767 1250 259402517 259402553
    0x3042706030b06150a08040308180a0b1f030203031e040e040f0b0f0f010311031011030105040e0d050403020d1703090610140303070204020d1413060c030603030519090909 75
    0x70014003403140f40c0d030442d4491244040001580c0f0400071f80040c0c021520241c210085014101d00608006101854413050701d0741610084486001c1102140514048020340018408441e60f61455580804d981e0f006071030783c0344a1510040308220304071540c482036a005143c00403803003015007050700301178113038402e0f00605850f003124a01c0098814014118654002e103074000c9011105d80c42c40e01c80d03a00f40c034500c601c80d640c94000c0c01d4a0041003110380c040c03030404034a4000c040344d80354500801c000848000d43d40041950308403500b60755803503070040c0c19101100e8041c1e901030f031605034030300d003030008151030703031024040f203a008030600c801c05400007a580e11a40100342c1c8003202503266225a010140d01c4404980d01d90720406c907000041c1000c3d005404120302d100008a00e40010000d0f00c1d200b0728003142c8100200d03184c1c501107024400c060040030590141824200202801d58400811611500803540703000c1422540301a0304034410701d0b1090090a587c4010481c2d00d4441c80c10340d0103810595958 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 259405017 1250 259403767 259403779
    0xa030b130509192001030b100305010f05030a051b0a15030c030e0303090717010b090405030d06150e010c02280305161d090a020901090c08130503042706030b06 70
    0x4400300c110041e5030045143c01030704c11100c060b620380094052603000c1d460706042544030703031018a40d41c840c0420720803411025140031030301e903040c0341240395910141ea003c0c3c1d02c00d5002c6507041c030106d00045100150a85404441c04108400002164500049910024031400d9071110210b815615034405030442c142030380c0c01d002040e00448641e0390390000761104802c039040b148080040c00c1400c1e003030710005850382e800440c082e0503c0002500e0881d040310b05540303d070000586a441c0010364401d40c000b1b000c5480040c0001c01d4410340060038035050b00e01481c10b01c4010702c1500199a113500c0d03059101003a218034080711000601c003a090030021840102d1712407140c0c1c42e03821400300385900e420b410344c1d0094810340c04400c200c07100c48012910241c2880400d0080212200240e02c0385513159000e031070070171004200c1c811034100041214000a01c40d60000320052081d1001810220841d801c89568191000e000c00c0d042d032020541015a130070103411a46010720020030001f03034004640c841d01044541c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 259406267 1250 259405017 259405033
    0x6060510091a0a09030c060804150501080a02090402011215140105180103110c03030c190f090306051801020d0b01090506070b0c030703020d0c0905030607050c03030c0a030b130509 79
    0x1003614006014002d000056007041c0c21145440300d904050301d19003425203011071342a9a6a11584c0013501a40c00a00001e0801000c01c000d000302e01591180801c4190070812681d850a551103444103403002e40284138800000201c1c06581c810900c98006100f40070003000645d5016001c5056480366115101c80300080d4501078109600420580d07a00c2e60340c034001d1555858190004500400c40f01400f250b100c0400c0c41402e0710740b202000510320481d520000c0603501d10f0905280307072601c02210950000c220198000d0901c01c1d904c0406401141c2d401580400e1a0302d560101c2841515032402e1403220b58400300d1224000f011a40040c008183c0a813118038020b40c403803080c0700c0240b0a070034020309210b1a000c041407840c90000001d507400b0341e00786001801c0842d081400f2003a89d2948036688009102d020003030102e0320b0240074540e003203419420000c0c27800340e41d15242500d902004100405480380450720060b610700a1f00880205e8070b0003401391103016800d01c2d40200030700707050354848403038425600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 259407517 1250 259406267 259406299
    0x20d0806010c030504050d081306030f05013201112d0d081f0e07030203040c170a0b0405010b0a0b0307080a09110607060b060316021005101208040503030304060605 72
    0x101100b81281c0564480d0702e403a0501c010300405588403070f000c0320030680402840444011a407410340c00740c42c095a0200b080418420020b05555040e00091866003400f00c0d1183d030307001344840344060705401c03c00e60f0081041c2480141c820320b14a1074142d0303003400b400f42c42d013000740083c13600c07150285070040709102c1c5651a01d407031503581d83e01100071038045035505000c070b00343c000c1c00c01c401c43e0850398074a4801a03198480307007140000c1100303580f4040865008400d0004010100f1200000340120b01000000b4181200c169503442030841e4018204240c505c0c08581406429000100742400141c0b9080320103a8076070580c507180c5d100325039007000102200081665405035000700b50440d908020a0390503400f21070200001070707018400407900b007640c4d40940300c1c10f612048095440345205045451514210107006400d09181d241c80707202c1d42e0300e01800c000d43c0143c2c090301e030740a81e0b41d0b40f818229842440e280140d01d600c600c1c0c025940c140700200070442004440d41105044e11026035100d641c40750b00b40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 259408767 1250 259407517 259407527
    0x3090201170603340e010303120c020601050609040b0915010807020a08040b0318070f0602150103150e03070f0804030c120210030b010e18040204050105010c0c09020304080d0c020d080601 82
    0x244499505402040511020110042406084000b01001c00b0481d1a0b140f00130200805154001c010200100300100149038009030404200714826000b401541111800251200341c14000d0912940c03010a041e0307480d44882e400312001c0600a0701e1003560741003810890381540d0300b6001d00360010b28075100042803d8400b08100a4450348008810b0510b41000890042504010802001134210500e1030300e003444c08002200c003c20002034290301c030301c0c20044000e0400a00561500130a68104010400034221100e06c00d8180d00754100000d44003810b40240d400c501c6203503070103020200420410800d0160a00c0103004480c829010302400d0381e0345011540650441e40000f940c46040000007031500e6010fa04803901c1000140342074500e180c04880010491484802c1040e0341d400442c042204504043c425103000d0042424104040013290381c034005495001d0041120458010012404018203601075660b03100442c0300c2402041d10f0030100a43d208480e0207081c00140c0401c000c13410b1940030f8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 259410017 1250 259408767 259408771
    0xa0618051f0b0906030408074713061517100608030703030c0e030a050a0c060509100e03030d02031303020d052104020a03061103010e070207050f0d0204090507060309020117 76
    0x1c1e800883c1041000010844580c000900a40c0c04502c20808080090880e40c1022810340000c01ea0a440270948000543c6001640780c1689410b680042402c042c000c00d00c01d82503024613000420307a640c203001c0c60004040e040307116010060301100c3c00045158102002c1d200303841510641107445217074903007035808140c682c28401d03406035800400a550100f40b007030b00320240300d55050602000400810021914160102d24196040e8000300c0c094802c00442e203444000601d218580380d410f015005000a850400568607903017171006002244070541c03401c5c01500c000c10f0003070408546914100c0d00c20305100c841044114018000d501060480b031f4001c0c000d807a180c41c0d04010b0202c9498181c0f04440340e4041c00f40c416603003d15410b800000041c1d2030f0003581d544442c0004035544a503d004110286040d01510500541d0440d078002d020545030201d644c040040b04440d40440b4805500124008204408000e011401074280209215401d50070603060b091003a660a03d003aa01200d0800f455802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 259411267 1250 259410017 259410029
    0x80d05031303032a1d040501031109041a070903020405060a0b030c0a02010f0218010807090e04170712110c06030f06060a18090b1807090e0a0618051f 66
    0x1c51400340c004244694040d040c4000300e000b00360380d01c1d075192540301c0007411300000c1c45002512040b15660044a0f180118521310400d0354248003550565460205101c10030704468043e280f52000902480a6188034050010b140d9045c03c0050a00a000034040912400284c2c044c60424011445500f442c200e0802141d00365504d030746c02c6840343c045621040c2e010000980c1151348402c61113040d09441d1004140c11501540c580300c000d16088005413005400901010a1204500e800c210007104001620b900560001172100681d000b0328003880d89000d02c070380c041c000021000d10040c00c0d5802c640c400d044003400004403011510100c0402c00d080c40120340d00e12400c0e90240200360300e414075001030b29460600d410441841c00d80310301e050070211000e912403210207448116125031424441e01400600d82080513146251500c41d10251200100e84615102c0d8240000040c2200c10558000c2c8060400920021224890320345144058041501c2602c0007905882043c441c480390001884210340d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 259412517 1250 259411267 259411291
    0xf0b070323010b0a0509040527030a17060d2102011a010c020405150603040b04110607030215190606200a0308010b07151b020c240d0e0d020304080d0503 67
    0x801c1194400041d007203001520280304050004d0901030303039907010301031007403462720100402c141221403e1880b014030ba0400041e42e03002000040c0b00964071485034404054010008030b003549603040440c01100003540090070718810320b9a8200120184502e1511410569000780101305604136042c10519841c04a41d01055041041c8401420309401040d40701542c030000041d142c2010020408590040320111103c04040c1c0c2000b00300b24580002c842c0700b001c191007103402c0590603503001e95643e03081d2040c240184410000a00c0500241c90641610002d005003800801c1d541d490140c031074680d0940c40b889210b000c81c80940111000916200720a415540c0d2100607441c0142c0076801c4d601400701914001d1040d90940519405801213204440003203100da41811041d49000f420001903803100c17481001441510516907030100d01c05907000c044001d080e0340c0c4d03190002005005004004031200749000360340040d000c00e60040058001c492a0b20251000c40b889a0740440342c5100485904a0f120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 259413767 1250 259412517 259412519
    0x20c0a03030c11042a0e010503041104060302042f030609180f031903140f0c0d0f240f030b011505210709080a0b0f10030f0b07032301 59
    0x203403203400c980340da0354043c035461035140c403000011400b0340b0905000c4000c19882200c1e501a98218054201340d498100e290508a90070303d0360008100d0321010380042c0c19400310a500c0c0541d540c3d55030004000b1540240704008107600300e011850209000700b1404424405160035680e0400a03004032441004001c01c0318603036540b0000c04907001d0a228814450340d03c00d0302038034080d4200400c02080f14070703460545091442c130a0300c0000c0585111510f58070700000134505000d004c5602c21102600440048200d58a800b00703c00000c000303018020b0b0328100c240c1044c4044088040b4050700382c1d802e048005810018584845c8240c04544a6200007045042600c0c01080f226600a0120b143d901071460558500700c0d110548800008502d80c02c1c4507408c02c1041030100c415004040000144509000380c14803940c16140c0700c4074080014440c00004925400183d229482e0007541c60145502c210342c800030b0445410012007001c0b04a8000000c00e1900e0744800e44205651248031010165294140c580d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 259415017 1250 259413767 259413773
    0x1b09051305060d0807050f0a0308150402160311031309020a0e090403080a0b06040509040b07080115080118021c1b032c030d1406040c05070b0a02091305010b0a030606020c0a03 77
    0x585c40780d102a030f01c600a510210354040340078031103451070314000c0d940c0030030b6410074100105039080c0510969200d81c2c0b04014000c01d219483c547e928000b030301420060700803101c1c11341c1d0394194402d6050002e1070400e504030103d1848030075809001094120f64495000f001c0c14014040c0c0040140c1c0d01034003042000002401d00e682941200d1a10b10340600814109030ba10400704410020640302141c19140280c10402c140380e02c01c4070079004100d03650056000f0001100090101801030061622070f1284c0d1880881c08042501107504820700c4061180344843c403503944c6070003010140041d400355a10010002e05180c070178020042007100b8010509148000d40061080e56900301d294001180000c1c001101d09807642d01c182919003c404000360764038500718003000304407001c90310068248403050001d80040707030020803800d44c8208084001651000c9074800958183d0218101d05c512504160010a81d0364454000d4004117a881c0c509100b5540c84d518280c0c0c07a8031500507103680003400000b042002c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 259416267 1250 259415017 259415033
    0xb0904021c0f02060309060403111f021602060f0408061e0c0a030b0907030c0801080a0b13080d060b0a08090a03050a05340209010803030112151b09051305060d 70
    0x160038030400b280030386110310f64007190194000310340e0400c20380c004504000901d40c215480362890302e45e0102800c000701c4501188555510b121060710105035011418564210701083c4214841da00105020388420f2583c90031139865006002d03681190184001054181e4102d0100c0945030f04c91504100c49a03966440500084c3c101008a00c201621000791041580341d0107a03e81c00364000303a03000314068a1144000e0701c420010391000e80941e10120000000c40c03014124a0341103003030010341c02d2401c10142010380301806010210400b9510700100000c009003400c0081c500a50325898a1711581d0f50f20500316202c04220034080c0c0801c03010000000654070400c024001c161303603486840041a600c1e0044001400c100c50071001c520301c07906403901985000e210103401025a00c0085156605080411038a625a1507000304601c0088000a0103c0e100b0b4210034203590400d182c1c0b803412012490001c0c0401d41c0d5101d05030240e40e00c4200c1ca40711511a020351481180f020304500380c9407100e565030303000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 259417517 1250 259416267 259416319
    0x11806080a02221a150c0a02010c050f060108060a0e0d020c040c1814040e1c050307050403060222050d02032107050f06040219063612060b090402 64
    0x86074060a601d81c1c0b8100704140b290b54018200044040301070407905080c0700e00075800c4405c0151038403003846000c104110003c0d05204041c0c0c20329000b100d03501c83d0702c0c00ca2318010107111502024080c4100114078008006089445640030b828140414240c5008007600c07130300251070038401078000702520051414580c000b50403140c0f2604e407140d26031086850400e4055915041020500d02c8001d44102603c0c0602600b603034005160040d04400c000c0f481c2c110440320702509450207001000c00041c0c02c0d1800758082d1780045030408425990352103034075050640305080115507001c15001e608003244d5070408204100c1d070203501070300034950080e54000216400302c40d50f00d8264a90000c20989000420074400300e074515007000c00510f41ca0400303104000070380d1308400c151200071040d444100a420303409034400070103074a002004038001c0b0340380b0f040307090045011030b00540a0700c000700001041619002d900025602407442001529150010000c0e0703040d0035213002e5800607001c80400510280044011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 259418767 1250 259417517 259417549
    0x90411012105060a0f0510030f1503060c08092404080904090c0e0a02070c0e060d020907020c090c090108220b0a091103060c03130611030f011806080a02 67
    0x90360074401e03a40d50856006007036200700354803525003081c800d0381c0c2403403200800900140d06613808401d00340307004210800c00c2943c1c080704064485080d0240c88810354046550251020b800814040d01c0f8100030018100c10f81c032010000703000b00002641460b000c60840581a040c80044101481a0b14801d172540c0010b0000d48040b101001030503d15039451181c007805a12a800c400c6886242a1030450900c40c020020228940108050780c0000c462030b01e8401940c111582d1f10781e00c1c0e11004082200da8450520094110100380248100c10b500051018903540c41100c02110790384d100c106248081c054000c010b80420511340112b01e62030a50b1a0b44159101fa501168191107555151002d00c083c00341d07901513189903240c140d0018001d04028403014101c00f0f9000344030506100304900311f01d100060458030f03224958882c10003044840d4101110050f41201580c0d228280b01a1418444400b03106006031010442c22602c42c81c10580502011030b50010090003503030020f9003e100c040b00102c404e00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 259420017 1250 259418767 259418777
    0xc010503071107171c0c0201020d030518120c1204050d0b04020d05010c0309030e010201140106110f06090c03010b09070e0409031b0303060906061407060f110a0201020310050f09041101 81
    0x4a8065070001c0000400c4100100174007603990301e102d108880320720b00c00301c0c0d0080050040341400540d8000034038080300c5289240010381b1340e84500c00c6a120340c4c142420942140228089140040c0d036003800b03005104000401e030340c610381c03e50f81e2270902c42c03081c0e1141d2030b088514107203182d0220301c19000303403a401750000e017041900300c480e60347d918211030075422075034080b940d20030340102490341c841c08132031800c902030000f0044091400480100c640052040204000d0040c0035030b00062005c0c0150000203006404890103401c2c00601c0640743d100211704180079619014500b84546000f501080c06814941c5480e1082c00e002000e00c800b400800c0d209400307101c5103803107002e03030529029588645103020350782c0002c286080241c41819103005522074001c200d48182e5804080704030b1030889018079409007000400103041504900a4074105001400d003201c0400e000020b5501900211f2040d400840c2e044607040d00c440400c04620080c024107a044683d800026000030700b204100c6030505414144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 259421267 1250 259420017 259420019
    0x30209070212160506101809051629070314030603150c0703020106140a0909020a08030720030a0803190e07080312011212080408070b010b03180c010503071107 70
    0x16004a40c00b00b50f0b4008860b601c110008107024040c04402c0e00320941c42c0750030114502d4840300703070643c141d01e08035402455a41e11868041213010003d0b042e01450600380c1c0d141c40c554421410300c1143e40b40c4050000c1051003c003402c0501c684070b0803154175035030645503018058116510400306030001440240c0500c1400c1150303690100c00c007200c40c0319050b65056a0f603114607901d0000c3c02d50301ca6078001d061140c100e1014901c16a0380190303407401c1e14664540027808111a000040e08107407603500c05602c0e8000010b42c00240b01c00075805625411000658000c5001e0341e400b07045e942c0c445c10070058034100e0f0520108010301e080c0c841070300b25180c0001c408514a00113400d52800c20311150b000c9413141e800001e1b1641c00c1d04071060b946006004034009010b140e84d064444a030504940000d550400c000d89001404000c040c0c015240c00d2a00040100d044c0c0da12075a01e82c1c9160310903521503040240e400008200700e2000a130560042506944060942e280c9035002d40301c1c1c0c0d0195844503810f025010f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 259422517 1250 259421267 259421293
    0x6170312070e04140103030315062001020f0a020606030f190b15040e1b1f051b0d0c1106071109190905010606030c05040f151b1406060a0305070302090702 68
    0x35406041300900e01d01c04154907500e000b8003100d440e496000740b400000482001940d0300a20b0b802100d407594540d840424580000301e078024425101c081c42c0440c070204107800055400200603109207025000c80e0380050b004c0c0d204503502c0c401d580070701c0e002c7c0c80102c64540c00561008526500800e40703403140c40a20b0302e520002415110410008445030780301042c030030031300810400c13400c000400c143c1f1a074800121105150b070100c0c0d03014850106110000450603030f40803c4a15007812800c404d000e07102e2a0304010002072a840c01c03000240c8034070186465600b5140340000445507030f0760303105d110070f04804a40c13001c0c0310007220700030043d202d8102c1c0304058100d804c203d40038074025a803088000240e42130034400d001d4212040c0140510400c08180814003800607403101030425100440d44802c14031400c2e1600710b910109980520794500c0e100e4103a40708000610115020006010054038016034484003448181a460710000d4156170041c181003016090400758550400c00602c1555140c0902038 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 259423767 1250 259422517 259422521
    0x9120c150106110c061b01050906060a050a03080702040209030c09010602030406080a0c0f0e060927090606060d052802071a060a03031206030c0312020c09040c03030e010c05160906170312070e04 85
    0xb01c9a80d142d4102204001e800d01e49007210f40037a0404884020989040d9103943c44140280c0c20001d0140e42d0024210703c81d960700300020b42c20050024505001c40d80c40301d00c004d4581e0040d1244401203112000494640c0105001e460280b80e40c0c0e0380c8101a000030850101c0702003540c061000d4000c4402c0007041d0300341e00e9041c2c0c0521402d1000c2440303035140074800051480c04800805500407078100d0310078000f05a6450048480c088072600004c60180c46964184030003020018010050700400240c04200034050f8024015031802490540c0c0843c10449040c2c244070400c5078066841b14202d10f007880003130b016a4903c170103041c202400007070460b181c0e0791b04e44040180f60010b4901200c1d000c1d40080c0e4641c10021001c000328144d48520450510b44c0e01e035940300314030b80002030502c00b10039405086039214942881d18260014100c40c41c00d418840c0181000718140180d45050341010b00c04900141040c1c1081c0d103c01040e0b0055141c04002c040319090140007800070b0301004041e28240510356114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 259425017 1250 259423767 259423771
    0x103090c14120105010501080103020108040c0506030406091a1902071103010f06050a080102090d02060901030b13050a0605030604021f14070503090a170c04020309120c150106110c061b0105 83
    0x504880d041c0d021400c080229400a903a0302501c1a818080140480d036800a403131411a80d087c2040d4269854524004030100d0007504150781011002c4108011711a4640141c00d5281c00f404031400850b901070145120b152080341c1038034502c400924204ea40c1d100aa000302000750113195a03500310403125000909540303100c1038050101c0d881e070340706003c1132420440343c60062485a00031840c003969000844c46c200318440010b48150404141800c085e4004e4120a05c00000141944004103495110070020a0192050040035240c19804506401c0c0011804d000c3c540050460718001c00d80043d5251036110038807420100310038004c0c40c0f110300403803001900015200300080c3d61a074400d0340910810012982c041800780003030740d030410b007542e0000c20407a040d8002542d0141c2d40b5601e122140c0e103800f500d00045403800340001103091414030080740c0300601c0a100c00011006981e02c0101300c038101e020f804040403e4010f07000c16030103842e00300000c00140c0020303041c3c03106242d00c21910500b15102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 259426267 1250 259425017 259425029
    0x141b12070305061e0c0c07030312020405040c080123031b0117010e010e15010c11060906040305030309070602011e051003150e0d030606020307080f070f080a02010f290103090c 77
    0x700786461349103201c0c08800c95446803a01d000c00b4107100103480483d030b40b0b8040707100240610891f011007400d802b80c280c0459001d44030150007448084a1020700426032034007403192030204200070482041c10003030740782281038080006000f4241000b41504103070704a00c111580034140400204090b6101c1407480d2329034001c0030480c2c041c1d5015071408141142c140b10040c034020b074007040c0e44846406a81c101800d000caa54021107503c1900c0e1035000032840703e203d1008429805040442c0000c1003240010040d80314400f08030694a0050b038504c03041c0e0030fa828031903111040c41c5001481c000304601c26400180e0002601c3e00040410360390b505e40001010300c0800d00d14000d5184d101e02444414104443d411441c45441c04004c1c8501d0024000e44902421400410700d070342c002074202d400e200f04026981860b801a9010719519154038000e4034540c480c0704404095428002012144d03446403080c0c0b032174507040084541c1040199002443e90f01e601d500b00f10b040c5541d481845020a030440403d6001d404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 259427517 1250 259426267 259426291
    0xa05031003050d0f020c010c0b130501060e010803220e01290f1b0a0507090e0c10020f0d08060303030118090b0a0c110f10020f070f05060103141b1207030506 69
    0x1340c2d02c0003800c0c41c00022503d414080c00f400c208000541d66a25294092080d045010806105260240c0500a42c0d8001ca0a2903007180001c604060701000401062480c0d407076024807000b40c00354400c0c80449910403108081c14407401000001400303c40d1081c803480b0640307840c1184407005241c4242e60000e68422800910120b480301d00a00d1442d00800004010402850140d0030380d0f0350240c0e12049400390300036881c0c555240064002042000b440d41c1c0f40018010384d101d01840d0002035841d00070700d00c11601c0b4800d074120400c10030700a21600780a45d10150103985960b00b40810707015200d03900a0071960701c95a4480c218042404508400c9c001c2650740401320b180041c2580040101c96290000c02e60f1f0740008607040d004480c00a22548000507030a07015031118400c3e00314040601980070050015007844c4003407030400c800454502d0503644102d80c000c1512100d000c10644c0c031815200541529441d1410b600280d190414644020500a008031140381e5101c1e03a5241c1080401d07506005d0005c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 259428767 1250 259427517 259427537
    0x1b09090309030212150408090a080a0648050904090606090b0103110306150408100c0311071a04060b030307260703090e07181203030c050901050a05031003050d 70
    0x1142c04200e4040301d40750440207022030b40c240310b140011120f001c1c000a1040c0000038480c0714942741c00044100420402003a9420450756040210203045050080c80c85050b18900e042c0d821104803590303210100c104082d903901c4845801542e034401402c109003005010007800740c031005503120701840c074041c1e00c0f4001c04600c081c5000e51900c1a01d20000c15241418104980d0740040070710507041d00e5203c3c504440c1c000d44880c040700c0000740c0c1e20603600540441d0181c240c052a59103802e4010207800c0500e5030307007002140c07502c4040040c03a01960400411031002c001005090a8a918130513801c2405241c000070400409000a0319540c0008c0045407e1200c188401c40305208507580c1006e100003171900c4070700c0e0951030740d0000d00980c61341c01444540c180c40000300b081148500c20600d1040c012000c040022900c8598012901e00e111b1412400241080c80000040d8410030683d82411811b841310b509000306c410060b00d403508001d0000751107600c00e8900001060041210703005044054a850502c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 259430017 1250 259428767 259428769
    0xb0406020f0c01050a0c0b180105070f0905090103150b03011b0905031608070e04031101090b0103020f0411030105130917120901022106010e04090b060102010c0216031b090903090302 80
    0x410300710700c8828180b04050151540407a00480f0601241e1f40c401c8000c809981c031648900500302e05544104071035031078102040300d066002040181082c42036181d43e40d0301d55079001046030901090100521610500600c00e940500a4005e0a18540020f001080b40d1608044801c40800110304001c0080c00403c800c00441c1030a0103080350000f0a482080303403160900104c2ca40e1a01e06201c1c007400d03840040d0000c6c0901d0310800883e281004158024040c0540e41d05100007080800e01080e48500b502807580042841c0a22540110310858801c8508680c603090070400031020042d44402d4482d280d02e210000100307070440c4c0a0b20600e100c1031454071400800c10100c001d01004102d002035a00c100424003414401811481e0702d401c4040302d035071460b51001c00403914070300c169546039081424070b280b61003040800114144108801e9000300300d18a1209012680c030b00411070200043c2c03031001014404104201c26041e451454002c801c0c0c00c1c00d6440090304121580d5034815000a00b80010900071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 259431267 1250 259430017 259430023
    0x90f08210a0218010305010503030a270b090f010503060112181502030106180b04030f0206120703060e06030a0317040609080c0102070614010e070818030409090209010e012603040b0406020f 83
    0x840300085c6810450f41d8140004039a0300e110744000c0d441480101c2492090f00e503440c0102900c85103036201c48070122a9034040a12594200310b40140c410706c40100d078400030b94861001c0d03071300c140030503503a002900f21401000e40c01021140c903000900c80201004c00d01040310041084404081242d00503969850141c004198980e4401002541111080200203020391356040d10107580d00f0414007102c0c480c244c40060b20500c5101c2c1e40c550101101e07001c018446805038400812601a102042d005949682c201a1075840e40070004002c00d00070855420038aa90000c01a80288510300c00203e508480d22940300c26080035502044603900060b0807800c1004c6401400300c00c1e9170240382200c0c154108401941e40c19002000c0c40c08002c095000039400a00e10a0412054018001035131b9440d074903228008007504503a00c0c181d02480c000303c00040c1090041d20440e040b554020305600c01d2801115011444055100d00f2010b2448280000315a802d0040b0044c40240300c150020010310300700b6260781b41 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 259432517 1250 259431267 259431307
    0x112704060e030306101d04140405071e030305160c0806011d01031e02030703080f0702041802150f040302030114090d0e0a0501050c07080106030303090b0a090f08210a02 74
    0x161600b09006205098031030003040c440740c1c403090400144504590b440d510000100061965020b81415820907008603801301d000d01450054003a10021070301d8070a8503980c004594440416807a045d00c040002c03a10074005003000e02848900001d80380e03d183c40d45410900650484000e90b001342004100201c260000f1311410400b600b1065080d40c550788804a810041c1e040442d041003040c0d6002046540502132103010743642c040c98054448100d041161030fa5000210104e000f185000c030403c0c00001e103480c0d81d051040c0c0c020140601140b50322a0b00f440c0390003062503105868800e11010005070f5003809a4134103054030541c4110145018810305140c110120700c41302c2071081c10819041e50303441c0e014420054801c282845981c401d00b5685c000c2c40d282203980080a15440d01d280402015030540200403e140107041182c0e0a4468030840400c54516003402000c040f801e120000020f01c074800501800502051079044e100c84d00402e808d8410320465241c83c00c5503001a449210400c070b421220 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 259433767 1250 259432517 259432541
    0x10b061b07060f08070e030c03060421020c0a1401172805060f0f060d02030f07020111270f0d060507020105130b06090901020f040618060f050711270406 67
    0x1504102c3e040800703040b101000c0d00c81c40800c485020000115142000b00d000001c2c0040c0454a640c50203040c807a0504110000707070703a40030b0100c5182030001b6200003685074002000030054500300d80351030149032840c090444514180103070b10641051001c06044002d108103d510f06800303258545000540c409006031600c18002031910f01440801c2d11109102c1c6c0d500102a206a10594a04800101d260144001c0d802c0090300002c100401d1860362004103000700e1040c1c001303100c651a0700e04010640d004801c40c415031000441440030345181030200d0903070708480141c030740107481110700c0100d05119010362003036408039101c8051141182d8240f040c5544003001c001e03569000d55880c1c0d00d240003094042c003002d1240d14803c0124144807829412502003103100074100b50790b1980c0b10400342c0943c1b40c120682250301c4a080c80011790500802e5600c1d4000c9040d62040e14001140d0f480c00307989000010040e80250455109a8020750513040d4501450b03140c0c0403440c440e203880e25100f803d40345940014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 259435017 1250 259433767 259433777
    0x80703020f03040209180a03020f0c0303030103120810050402210a0b010203070305090402220f0902040e130c05032401080c0d02010f11030d0f0b040b150705010b061b0706 75
    0x50059481c5241500d030004d0b4112601115a2901d1504807001480b11000c0041030040403842c4040540015807800003480400946030b40d19803d400b0035071680405d01c130140440c102100d003190f2851003001003a0348030000f011008141905d50011404076000142c04035005400008a100841d00d2880526400101184144440ba40b07100c0004d48901601074000c0910101294221181d902ca40690390032194102812860f0082d00c0f0655001c00020700c44e440c800b68022402080c800c515008035030680b00c90401c0049203446603507103082c00e911001000d0320b920008560104a681d018030182c0c1e20010110500e006080034000b80783d82d0300c0b8040c0d225680079444500006501c3e12820070790303d06140c09003000744855801103804d0715030654821a910541c00300065401203003034541d00c40440c0300c5554408010b00b5040b001400115814001420340c040c05044031141030550000090040c1403103040080303000203001c80403c006801c26481040a00850b07907042c80b40c20010001c5a004256605d0301d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 259436267 1250 259435017 259435027
    0x506030f0705040209011b030503041502160201120f0501150e010e0a050f1201060b0a080a05060d02130b0a032010050306060d0b0d030e0301470d030302030708070302 73
    0x14140e5100d055208043c040c0b80c0109074640160f020300c54900c0e51a941040540e5803140300d2500505c00e0b8400c440483e5445c8034501c0a00c8528090310984240e5800c0721035054420300f036030700103441c405400001144102e455000302407402010303005150082c407101c0f00c1d00e86000e002c00405090400c60020050400c04455843c4003031359030305ca42c92402c468007075440c0080c1c1e980c6440841d449003400c0f00c90320348540c203024001a450f0986001400b910f43c0d507540e428801d0300c41c0480a010b8840a0340c1d2030b544401003040e04800352600144c0183c0d01581d0280002d81154480c0101d10070a04960003954406a0324042080c0707082400f5141c14941c504a88182c0314280c0b421000d0100d01021741700d5806480041008a0a10f036968404441c2e1100100b1b064403080181c0707001040380c0b40d0401d9060082d400d11000b9080500711b06028194004951110703c0c14060034504038030804101d020204600019100080450311100303620b0216501954026a483c5882a000751500c00094044401c15104000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 259437517 1250 259436267 259436293
    0x9050d170c181c0c091107110a1502060f0c131806090603060b030706361208070b07390615030c0b1801200a03050a03050603 55
    0x50034651041856030041e4403840501d081c0700c6a04606000c49030421034801114a450580842d80c010f518803580020500340c0d181e80c01c0c4800e403034400c04008080c0354203010800c00600d084038140803003100500a102110307661900d00360529400613002e80540c20290038070610138a0102401e51003038014220601e006440c183c00f01165010344201c5a00c1d000180780e9015400701d58000100034000c40400307001c0c007901d07414528010b102030b802a40c030910a002d030000300c19004035144d001ea0350101c428100c1c500016100311842c10800980c0450513807a90300e0100b68078507146140400746025209882c2c07200c5c2649020940380d00c001d07214000b40280d40910b00144c614625240c0c040b601c030318894109040150400d001040c005043c020034540c100008100041d01a9000b181143e00820304c3c9130800782d0701d020103603da110b40f454548102c1200c1250350404c0d4001c19640c548000201c100e0210a551403002c00d051880035101240003560024401c3c091560502031280c0282c0200c014002d4014030305 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 259438767 1250 259437517 259437557
    0x307051b0114060622230301050c09040902190e1e0412120b0a0303020c0a090218090c0d021c050c1201060e010c1e03090e010b030403030b040e03070609050d 69
    0x20b01c242c1c8900d0000608100e4010100c2044041411128483e50b5040d00d50103e040081c054022542480d081c514280d41d16147c14000d01b0301a501c001d1000c1d2802c4000401e0001610f1441001d80c1c000c100c03401e43d1003c003018400800c000b8280a40c1030a02c0341080c0740b0050707034209000d954031440c01c104000d0101180c0892104001c032411410301400d40711005c007503c00a03000c0b00c01e0007139106940a07000070038180c0114001c01121411560380611070f49036840b00c8203d01400980582c0e840041d100c13601e640c00e1164840b178000089041243c1004203240d0030300241d0384203041004c580e180c0034078404d4600d4514050326030480143c00d149810406000d80f5100050014814801000483c0341a030304164010388010040e40d0304482d49402c8081824400d00b0f801140f00e5081700080c1250030002126450780c0102ca060741e94509500b0300d103480d6034404030007800c485050540c6c4103644100421304007074100020112984280c1d80418000102c1c2091400c01154200d0b00041c424144040740310b100a039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 259440017 1250 259438767 259438771
    0x711010306120803130f061509050901020f0d0902030c090411190506070f0c18020408070602010c021f0f02040311121204090e03070209070801092004090903140307051b0114 76
    0x5c000104c480da030a0b410b04c64180c19042d1380103440c2030310b00b00e00c054000c01807150120990b013004ea410302858442d0201030f4203d00c00c0402c40340c004c2c00144007411500e84150440f000c000d00043c01c543c000d03c030f2940058140c070f4059034111201202d2407451751031410040082603258428041e00f110061514002c41c41c14855104018411b18200c000c2008001c3d60110301005461201b80c2e81c0c000412600c0200002d6119001e0305182d441650740000e02540f0501030240c1e0703c8015030103050718449000e4569880c100128a40750501c1c0c039944901c4050800b440070300001e50041d240d003040c2480007c24010f50540015640085411941d41d541000c01c90904407000c8031403220000812084c0031100c1e5066004100c40290b0020401c8144131321a5072000a0905071100c0745010003880c59150242000c00180700d9260b02400401c2c4410003c092050780100c1c0250701034200203d2050310301c0e12400e000d0348125071210118402080d900305402c05002811880c0700841d0082105074441405480d002c840 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 259441267 1250 259440017 259440031
    0x6070b040f05030a021b03061b0c07050d0804060f022107050f10050105030601080f2a0d03080a061215020c030c03030703050403080619050103021605030711010306120803 75
    0x5000125003000324038070181e40510b40180c260381e200d2551100081d1110f034403030a02140b1b02c0d48074010341814940498843e0066140c407840d212545082904c00800c1c0c2c2100e030200e402401200000551a2180940001160301c5008207680c0c56092190142040440b45440303001c6501448000480380c6035914040075241d500700900751031f01010700d01a880c05801d80600e95107401181d51f92043d034486600443d040c1c0e44110203a948e180c2c0c031046000d0b07540544985c04003640d481110360445000e401120400c0c4600c0040400c06120340301030114507852044c40b0220001000001009920002845040c01600245422543d1314802da01c4603410110702c100c42c1c1c0103890340060840c011520800449101258003003e481c0c81e4034200710003030002c0000721020740100c0d4441c1d000802d00c0c54518900251510080320f4407a003941030900440c002d422041084540c0018006080040303001003000c0d24126204100c0080711040500005041d50f1040c1e1060150702c15141a800010b47d0080c01d4a5200c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 259442517 1250 259441267 259441283
    0x60f080402190b070b09060c0304030509010e0117130605010902070c0306050a0b1f14120a0c11010e030c0f0a08190c020a030f060c020f19020d0b0702100b0402090607 73
    0x407000a0b1a60140180d0748a26034000c1c0004e1a01c0400001d13466080c0f140c1c0d1484182c6010756110030110103540300c00c58009000800c01c00054406600a41c00700542401c1071500c441c1580c002c3d035001c0c04a40b8107031156402c440790000308500300300b2a80211800341103c030700c056092041594400810301ca55002c000d0503540c64100240340880141c0c0860303000003000700040840c0f400b180c1c1e01600101c880f9200400030301d00f4508140c001c0092401c0303034200c85003162541070300d55480f010f900041c1240c80a800070000a00800b202200307090044000d031144110285a940c204110340c2c91425265a801c01501e070400c45410022421540584501080c200c3c02242c150402040071592125000002540401c0e45030020080c007075010010b041c6207100d54010031051507224002d2341d40b052100811020313948503002e000505502c4600100e41ea92024000054821807540d6408402c01d0455071000180e0100741d0071800c0c00610702a00780c0d02841980c2c21841d103418680494110300c6035840c041c00d104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 259443767 1250 259442517 259442539
    0x9080c090a0e010501060c0c0803040614030414030c010204051c0f031b02041505030d080f0105010e030a0b1302211e0312010806100f0b0a030902010513080604060501060f080402 78
    0x40e0808080701001c100200255070310b43c0001f03003245107044c10940f5030b009903020208010200008079004e0b1805900d402e4984a08554030490b40d40c0018400c4510184029000507020400c0015002e0304015100158031a8240001d029800b03c9540342040c0036074100d407000b0300ac525965202c488640c0c0600e4943d40400401c3d001862000000d00002d40240c5007260076800303820588900710650380f0840a86800101020703003101e409105070703480d040f4a09240e004201540c0100700c038044205018090340d141607801c1d2a121003440080b5805404003006e81400011441c000c8100b00d043c000d404030080000188101141d0f80d894080d46070903008203200c1d280d4003140c40800c15580d002c8000c09603d5030943c1c55075807080c0c80702d10907540e1895080e81080c0201c1c010728040313401000d1703d1b2201d9286041c080025812409001e101009906000b420400481e59810080b00400903100f1100241040d04041c23404c0002c482e016840001005402c924100309035078890605600180c040340d402d01d01c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 259445017 1250 259443767 259443781
    0x8030a02130308040b031603020a021b0a0518010302090f1905060a0b03090c04050c0f1c02040f06092408070806131e150302060d020f090904080d0c09080c09 69
    0x25410503000940740f0311020070300041d0214903200540c07103256402441e600c215400ea005405030f0188110107070240c0c01c01c0b40c100781030114034050305000c0d5000800004000c2c0c1d480e40802c50020700d003800080148058401030040d4144050255000380913903d108a5500c1c0c5100c042200c0d0000141c2e07411200e80383c102042040c0d848040a1000e0010080359a540b8105160540da40e84a04070086001c0c0d41030030300150398a8482010b4030702c0010303c2d1004500e0a80d812804002c0344211041720ba02c0e03940d00744000300e00c020400c00c0c58805808541c4854100d6401d103102034018048031040c03007403030741c0c03540c6000426194060041c40e040341c00d60800742c6150f103035440000e40c10350b610813001c52414504000c1d954520450f045c482c0d0751140f846400c1202c1e4281044080c1880e01c58000a90031003010000e00c0504031140d0f00400e010240342c00c00c0c1d82400100b1002406d10075055500342c030070001c040340d07407450382100d44aa40c05c00480ca081c8020308600e1b0440041d02c0b0181101c00910a00501c0005000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 259446267 1250 259445017 259445047
    0x1204180b090a140610170c0d1b022b0f1205070c14030c03041509090510140307050a0632030403080c0406051902030c0109080306040f060308030a02 65
    0x4104018a2034469241c04090309009103450003000404400b400007182c61400c2c03e104401804c0e013503644800f9424502c030450007481401914a51705147c00b00400d406010340f0380318100c05c0101000403005c0d500e07075400000745840902554106200c20541360085e5400e180041d804d8858030398100400c0100780c00c40141c91114a03104241004c0b402c00f020043d44542c02020305600310310030080400781c40c0d00c80c0c00e55580c038002c030303002d0462660041209104069050040e10070141c018905461440d807105514070580b02c080c0d8500b03000d01c0c1c03040340c00e0080540840003400d0820081c0e000b0041c240c6040300140200145101c0c10062001001560901c1d080d029000d031050000383d0205003400002c202c1e14052684126801c0e00010382c050080b80e401d1340c040d0220b0301290416a20030b41080c00345130403000038050740030406041d44010486d03c1c0e158082070246807025809520038546900d894001c5c0801e1700c142c03d040d100440c3c0b0b000c0007170002800340800c0d80e402225400f00140c8030036100c198500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 259447517 1250 259446267 259446281
    0x20c1c030e1302030108070b07050a061806060306060e0a0b010905130b031615110703030807090816060f020c092d0901020a0e0f0612190c02160503120418 68
    0x14120310401011903070380c2c040c0e400540c1290554011110721075503400c94484140250100140f2642007103d650021940c59003149150620800101c042d5200c60b81d900011a011540301700d50f907984070f4804200040740c0000e40c982c8544480300c00d00480392400c00003403061025000d100e206425850000d040721706c040d40658040b20700601203c041308001e079140702c0001907910032030b00003440001c1070405030b500c140c010051050000004000c4682540e0301658011402459082000340c1c41c803000400401c00c0002d0b0b94400d160002c0681528200070000f00b9601e1480040019907001003111811515601862035002e080700c0c610358400000b02c00b40d4030704903800c011184600c9074075030f003405482507044d801010580752641700c2c04442c00f021000d20204d4800c4884c0c050388404140005d0101ca81c1029500d644000b010080c08440c41070500c7d00400c03101069403180050b071201d0421440c49030118403c1d40504070881c001c06e40c280c01c04d500c51420b44030f5030082d0340c0c1e001d8007003207041d040060b02c0e0001c02d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 259448767 1250 259447517 259447519
    0x804060507050d090812070903080711030a12030e0708030423030102090907051b160504050403030906150e0a020c0303040f05010e101b0e01050d0903091a19020c1c030e 74
    0x403060051600b480710ba150403800314143c6c204241000700c1c510a02034104d01c81203e0703100451a040c0815915003041e202c40450001d50180503001010001030010703c3c2c07140d51651542c400042021055014500c0c080150700024400c0d4801c000900841c20503e0322600e9507c10200a61041500d14000c00d01a00405003541d0700b0060711424010300f00d4001000e456110803081d0070903400180050400e65402850952a002d07807810001401582000d4108945c802d0003800c0110740c00c2c2c0a940d460040b58003400c000000c0a108407001c0c803444510b0003841d5013041d41110194101a030a020280e103070f2102900081c0204401c7c1c203510704001003174204c0003d079215607040c0c8201404018098024101c84400600710400c42c82500e200c450058044da582c903001030f0750b401d050403c3c60884800905801e8401d9023840050b03440041d20f04400c0f03810080b040c10000440d9120034100498825025200e12914199000034110070529140c00b40c2405a40d00d510703041800405141c10b064907c114060201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 259450017 1250 259448767 259448771
    0x7030c02210f030a0501060206070c0c05012a03030609182a080f07090e0f0a15110304060b03060f1308070606091505150403080409050a0b030a12021b010804060507050d 74
    0x2044e501c1441c0d00c0a41240c0040c1c0a8130960382d500740003116981d15001006241c585c0c444401c0c0500c1d40301c1c103200602e04c0205589070905c000440301541580b10368103411400a52598401c0c400254280926209503042101102842c0c4655485c440e030060100801d030554200c00c1c610008a02451402030000c0100c403003900c80b410f40420b03070503890341d50902a2203105070814104e00d00d120710000746504424581d00103040a004240e0312007000c141c058245400498961500c860080204401540030394861800002ea2080241c14103041ca18002c04070521095030008000002542c0c0207900030b075603480440540e40310034a140110040202d03070421062036203400c0c082c2d910607801240700000d41e1740464041c140205400d1400e90310348254040103240f0300f000d101c20440d8071036581025802c00468035003c111249c55901092405002c200b0a881418002c19030728090303a010300108407100c191201d10603800540c0d0001030003110780904000c082d15547e9001400c8c5034130400a80c0c040f92468601 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 259451267 1250 259450017 259450021
    0x110607020303070c030c0303170114010809030c0f031e0304050d050c190b0405100b0a050d0c0305011104090506101d0109180915020705070315020d1103090607030c02210f03 76
    0x420040c0c06c805000480c04110401d014903620f405030490141250403c110341d83c440d100c08801128840c0d00500214807600c4244022200d680b001e02c89410040b030010021a12032411001300c0741480d444400001e00c4a404006020102e4030104007480851110308005079541e19846c030440c0f40c40a6554190a44c0e510204890f04002103030f11054001c9000e030080311504041200c3c0541242ca41045c043d51000b1100700411840c28120a80d12100c0d00409000b818143e80b6110142902d035610348106200030000703402d04c4100346d9071007216000f842c2602c0d181041c40140201501200680c00b030545540038955030042241c4c85008003c0107010412640c4404440d04c80d1420083c0541007001c440c480b00c2c2c4018524810002c3c07003503035444d98100005180d568650746460a80c600c0d031105201c030040e001c11402c00c24100078041c0e42000d07a4540b00035907803894403103400c60824001a10b0310b41050b05004144045560000d0701c01561a804403a502d0351540b0421a2001d511400000400004003c42 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 259452517 1250 259451267 259451273
    0x5040e010609170105090616031d0102091c03050901050f07060f0f0e010506060a0f170c07060b190504020903031c02070506010608070518040b130c0e0607110607020303070c03 77
    0x849401c90f443c0101e09a050400e42c0f209500341d440890300c180c0182e10000c0000d1400c0d601c1e0511640e0503a090074000307500f501c1c542c0d400f605400c401d00e5000d2540c2d00000c40c600d0a080c24000004500c164031034040001009540040480c03081c842907038100300001c00c91b00b0302d00b054801100c0000303601c884104510304200e07400038054038242808151641c0303481c45080300076806004080c4250002000586010041d8800b0b40d02c0141100080042008588a030020005160081340c010006090040d490b6101c5140800903240c00ca201240540b2211407090080b40d5000a20310039114225805030310303541c3d00c1700130920314010554003c0f0200302c12a0444e000300015030007403058900403425900781c3da0302c8000640700d4140c01c0d200b40000500421210700c40c0c6050003c22191268010070103c1d15500c03907000180445035828002c65003982c0c50b0b0f2400e28503500014410169a4150f80d00c1c0c0c1804070580700c034141c240a00d442140120000148001155020300071103501543c0901001c00300c40c1c91381 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 259453767 1250 259452517 259452527
    0x20708090d0c0e0c0a02100507051201060e191809110607030801050406050d0b0c070303140405030d06081b12010b040e060a05070810031b0e010b0a0306050d0b1605040e0106 76
    0x4401c3c0c02e08400700401250210105a0850398078400c0c5400134031140700f281d440b04005201c01410340b41041410302c42e05100702d0450000314004c00560f40c603034002c6080f00c0c00308901c842c80748208505ca00012001000803502c03004401305d40e50401080000c1c3c042d0785041410910065024455201e50000b400800b0550881c02c0103041e500283c071304002192f12101880849890714002400f2601d40d080064071020800000f408c246100340742c040381100015268480070803058038100c4041d0000f088400440c1014030604000f13202e103034018509031070042c1c0d03005c074042d100d42c0e00240190b4505091000c04002508071044220010b0410840303039091494440d00c81100f610081c50345820076000c14426842485081e0069099501c02c401007459a078405c00d000d00500e2602881188010000501e07a08510440d4004c049281501e65122514840102156110380003140705510205140f40401d040100e410f5100300300c8010080d0000ca402c0b815201ca00865215081c2501d1210000c50659404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 259455017 1250 259453767 259453769
    0x42106140709061b02060304080d090203070b0909090c062a060a14070f200a02120601080705061911030c030a4b0e1201060521030409020708090d0c 65
    0x50340d407102c403070311101c00407400241d0424010754046d109002150202d038914001b400d5a1483c9407001494400d45e502107428000c00364414100d400d00801c004015041c007241281c0e22840f50009040e46501c80030025000d8003444200441c049014410500034280c1c0c0d0b00984040c11090f400c45401c2c1c501000c07850060580c000400b003040303841d82c000c03416243c0500c03024000e400d141c0c0c075500c4006c00640040c0030061400104e107001482103900580258490241d0105180440300107400c0d1903040160061401a850740720030700a003010815450004a800c0120150205601d0300104281d10366034401d2850140001010842c0030000301c407940d80ea00304481035401820310a0100071134440c89000c8400d2401e1840081080c3c02a00304980010f22203050040c000c134581c201020401e000101241003030a1507403151141d80c0d50380f01b09000744d1500f44034210100c0503005400004510320f80c06240c0743d0084d0310508022a0b0045051000c0089a405988003040050100ad0082d175250070011404982 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 259456267 1250 259455017 259455029
    0xe0405071d0a09060b060a18060c020d08030601180f060f031b0c050709061206060b030606071212050c090f0103060506090d0213020310081002042106140709 69
    0x20314400140341c1d0440c10146094009400030640c0540d545258040a00000a8201c402c2ca41d515400340d41692404090a281c01c03550351141030303040e640800f0518003041c40d00310405002070030540c2e0700143d031040b042502071540105119129110100140c98170020084204643c0c2c226207400708440152144800c1190090b95514208001c415000c0e4102ca0008500d6050070300a441c040180034001d041007200d140c0725004650510b59524441c0c400c4070002e0300314000c8480d6800901c000c3c040350b40aa4006003a2000d940c928600b441c1c4000343c1c8920410300000c00b0600d4a071085e84000d070190001c0558880351500a00203460150706100441d031200c60103500c607641da003100e2081940f04e0304c00d500c2500c40c0034003070724540a00007042203240d9881e47e0003207a00c01d03842d00d661a0072404500196008800d0b290019084034240800641054400400c00d00f55a1040c00200446401c0d80300c2c005942c1140c47c07412a0900b1981400070181201840404e0040f035000107028019610415103421120 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 259457517 1250 259456267 259456273
    0x405090607021501060903061e020d020705100c0e090901061505070212060910021b010c030605030607030905060f06040e0106150212070b0c090a030c031a0c090a14060408070e0405 79
    0x405920742105600207000c0c000000e102c40c4810720000c2c080c2c9e4088039422002e040d01c0c0c140301d810f4052040507648103080d2810101e802007415420481c040141c1003c07040102d000b40609240160000c144840f00c1c1825449250428041070608600f0750201b0081c202c000c1500c000360742c80c814058296480f0b410b0032401541490840d0641850210340c0600910300d101c05090403100d40e20310400039422514810292429061b12525000000d218403049401103407004204641b40c0002c1601303140008088405160910004400140b804141543d000d01022000c03869500da032004140106050700441003203601c0d145001c90180201100e00c062100c02d682290480d00701803905c61000d0107024001020710510401045a002c50074001d88070117240036003002030750381d60781c1c856617080c84240c2e000341c400c01041c014020003442c800030bd40c0e070b000c442c2c000035a141004800204510540b0741c80b40c03285840c42000001d00a5640d07004481c01499803504490446840e0071404d80064425142152284 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 259458767 1250 259457517 259457533
    0x912030518040209030a081b060f0103050715021002030a02070213050417070c0509040305190302120105100f140c01020d050603010b0906011e0212120403141c0b060405040509060702 80
    0x450540216130b10090040e029044802c01962804002d810044890b01da08400c4650b00b1008a801c02615103c0c92002840c0507403549182091414102c540e0052030301c01512505490280380c001a052000b516044001660b0b6900c1c401c00d10000c0c0251600294030010804c030310800211303240c11003070149000704481010b68182da01c03004610b02c0344420041ca5100d484404000c6880d1841e481c03603005000e41403051400651044c026031900b40401c4c1080400da010ad4041200c003005003c060240906072107a8190024824019022280f1034401c02c0410a0400c1c120101514150903205a0f88401009540300c4d90030b00e1902c805410300300c43c01802903107820070307094040c07070030014050044006850700100740200000307180343c40d10075100003400e502c0307810b01c08804030040e04028042124103440030b040b541401d2500900c8003000a02d0107203613100038041107085009039211041c48071940100000c0b681ca800c0081340c502d0182d9402030364040d243c5402c01001d1480401c2481c403503030744d66098500c0743c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 259460017 1250 259458767 259458769
    0x902090a060e0d0206250803040302010b0f1f0903120f020c040b10050304080c06160e04050f0604090c050303030a0c2007090b030a02100f0f0203090f010f0912030518 73
    0x862400482d00d40c40040002c01e4000b505101780141078181d49034000400c0140014245659501190f0086420342c00000410050660a200c0c01c041081d0468110303020801080004108220702080c079214040c007115482c070f40c240904240801954007000c1000c5100b40039501411500002c140e1001501030000d800c40c462425208200500310300404440c400c3d084542d0841d1142c100070011680708800b04a035540d0144100143c9100305000c90f082400700101078002002031004031081800340341044140024400841c0e03c0c954464419100094140064140010448810380c0459003500001050140d60003441d04501e1403010546c543c80d440000701c039410078188a03040171502c01c941000c5030900030788400b900b010094240080850300500301c0303a00056100000e9055103000704000704280c021076900541401543e25040c00510300b440c1c001c5012032540070f150342d015810000403070386010340703a405014001c0141c0940748034a88080740030b19014040d58890174104403441a070741030041d41e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 259461267 1250 259460017 259460027
    0x31507230708071a04050706030e0d081b0403060e0607030606020316030e040615500c03040905010513181b17010209090114010206011206150902090a06 67
    0x10680e001240d01d03051080c2c5515071190001d9008480340c10700890405544140341e1900741c0078601540162400628016000c1d04507003401c150303481d0340c3d005000320860164001e0030751544551440000c00b00d200b0121020746580c402d40e003008045500d001c1c0b02800141d00000e01d184640304036101084a26102c12040e0f0f56170052042c80200044003030890000a172103208510411a00540003041103625140d2a0301c06034001b05000e00092200140301039515100702440036007501d070314241c05410702d0304841c8550103810449080d240a0100c81c007668261502d6007110155090082500d1300d0300d0f10b038100a40540420701c1514498122200203490442861003191120b041341c608028070002103980d400c090781c0c9200441000e445c8200381c0018010b4011500340c0e04020342c40300042c0d0f24264881040301d180c1e81a0041000c0d2110741d00c905140c1d980005225056030440901101c0c0f241c1e440c9040340c064030406400c1e850541c140300f40004c4030411900641514181100c3c180b90442e00c41c102258 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 259462517 1250 259461267 259461317
    0x804170a02030d06030516060503090d0e06070515041214040e15030102160312020705031b0c03070b030106020f06061309150c0c051513031d031507 65
    0x22812000014004082265600620040c801401601d080c008010140c000315400390380144d0329504642d921000b80150b003c5d0b0007000d040070b420b1050039410510000d41c0d0300d8544840d020b0911118400072011a42c528094401e00c40d031140450b56280702a40c101003501205860441b20b50f00402c0c40a00c0c1a4080c000c032170000051106024102440c019140500e1500900010369100c4130791070410280d1820700041203a801401010200c1d850b1918005062052200b400e43c6c4440c818000400040e41c080102d600c16122070342c0328024144241002d034100b044100744607605200700c9400103080740460340074604072880d6409484811915424030360b11440210750740b40c2d00c80810880300d40284256400100614014448450103030103241c18a4101c604c42c0002d85c0103d01041c007100c0400404010781070030303d5407031040e0300c03810304104101907008181751a0007802e10924004012910040a00d412040b941c010100c0c1e0090100b41c010b402844016510a000540220481d098590340c0845100b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 259463767 1250 259462517 259462523
    0x108030a05161a07020d020c031f0c120e0d0f020d020d122004090c0507030503070305061c0b1005040c0816110f071d04110f03070801020c1c0804 64
    0x140381040700d40202e001c801e034201040b5031950140c01203040f110002c540c614400c1d4070a0700104906085160041d2030700b012804400d200383d00c220701c03220800801307200080419848400214030340c04405000d48051102c43d940402c0b55280080e00000e424002812401c90007a640ba00044410806412a26035200c2d452000142e84001c0c2c0c03003c40144540702ca18203202403908001060381c40c500840c4200d02600304520050b1a012a050010301da1078490940055418103001d403802da034554001e00140801800d0806244d42c03040052402d45079482d03003041c50340c6d001c40541841e0f2042d180443d5850783c21707038200250a04d09d00700403d035030074148101c04c2d1842564031442c044c0e44c0c071070301c24041462141d40c0d044204075145201c4250320b80104810454000b02c41c1c00780c4559410540700807000b02d5015180c11403210003009110210710500c0d0811610803098800322201440100841d29207841640850520340c0300050790004510045070009076824040200d20303100348440c0003210780f017000752005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 259465017 1250 259463767 259463777
    0x10b070209040b190603030801080706081006030e070e07120f06050604030b060604030c03030f11070b0711150333090f150a030303230403020309060f070b040501020a080108030a 78
    0x89008640541d0109078000d155a501070070704c40340c10944005540e1564400c5001c075400f9401032005800900c8108081e00030b901d80740d6001d15002005446230392040c4213120516a60300310034100898180032690180078034401d0b145550419040040922042003c0f07200e016181c0300000300c0010403805076070708884009150b9400e29013142c0700d01181724406440e85074885000c11000000a02030060900218007030f8843c01c1010610000240ca8500c401480f107059810540b024400d06000c6015250459000b10900a2031407100c2c01144600399103e0551031050b00200030400c401342c905032100e0f008801260164a0079100c00141c42c0d0520034602020b0303000000c140001e581040a0807241c1d409104c036a5451081250000414000202500280c0012b41c81d440c86905001d01c040b08200100702121400c0300c94078003074400940b40d0080c1c01c3d465100300300c00140590a00c0042060b0359903113030086920305260400e4500300e4000c0d40130011400108907128000030ba20706010056580f440320a880e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 259466267 1250 259465017 259465021
    0xa0c0206071b0b1003020909061b030601020f06090715030509070b030402151603030509060412050c1609020d150b0909040c08010236130209010302071b030209010b070209 75
    0x1007664118241e04500b16440000c14150012490450303100307029000c1518040d4641d4150f005012128800900c900d44d00d41c0264140612074844984101b141c095020381d0390385984400004074104400401017440511904061001e06000450040100c60050007600001c040d0b206055054038412200c121460b00006030400c5a03281071001075505c10b02c006c041c01060220b030a0551615003080100000c0c40c0c03004508002015014807a030303900100c0f030750000c2580c1d15060350396100c00b50306c0c80381503000c00401060254028608001c0100e0b0104064103d40100385c403440604001d40004070240143d50424204074107059050f04290140c65002540c0c614110500c824480c00790300140007141c0c07007181e101002a81d0002840902a040b2503030352040384080000401c3d01c00c15a06800d00704112001c2c01884140342d4070b92240711aa500a0800561284c0000f001a0000e0080032400341410001c481a4106421840e000c482035910848200d103c59882c0c0c0d07404d61807400740c0c00c8003e41084031040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 259467517 1250 259466267 259466281
    0xd14150f01300501060f0305010606080a050114010c1407030317070305090318060d0212180609031b01090203030c060406060f030f141630050c3d03050a0c0206 70
    0x10a412115000d803001145103941d46e1501040302c030b075643c81502c0c00d9565207014000d10780d0040d003064100f95110000d0240d035040100c6046003130001c1015074140300c099010b000c01c01001d58104150921040140c0c1d0748142e5a05002d03007c0c8142c80d0211188540c0c240c0004c1129000303105160040340400020f50030201744040050501150800003a400042800600d110580c140001d017604100603c18114500b007031032108003080425400c1409507003160003004000d0400005072909540d444844800c00070b0f10800050040800003400b035014003001520f504400c00000d04540507a10501e81005500d6a4188000c00c0c080140401040d034009441e1410204001c0329202040c18110420b030761300007112440303804007103005510030039441010f984402081c501304900309031000115000000000d5503039075807980710542c0061251180081184a0202018400c99100c40304100810084014000e1042d043e007940c48036000c200080c00e01c000240f140b40980a101200c18041c2c0081c2455282c0d90 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 259468767 1250 259467517 259467599
    0x4150e12070b07031817010f090b0a110903030a0203130e040c05012007090f0c1805060333040c020c150a030905070b0702030d1404050d14150f01 64
    0x3d8416001c000000b2003185003600c1080001004103028000c0800010640c2c0c2c03954203440d40024114025490840050f0100d0a1114000d03400b0f028440d0014141e4140c52138610640690b080b0a0f0701840041002c0b01041c4e0000001e00c1410850708010107601d55078040451514411100102800c069090400c1554000d004140c0244c1410200034271040c18480d0382407800c8415401070b45050303166aa44c0e009038040d44a140111030240c6030003100040c0c0f121581601c0f000314403480303008040000002d1500c1d0070380d41140c0000f040303800e20b900321807e8030036520002c0442e5a2605200e04d241c078004100e07090000684801110001e0302c1d04044004219940d58160006403142040c50384071a040000120184000c0020303003410b184040c1c0750301150050502d090500c030700e0b260503c205100e100ea10603080900fa14110388080f1070540d03c0411500c1c042c49007101d00002d8031114881c503a0b00c0b000300300080c00c5d460b125803203804a00029a03a10801d0f0341902c041c4a20b20b40f0a1001c3e0070030520001c242c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 259470017 1250 259468767 259468777
    0x60509061b16061806050702070608061002030c0307030306150804051e1204091a0a05010507080901020a0b0405010507170709060318121205070f050f0901110304150e12070b 76
    0x3109000c102c121494840300143d9a40c55084030690140c0c03104c8508201c0340d40704440d00f019984c0300400055040442c040c002500c09004188a16120118200c0305882081112130104d000825203031592510b190107030182032a40910944141c0c110541c030440c034803078070045100b17603002001840d0740301c0608000e0040102d5a041c80400b8000e0018212078000c00000410007000700305000101d01c8141e469180d00200c82d80c07482c5100718004401008540e0780107040d10015904411039564601c10000141d10300f20b070b1024010003000c01042044140401944540d10880349520ba4a46014208820011110084940c00041002e0b56000e11a503403081e80203141541242003820400b0141d61100c80d00850945041c00018000c8074041c0e80042141c040e5642015407420503848142100501804502030025040450040031404c007480d0780c454050a01d0013603010003075035662500c1e0741440034030410f040c110001141001c27804030b59906007080b00e03800300e508440c0540300301030526001725455444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 259471267 1250 259470017 259470037
    0x30c07180c050906090f04021803061005030307021e091518011a0a03140c030402010906090b0d05060118080610140f1c0c0e0402010e010305090d0806010207080307080304060509061b 80
    0x1007200e021210b0b143c5100030b005014810315090301480d00c189c201031902000500741e15580f06008800c0203070340c13400130607160300c44ea0458010303081802c1c001000d02c82c0284050180e92040a00090050700160310512030000c880035104158514000b040e10398180308280314a0020301040c0400300690740d04400641760180381481c010410908424004d034028405484e28030032014000709000031581c005607010700515680c104068a645000c4003c9018081d6580036101d40d91102c0000e016a8450b0b807900300740e120501c1115040544803585950340d01d00071102c002020f0039200000c40d50640084142e030701c8101c014182c0ba808a420424030800e5107640304021100b001000d40c01c0300103101c58903200c0c00381100a0304035601d40340c03d000040076144080100c1d4181031600062011a030781c042082003e804560405070140c2d00d4943c0104d107442c101e64020409408089007843c204010400194095802101d0510460725100300e05a180e010a9804107610007d41140c0300001140741c01a02c5070040c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 259472517 1250 259471267 259471279
    0x91c1106010e011706040b0a0c030b03160303110a200a05120105040b07030c050304020f1c06020c010b030721080706060b090102010e01020901140d020705030c07180c05090609 77
    0x41618428600503080c0c10414454400c0c000520078101d0400c4060800f905410040589013400e031282821444041c01d00b1341c54a0700c860245d404207004ea00f04101c21040074085901d4002891858005410307140030490000302014007000d41d010b8001807029840743c101300c180400c0700007080901ca01402e480c2d48039800035804240010186d445c440c9140c10f0010440010075185881d02d000d51034824000c2800040c076150a00a6210382d03482000d40390302c00d605070b0300b0640003001403002030300003c4800c0725200c1c80d86070701e0801010400300ba0003805071001c030a4004d0201d0807242d020580c6406913402280603140c2c06014407401e0b0340707602024880c0c8900459806191012076100c403820341e07040d0742186000c00400110703000c541d40d0900c00c01c000d21910100031420140d80c1da000802901c1540619200350a001c6215040d0a00c507604031a212540b040c1180d03502c802410803ea115141d0b4811010041c1554810002456080c010140c1740725003682d03070902d0308003a00c0c1046400e4000300a090f401c18 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 259473767 1250 259472517 259472537
    0x11a1306051203180118030609020f0306090f01140c030f15130c0807030603150c032c1e100c020f070e062106040201031d0601030305040504060e091c 66
    0x5111941242d203100701c6840a15039500605107101c4122941c40308141c100700c4070f01035040e03800001034038490076203501085c00b103000c0d02c050002400d180702903002c4075810302512050040c189030014205401e808150024004220007040d210360000301100c500f000d40b01c040000500701c40c130a80340c40da84100190750074440e10341c00c2800b0070041c030004000c04103041d640c1c03000c184035182c214800230b0384080c25141c18020b1505503690111020170b00e41988510f00c1d2a81041e02c030450190700f290b041c2d8900340a640000000c0c041c0282060710060085c0b900a001c0c0b260300b0100444046c0c040708010607104020110800c101002000510007a035440e01180601c0b00e40340b00c18841031110388010b100740d004c0c0030194100b120400c01c0d02c011600c804c43d040c0c0d61407803603101080e0700460426031080d02400d0000e85c0d40200c402422100304203140100560103000008802c15411201410640d034059904005883d00d601c0c140c46c5a0070191052406a4041c020304142514003031240d405d84002403a0942c524 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 259475017 1250 259473767 259473769
    0x4080d0f11030c061005030a0f0204180b1009060b0304120804080f0a080106020615090402062107030905160e0415021e0702130c27050907020a020f03011a130605 71
    0x1900030100840f20340c0c01810900c00740345141c0743e0724000707400304401415002806513103112082229400080c001d0343c9500740402050f80d006030880c00240c000300040500e16200c22507492222950060750455841e084004c2402d0b03059000790707403159a006168400c0341c1030310701090b00c0041009004440c0098100010380c0c10385221000340c00139944545412505504064010307082136802092444080c070300385507180440c0e0f608030001c0c0d0802e80555509998440003004410741c10004d40c407901c4500212400d001d110759240c0e00c43c0356030901500c15100c200b0340010b4400d01540c40c5200300607d20071424040ba002c541582c040c0c0c4101c0003e01001803600070b2040c2c80341c1e11041d10340d40c117003410a80480c02030b0a42c104240b00903440c3c00c61090800a4080147d4050440d80c146001d91841855822010401e4110610124090540208505110702d85911300075903494503100c0882c0200240a0001c880d41414010403202c1851300003410440c100c07200c18440d0910818040303101d4561541c2001404e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 259476267 1250 259475017 259475023
    0x1201170c13051b1c0506060415050307080106081003030e01030b130b011806090b03040c0302151b060c040b070f0b040305040e1501020703290705040503010c02010204080d0f11 77
    0x19a03488400215851030030070503c1a0081103010b5103000d9903c100080b00f000b0942c070038070050400721402c000810361946004103181e40156004003000e00794119400310050341203006140b040100ea0381e0801e880c2c0c0c03104800c541c000350540340543c1c02d5091480500019020310623407444180c040c90700060040752200041c01d16513031800c1c5928800d5562402100c0c40d6440701040c08901c0307080d44498031862420000034030780c4507a0b10504100c0725001c4003160400c40104036000003160004c04000d1a04203da025551590100900300780d01e1420007612400e490000ca002c51107003990300e107210b080c05d24000700070340140d0001d8000c0b20102e6020140100080c0c5050807680164082e50300c80b0f0b03c507820941c003220741c0d15001d48241408400402d21141585e800100b507070030f50f0740c00b075405100d1040e05649550703050005d10340440421504010000c0c240d5000c00604200d0324100c000340170480c14407a041e03080b48114003038414035402840c4803142d00e07030184a140441c070761075140a204242c000540181 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 259477517 1250 259476267 259476289
    0x705031e030603010f02091c0c0b13140f01090303180306060f0303080f01080a260d15050117043507060b0406060f03110f0714070801021201170c 64
    0x20128001105010283c2030074450a0040141108210301c2d1110b408001003c04017805030b018500001c0300b00c010200110342c00c5040c0144400c00c1d1030303074545000d00b10321882440b1038003d405480005c030104003800d14000020179034050041c0c440301411801c2d81c40c00c49111862040c0044c1d916040040000065560b03c0350000900342c2200d40034080e81185001020828007130314030641c0c00b181000500c040f81c004220a031020303a105207054020780003034507600001012008a95004000441c4004c40031009400c110711075036241400b41601ca455034011741d28003e0b400011745030614100d00080c00510303014880b0b050b01e801d15003070102d000d14580e0310104010085050000c41d0310f010990070100005030203101c09a00b800c640a00000b0309001004080586402c0401c04040d1241c1400c10f080018408640340040c0c80141c150b034601641c148039503460b08c20070003408244120f01000a1040040c402e6400354440a42d01d110b5503443c0c601080d00710055500340201a002e400c0850255548050620f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 259478767 1250 259477517 259477567
    0x41a0c13060306090c1103030c0d0f0f09030f090605090402031e04081201120816020f100207080709051b0a1e08090f060103022b080403030203040f0f0b0d02070503 72
    0x4641d5074185180c1006888010074945c050000c42003443e0304a06022080e66803021510803450b46a6001c12500307000f030700c240b402c084040e510303090000c11b405c06582c0000c8000c03030090721009100d0203070301c03000c03a250003080c81910001401070041c008d01f454039800540e00070001001c450f1004902030040c0380145001e03141107132080c80c0001e1882c101d0b900c0120346c80c010a40000345603c200020388640060f8414940350f1078010764040280c034210343d1580300030800383e50003600d041c0e911090000081d5940096000307103002481070480010f240c074058012a4403414815a441081003000c003c0f0200c95007005030000140a200901025501080d0302580d10314050f81c0d64032101828003440d00c9060103009d2254180c550008030044c80541c0307514458100c40c0b414400300144039103449000080039150414020301c48000002c00200340b40c0d00002602c140e40d004262000d05d19503030000b00c2703402030302803003000380030303c020b00640083c0940795001d03160040c05401680d1403c031403103005891001c6580203034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 259480017 1250 259478767 259478771
    0xa0e0f10090f06020f0d0309082713060302241b24130222020409090201020c031c0302030a060b0720010201140609060d020d0501050a050708041a0c130603 68
    0xc01c0180000d1140c0c070010050b60018022117170a80c0602a2201c83d61881e03041416222524107040010160403181a009a000007103091407110751540c4a0411010805101c1c40c03a80c80203c0345102184240c0080fa40c1c0100080704201d54560700d00e0300c240784048000c0f2195000c2c00321704102100c429a00b0104000d0001805082e080340040309010b0040348000d050649281c81044810203011614042d00d40d011607141c032400240420350202e000c4050029081640049400510f11700c0c0b5070407100d0441d01c00d07000c2d2010b40c080c5001781507842d206042000c1400c81e510410301101741c003a0340250b030001c000c003201043c400e48880e21010a80d0255a081368a0940d25a01d078581600080c20300f11001c03002d01c003e1021550261840fa43d1100190185100e201544081440ca03a5a501280c0e1042e1340a0038041c01001c290402c2ca00030801100c090012a062a0000380c0c1c0030f210b01d40c100e02c0b403640840c1540c40c2e0007030107a1154100c0702c01021301410407020042d03003071250366079103018005114581d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 259481267 1250 259480017 259480019
    0x614041a0607050610091109010309080c030c030702040e010509030d1503140607090e07021002090a0305070f090b0103020703120c0e19060207050a470415020d050a0e0f1009 76
    0x3c03804c9174a0320740d84407000c0a45402017400c00c5410040442e2000407007403801250b0441c40b402d1412103071158a0f40d041a500c00014103d00d1340c5004370103008240e0086604001882a0003041c1c3c2c26031740c04440d810540d030001c00606424118980c820079480001c0c001368400da54403680d4805500000d42e60080d83d65028004200c00581c4c00440c030805880d0100c2eaa84050400c241c01075900d61008151030500c503008510b0b20807070f40790303921074030000c0da041806c807035010f6521401034803212546e000da0f51145003041403855030355009c0d000f02d4a00325807559a58100b0380c1d009000a0040c140d00804034104415100c40c201540d842d0020400000303a2041c14410252800401030314100b03165110f0790049200320300401c5044018110800300c1e502c014403c510b4021700190b41c10700c0d41100320000004e40c0c6082418140c0948401c0540140c402401032403a0341540075070160b0f40d8900f00b4081c0400030b9001c0111000c0b03244030304010b6060680203021007000603c610001807201c00e82a81a400207003112074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 259482517 1250 259481267 259481281
    0x1050a0b030c010f1409060f03010b1b03072301020705010501080c0f150901140c0106080114070c11060d02040e04140601150807081003021c060b040614041a06070506 73
    0x49400400134249600084079801001c0e0140c104005145a140e9001c41e0810309038071454115001c014880900c11303076135a10350b002c500454000001040c07501e0043c010b006c0c5041c20020448400a8110240040c00742c0c078109481381140380c811000c0e0780c0b95000c2c0706102c0050800d004050180002e03101510307021100744148200714030302c0025035104641c3c2c003010307140b070340003050440c0c036442020302c1c0c51007039070161817050401c41c45241c2c2031101d10361929400240280b0103511410060b060085000e03001d4482c41c800700c6100500c50000703041c1140314840d004c0e15190410092a003e04003440c00342c00c0a540302d00a8454200440e4280e80f05001c1170140e800c0c1e918140101405449200e913048502080c0e240001d0500200811040074041c043c404107040060b0f600004008603401002c4202c0980c180c211500c81c403106107811914a410308050030094502405180255410700041c601c0c001113078010007014200b100844000403c0242e403101c3e89407075000081c12130038018401001c003410301203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 259483767 1250 259482517 259482523
    0x1f090516050f03010605060f0706090f03020c010306090c0e0f040f020a09030507050102070b1602150a031406011b030c110402031e151c030e130c09080102250c0801050a0b03 76
    0xf44640d150260501055a60700203694136403000b20803054541000b403418800500d000075014000080ca040709008040e800a90401d101c83e007070340c042c03000c1591241c0f16020baa420032040008101030001c1c0c4081401c011210880040b0010008035000702d60148104c101d90003240d4240005d5810f00c01842030080410040740200805e02c020840c0d0740c580381400045004d5032101c280c030012135031030410565840004a004218855298a545084041d0098000c15450070880030450070320000075500c1d80110300b1184030300004603540352150380b5680d0840d4038070701c42a021a20500401b41003503540e200c500c0a14071806100c011500c4041c0c00707401c1801512001040c010211026420075411703600c0d0003d02c504811030300b41c400d550030301c075500d0700b40c03803446000d1326594011300c912002d094a0782240e00185003003082516582c1441d038881000d94240c0c03086561010f407403000068a4684404c83c514292040340c020a402d030951503d072650030b825648107850b200265a200c9c015408645024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 259485017 1250 259483767 259483789
    0x424092a0b030103050303042a06031d16090c11060c0703140f0f0304050a05160f050306041221060e0708132402070b040b041406091f09051605 63
    0x60349158159891a170700c0d5544c0e40300c003c04c0207150351410120303030401c0107040c110101005244000c0828803526240000d005140c60380c614600c0c002e03405442c0702045004121200788005520304100300038101032207040a4034190350b00b8000c100804c0b180b0030341003000303002c0c16000703404d00d070000e0303039206071605000340010a00c80fa200410b403020884003e0714101b65088520003d0511842d40e125605da00b09541440d101da40b0144c140d000340c500c8010705d080c18180e0307a000d0b152a00c2c0110700060300c03031050541c0c80b02c044800803e0b0001e42c41c204803002c0d001e003c400c41e100f070b080002d4070382000070018500c003a5005a4491120f400100702802089504048040e60201002074500c04043c800d4031a0404100060707074005600401c0f2500e0b8092101d5a0107e4030701507045040c00c011800c007458011010001100c059400c1201800356508004001c140f180c007400e20803008241828990400080804041c140b40c00300316510928400020814414481d0f0964602c20020445140409001c081808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 259486267 1250 259485017 259485029
    0x30204060b03010b07020d03050c06070e040c09182007050106031e080706150f0803040305060106170f0903090d080d0f020906040603090609061416080424092a 70
    0x4140b0051013103415000580c2c02c4240c04070350102d03002c0481d04041d640391041c8150f100d0a40200001c0042a64108060300004501510208a0021030020890b411103540c001ca4000c0140c14050300b00007025504081c02d90350700c2402400c01d00100f641d8034080c6a00c55a07027143c141c3d44840f820801e101c045841240d03da452440c5882042010b540d0b10300130340c411504000c0030300c0d580d15080c4c0460060010154003520280764040c81a5403a902c000b80d491300107102c01c81c2d50344a100d001180c0b003803040c0c9840c01420714540742502c650701c0703103a444140300500511441e95440280b00284a50741c0e2915140d20171406882065903c0074610101401e564958041da00164010402c1009540320311044070200c82052030001a000300515114014001c0520b02400c1c2900b4001c2400c0b00300001508a4050011503030484442d60401c2c3d001d84031054220f03006441ca00d4a1070140700408410740c00034041c402500000540300203140d650140d90500b10700f11030000d0402c03042c400c4040c91002220805011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 259487517 1250 259486267 259486289
    0x18050d030e010b06121504020a0302090a080d140d0902030a032604020102030307030b03160e010501120506030a08031f0f080d0503160c02061306050a0e0f0904020103052e03020406 79
    0x250f0040070402e030f03200f508a40040e00e01440d001495400e01c884011074038440092065640300700800c4010040e4004004062080c03203920000605000001194000c41902e40c079503943c262200b91403d480c54120308030081d030280d29003403204c005a80501c11f41212074483e456042c03030b800c0c06c4001c68032921030034650b00781d603003803194203110160fa000426281e03c101249004600b480b010b8000c40c7c182a417100002800f07215030758000c0740c0003650225050688400380d0750340030098000103030b04c025a68240c0d209501034101800340004128400000c1d580004007103103654884540900074032901e8035035400b07440c035440b090310248a60b50040c043c07000301c0c01040ca44141181419800e010720f441b10503010070b0a010140b10004215110803050310142025100b0b401d108070341d43d4202074126030000349880d002501803034940d401458500045a940352014001120700d43d559401034000f031001070040c41a200c00e0715800d21350040740101c0d0360071785084180220030301440e40c8140801e460300ea410402d5004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 259488767 1250 259487517 259487531
    0x1090902010206040b0a090209040f060507050f070f032607020c0609011b05120705060f010501050f030f060f0a0f05090a05010303021b040609020d0518010b210118050d030e01 77
    0x307030340040d0b03c5402c00d030040303012000380d03d540c100034009044140e0001c1d003140d9100100405d10203c07054422042c0e0055806202c1c139690100115428414441c011841c85030a01c842408035941c0f1a802c1c1000d442410030b0496404121003c0d0f0315010b000c4808003081c48100100034025506014a11010b102074030802d061804040010301944008146540c850300b0716180c8005108041180d005d6400109a08680e41c02840c14210340718541114000d250102060000a595210b401122140141c4405550441e141d42c8040c1c81301a13409811140d0000851588000d15031300c40e400e80002307061517000c040109107010b00780018400000d0450329194644001000443d0b000701c0c030042200d80c40c03110b940c02400d500002130010f003000d0700f0000c6202d101282000850b1a560302050203590301d02500d408150711201100d083c0c915907883c054100042501010903d00e1360412080b107903020344000319a4104026019001c0866070106407050762041a00080b038a030140318461000e05c4000c024402c0e5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 259490017 1250 259488767 259488769
    0xa020a0902040f0e090705040e06011a070b180a1401020703030b190302010c061103070903150e1c021f0c090f030f02090c0c16090f2a090f03031701090902 68
    0xf500070340c400c03c1c4400807403400140020030306020745070280400600030810b00799080030392a41c0e50002d004801f8001040311482419400100c2528410380d441314101c5659902c0429503400e1408510740300b03c0c5031041006000001d40d070590445404a0240c0005071282c6140c100201602c0401641c58000e0900c00c142c01c2c4030310300c1c4808400c141c1c0d40a007002c651100062422400401c0d10b6020800c000030040b0522110980c001844e40440780512880c102d030401c1489102c1c1110400e154100301340c1d1000c00e0752003010075192502c0100140c2070069402041d200702c003844d8140820001030484070b81e1100e22000c50340e002030140d00601402c80b141380c03020303041d5035880e0040203440728007078031910307091000030307074440801c82240c14007182c40042d18500c0c901c0102601e810026402400d191609040744080d68200c1c92080494814004108a200d080a00d0450100b44000c0510b04100002098081641080c00b5240402540301c0c0c3c2d070340901017400058520011406800920b429810a5008405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 259491267 1250 259490017 259490039
    0x2070c050f03070e090706030e03120109051506041409070f05030f04080408190605070224041407060504150e030c040b0418030203092107060503041a04050a020a090204 74
    0xd450040d03403503880310380380800000d1800e05141d11503005000c0041c10484003480202c1d80e44200d99032928240f000a40348501a078403070162000044005a92800402284400f80c0255130002100e10892500040704804581039900c40d801c900a03403900e2465840e410b003030041045034088000d1a1100508400480003003031440003130040750110b00c210000c13406010030382e07040394000c00c0302104842d42110400f03088001600c1e00481941d8051401001400840c004111a13518400600102c0c01002e01e42e040c10030a208082d0050b03a180125070043d4184250420a10f00076080d01d44441e07480f01d1818020050120750704000c00100540d0f076170f1310b4600f5140004c0081d04a40111404107241c2c0481011400905900d845060301d01d5804006500f403640100091a07610003d4506400300c00711100c1c00f0300407042c1c1c040172464540c0190401c0001c684100081c0d900315104660201d51300a00c220b02c401c030210144c40036622600254128411490310700d140d10000c1c0080c4000354202840c014040c1c4d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 259492517 1250 259491267 259491269
    0x501080406050603070504020a031410050f0d060b0301090506041103120d0903030e2509020403021c06020c0604080d1a0102030901050901050409050c130f03170a03090203070b0a021002070c 83
    0xc4419102c10106506540a125100245c10050170443d1110115140140139021071008401c1c91004d0320085040021100e8003071040e50301c060003c8802200c0e801c14003906d60340200c0c00f40d070817680d078040614056034280a296a180e02580042190381000e08024042040401e0700da4400e03800911204001801c090982d206085101c10029000005090940c01380101e808000c8160207462500d24171403c41c0401501c030790001c20071b0040310b03035150b0501c00300300d102c4ea010196122072a01648000700b83c0c481c488104030352044201500703220001d1350080c038101d8103480c216039040d80440c0700400d51030349204410032945c0380c00d8030304112241d010020b901d034416a01154100040050803044a0340207004a07001000c081d0350800c460319244510103680c2d004107044456103821800001070311840b41c0400d4082d207070010481c110700d24528060380c0b425444001424245034035214408090f9030140f240500405400190a65801e14104000e0034020050094100c040c0306002d118046001820a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 259493767 1250 259492517 259492523
    0x40b0418030f180509130b010305010204140a03080d18061a0f1915110f1011030408030105060d0f0c1101050603010903090b0d060b0705030405010e0d150f0b060a030e0c0a05010804 79
    0x81706511441c450120342c21140e440a00200f404c1c01c000000c0210540c0240110341c0200500303801c0031000c104100010403584009420b462003845250503580c5646c1c003451036500f10488000e01e28807245c1d0782c01c3c10340749401c0c5001540712810035241c0203420240c0c45108240d00445408032640d89084050410750010301400501c019180700701150507004411040b80c0e1030141c1e04407040403a6444020382d940f007903411980000b0b41041015802d0f1401442503034000e03684040541d06580c00d10060041c0f41e0450000c4001054480981c8021031049100b146901299666021000a104140319003598005807a8900907803500d070000f4082a4060014002d45a020182d03a5950340f840950601511460b0401c1e01507020000e5150304011000006008580b030a8a030901030f0150303d41005400c103803040018dc004d0903945108030090b1550340c44003686100d43c150000b910004400411543d030404040c0d100401d030b03201c0c0810125101000640d2040d0004c54a03100610f00341400204000701c017034401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 259495017 1250 259493767 259493779
    0x2180405040b0414100609090c09020c0706030c1403071d031603110a0521010e28170a030609060504020313020603090109081c0c0309050714040b0418030f1805 70
    0x3404500405014030581640c05d03001c14050607807a00440d8000b4070400000325504504414002a01415402034070261000d110241c010319240510640141c0304c4440404100078030002c084581c00c03a02e101941c022805980c800080c114a01c4000341203800503512648283d1091041800b01c008040a80e400e681c0e200504207c2c51000d04c0108803251010b4200c15841003c0f001c000700b19840c0c06200054202010000b48100e61000014a489942c010740f07040003002da900d041c10182481004544c0c12074440c90032440d41031000c00142215810000b00007000a88a40702001282414000c180281a0890f030131031541c10034204004903104038000c0240a0b03400400044c60f090000e612000015400009607641c5400d07105a40100c464000c280f00101840c01c200305403520310a10861340065803100081c03003414200000391014a201c940c1540c0e1140d1030b2a00c1544a40326170141051800a044603101e0000462401604040181a42c90308102e42d81d5031144909009030f030f4510840310282c0719 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 259496267 1250 259495017 259495043
    0xb03210307051b01020705010e060a0c1407031110050907060e0a05120708030c01050a1805060c220909020102071d06060a1205130308070e1305100302031002180405040b04 75
    0x1d191a030155101041da01d03520114070b04c1b046c8001908817102200302c04050b83c005607a1042500f00701d0302d44100e00c10004103400b8401000703a1b0180014074180d8020305110f01c0c1411305140340380c542045882e658032102e4840041c440f40340c0c410001e18024060342d0801101882c070400200e00070315118418203105100f10036a600c0c540009020000180515205580d521280402d800c5d0107010103545184106190410519090000001c00a050b60b4040040d010f00e03280c900700b030710254000040318217400140903480d00054104844002c002c1c1880040410150481c1c0000b908150040d0b2100500942c00b158420541484401d02903210108441041d110034907484115006054010305d80380191030241441840900c2d03940302c10710513100e42d44e468201e50368030720115603134403004048503004080b00c281244055141c0d08196800a80880d4625401d82e59400292a1227003000d1401d80c0c1c25400280e60200c2e07542056900600501528244502e080c07030b5441d00403200c40100050020201e00b42 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 259497517 1250 259496267 259496287
    0x7110606012c011110090c14010e120c030f0c04060e070507030f090306140412030e0a0f11180702010b010201061503020c010b130605090105030c0a030b130b0a0b0321030705 76
    0xc4219880762010202e400201e001c01d161002070410346c006541c220240d03140000e8003c0b28402c10b180d0841c0603901c8100740040b10041c44002c2400001c2401c00340143c2000064507202049104c0c541a0114010240440c1d00d0041c402124110340100c4103440301c040400c09019048001c950307281394940b83c0001c828601e54001c40310011190801080c990801e02e075a43c0380741550078414056409802c0c8501309804024090b07040300c28040411405401815112001c00c0d1302400c01c21400e03000341031041c00600240005500c10303104a04010700d010b0380310203201c44254244600007100c00c0038002000040d04214001ca1419601951101019000505161009403c0d04160070711b4202602461220b11700041010150400d80a032501a0540600014192500280c40c01c2100c1000e07107800d8031141191600402104000c1c100803914110702100800240712802c03007803240b000f4110020b01c00ca400750805007050241c00307c100300c13032040c0c0c140c1c2140150310004a03500a07240e0709115a807248040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 259498767 1250 259497517 259497527
    0x18040501020403081c0b04090b180708030406021609060b030412020c090a060602010c080408030f0601051b010b10051e090301060803041206050f040c1203140307110606012c01 77
    0xa00010403884c0d020400e03640382c240d4254882500340c04c4420034001508084180310446007040e801609000c011004100040c03003002d140c0808100d2502903900881c0c5840c4414a180c2c085e600000041e80721100300000c10782c4441050300074001900c000d0000b507140660f400303902e002c050400380c071264002107480016802000b04209001c0e000d0403c42c554902004400002d03c07441c422600954244036a800816200e42ea034140b10740d80c4840c0850454848000650110304002c1c5000e0501c04c0800040c0284091030084072003c00c8400004101e150b050010b002103915150259401d11205008032500d8151140d001c4000c07420340010340e9124000c0c080041e000d800140d0015800c0e0000040c082006040300112403115070240d2024000b80e00c4d074107201e000c01d0200325005840703403000c4282400006100c0982d4900c00b800703460311603400d8815811003002503005450b540040740c013202c1d020718182c2c801d00416038000002d003010020380507040c1a01710200d180840035a804805400200c0607a8051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 259500017 1250 259498767 259498769
    0x4020307030e0f0d02060a0605030a0609030c15051506040b030601030905010b0a08012403020109290301080d0f020f10092102030a020c030106061205041703131e02180405010204 78
    0x1042c00c540000c0c40c00c01806448465008140005005250010309103640342e00403101240d0000d0000e00600c82c0c00e031510b400800c96000e0131410010b03552020000b0600c01290b48441c1a0707544000207446c109608824518464180428007400c1e0510041000751740c41c1c03068942c00b0000b800c02150511291070850b0060180d090900d40c4180c548402003130310041580041c003100e011088480c0340e07454011034140c1e0b130800780c4802800a14241360a210200c0c1804c03a91004080c517100c0007910501c22140655643c000745c0040340b0960102000d4034685903c2901c1d640c0002e4940050b000411540c00041d48034100a91151419030711603e900c4200401c9040840d10705182059804d444009848020344a0348400c000500612610480c0c0545140610403c01150f0850300c030850354a0b190b5030711802400b0028402d40701c00d1100c900b44045031503000700651145a071001e00b4984140e09140080100407000103c051401c0c0c404600b6005071503143d1920345080884000c00d007203070b48500d0039901a04c6a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 259501267 1250 259500017 259500041
    0x303020d060e07263c0403110c1e10020f0a050f0708030a09060806032401061403270a0c06020a02131505120c04020324100e0402030703 60
    0x402e007007100859104801d0610104004000c00512030b1240075101c003003000365458120080850f6000740341400404991100b680b0b40c0040e105200c041044588a0701403c4805802151010214103100f6006120300c4025440c02c0f52541d20854409650f040a40d004060f0540507603100c01425600314000c20031314140501280843d2103c034024901543c5513400c00e8892138443c0f06a881c00f003010380012060b07500b410880da035a01106460f0080c01c4a0341e0700c01912250b014003c4141119000040d40780c40a20300340c1c00d0700200700039454080c0c000c12198a2851441c100d2405006200321080c601c071000002d500f400e203200f8459062540e0190401d03a07100002070001d5110900010031503004503074001d10310b0085465210f442004c2404109440c50000c1120754509400030071301042c40c0041d003940d0700390301c00c400701c40d5012203890118080742d0054032542d0760810514841c40001101c030110000c3c0c24002c3c0e510884040030034002274088000080d0003442180c0100c0002c100500c42e50081c007030500707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 259502517 1250 259501267 259501289
    0xf010b160519060510080c043306110a08070f05011509060e060f0d0201080c040b1b0f0a020a030f020d0807030f031a0d0803100308031014040b09040303020d06 70
    0x20b400150591007020350600311005030a08000442030884c00c1c216200711040e250240111030303512001c000003850019404128401d007900724040c07583c11119000315900d000c0c0c800c1d828950420b01e028046e80318003404c2c95095481014520300059407013040d548041e030f020f4a02440b504051812501401c110740140200c00913031800098400d00175002042210904409040d05480d0002486020020b00700500d0b080442d5010f2000103502c1002119803100c826020b0b50300707194a4072030480b00703030344010002c010a0701c110321149140ca00c144400015917420500404c40900c655000c40c2400d4402c0c8400361407500030303820081c255155200d1201060340c0c00010140d4881172868054107903200103105100207880c04251202c1070a44100e140001c0e1801480720300b07003018079640d59465510042c1000c0440300800400400100080c010798041c040c0389909195060804003049484c0e0703580e0038014462400c0140701d152d6a2240b81c2d103150001d8051402603a078940d87c6055002501c55039000e2107842c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 259503767 1250 259502517 259502533
    0x200705070e070c030e0909010603050f011a0a05010804081602040903030608061008100b03010f020c0f060f071d0102160902031009060305060a2a0e180f010b1605 71
    0x100012400009540100841103407a0302d40c02001c07619040c4210004003c20040507001180d440d04000c4070303603ca1a00300001c42e100740c0302d0740c0b01420104001450b4440b41c0d12150303044156814020604043c80003501c6811000b860280020b00044016002505407900011446003110741c811030640a00c0d000340080c003944d5a240340080040625124550b16806110301060300c2100c0c0428040454100b24001d002d48001d640e005002065040e02c00c80c0d0640da107840b203503020031590000d8141d9460a0015040c0030210880c014240040244484040d80d04002004030480d0007000d00c4d80b031401031301c007803200740345030800140d1a06400740b000c00d00341800d10800091162664000b540302d94030031171004420550740c208910a591140c04001c00310b030041400508582503560085440b070810455100a00c10503898a100ca12468030300c03180001e00105100d0404e06203a0015203c6083c11070f1400307542e10f0000404001c54806008440c48002d00040c50120150300042d05010309030010291502c0c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 259505017 1250 259503767 259503773
    0xf08040608010e06120a0602090a050409140105010608100603050709091b0306060504060210050c0f12040308060913150204081027080313080d0f0b2409042007 70
    0x114800d01c40c201c683c4109500144080c14885080303080c2000b0a0020801d41070240d030341d00c0103500000d0042c0c0e00b20006408c0083d1a0780c89000b42c00c1c1e103900520f04800d211260403909801e49030141c1288003030113070070014060348441c2d10031060100c40e82c07031038005110f40360b44030100d07404001c0f540308500c003034240121041c0b62100000350b611b0450154a00300300d2180d490030140c1d0f103401940b007002c016030800b1b01143e11b100410f41149a00c01000002d04e0f290000ca00d4010140d0b8001d00280d4014040841c204030802d40c001203c984c00c030800b1104000300d45000030200c03001030080400103080c01c1821084010200c1160143c5000d44414020780f2080c2407142d0740c50380201960003591533007042d501000710000c40c0f10383e03004c0c8000b0340084085240d917588a4000c500950112030403501100304100b00b034401c0b8007500c54999011910400801c1c04484582007003000512282c421070401c1c003090f24291941c1c0840c3c2110000c04043d100416003480c121101040d90000501280103000c1c006503100070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 259506267 1250 259505017 259505027
    0x13150302040905010b01170c1b030c01060e19110702010f030e031603080f010e0106110304030b010e07030e070608011401020712030e012705040207021309030306050f040b090a090f080406 82
    0x40c000c400c1c0d030307043d0031100540c0d41c0c1c0001040c10f40d04000320000030007085272075100e044218039522207007008483c5882c103018621401c4036a594810200c80514005011411f1721240c00030380f083c4100b0b4014014804a00f40d801c0d00c5104004000303040c04880780265203c98000c0d004415144560713010390342c07501c104045170200101403880231030014179800e0000da900c030012001c1034182c0304c1640c021185e61f0300345401565150a84001c1800c0c504c07090100000040c3d4041c1000d018000e442c2c003d94031424204009000d9a9a032114242c40d0b80040105001c1703e540080f01904403040d030b000d02c1c9421f80d02c580060381886000c0c2c001e0a9100c0069116205040c0c1003a40240101000e80c0da00316000d0b00c0c500d070180b0750050541c080e2148890318070b08101d1850513030060206640003c24418400000d44880000c0307a901450403400300f030711070104000e00d11b00048801c08501058070240545401c130800a01c0d9002c004100400710360341c0741041800d008120103c804215402000e00c1d41e03e949910021702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 259507517 1250 259506267 259506281
    0x60504121a011502122505070f1e080102090310111201121202071401080c0d0f05060a090b0f0d0f0203030a030203060a12051c020111160b090c1315030204090501 71
    0x241c030800e442170310481ca0200c11110751410b421201481d5101840310700200c2050844161458880c120001c00c610703074144890b400038074484003002d80003801c071480b40540181580c021191a407040c480c4c07074000e4030042132044044dd0001000504c0c01d011104103001c41c010307445070b8001c641c000000407402902099194100e42e000e6041e5482c0309441c214100e9442d205401011884007036810800032950084120542141035146424142a250386080003280c1083d4255010192541706029013401c00d0364a01c40a01700140090011340e1950020416042e001d101d441d0255011341d01c0c1c10b05003c01d08184c2115a036008040d80d55035420028001c0207508140d50241c4181c0d06e4920010b511740c107224010555660000242081d40350910343c038449040340322003100640d525060340d840c0c401102d03001015805418003116901c4502c03414001300071f0070014095651944081c610b510a0380e101e0500100c94100d03a130000c01c034440c200c40d900500304078a40c4001e40282c100b0440c2c60800030103400502c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 259508767 1250 259507517 259507559
    0x20f010903094403120f07090902030c0f160204050c040f081f02070203010e010e0304080f03090f10051c02040305011b050d180f050a050f0304060504121a01 69
    0xd40e15120403280800da04a02d0340349004803000f8802810040301d004501c0c10700c0842e07000141c906058541c1034145855200315103030405056201c081100040d004802c1e4406015850811400e40c904101d00000d00d1044d581104001c00c0b020501512a503103000384200c3c100e034043c00070302c00d90a204c10021129085400f55002809811602160301e00002405440e050b030030800c0d00070709001040f200300082d449184d0998065403115141480070000b400b400c94280c071080c000315a40c6d49040ba40a060070000404400d0700d4000704440246540c644d030316031078400b5048980e043d0704080d103c801d445501c5a030f01006810340840c1400c448260143e030281048a0003240280708a0b5002040c0a14009042c0b07c0c2c4000f14000b4000b40c051549994400d280f00640900940514000c94444025440810f00c2c119256030010b0038200c1001000c2c1b0264480001400046040c2800c0550207809405240140700b503442400c10100d081c4111464085929802410038100558541482d82c6108040481d54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 259510017 1250 259508767 259508789
    0x30a05060610030e0307080306041b0e100305010e06090c04030507080303070e0607031205150d06050402181302131d10050718090b0102070b0a0503070813050a0b0601020f01090309 79
    0x461126000e4000c9103803654000c00550310340311b029980c5002c2c43c0c001070b08440d08207940300c070509540120000514a4800b141c0c4510340d074189418200036050b203601156504141c00c0c0700040140280701e648464005a00700c03485d4641d9070b0303410380580180c013031503102504038803424000060403400070004500a144c1ca0b9644032145c079100c024414944940c10b07000380000d691b2135006410380f52a41c0116000b18042408900341e100020010300044058a015131310341e035840040c40214941604c3ca8088113080ca00003c80740d00e0440b042d22201c5003134440103806041c10000400c461146075021065916809100c5411100600d18090740c6034036030080414030901c1c00c40421115401200000794190840503180e2240d818169a41c0280043d00b0034039040d882a00c2c0c010070b00d0240c01000d0009d000c5c8030b9513803c0d12864189001400340d10050f040b44104e0301c100e201c440108101160700751030742c0e0f00120410312941358040100d141517000000c1341c040c0d5180c07650010401d5403045410044030303143c04036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 259511267 1250 259510017 259510039
    0x1090b0114071b0f031101110f0a0809090f07080106030509010212070c032c04021b070608040b0615030703020918090a060b090705090108040305040b07060e0d020607050412050c030a050606 83
    0x214400401e1400301900c1841b030304041000c1988100d004a44511400d0203a07402d908005c00e40c94600300b0106003c5560405c04038541e845410071242995010124038441e0703403e42070000c0054010303101805404100340d01d5400003410031a00350111403030150800340e001028500f80f2402801e2080c071080490000f280901c078050044040d6141c4151540701c1d503628030900c0c40050030400290b1220801c903645a079003941074090351070180a418000c14a603268113003030746441d2404035541c0c0b10007044144100311400d04010100d20300c400b80c80d4800c0d00c60a00603900ca41c448000740011040c07280d00b00005513440200107a83c000031503d404514400c640602070400020704114240d4401c43e04a80003c0c828030443c9040d6202c1c10001740c001d4001e0a00b58a000d403112040c2425600804003a901c1c2a00c60401004002c0e04200c0d1500040c0c80c3d2018003800d0034030000c0200107200d1071140507245d85010342d20f002406014840142c1e404401070031640681d065161507512071750201c0f4002e1061140c501 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 259512517 1250 259511267 259511279
    0x5040510080105092d010f1d0c070f0819030f14060906010309030908030d02120106022a04180606080d0f0807050a05070f03112401090b0114071b 64
    0x1080c5410780e040101103003820385e60720302c00500f0003c415990f0503414541030b62000103402c90412090103861242e1100f410035051690307422401c2e8a0303210006030800d81c0b000300f201c40c0b0401415219042d50191403c0d640610905104020f03018002000300c111049101d0009a070340c041d400b5806039105100180401d00d1540801175403000210f4605420a4444001800f25071196008000441c824103280180c6600c56950034a5a0440342c402100b079030b4005582c01c400c0c41c0701c103402401880305100500443c1c403010408010300c1c100c1c4407107003a4101e9405130101695074903004109602181624071780f404d80e480c14803034094003051241010038010103501e000302500c11040c4400c00e62850312000080e0700c401c0001c03504c3e5440318407280204113050101100041010104004480c02550740c0c2c0200d03820b407012541810204600712401400c094020a08208045007481c111480200c0000d1000d0400c001a40c0711340c00c0201101035400300207080300070000e900200c01c241001080d962482151120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 259513767 1250 259512517 259512527
    0x3140601063b04090b0910110f2a1506150f0f0a0e06070f0308150d15020d020301030516050409020603012d0603020a1206060804170f0a05040510 64
    0x180150100ca60740030400d0b4010044035114118a030b0040c0c00040d10446940f07564040b494140e8140100c0d81100031247c0000b81c84c1d016184042003940c110600d446a020304450491165200440c180704901d02003c1c20102001d80c404c801c0700d546001c1e074000319a0490500c8501a040714240d200313030f105c4403222030131440d030205844000d000b6080d15031030305422003070001d55900b19804a004020b03802074101c849071100d40107094414405c4d9200c81400c440c2d03180203403111400400c030112426030100040115660584401005a001002810814101d119810207446038507110103038280000000000c004000039910100e05941e405a0f10854a5808000036507803a042c010350310600070310050105888400c0c44a1f0101220381c525101e2424049100d541c0032080da0040000c642e0221710000346640203442ca0300c0c2c5151040c0100702d840d04100010f04801000b074409071601840c14400c195082e1008100c5584030b01d4814025110050050010001d80c0180240d43c01921280f1559028a00038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 259515017 1250 259513767 259513817
    0x1805010308030f0406110a0518010809030904020a0e03070b040317070807110409060509010b19031502090604030611090a170a12030209040203090c190807050907090314060106 77
    0x21501890b5844502e00b98180280c0500b055845650f14407443c11458000f4009150610558a605860303070700300388064603090030010190307060110700c2080080e014404000c8904001080383c0040e128101c1c075000301e408420620800c0d07094031400c007010178144040c03005402102e1240f01440c454401c00312000d5068018030b4001403501d1000e0180500003004080f40444060000c0c00007d0060040c0e00c414060300d4040e035080909944d10000c0701c0040c00d00800c1801100c2524504940722407460395140859010100b08004859010601118594940080380e0046812150500040401d0920309502d5801054080e215180c80c882c0040c07284414401586040254005802c020720340b80c032680b041c16201122242007541c20040003105580b00d01c007840c0036407485401005401c040c0c00510112004c011413154400440f080100320103040041c0400036101d080d10301a8003621001e0003a01d000c0d00581009065000441a0703030621600058014101d88556036040105001028100c02225071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 259516267 1250 259515017 259515023
    0x90c030907080d0519030209041a03061803160204060b04030302010c0f030b102304090b0f040b0901060f0c06050c0c0c010e06040501080612060906041a010608010e041a01090618050103 81
    0x1040c002d04000c0c17030b4165641086903102d810702524005800000904688078004000d007010400c003200651402c0821240d80d200501c1030307042d848440c00b408107a0341d078041e1010b00803001d60f142e4407100031902d4a4002400800f82032891035103507900da24020380a03101806000001070707400c0004c00d600070301c640070b0f649030709901500600c50802e280d0000c90703885150365000010640200c0030401b21a004c1d0380107100803e03c00100003201c003086420040045c50441c4494807550610a12981325600c14004034116078280c140008540705940b016202d4140d02035001d8103640c9400700300315011800200038040c00500401743d4000040c0c000c015912401801c0034a41c00903002e00040c403031940281c2c00d55401a2009110071503544084082603c2c001e000ca401c0c08443d0480c130244070412480700401c05800805500101456041110042501d8414400c10009441d0b9001140c02d00194002000b005845485100301d107684902450024210a1044407030041420001c10840740043c4103090503254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 259517517 1250 259516267 259516277
    0x5060a18080a030f110d020d0609020a0806090414151e0405030d0c110102040807031e08030c0313050703030228050d0c08040f0e01050a050303070b07110309090c030907080d 76
    0xe140b10224028901d141c80d03640c61135540e50404403111502006841c1d0240c4e13040d0096a02c0300701d02c1800003641d40c207501a07130550f030040c4205140650842492940554207071000b607030642d50b0f810b00e55002d55040d003030307040c00713001c4d44100ea0002e0f8800d1007118071904000b070301c0c1c0151002c1e040c03030301e998000129005000c68200b400301d0741c0300040640201c800081c00e444d041160344002d189145c03c90f44070764040e00d4aa8401c1e0300400420071070301001040030034901103480c000a641d4032408000c0c40300410388a040c800000c002400005004c81005902c1d800c0307422144440d45034500030f95298074042e0044200700c1c10441c030761526440e6000722a05950700c880a03100f00110312200307072144c84801c8001c0f44c0302d51040c400828005140303440c00d00140110f01c5d0003080d6515120a000b54004a83c00050280d0010002d800c0421211800c0641040340c03840d14880700050480081d00714052400b220364400c03802030500c480d000304c800195000f4455001520700c4070360f58a51540e980c00160800402280b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 259518767 1250 259517517 259517527
    0x101a1206060f0405090120030103030e03070f03060902270603100923070513020910110d0e06130603051f080a030e060d0c0f0e0901050102030919030501050405060a1808 74
    0x403c080e00708640121000d030000c6400782075050180069203148607945082c06001c4010024590320041d0f5084803c010ba003d003040e41c2c00e00c054030101c01c6c0d8600019001035195034441781191900322000c400110503c0350010481242141c0e81000e00064842602c20f10072602c6000c1501c01601c0340e1030286a200040b0266020741c2001c540c0c14800f45c840000b030b14000e074200083da980329000d03401449025601c0059444c0c3c2c0c12020000b5034440640705004001c3d900103140003290000504811660345030400c100102c8221000444600c200314242203500d00030f0704001441c036096046240110402c00300c18a0a86080324424810341c0f0701d10503a21954030205c0c43c4000b181c01201c0400000740007510052401c8084100c1c0d0303080c1ca00b0b880d42103001a6a0804e500c210540c09140380c0440750044070710161951411340000d40c1c0303020740840540700e441d181c42c0300c00d907499200d032003040110f03030100c001c4c8141c3c680390034469180e000c00c9484026240c2040c3c0300c14000d424104003800c08d2544140fa0714100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 259520017 1250 259518767 259518769
    0xa0c02040f06030203030318070b13170109061e111207050f07051c080a050708070f0207031a07110a0b0109020c0109050a080903070902090604120302101a1206060f 72
    0x340c9001d00000e9800c0380c1d0b580021025032070038001507100b5241811002140b032000042c45142c0a0b8907403007070384803201c1031148020b1a00034000e0b1400f1039420303001000c1c4031160609564014032980c2c4000b09030385d103045609100c4509a90034034000302a00441001482e01c00c0c6640d000e00d00c502101204201000b01c00030314840d00800150449400f04182142402055600c040c81c10500a07010510200c0c41e502910107181e20480d42e940c00a0941414410750400f0b0001804540018100c00c0a00c8008041c1ca00f03994030801c0944015034002e05000400c0700c000411144040040c2c8000d80000d1000e0700ca410140d1001a03141d40301a804284c054450b803900c66944c0094000d042000d90702e548440b1390001080341001542422130241c0e440326a0b4110140416240801c0c6500040542d030041c06035808650750f400c2614100d40c00c0310f9005114812600d012810155140e580c506010f24101b00c140e00070942103a6403400d10000e035003244200407542103550742d80d0f0342124070540c00201501c280e142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 259521267 1250 259520017 259520021
    0x3090105031314010614041506080c0c0604080901031118090711010f0b030c010215010b070f05070612060504050405061317040303020327030a0303091a091c03020a0c0204 75
    0x100000b1800c0c0b2410100c40c680d07484480818485001c0010b079120350041c400214014541d00000208603001c12070503141e0001001e92842a11581e8184040a0009214100984121a00383c1074882c1510281d140c40e18000c0a150003402c1c0490000f46042c0b40b400d901c80180302210080b00e420401d070208480c1c07030b0b403c00501c002c00600c802c00708140c0d40e40b01c40880209000d01c014003070a140c0003183d11028441418030b020f1301d59104070304544c8641034000304800d020b107031203040d1240e16050a0303076004503040c240400c013552007008165101e40c4100089071030340010344088a10064009104080e991820082034400985000d88a138201501090b5501201d0305110022071140d5034081c0c02c03910324100d401c8242c000d0761007503015130400241a0740c40008014140c0840a50a1407422400d0107400401e54500d0014001000d0581d59402e40050022480110a000c4080f03500d4102520705448241e0711416503148604401e220610b64a80784c0d8000e000b6101012150b680e0320074100540e40170000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 259522517 1250 259521267 259521271
    0x6090c152316060e0304051008070e09131e0b0f0106080906040804060c05120f0403060b090705040509181606030c020601140d0c030b0c0c071205030910030e0d020f0706020f0309010503 81
    0x81e0f9100070040007c440c2c0b1009061500300c0070703a03128011546082c210103450001c0103101d040c4602c0b00305081000590070004d40c44203003a0411f102080c0b8081c816100e456100d0f4420303001d010300c0006c0007002550060700d040340d4182d4615a40b58201c5440f04000241e480c203061754010a0b52009101c1407010521452110480d035000e40b04803100d2051032040082036078403801c0200c020043c00901071090202a02400d00d2010061b1070000d8035141803400104030f030056000c2c0c01d114031402030110b03005032042501c7c40c2c050304203c002c0c2c804c840003014141d440b446d5070341b0501000c01d06005414582c240040784181c1203a0391294140911940b00c8100444c00502542c100c440140e9910084046800c10003036070b102d0a01d40315440c0e44c486041c500b607860030341d182e40b000b1041d1145018407c0022300203c2a00e12602e400d6680e0854050f0703845054024050003c0303222054030584000c0ca40f0b82d0b0f07000849480c1c5180391002d48035001d46902040381c9030301184181806550040140d01c0e90303544288001c503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 259523767 1250 259522517 259522541
    0x30712030b1f0c060510091d190f1208150607020108071b050f0303042310020d0b04020c0a03030614010503040b07140c010609050606031306090c15231606 68
    0x29007915a41c2c0d018221a4181c410341030a006502c001d107c1d0f03100900c40c040c55060000f1501c1542501050140d075602151040c6042e245050700c0b82100f044410880f082040d60302001e000700c0f2801042000340229802c032406103810311060940d001030300f0a10225407556406a413130300d1035950f40030b00c1078403070f00c0c2c0c41488054900f0506012002064007484400101d0b02d504002c0c55483c1040d0034405407054219514900207003a130b803040c0b080c60000041d84041c7c600003101c00750325821304461040040c003540c1c104a0704035000082004200102045040b0864449d880401a90b91244226000e402c0d100c61007074041402000482e000c11620b1f11100d60180442c0742c0140800048054081c981d00405400120350391140818444810b1a005407607000c03400303403155411850908081030117428100381c00b0340a0f60b84c0b10003400c00c1c4030484003507070042c1c0b10500307141d40030403000f034401071022200c0ea40318100040700c110740c4d81d0040c2d801021900f9211044001c035461002c1e54031503100500c141e42141e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 259525017 1250 259523767 259523777
    0x912060c1103070c0503060703060608130f1202060f1609091113060f02010f1b0f0905060313020f030d0c0822030b0a0c18060518090108030712030b1f 66
    0x712040360070402c001d1140ca4800d161340381280f07141c0030900d0326004010f01402e0515040c0302c010300042c1e40c0100c015520003002c104c0c4a503c0507250038200b904050740c207406071094031101190040e45e90001246801004604040d40d03d0355250108407040d100c00300914000101c02800410905d0003540007044106611840c152401030b20762480602840c56070320250124a01c07030240c019941e028030543c1704031501080c1c2400070001c841d078112405032070041d0f81e0b014020300700b41d4070500c24410180c560151002400c62940ca007031a00156403c084205812031241400000e0a0001e0601154071150502542c8030840210310300d5407070003419001800030100b00d20a8629007035404001d58501c1e001107019041c41105420400b0001c002e507022901d0100030312031700c640c03030340211408004411b085880e1443c00302d4454403000b1610031480114102d20780d1202c420400462511408002002c1071842202e2040c0925041d030020340c25102944c040b2513010010007034901c034092001f074001b03c0f03001c858602 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 259526267 1250 259525017 259525037
    0x402040b070308180601031a04060f14090c06160b0603100c0c03080a050610051e0417010e07030308010909080c01050a1d030c1002090307050d0f020a060912060c 71
    0xc480140e00280c105500088885040c4445501c948003400100c40d0500090b04a030360543e210070042d5400d6120215014188000150038080d459200d900003480f124003c0c080525600c0d00344440540581d8036141901402e03131085040d1030104d01302c13201c0b030069526009006032240c9515405d0351000340301d60340500130448407400500080c45094a80c401e40e480b0000c0c2801c00381002800755000508030085246407609001c0203998400c840000d00402c1d140450303680f80e504485107a464a40320150000da44086008180480145180c450340180c00008000903454075081c21b5903102d0354030000e00800e060320010321035041143c1107041c81c035000d0007003a13140c003041000803403c43e0b070101c0d11039005039a5080c2184400b05611040e0740004008402103003884851800103840e40f10780c425101141c0c0e40092404610b8038148082d0004101c003c1450700319400e1802d0034100b81c000700310100e01c41d80c2888400300720303240268040700030f07180b04d04003030090103400342d8642000b80407403240e2100380150740300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 259527517 1250 259526267 259526279
    0x703020405030f0604170403080319061d040210050307091a0f0a0507060e01060506090103050a1409030a0801080a12050711130204030c05061914130f0e090a030203030a0902040204 79
    0x14a83c3d090054500601e10307840c0ca81400300200700491440021842e04100400c0419080802e50f038010b0b40d4183c13003000e0021005d80500050030b007540804514500c15400b10084150210301034880c3d0300907901406601015182221030348030484207080840c00714182449001e40e00c035204c10fa007070a03154a0529050602272145180d4000303914040004000183e0801040320311700404114510400c000c0c02030702c0c02c150008290b401a01c081c0b038101940e5a00144045045401103064662a00c03040200703414140d8803541c4076031194210f070010a4401000003050a40025065101c0382c0244a9441e2010b400104403aaa0300c00c0900750b81c1c080803c881c440e05035403501c200024507407188000503541c600e5854441c08080301680030720310540d41800b00c0d00d101140400d07655070030980c6203480360104031012003d0308039010724180d440e9003104207400460302000450740c09040d2005100d61048070303512290b4066585804802c000c2c0181c005001103036100200e41c0041c00c02e0381c4010409801d180d2030303071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 259528767 1250 259527517 259527523
    0x209040f0f060f0c020d090f060e03010603120509010f090303140f09032e02120c090a080307032307050a1b12060b0108010605030903030f04110603040606060207170c0603070302040503 81
    0x840c1c0f0510403a0b49035403502d44190104140d441c0c0f0003203814081580c900d00344403010046114464a42130213601c10f07446009581c01e600c640f0241d0391010407a842c00c1c0c9280c1005110360008074116000c1000d1100c800d10007401609108100c95055456407a01c2c0c0c3e40801c003120700d40120085581034070050200003195070b014407440c81303070142440c48507420a10780406051092204c0059100c0700e48100040000341c0b41c00544140d011072001c0146559160101c0800c101044513408080c0380c0c0000b10b007260030140d000310b6440c941103036005a44e0500c1a01283c40b4402c0c0b04d41003008209500c990013100c0091168402e052100040c9400c9611300340e1703582501d804100c6600c0080315040c1e62012181413035a0040c141501414040c64201d085203001714400e83d0302d00c005000100354200c03a00c0010108498683c0c48600400041c0040d40c0380d08161078900e000d0400c3d8091003016000780d16000c02c1c034541590708108502107003002011120401c00510041e45d2003d840391081580070400411262010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 259530017 1250 259528767 259528781
    0x60e090c090106051314030f030706090b070e010c02040c1b03031d0a02180c070204060e041a16032705031e040311060a090306050c0901020f07030209040f0f06 70
    0x50260808004480c1003000e10003058209200f0b200301070203c45203003248800001c058403002004a071a40a6040010703141003404500c4e5000703880001521010440c19801c00c0c1001c0740b080c050391840751070304041998030740702c0390042c0c070300080f801062280503180c03a420102e1080001d0a20071030702c044404144412113030080041e008661100320725500149849444400e031448038000c1c00080e40144d0005003264006188070042c040070030082807912001800300d441c540d030b0040003000b42c280c0c2d681c401c240c03049085400340e8013032802100c2018500c040f5010240300c0e01c204510241d01441040702a4010040107401408c51400d81088001c000c551030b05012030305000340d00550300c458283c2030360a50302d0724900802000c0d003c20700c1704100244036000c2d007003d00c0800721081d949034144018100d61142c1d80d0350000d02018200400c0c003610900150080414060030707400e9883c10421140e0445d501e18071444000c0d003122400c8006004500072a40a01c03240348a40014a00d400c814ac0703410050320f900c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 259531267 1250 259530017 259530031
    0xf0307110d14190201090509090606011404090501030309150306051f05070501092f030703080c010e07090e0c01140d050417220801232a1803030c06070c06060e 70
    0x3d00c0019900395a040300701b031402031104407542c1c4858544144103c4c0c941c0b2019000c0c0f414032401410000d4003502c0401582c0291813000d004201c69a92414014951000342c40740024004041c02203040c6580701e8042c5a003551806045150103058400a51105000b400d105070704110041c010440020390a0050204c403e0045098003080d01c0008803400d035000c40e50400c1581c68401d10064442920b0106100c001c03203402003016511040b068144501500b504203d0202c0390040c0c3e6000306d040501948200080e200d8030044800043c0c0030340054590440e400d0380e018101c00140200304401c0569080729902c03c1c0300d84624080a2282c80300c1c500190040050140c0c20300c07010100030302e000300d4401d40d84004c0c2400d00081c4170408000d030100c141d60001400390842d164200303001407400500d64001d2446c01413508080701c80c034540c2c10824030654004060301c04031480401803000c0385150020a5541500d13030301001d454151907201d0b0a55043c4840c81c7c0440d4290f894280c00a00044604002d52240c00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 259532374 1107 259531267 259531303
    0x40501142b2d0507090e19111804050105060f1005031b1308010203060301060605070503040b03150a0801020c060a33031e03020f0307110d14 62
    0x2801881102d8038503000304401003200004141046866090040020100d5680f5090b140c41c0c0d1994000e03081c40071500b114010030000d055011003400010180b02d000c060454003422041c2044030700380c400d65519820003003039080c421010b01045000b160201048074404c200904240000341a44e281914007000c95006046080100c0780003e0a80007110f20307031903840f8040b50207544204d40050103542070101c0001c00718068402e81e80ca042e4410b000e1810035003040092002608010060f0f0700b80003201510405d651186c00104d00680001e00015170351341904c011481c9011000351001c90060718008000400c904501d0101056070800c3ca115182d402440c0c0d03040d1500030841d000a09a041186c21038905240082c002514442c441e070290307000300d499440750640ba40560000685015143e403400d42440c0f4210080d4542e15118601200a2003110110325280548051040c90200 = true := by decide +kernel

theorem cover : BRFrame.Cov 259352517 259532374 := by
  have h0 := BRFrame.cov_init 259352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 259352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 259352517 ≤ n) (h2 : n < 259532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
