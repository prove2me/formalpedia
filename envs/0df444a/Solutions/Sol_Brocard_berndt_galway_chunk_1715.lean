-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1715
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:24:41.248987+00:00
-- url     : https://prove2.me/submissions/fa13ee45-9893-493c-a5a9-3c23d06579be

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 308273381 ≤ n < 308453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 308274631 1250 308273381 308273437
    0x6090604020c0a0804090605010905040e0706260f06010e090105090705090102030c070303020c1201050601051c0e07242610080a0c0321020d120908070b010602010606050708 76
    0xe01d0f46600949442e5a00d5890f84280700a20050203080d002800165000920303203403034020042501001c2014207800b500d4150180c4000386070004461406190b070300c07400a10500c01110502c600307840c41d00c0300b40c1e130f1801400040145a112400c1440350f0300050040c4059103510406640c00b125031b0600c195901780680061740b86000b840d04001c21032286000100c10540c0c04600c40d607404c4000d8402d1200c0140c240d20b440c0c20780b41d0490300503001420900500002e10421901007c0d1454810b0000400031881c608007402e258480d04540d03071a480090703401140d542c00802e110924147e03803420041c103060445445190019002110120041c0d100c00300b4412000d40c600d41005103070341411140160181e19082040300040c0c8001d84040901100700d00007411210700100311540a40c0c0a03060f0b8010034402600d08030039007075070383d407180381c0ea0268040024030030001000303124000c2255000544c505500203084d20303005d401900c01c0050500c5050f0014503200162000e0015205e00f003518007802c1000d01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 308275881 1250 308274631 308274643
    0x20d29061305151207110a030e01031103091c0c030507020409051c030e16050d15021608040305071a03040803040501091205090f0906151e040314010c0806090604020c 73
    0x59402060765807180600322842c0c004090044144034400e04d80e6403107401c1a24028850520000d143d000721400c0d100091141c2c0069511034014180080c8400500c82c0d0a0070f84d4008854001003a84004001400140015801c4c0f000c220b00d0714111710700d035034142d40050150140c1c1e00700a0180c2d0300c0b00c40349010008180003a450762104c2440c4005084079062008010345890704d410519170060051407421048403481c1101940c50140c00311003d61515502c0c0007940c0d8214080f81e6100f5401c0c0700d015019521100e940040c80e0140440b2919981107082407401d04006510904803221080e20040340c802d00704040d81e0b0722507009001d9503140c2e0742d5414424058807500b40020090340e090a10000c2058102e40070344a4644141d521150803168001071140700202a50b041d640020041207a041c0400c0000c000c0044100703444011248111040c820000c82d08160000c80740c408035020708081401003481520524100340c94603401a04000000c03550040018103085d002e5a000681807805010030466 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 308277131 1250 308275881 308275889
    0x9060d0b060307081009020a08040308090709050c0a08090601050a03260d0f0c0305010b090418080c1e010908071101020a0b01090f0e010509060f10030605010603020d290613 76
    0x50240c1d40e00c3c000c0070003032881004507072090f144030310440085041d90b002e00c04d40390421050340f141b040c192142c3d01d064821850040c07a0100701d00c900c2c80049581c41c00d038025640034410441140751540d403a0480609080e500034450805a4404801041a55540114902140d0308012144101d901d51040c1c0b840d02c0b40749510410500c580000c0b01141018590300090b00c0b02d070611400c00c50b1146d000003c409950080c8984081d1040c14008a5010300c0c043c1e00401c00d100707002e0030f15901c1200d1943d45512a402a10543e0a642c200c02c14003000c142c0e01c121180c144130710b5a0001c000605a42c2d507081310902685c003020344024109402c548480c4d00800c1041c0c2460707040403a425803903954643c4480640041e14281e50503906021000004001c1400340c00c0c0180b0106018144a07601c1102202c0002402000400c145814a2000000c14601c2c031405010f016660750160383c5030410304a410965143c060121441c0c0442100e000c510009100800100042112101e540d1024075844584400f200d0b04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 308278381 1250 308277131 308277139
    0x1030b0702030f19120c0206010306150305011103040218101a0405040e0708010b030307212102040e010b040506070b060102010f110723060f09100603030c0203060906070509060d0b 79
    0x703101c83c401d04104420b01d04588280d545c0c0d51700344440c2d0207204e0542d844080400e001d139200c0e00040c4005007442e041080c40320007a000602d01c443c3e50792242805d4418100024442a20000030704c030950400c1d2010504450400111343c0032070a000b0602104241540b044203112540002001e251441301c10494000300f00040c8180501907451b400c1580b07828451281401031340c40d00340e0461282c10b01100342c848070354000400c024440880200c01c000112200c2e85041041720700903d5080f401030084000708100103000300162a00d040c030f01d55110300201a000705100c07032420f020811203036880d0421941c0050703000c004807540c2c2c4c4400340180e004d00742044040c1c00640c104514961a004464050011140900c0301c000005050301d00c007001c0c40d20b07440700e0078121360401000101401482010190020018000c0340c1c000a2641800002c6031081c2d0001c9000039075401213241985000c202860300700100d60007078129030030040700150107840f424034a1030140e100899186401d10341d0341d0042c891110050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 308279631 1250 308278381 308278387
    0xb1c0506190e19110d0216062c07030206070f050a0212100b060f0a180b030c120f060a050d0302070e0f07110a0506063706030b04021201030b0702030f 66
    0x202d6079034540440756816150480da0550074580711030300a8015110344030705250328080300c100200b0040d500007800c0400001c0c90a8054000402c84e105880130407410011a0a0b125203103c071a04092a9050080c581075101c0c66040c000f50b6114411620f9940c0d114820008150080c0741c0300b41441400c0001070750008065000c03140c1c4420205042d060b4000070803040003e80c06060401940c0d0094041000c8110804e011000300c1c940142d00010f851180c41e56036951260342d5031b50440c600e0b80226194180d40754040303181c0c40710500504c1d81a07040481108900c155181c003001040480b1110f100f1188070b00000340c2c0c030506050003842118083d00402010900d545424403a0000e0204103449480000340c10490034410003002250300640aa440342c05080c071078a40c0d000b000002000c601c000445c001c522090508441d507000c10a4040c404c81020550405140c405c0140c102c03203100305020702542c0100030b0310f104821441a6581541c1c0c0c04000802151600340080346513000b00441c00a02c01400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 308280881 1250 308279631 308279639
    0xd06020c10051603091a040303060302150a080c0d09050f030304021206160806010527030714060f07060b06071a0709080c091515070204060b1c050619 66
    0x194008101039108001229554001880000d0071658101c9819483d500380c0540d42000e284260010411140180c00d00000300a44055510300c0c9001a03404402099448170b0400031400c0c00520300c0e030441c80b030390354250a290300b024000c0c128500043c003025150000062460b198440b95112050b840d0304481150309601c070304103a4556991040d10160b01c00c0c03841c8649180f101c100003030310b18071405c1d41c2d000c00c02401c901482c0603214107201130009814400c080c0480c1c203414410784010400b4400d24101d204082540805150414030250400c26400740000d181050503121702044031900c00340201c4d072503655440390a129004014801e002a4448400034000090015110030074a842d0a10303954070b04681c403000001d0314010110301c40c1d05150340000340c201c40c507450801085a0310080045400601c55103c1c40002d821140000c44900d0079030021a0080940c1030511800000c0e144184a0b64034003040714005046003042e42c030803100745c2c90310f03840000c01075119031113410083c000050440d2007468031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 308282131 1250 308280881 308280893
    0x712060b0a08030a050711150705010f0b1c0f110d0804030b2202120f0601090c09050a1a0307050d0f09050606040c1d0d140703140102030408090f0f0d 66
    0x55052141c0c420061940082075442d404821121302840e162034180c5418596980d6088030355081040e51380c405814500c00b24000a484010703c0018032480001508040410a5200b01c1d0310520701c1c2800f41105080c5e030605039000c00929a40242c120148121756041498440c2040700c0049600d40c0224400c00c3c2c800422079500c01800980348140c59282d1580d4800b00d0344130504883d40740301c00c21f0070303d41d803020000f6013400107018044510b0441628217040180c1e009520b8070000382e004a41b201d54a1081340c01d010760110b40e0402406c0308640b0310254600d800d101d41d03501d09101d90b480060440000100d40418019004c50341041c450f044140603032442e140d4404000c01e2075007010755441c0291800501d82c0e2070b051083e000881c0003030301c03070390315003192505050b100c21510440e480c1c0045854005902103102d01c01096412003200d002000118114544000b500114446032801a8018000d000c002008a825115906001c1d12218815a00500020034403074100b0441c9400c40c1400364403506000d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 308283381 1250 308282131 308282141
    0xc010b0a03030f0206090d0801050607150c091e0513020a1e0822051002030604020c01140106140f030109020a0509120d0e0a0f12050319050a090b030108060711071206 73
    0x2056020b64020f6503e60240944800100c0c201000185040c3c0041c0300600c0e05501a042c864000d1100003400086141e003082121402c517442004101a5041044100945400c2082c0941c1000c850d031202841d0801080c07014114407005c582d51600420000b003564440e400702c0e01d00b0400d211928026004a00c0080c101e0001a1070410007540c04522603800003404030040544141e10400600702030b400e407400d0030007e4002505060744580c08010442003201c0034010010850622002115294034001014103508004603d0045240701482500e03800c101020a80341192007001008d0303a1410724140407612440b8480820364407020404140501c000001500e00f81001c8030b440d259240050a410081c0350096840b8031002d00304141010302c001c0b90807011102c24a4400c600300c0b0b090003942c88000310300d10034000f90580052404070768241c0080e80851808014403000070031301e01d9541043d00854461800414040a10040c089880c2c0c6566041283c0760081120030030300c0c0010b040518004001d05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 308284631 1250 308283381 308283407
    0xb040302240403120903020d030509031e1803010b09010e090a06050a020a02010b120a06020d0906050f19180b0702070801020a02010e07050a270905030a120e0609060c0c010b0a0303 79
    0x141d204e110310740c050349a9105220b801905500241007400224900320043c02000300451001e0005112040309041400d1956a00f001e1a2010544500e03203004c10146041a045c101440b90781840034007500c03610f828402d6030644040d41014507142c0d40359000513142c0281000028070152a00c003c01800661690117015000301c03550091001d103080d0010080702c0c8881282502d004d410520688001039020b6005281c062140740010602034000d0712643c0031030703a0031180021042ea00740100b01408480c04900c107c410300d65042001a00c4881d204001d41944445e0014040e0042c000032950040c002c0000d20001c0031100e0080d503586900e144020302915910b518100c4610071003401140d01d143c1211808181c0b06492440401c41161404031520002c0d20342c7c081114590f80ca284030003051083c001031601c2d51560301ca41100c10402426a021030703801d00040209a00031000380000344401156190708191001001070b2030b400890501401020206086523000c5d8a1010010406d42c21400e01c0d1980c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 308285881 1250 308284631 308284637
    0x408061806071107060e04060305010e01061a03090601030308060d14010c020c04090803060d0c03171206030a0f03030509010b0307030c06080f10050114091e030601120f0b040302240403 81
    0x15102c0d040207407a5030301c258103428501e030003c0400340032140c4505900f400c0d40c0001040451314607a6a20741908640c4c1c2d840388641c8507511450f01f840301814800100c00450409082c007440c40c40c050f00195118501800000c04003c1c1200c0803c4895403810807030049aa000074084201c4444460400d0003410346800d505c0250040c0c8a03052a20701d0544100c9100542000c481c0380742d81d03604801c0100780962002c003141d0810800c01c000c00428240400e125001c0101401d850b40c890151800d42c03100480181903611a80c8094130040008021801d00100c2c04d83c141400308031610b544185030b000d0801c21180301e406110790103001050041c2410b00d041100c003251a040002c0e2a54440107005a00440700d42e81c0c80c5017085020492540700d801d00d09401030078000e0381e40c01d0034009030008110280440b0b40410002d8003500090300c03450148000c0380148081d50092006040c01d50340c800000e0211358010302140240000501418002c1c481200d000b0415402d100601c85041344c44100783d03070156020741c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 308287131 1250 308285881 308285893
    0x717120f09100c090509070c05061501030605040b0310050709080d080612030c07180908040611010b03010b10030b040603020406150f02061b0a02070503010c09090e010501030c1a04080618 82
    0x182c441c082c800c40c40c040c0708541d01d800841c1c1c00d020910452040240210041060b250000c001086007070210a0094031917009100c2d04590142c001000e6900e29040b50348034602d0040c60942030341d800203510203c014165804501a6180c2809840110265000225078014000e0f00406207034844c0a40d48510012150803200c6203c180700c46559005941241a031a40021000d004003034100d18000480c1c02ca5580c0852908115a2101200d4100c0d82c0501c0205044030010a0f80e0726081c02044880101a0004c101690300701001541c2d14000c03603580300030303d50f0382d00c2e0b4060b25071520341000000c1d6802400912182d0754983c1120110601c800d54440007071195440300c0c0c43c2e6880403904074050301058000c0180750b03880710350080565001c180325100394403651000051644082c0540052012203445401e1306900d000001410345090321102503059142900500c00030780c0300640441031310a20a124802c081c07030503032114024407070b03030704408007901c03c50302082040403001c64000701e851030074401c2e00d034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 308288381 1250 308287131 308287153
    0x302030613170f0903010c030b011704030806041a0405090d140f0703110102070b0709091a0a1a040803030103060b1806010815030a0b09030c070e0106050717120f09 72
    0x10000004400080c10404014689650014100b000d800e6000c281d541d0b6a00d81050040082d0031180302e1070b07103500826120881254250303040500440211103202d0038980519060b6001800360a0050040f1b10444c0d071810400034540000030078412440000d40204883d00b04000c4040d80e51001038121000100e00d500d0035450702401c00305a829096800b8643d5040c2015540c00355941d00164651f080c01e90b601f0f10405000c50700104600e030140c40592180c0e28200c0c10107590100791118011600c1246404001c0144140c454119200803203920304c05c0f02c504460560b80148071889944d02c00c4480c1c2c4004000442031005a41c02086503050455002e4504018141040c0c030b144130841d1518045180c0d1000070706900c80d00040c5201040c802001e41d855008107039581502c0e0001600c407036046900106601004078410840500642507003041d00d900d41d89403c100808500c0741100080010b5241031000240b01003004c2034502e1603500a000c1a810b203010240608070703403c00c840401040c80781180700c1d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 308289631 1250 308288381 308288401
    0x40803040f1208091003141503010f021806030a090c08010e01061a0703030506040b030a0b0624030c1c09030302070c0605040f090911030303190e0303070f1101110c030403020306 78
    0xc0c240d64041022414a10803204200c44003105070300c0d41c0c05060311110914250400c7d200d140d4031800e00c604805403012080c1061508507060006a007038120b204020900c805940b01d00a072251140807550b41c1d5496881959031000741c04030f054000e0022812402c04201030380103411000302a144003000f0004039036200500c04500c850103000d480514020452000468400c3e0011035120402800205040300b07504042850150385c02000c3d901e2403001410721203035240c03118900d01a036181005500c492805400c0d01e0038588400b4002d04009034001610702e4808860010400c005905850204001d61203820003034081d50250608450b2203c00040124101d4010010341c0c00303903007580d851060b9980c1040070000c005c0121820554514a10010741026a030303041000f54032a004070145100d0440101d084070081d01e60601031100c03140c005200700f0010b164400d006440307008180c90010352950090a90034010a410001e440030035100003064491b00c10300000810484e071003035003284c2e2244d842503044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 308290881 1250 308289631 308289659
    0xf23030a06151a0f040e060a0803040f050103140705041e03120509030f06070e06070303060302030105070309021002030c060703240602030c0c06030405030a030c021203100f0e0609040201140c03040803040f 90
    0x101303a400805020900201181e92009035020304050040021182c1fa260058039507040317540425001c0c03000c0e102c00d208a5915010b02c40781085000b14800d40750910700b01c003078514042d500580e1803041c040414206c030300d41d0030300400008640044d03010070940524280102281d2003401020f01a01c60480c1d440740d00500003d009105e4005030303594000002520040009903401948142c007019100c40d404005039400307108103030145880b13442c00909282c1c0d510500000051700d0b000203042d508140320741101c4441c00b0072940c6c0d00c40d000c3e00c2c00107880e04030782001004002000401560f048040700700800c0b4190000001e040c508000400c843e003900828041100a100803103004210b50030030700c0407100e0640603401040640a40340142c03081c901c468400a00a904110f4604a0705a0f91420810449810800c0f0030040c1900b040801d00314078000d00442c8520402400c0203041143e0481428045c00200c0140d40210001c1010b40c2e40c1c85c0d580d00c012503500e13000350103140c01c0f4000e42d01000610070b01c280301d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 308292131 1250 308290881 308290897
    0x15080f1503060711100e0601050a0510050f070c0b1c0501090e03040e090316060b040b042904060909050601140d0c030b0c04030f0501090c0f23030a06151a 68
    0x200803d9035041070841d81095200c090510720300c9900b00ca414160f6146c0144210481000c008040c2c030340c500000c0221040081c0d2003140106d800e0060300e1042c0390302008881e4a504180429562850f891400c000c0305071789513000703800d50600030948820328a81e00740e0491100b4900d1300240060398840c1c4a017011188030a4091200d60b008110400400b0480d461143e03000044506590400d8065503030000300003074802d4111401d82c4c0e144844111071a00c1c1c070070905c54240603030b402c0080755a10120300c1c11407508954a03040110481d1581c88070f48c0c0d21508240301400401c0c00c14000810140f0b8821355417102070081c00564504c0410060382c50914803a00c0b08591f400c0a01d0703107012882d540300d5044420020b095440c5080003004048085161000b8461455210790300014508502e0304003914103481c01c0d00204003580c200d0303204210801c46669400018220041280c1110201000103132501d011703948020520f81c00d04000e01c141880184414088520100a054600341e801800140790300c03c10103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 308293381 1250 308292131 308292133
    0x70215040501020c0f130c08070f090b09040f110d060305060114030c01110f0d0c0b0a05070207090b190e010509070c0308011208090306010306060f060e15090a15080f1503 75
    0x904d000d00d4540e1001c502c0c68405800380503000306c101c1500342030350710a00851020440390306c18032416036880500080c50b00e03501d00d00891600c1c10a1600c805900c50080414030072134072110341081e2072606a000044d140900c2d07074070039500c0203001070300d5026001c1407005480742d0245900001d941c0409040c143c203480801409072a103643c5a0340151103d00c00c145c6c06039200d00c140d11a107400c1c0001042040d0308040662200e114806561030000d80d0028014501e803509810300060042480c0c0001e5040300390303403000102081006000e030108a010300b240b5240203042d84c039050001041c19842801d941030321015242800555515078040e60480d00c03d4034010009400c03d80104840d203074907840e4100041c4140b001c00e140601d0030000a00c0c1c03074030030381080d2401c581c0d4001c1045203c440340701c1c28009014509103c60601803800000d030387c19449443c00181c03c000040d804500760344048160000e8117007800c00340c03640c04400400503c050307021606040030b00035040c040780c81000716101e58800703000014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 308294631 1250 308293381 308293393
    0xf06031401120510090809090117061602010209090109020909010819110a03140c0102010e0c090a0b010504080a0b070e01030905032a1509070b0403051903200307021504050102 77
    0xa820184442c0d8001c1a10180a8021410203462503401100f0071a402440300c40e4881c41180308000c3c0e80001a03000300c8211284450350f092290003c50600c0d8481d06020200c14410f040020503400791141800e580c0c0c1c460a20130009c15001c100f60301800d0001d20075649507a05a886100055684280e40300766030409840003c0c0c200064400d48000a0886018010b610f14698a0359030860340e15001c0741c01c50040d00310b01c4201d5565642441110421030341540202a072482650210b0b02954000d00351035603041c1c4030850760758142d0190040701c0007000304070f08a8030480d41c117003006c19040c00259400300c0000e045e48809141c41d1302c00d000e20b42440e50048061403414910375001101d6000d00300441d440d040a402c4c518500e03040502400400f00d407a5032100c403492030006845403d04480b500000945441030200b4004141d0001d1608100e55014080c0c03115a000d5003004e0380c082c01d00d4003d000500505510343c001a920100140c83e41c24800d07501c01c11003a0580310020403a002d00c1c002c50340160b00079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 308295881 1250 308294631 308294639
    0x1090e010203090a200a0603020d0b100e060d090c060c0302010b04091104020901032c0f0a0b070f0c0b0a02041e0b090d020a0e070e031b150f0c010c090f06031401 71
    0xc2070310280740010f40c175010f0b0750f11001400410410300741680708030003180d404603144401c19003902807207400c21011a0064031b0300d03c8420010300000c00011006008a20100320703104000c025622250100350442108002d880d9148001810001d507400114015401e041c0c001c05a07040034014145019449441600504140d000b400000c3d0040354000d4100f680b29540782d201c440311003404030004007010030707083c1c0c1c1b8800e2104164a03204181460000c40da0203131080c8008554401c0b02940c0082407890010340c2004606411904d140c0c0714400641808140d13020f014079983c2ca603000f0800c462016180c40d40e16201040300c140c4681151240c81d0303420100304250f20b42464100303100041c0503c000c1509000c5601c2d07010140d48130208548020102c2c4080187d00d80604d000c001006054100403455180e401d5011f010500c0680045d180c203c3c075620100701e50302ca6807110025a81354075a04c4008202002801800606000503407085402c04041510003003451131003070040141050840d14207500760313464 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 308297131 1250 308295881 308295893
    0x100207051f0203090901090209010f1706040b03030c0105070c030f1e0809030c1605090c0301180903030b09070c03141e0a0e0303040f03020f040507021902040f0c0801090e010203090a 80
    0xc804090114041000810010341d242c4041c2400b1f00340d544c40060f100c1c4000d9001408030b1061141e141c0c180309100908041c5444940c85541c0d1000040d030300841c5c0c00c96602c001c24958010f10f16034010a500782410040f229505c1010255401d000340d903010244c5c15a114241e81e00310b001c8089400001000181007110340c00380003215000442e00d0126880c1850741c440240c1440c50a2000300031040004104104501e040311031141c202c00d100c0d500314615450540e1129a080c500703281521151b0300c07a0800d4003814069400b6400e0b03080c010f4002c201070302d44580d00a059103240601100440d048090481ea000705580554004214030022100c405900640c0c0c112146c1040d2401410000080010101900c007071014200030403607a094040e000381544100240c2c22140c80d480c6000c3d038038290801821a81c00035100240103400c0400b03008600303076030022801400408541c0d540550a218642c12130300e610502076030480d080720704108501800340d0f4900b800d030320003642c0d0001c081d405282c0e2035000c548 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 308298381 1250 308297131 308297179
    0x30f0c070209074d010c0c0b100e13021806010906030902060d0c08070311090108010302010f0306210303050c03090c060a09080106090203090c01030e03031f0306091110020705 77
    0x1005400050019118005103a007062440344000e090007103c9030000444c0da4a4911384004080d004000d200301510103100038a0443c90f02c0d8068400d80c140c0000c107541000601c101c0d070141c2265205003d141c600b01e044a0a2152000000c90040b41140c3d070342c248500550342e07114040c060503540e140403c1e160250407000761480c14016644418200030207810f5400510410b04401020b0315802c0701031518030310150403030b1015030415041d544200803900c1c81c0e03a0720452850640b682420a441c08081034101240208502e80120315131140b900e040c0701a11070000b40100009201cad40c0c1c14051070350742c48030501041c007060341c82c0e0b1804d42c400ac103008000c0c036219015040800c541d02c2c043e035005c1c0ea07848899095408a50141c0225540081408407001c001d1104c814111030a003014040c070240088016541d1000030700042407111850b0714020070074090000e00b00290341000c410322541d82e40c0c3c1480d2401e45180100b00e4811022010401d001c5400801c825003100e800400c100701c5404002003100c0440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 308299631 1250 308298381 308298407
    0x80601120209040f0203040b0420030312071b1518020a0902090d060501060306181b1107080a11090f0903090603060d14070303120b030606040209060906040b030f0c07020907 76
    0x1520783c4d002d08085600d51000c1d52049005410300d200f1418a400d0440030f0010050342ca050505441e442c810417a1000030488949071803000c509403542d544c40d44101c9018500080b500e428001d0700880c0c0c42807010601c1c0306052040e1000040206102602c180041c9180d00302000750402400703181040b561000da40681783c2c41c0f1000d40310314004a141d0b5070300030843c0e0098002c040400d80c2c2c0c400a014000310742c1c01c1410300059070319003080003400c1c40c40200d98400c9044089420081c42d248800c14154060101000410200040300ea5561007458840050304140c40413501440c1c8202c0010140c0c00c4c0c4100f158040d83c0120007441c44c003025075003440f0007580011b14194010030b9440f41080040c400051090b4802e0740000a41003c41c21440c0c02811090180503000146c0d082c00c050380d0095401080c142e400010031600147e03130b810781001045d0240194403d5540c440c2d00070a0000b018220f03600214072a040120342d654280d0f4401000d02c140340100e60002c0e40002885c0002141c1502440461032a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 308300881 1250 308299631 308299639
    0x30905121305060417010b060a0516081c020405120102070b0403180512030a0206070203040f0e0a0609021c0b010306030b06010302030615030106050a030b0315071808031b0c01080601120209 83
    0x58844000c0f420300c1e07000f0f511030006801c81711010705070701e07030b003803141c0201280100c8140740b811950540050884c020140500c8581403040c2c0301c1401c1050103000c9522500040d2030001d038060300340c0d103600002d4115100721400344141145a491451341842212034180e4080c0810b0825102ca40342200d203624001c007900400090854046050768811038001c5442001500031988c1d1400140028203001000d08500d00759402070005200c1c0b2903515020400f502c448a50a0140c4d07900d19281034060016640104c900c1c5100285030742130b84040e05003001c142080c5607c10320440e000c003030046044480902c0080c1c0b800030300b14089074041d03100350010368012000404000c2c003409102c1d00b444c401d60080e40604003207800043d10106c040e4250062180c500c000310003401d8004a00100c51040c1344000700241c4c100800030f15202005080c01c070b102006002840100c94442d400890300400070008101c0d6110709124400c1000519071040503128130500701a9110b41380012a200c40c00040e4001401107540 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 308302131 1250 308300881 308300917
    0xf19080f0904060b040303030b1e04020d021603020f2506030b0d021009180506090a09141501050108151f030b030124050a1a090a030812010f050103090512 68
    0x90380e40c43c060400904818440341e5503c1d461490081c0456000f0308000d80035000c515819040a0035003141d1410311901610050b0f0303268440c1300880000d01c100d0302da030882c542081c00c1040a2541c00906000408281402c4611806100c10620074407621102d101303d80d01c164038400c0c040140b0a80040c1c0f0720000207404508141410350001c1d8010360020346101c0003070000041004010b10311111098000e05c140c00070000c81c1014404240d4004005010301052501c90048604110644582c03030854646c840c140c0f034080a01d000784068500007031140c54002920a404111400f400e28003601c4028401010740c030460000c144101d510100f04802a4181982d840d00550641c41c28001c2694001032014040c00e80f1030240d010921015440e00706070b015480c514002d000456103602e441220a00c500e080d1511019900001800201603403c001d120b101c0101e251809040b03820030740385c140d0f440840c04102c2e03903071104011001c690340404084d005502106030300382804000030040c1001844845a07440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 308303381 1250 308302131 308302147
    0x123040f020d080a080928020d08070b0c03043807200a0c0f1203030525050c01060806070e0d0c08070305030408010c0219060b0102150a0603050f19080f 67
    0x10081e0058201e81c40442c03c034404200e00c0130410720019100060b07260f014041062103c91300c4100310710203139009000d0015827003c0030a1140803000d44114035800310000782e89241190403a0815007098804481021000600c50031481020050001c104a00703048064031100300071201741c0c81800a009403003401442c5007051055101d000c01c114485000b84001d0528010500d02020f40169583c840c4150180842c4d0502c10400c4110f80441026014500403070035440c2c40c40042c0c405072003070364020040d000030791499000c0360b045009132a022403140002c100169031a09800e4940c1000c0b104040041c008000c11980381c034002e0588403003a0301640312801c44c00e4032200910718002142d082520150710104007000f0748202402590100307070b09840a41408010815030b41c11842c03d01100506482d110410301449034400c211020610100e40c0c5580d000d41002881e220040055010a0b5524055542c011400d0b103c00100c03680720519107c420a03418030300b41c03200c00035070700081421030300d81004008400d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 308304631 1250 308303381 308303393
    0x112020f13110c01091a090c010c140d08070810210516080601031b0b090f030c09190e0a0b0411031c050315011d040c020c090a0c020123040f020d 64
    0x1c242d40e0511000055000f01070705144042c11031b1081d0601101d5483c400f04101e1043c0420581c444180078207082c100441c840c030701100301140f04040410075124420b07050b003113903500c00e09580c084c01030341d127412001e915071400003030040c20316016240d20050452030301684018020400300b040750086007911110107a0040d00044500f903a4402503141d07000700018410700c40c800c0712854000100b100c42150072850062215043c2c051100b201d44500705108205506450500542060440041c00b06106180501c0c88004a400084c8190401c1e03107400d400ca019060001110001c0d01d030405d1250880b5901c0b60b0b602144030075200b218030b40601882c0504c0c41e40a2000103980724140e007989075151039203407400051406899400384c01d410018512462103d003804034060b2031145200340c0340840c1c41349441c0e1080e481c0c0840c000704580c02c04000c2c81000b0600ca010b500c1071b50711465039402072107112000381e0b0711101010aa00c03d841e4400ea40d0010a0004540200000c14144094204400403101e91124 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 308305881 1250 308304631 308304637
    0x7051308070906050102060906070206010311151318020f030f09010213032d080901110309030d0507110f060d0c1e02150705031303440112020f1311 65
    0x10b81d914945541d0203120640e018401980d20281c100002c1c0824179001000a607941c6040c440944000d2a440d103001d5a030710345e80d070303070452003580f924000e9622030a0701000341e0500c4240c8104040c01010031580c03440c00100d8000c440300c141c4802252401c50715000484442410080c140300440e40d070030031000101781c010794016001140a120080400b80d40070101c0b04801903002d0080c28800c0103120004d0026a0010556600400c02e1070034503259100301c40d540380707903215608140b40c2c148564440809072603802070061400901c6076901c0070001a6801c1030202e038105010300f150b8090f0b02803000410102c090b502c0004404100d10b08100c100bd07090810200d0b03415800894001a0804000c010081da01d0001d856088041031400d14554580803640c000035071038012008007040382141c2d03489032480e01c4e032a48018421464114800d0340c0034401140c94040904142c40700400503540000400a00c110780c0c0c4400f45070060501f401d041e91217000c00110080b40d501c030b82001075540341e010281001003400303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 308307131 1250 308305881 308305889
    0x200102071409181f1407120507020703053013060c06060f12200609100311040803040806090a0c0e0406090f061d010b0a060807051e0904060503010903080705130807 72
    0xb000901c0d00403842c1c0690b5140c0100170121080c141c14804000c0e0b00c2018008132803000310001510742c0f50040c04070f0411015510140c240d1003a2190750b0309014030111412441041a842d122200418070200d85850141c9480800b031b00e20900002c0118502030207000748400d02c600d80005005881d00140c2b4803150311604031000e424001c08000c1d003040f02c400e43c1e0002c1c4c0769071941d101d50803603011130001d051403140703452483c0100307402034001c480580242c104100451900c0001a200e40e141c1d40e41c01c7d62900a80f18909251207003502081c3c1e9400e0110321900c00a800682e6810454102a2000c201d80e4002c0c000722401c690303039103012011500c1c1e449040d40c480d1165802041c80b006565103031007420302c890740750301d0b4a9242c140e1948031541c6d03070036002c0c0031034040d801c020242e41c2d1441c1c4e0940710340c011070f60020b028070b135601000480c5421a4004000d03060045604005150b120418182261041d40005011609800100780824000c8000d01403240402c1101030029454201240c100b25840c3c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 308308381 1250 308307131 308307163
    0x40c0b03091c031e1e020d05091903020d140f0c0a0b010801020f1c140906060a060c0f060b0402040510120b1507030f0c02090420010207140918 63
    0xc2e61003402c00284042e0000400c0078901401001c280d85181022010a09602050140d41d28a0f83d0b6001c80a550940690120302004649030189010040f0180030100c54a10480c010400c604502c00424003680400b160194010018524007540540d8400304001c24800351600500c812041004c00d040209422030545014000040c440d1600e510440e0042e045000035034014081d50b500010f01109030351000701500c407074017207410400898100411040f0710251304404c0da002007001c641d0b000101d02e40500025905501242c2c0c1e03a4000319010400e1800082510705900b010b0700c041072407500b081e1b01a203801440140f811b950740c800a0003510064881e10003203540d02c0c03039101100d07116106d40e490049040c1e6107080d02c650000c41d5803007180b081e80070083c10302c680700302ca00703802c4d5104021101c00782e076019120000504180c10b1200608a42c0d00c6040c100360912180c16070035510100d06003081301d1807040c1289000350f842d410132640010007031246186500c01d07241d9241c0300f0300c10012600340b452656 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 308309631 1250 308308381 308308393
    0x41d03090307080708190c030b040b090c01091505070528031206060e06030a140a022502010503150d02031e060703020f0a0806120703060501061107050306070503040c0b0309 76
    0x2605040c10048240c0c403c202ca50040002004099004940c5034001044800042481e0045142009920005400103070614518004200030002068950740c0203c8502003102e09103001000110348150443c05104000c08c086200c6801ea94000d1020b440d01d24070582c10f80c4e011034bd450101103090070003207022810324482d90340704030107242c0c000c07164160060040300306100c91420814050212054520158020340780000020380d013501c1540f12445e400081d10340b003521350900c0c01d0502c020350084000448904000c0c1154100c00e40c004130300c06419581a1034090031341c3d0380c070b003a076800288001a50300d800408450b001401a0b9090107070869110200314601c08500281014601c0e0843c024465828544100003c85c400c3c000e071015030710050400e24007124a540c444021600504000300ca0200921940001008212076034000f681600e22541e0b0f00d0303400d00e1200c03001c90341d0784040d07218032901a0400408103840030b204500460f440307030084440d501c0340c0d9138035112484a58011607948010f07030814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 308310881 1250 308309631 308309647
    0x130609030509040612050601060c03091703040f050f0a18020f07061401060c05060c0a05220302030105060f0d14031c061a0711040b01140d020702040501050d08070b06041d03 76
    0xa1041d540a8241d8445d44440d14960380d9517030780c1c0d40303006001d0403060104600c00001018810001d0001611883c058619401c0d08890b0481d580d400c01d029031a0b416550080104070360034004140401c2d41001020302a08515020503c1100d02c00c240d0101d030780c5a020014032500d10300140040140900c6240c2c00110a10b0b44d0180b02128601070304004100120780c4555004500b000507111703001365050705010b0361000700d08002e880b80d2040583c1d98404078541d400d241c00b0f8020288032041100e00a4009010303075511501000418078107000c44a900c118484540740215000844602480014070100c0e072800030b0b1425207400134031102100d1500b4a840d00030501182034600d54620010541c09401c50900c601a81e0b082e45501003ca0001c0c0602d5580b40c189095138411040581e40c8650400c4c2c440c1c0c4c44c896503451a01a40c00401c040e8000c900f85030001a440c00d01d8200c034103c150300040b40e20308113603c5030b036108443e0700003400c219409a00c030078a604440214200c0c44c01d50380e0304031004583c0d40030341d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 308312131 1250 308310881 308310889
    0x2a0e060f0909011d220f0f03020c010f09030809060d110301090b030c0127090510051903050a1b030203030d05011d0906070e190608071101180308130609030509 70
    0x2c1600456480c25801c4d020a80d5030030220307100f982081000c00a0300ca603104c0420341c0c001031000036002034418101c1c1d800d00d0b010f00c40c0440100080c0c600940c2a51180d070b04d08401521420441c0301d48400082281400304042201d06024081c4901d008203520f00d4210f14064070f0b0300f910000d058501010500000402a0b1580c52050180a54098003e8443d0200309800a04051154640d03440c1e000008011181c0c1400c05141040c05480711803010810b0341000540490082d40c0750244e40c2c01403400c1d101704503100e003100d03030000200c81c2d2040082c4a2001203940d4607200c9448568111000500c2d02000300c0140d805002401700030454207400a8075600d0700d0115401211a902980e01c00000c440c2800610700d404a8910b40c0b040c1c407820442a03a1060740041035005100c03a03074030722001004100100d142540701400601552082d512004048422003079242210241e00c03441c10300300009880000040c2c015809543d01500c010801104240b55845d0103041cbc40e20000b00b00e000900001d05400703d450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 308313381 1250 308312131 308312149
    0x10020705161707092304060e0a0312060e0408070602091c210305090c0f0f06070501090228061407080d05040b0109090c05090c040302030d02031c2a0e060f09 69
    0x10800d04280700c592465940d1740c08207035a09409030240f01d688000202888076540040b141d0300b10302070031078580c1407103402c00401c000f4403140c000c0100c605005000900460798140d060240d17420481c09850700c40d0903030381c5000070340c00400c3c040e0f040784114413003190244060304401517840c0110304641103001d05003104404908505c035140181031521044c40041d15000401c1506c2850a13110350b51810800000100b00800016816503c2000020200c0400106400484190344262000b01101b00300c082421154540c55a12000581c149541084620f00c40d22500d1051503106290518010342901c828805501050b44c08003155245c906200800c244803580c2401080034010401400d2140c4e520000700d60480d1180b036210b00304040c041100c1c45825070850307000b560700404488140c42c0081c0d000e5242c2c3c0241c0c542e24401034002d6140d0070060910f0041014041c40c0305080b00394940600f26107210320800308507440400564250004540d11400d00034100c0d401c005c2142ca840e405c1b44410050244 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 308314631 1250 308313381 308313389
    0x20d0c08060a05061c11031908040f0605031915050a090c020f0f03180f0a030c06140304030903391701020901050702090a020c0d1214070210020705161707 68
    0x301032040c5005c6902104400c051344603070148418441e05005c00000b0300d01003040020f0441c0041194210040000d00d9004008031614030420f560026912407042d900c600048650052071445a4044c85104020394000048010040c0c680c1050540b02c1010801c48440345e04180f00311f50f80c030b807104500b694040040e041f041041c2d00042c098150354003003031503e078003d0340750180309441c02090001e155922180044131820740500395000c403a075a401d00845c0300c1024840c0d6030200b840001c42c183c01d901d00f003084920030364150301d88100d900d18617585da1030350b060860680300006001180030f20161185800c00820141c8128000703502d00c1c2080e002e00c02d0401e80c0e40030420b07580e10400c0300c1702940c3d801c0825900b5154046505800d01d44e548400e8101038400c0b1401000d05000304010b00d1003e079000301947d4149034940340200308041d00c60b0152280300721709640031009640b200041f001481c0c01a0001c10016105200f034410300852084101d0040485030041c001c0c2401c0c4200070324100c2d00802c0703942c00078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 308315881 1250 308314631 308314639
    0xf080a02031903024501201c080408270901170d0203071a191401090e150604022101030b06040e060f04030507060612061a01031e09020d0c08060a0506 66
    0x40f83c03440103924101d01c620f10149080041d01900407168001e001c200311103a1f142c0301c030481107885040683d80b98080b9144280000142074100404144a4480d092003160b11001251400701c11054006154840c0e2410007001000112030104548840c1d4609000701803031191002144000c01405003003c41004d540e0b400c41d0700074040314000c5080c0c8070701c038451401403050362203003038031001c500e605443c44002c60451451304060050302c0b06400d038180a4125501c0d010100a11b650304404542c84204c40e1884020302150325012420078a4660300034600e00000b0750828400949010103102c440c0400da100b9030360b941b0044100140341c2014014540c008806101500c6145803d500c4040c030750034054406420030001042035010000310343d000d0006068420340c82840704641c2d19203900500710740c41e4402000c04000e0a50005540a405045000300302545070052541e041400c1074002c0c00d84c074009070303484031903040c0350004122007500f590302405120010340141e1410b4440d00094a001030602401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 308317131 1250 308315881 308315947
    0x13150b090901050f03030708030f09070906141909090f0212030a0903031115090a031205060109030b0a0207020603040302030a031518020d14181501030f080a0203190302 74
    0x8141c0d1021000d506690040303a040455210f000c02191460180b582c00903d122030000c2406841c20f1100700300c1c2c1c410b003007150840e440d180d201d82c80300c029241c0340d01c0790001141d83c0b001c03130006510b00f2248a0081113000d146c4036500640c0e81801c0c0d8196101c40f0025520440541540f9055041c600c43e2250750604c07a50046151510140000b800d05640340b0000e0200200c081031041d100c071080c0300420410781c0b2180d602406003030500f0a19283e172a4808100c0c0411041c00d00c1003e61021401424840c0c04141c581800d15803840d1510164900c00901980d031103507080141400590740d001c060340c043c60181e03000b503844000d1090301400b11100c1c40448604241408000c2200340e8004200074130b04c00501d0b2000d85c4072044e0b902700b000500110101c070749003001840d007008404d140c003c3d403071520030505404440b804241d90708071a50311682804040c08151480d001d803400700b040c600082112103002e01c1200c0c03404002c101c00107220320401f0303000310000c0e40000f00200d1800310f0709042c5030a11104d84402030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 308318381 1250 308317131 308317147
    0x90a080418180c171002040e090c030d090603090507031205131a0702040207050f0609030901092106320604110307020d0e0a05060318061819020a0513150b 68
    0x1003c1c1000e407142182c40700240d503600c00e00c84418401d822100303000000540d19035032101c0c8001e450320702c03c9030038000a1044000c181741c58603000604804202a58032604c95150401c1e030304501600b17014405407500e108030b803c00800100459021040e89640ba03850703945072890400c680500c0c416a0748440c0c0891304140054801300b444a04030b80105a044a0060382c40c0c02900d48141403001c01d6495060314060300c0e00300180190007100034200080c090782c0c0ea5141503190503000103400789c0740d408002214481804440080c10562110003014103040d000540800c4020b81120440d840241c20360006411909000b2981800e0080568035284e4642003401c5280c403034002941d81e083c682615082003032010f4501c03c0c035103d0391100005444040c1c040d6607a490f00807400782490340700d2003160b10b45110304400100141070030352003c100c60200b10054441c101001c075003480c0030409441c3c00d07640640345001c0054140e80e000c1400301c483c80c034010041110f101126150460458592000454007010400701c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 308319631 1250 308318381 308318393
    0x30f030406050d110703080105030c0607050604110a08030c0f01150b0a080627060f0a060503040b0703060b0714100b060913090501090302100b0307030b0a05090a08041818 75
    0xa0995107035141c01d42d22640b546483d00c3c0074200910b580110200009041c1003031640c80b044507410307100284e003100c00c0c0440c1081801000d101d07071100640150005c40100300040c4401c0903c200070a0003c102107003c40c5c40e0404203003142e0180e5160070095001c80d810810000d808c0c0600c40480740c20040c0c00d03007502d2401c3c0042209100d03001c0030b2000c1004e2100003c00d01c0e6074243d611180c0c0e40d00c0d070b622170000e1450b03103114100c424030583d5810320512403240c40203141c2c0f82061619040e5102e903650070342162102d60300c00740d030b820000c0d282030241901d99901282175500c01025283c01401030400440448040002a08100c0300100395201181424550b00c29a1a04001c40b1000319080d280c60b030071000f03415084c100610310717400010400e50800041800b41640011445c1c680c401e035000400414950800b0180e880b80785d444001c0c41c40f0840c81c005501400c1c2030f0300c0264001c20b00400d0725944002680d5580c00d41d40a03400c0305580714800014604600c3c610720a640038044802820444031046440d11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 308320881 1250 308319631 308319637
    0x70f0206160312110d020d0f020f07020a0509130b04060e0109111305010b0a05070f12030203160c0b060603090c0909030423030a020913060e0304030201080924130c0e090c030f03 78
    0x442c217500c0c0c0020301109074480d59800640601c01e0960110344824060b07500f01c20340d91004500740d1050340342d054089220326150000a000d080405d055071401c00380347e80c03520f0701118000d00c195a0940c1e20800c1c10303190340d000e00460300181d2203650070301045500c1008003c0c1d0031403411440344160385424014810307001520b0466601d9541400c00c0c03038544186162000100740c1104005000142c01c201d0f80c03441d40d1f090b80141d07004505100403003a240c0c0e41c20004444212035403201808240045000c25814246503009607045000601a0703244a004030000c1078400000b500c1c071030019440060108a500d0702000b0030603a0080380306a0180781c800342c80010341d0f81c07600407501030300c40c00483c40400c260703140e02c1c071550681303d0703200405000002c0320103c0d507910380d009448180c3c04565034800003511984041036034100c28042c03001ca1001c880e070000319060b82540080c0800803046801d03007400d01040c900d82c0e0000c014803000742c5810407860f0941c401802e000342200850300035030000311140c8680c0804019 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 308322131 1250 308320881 308320897
    0xc071214011b11070902040e06040b09070203070f290405010b040c05400315060e0a09020a051c0c0b0a02030307050d0b13050a0605091506070f020616031211 69
    0x208281c1886000c050074101030b01540000b1780284001000500d400c0d250030340a200320411038042014503000c40c00e0280102c2e0440b404001600104a41c0c0000f40c8046100041c00d406140503d102d880e1611040180743c41507203500c500a1034560412081180074000c1ca62071f0309c0d0960301800920324030071000c0c0c0540a89402c4800081350040d035500201007000c209426100700c1881103043c14401d00c108064840c050109441c0d104841e00110700b4642c55010b01422241c041c607007403980303a80300c035041d00040ca481c4c40c0482c0e0003002d0080c009405d80d903035100c1100302d40d0800a4031903074540c2d81c43d008100c0c14055004101c1c9400074800c06188030740100507070390300107041d003440341c2d031008600b600c8001400405101903002503016103000201c8011b038002d511900d00c60004018480e01c610800c602c516088803850f07803520084620340c03c42d04116000d041c18501c141e8407100d03001c00590015070715400401840c4007001c1030048010506600090010001d010094200036000900810703000c244185c01c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 308323381 1250 308322131 308322137
    0x20a2f010305062404030c2304090203010f0f0e010605040c0503060d06060e0f0a0c1e050c0703080313020901060e011d1f050307180509070807050c071214011b 70
    0x1541d26260384000d50b0111004c0004072204801049009100d43c0160005032829403140c03401003012203280d00100e000072000407141d40500320450800001d4415800708030781554a944a07500003039258007407800c1f2104001004581101c480e8203281c03c490035039210603c2203013041c48105040d0f0f007150459411817016507042e02c1d521924140a40540820b81c80207002294400c1008130740c100419016000e181b880c0002d01c1441e0f01c040007210941d03001500b44902c65105920240d04501400c024079164010070103440c01c807942c94580302a0b681048407906540d1208a0008003145840e1450a014002c2420f0000c00d410034400001c0c01c96040380400b507850600550170034016902e24a00c2c840c0d50011a2141c1d8540c0d155900041c070542007995048080783c4040300390354100d5100120501a540c2c050038104103555040c0d0101d80c1c03542c000d08501e050040421008602c0304050013038101070900c00c1c1c0c0f6900c3c2080c03c1d24081c40aa0a03411030011549d1520403900c61240302141c143d100281d00745 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 308324631 1250 308323381 308323391
    0x509060405040e0307080304030509010f450308090415030c0302041109031b190303120b06070807030507050606010302040b190e040608010605030609030309100f060b030403020a2f0103 81
    0x8403e51561103034100c080e007006408000c100c101a445401412100003c0e40c0b002c00c426404a820344890300c8035450442c01e07a0310742d00072039446456461007040e241c43e0402d008410543c0b1080802c94140541c0003918200740003d1800160b003454010003000d812880c410342c030514070755150804c4455050100a110300c0e180d40e04072034182030308820740d044044d006042c0d80142e59182008485400410a6103000700203144441d10403020344802c80046070303055218403041e480c4030f80b41040201400d8160f01d503ca1414440b03080812015809030041c50700c60f449455403124542421440e09170000d140904060041005014560707e032000d89944100004c00c0b04c2c40500825030598031020101c211541080c5000300004046805400039411200d040d01a03c000b621405843d40d101e01c406c4136074035255071120040f005529a181d200034402c60f25240c0020b0303207944940011700d0369441a80d042d00142e00ca20503c50921102400303160a42440012115076000ca8040441e08803e44140c1c05042c1a03441c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 308325881 1250 308324631 308324651
    0x6172e0c03060e013215032a030109050112030507030e01090315020a140a080112030c12120f0603020f0d030e10020703051608120f1b0715050906040504 67
    0xd8000d00050285001d0880302907171185400c032100038882c40004882660585001c0c0c0c05100901042400580503004140c01182e0400c140b4040e40042d049810840c0d1a031802882012028001c0c0d03000c0c212410156969454100600155181a000885e0010101e000350340003a8001c0205d52007642c1c1424982da02c801ca580042c0c604103880e602c081c0140c030b558141c89010b16455401004500c55036280d020401c800d1040380c081c1c500911040c000407440190041c02244800b8000460481c4245401b22a80d4403d40d255001c022152045c5000f2550512814011440300d004552010000c01401c0002610356000a00018140c460450207050f0181040c4240343c4185d6001142c0c100290041e500690540d00007903450300d81d4801903400703018003025180400c1002e120402140c0c9454002c000d94214070705070070203503405507000707240c0c2071401c011031446d20002c40f00c500b415a4070800174000b080d15000c1d803058012050007001080000401800c5180d0361280240d905031001614001108128 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 308327131 1250 308325881 308325887
    0x1150c081902010204050310020909040b060a0305030d09021e030604080c03070606031a010608090604060f1e140907080613050114041113090f11011206172e0c 70
    0x1d8030301414041162080c2a1400c141c054000300102c90082e800c9032107001c4002210300490241866065112840801060100b10301c0c500c69a00100020501c03000c481d541ea40349450740e441491820b11007500e507130404055140c4001c0c0c40b14080b5140c1906000340c0d8114000035120400140020300c0c0d40000f0809000e180400c0007910030700c1d44d01c140d0030000581c6908214111003160740203404015064400807c0c03252051a00038001c40140009026644035903076403602802c0d0072040400d105d036840d01d002c01d0310410300c400004800042030001a4000090090300042480101000741070744c0040f00c20400e034400001c440d039024803103025810380541c943c070b4140c1c050001c0300300421a505a08081c4020711000810255503041e0840300414443d01c003a0040c0c068a03076280c00600800c0040418401148100390b000301020814900108120541030300300c0115012900704c03c0c4c000c001d41c00da0702c3c0c00031003c012950a0106003106c0740349003001400400c005003409251044100c3d10703078001140042c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 308328381 1250 308327131 308327137
    0x105131a03030a03060f1715070c1e060615020a06150510051201061706101e05091e2101092021030d0902120601030302030304050d0801150c08 63
    0x24160b0399102d408000050141ca405d0051410b0410300a0300000c203024510320054070b4a02010152400c104809880c40d0611070040043d0b0501c2900060280020107800c6202071680140a8001c0c10b13a019082080840c0d0741900681d80c0c41c0b010f20300c0412405c1e0001034040342c090303010501150004581c020b4000350b2590b644015000010034044910180c0c00001401d544c1004040041c1d003607a80303c402b1035080c00210414400c2e05003160202c1c445080004840200080724140b0810185414003403c8110341c5c074240103800a46c0214140b0014034020038094142c1007014240070b8012085030000f20036801955891542c184500d82c1e4111b54442900007a1185410010729400b10790100d11185210a05082041c410140c0090741020040610100d040680b43c600003141031550700c11440c0014142000181c2e408170344070105e05002e00040048a000c0c0d4425400307580c4030700b8903151482c541803080998005000390b4500522103004080c924038002401032074a40c030f249503d802c015520348 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 308329631 1250 308328381 308328431
    0x160902160210030b1c0201080c0c01090c03150f02091c0f15090c0503010212011a13080102040f0518240306070f08090c030a060c110d090f0905010513 66
    0x7892080c2e41444907090ba100e050f0001e0242c46210340c1114000c442c02d940018030f60024042071541021403d2040100d0250141544440000440940d9038030303860400405980110703a10101d41015440014560003800c4543e000003c2c01c2d400c00750394400045222203802034400d800b0403401070302d6051007000017100034140c1d08041c1034043c80040741860340250100c0b2009890000c0c80040010305800c051003258202500c08070104010f900700409884d6107075040418460300c01301480811101c0c0c5a81c0c980e08010101c42c0c00040c0e07158030305280d4550384241a07015500c00d141d0b006281c514a4940c22290350308c42d40300c082303070b102c500060904280c4c8000340c542142d8042c0b19101c00c01401d542c0080420100d00c646485220259858210259590203100c046039007680045860f0400500c083e0070032180b01c3c18074201100002c0040c01136070300c2c11115002038000105c4040c01001409442d42c2140c01400280f50107110960411003c40c104440316040c0400d1282d5540f00300340131201c8410820f03498 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 308330881 1250 308329631 308329639
    0x30f070324140103060f170c3303060f0f060f0c1608070501140f040f0b1b1b06070f0602030c0d0f060b250b0c0c060a0e060106050703021018141609021602 68
    0x110009427420b607580170140b03510b81000031070b0b00d10ba1514440c0034420380c3e2081e1380040c04011000b00c80170a05c914030314625031244d08004203105c05da0b50340b40a82c0162544070549401821010706034111703003a0740b1a07254803d88182c0c10841c4144516603000b16105425011803004594600e00d480b901c3c0d89034030441d0312403414100c0c001c00c0072541c3e50b495030081c00400e088211001c680310b114501152504900a405040121400c0d03040c9010b080c9000503120003401000704c00a03c2106840700b0302668011500b050340c1500000703d525201d0300d9803052240078004484101f10050600100800038030480508100c048820442a0865440c1a038188041a170000303400806081100300740c11a07802c0305154400c030b4010240021000350a0b4880c0040c00310a00000b040640d00c0c0c08825036541c0c0c40300c40c041d002c40c0100c03036000e0116007290042c00400d40c0700e0481d038107075a41d40d810b145464a42e108445d240b550404601d80e403d904440e82010151140100e006a8519101c0407040c0f61185d401402500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 308332131 1250 308330881 308330899
    0x20c03011104030204050609090d030c0302190804020a08010c021b03010b04060306050a06050418080309030412030206010312020c01020703110102030c1629030f070324140103060f170c 81
    0xc0544200c0c00352040321310a480c140f10507254401000450201110800c0e01d90380f00048204515120b5009110003004904005240c9111158040c040500003655100440d195000303010071810f210000b2401044004000c210034108010002c1d03c1c1e00740d848114601410446201c10745640a600480003c04000c004100300c942d81d143c460060001101d20243d030a14206000030710741814022446113050315840b10010762620b03074841d0040e4002030706100076444144000300c0c07038080180e40d01001e50b0294008107161b62551420065001c044280501103400010310040e81d6600000d4400c02c0e240d002c1882c006241d2010700403071545c06095194100b40c0710b01401c8481d100c240c04415000e0701c031015040c0907000780c40c4070004001c104214140181007000c100040307282d41c0040402c1e80090061801140309014400c0180d4101c213100c0704000f541080c200c0403c1011490400d051850b0b1003070030103000061400b44164459900d511841e071591208900c0300300c00701021300520103411f40061074030b08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 308333381 1250 308332131 308332151
    0xb070b27011407020f0708150c0403021c060b01030b1804051015030512190e060d09051005010f0b041a0d0203010807030b0108030426150a0b03061305030f0307020c0301 74
    0x5090070180d0f582000f5028460f5203850f565008109041079070014001002c0b15100b400000c103500200400100c2e5050081c000400181c0d41c89540c0030080c810f03030450030307400249402d01300300711008140428145803070050000140e86800305240c40d40580c03103e0318952a80d40d400c009081401c00d01c000940036143c0034240940c0e40d5105807503000e8a000d40c017180c40c2e020380241d00050078468842d100030700b02081d0080030708881c46040c4031920040b002d04064200f181d01044001660103028048800c0c0d045144801c0340241a441040d0041620480011072140740c00810340040c8503c5c000d1084120110030f40040041d20340088a8040f210100215074035a944c2607100d48800b4180011101041041c1c00043c0412001058400740d5191546140001440b180d060074440d201e0002c01c03e150003040106c541d40840f41703003400e1250418400100f14584184101820014001c0c1994260842280200c0120341d00009640c00c815888442641c1d81c0ca8912090b850903803004c2c10103a1543c2403510340c00e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 308334631 1250 308333381 308333411
    0x7110102040f0f0b030f011203090f0e1503010b0108060112090f0b070906050c121c0c052a0a060e1204091b0305070e010e04091505070206010b070b2701 67
    0x54200c0e501c1d10007a1a0580c2c56045201301444140c070100500030707483e00144180a40400741d0105a480390034921940c07940c40070b5007003400655920168a0000700070800c020107c01140e51809220102c008114407600c2000203018107001528840c100107070f55400c0f09015070b00d0f90101c0300c1d00f6009401429220000d181ca02c9c460a0100c0d00c2c3c0c00080d0044c0c10010b95640948180c5582250010190150301210202d4882d2a0010702e01e100c00b1901c0009850101c951510a50b10907501076601c25540311461b0356802c0c420003200000000680042a2000d011900480c2c0e000c003031644183d0110700203500d81400351501400300c0c03130040701302c00000d00011300401641c0681d4004202031780c0580b00350020001902214400c9403a407001c106a610320800c00d6200309015058020024000141d0358425125106911041a82800391680d01c1c0140100c50f0340400509005004421800c0c2c80d0800c40c1d81d400304040380c0940084210314134581c03030304d08a11602c80c0f032005602c8550300030403041c45025801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 308335881 1250 308334631 308334659
    0xa050403020118050c0f0a031e0c0501090f03060e0307020907020606090f0f070c05100c030204030506090703020a230405040602030402040606051603110c0d0f030e0609180711010204 80
    0x100c0c09907282024041e40c103a45011049540c58000c4064282802408188076041c000c00407110381c000c0409901000141d2003140d0710065404225803110066040c2c5040a403081c99a00800d061108500d0200204520500004142e0794014000b00da0300c01c04ea00d005296005000c0000d51000700c110130411100e600203005403145500300e40d0b24506841d603250340c10b135080c410360342c40325902591000511001d0103a011601014030603000c550b0341620542d612001c584426a00ca00005c3d00003030100180070b010409141c100092201030b00d0000c3c40c0d50b00081841140384101030710212903a1040149000d8900040c0320f2342d101800c280700c0c13860a0f2070f0200c025401110101c1c03080d454a43c0100d00c0d24800c0041c0c0d425156001050300721201c3da91403c2d102e0307252000115200f40b050f010b188101e0b0329074100ca5008144200180b150100a524000d8501440d0760360240c001c041c20700041000e9628a440d000342d401c0a44a11003031a100e0810864152407000200e002030b60001500050001040b901 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 308337131 1250 308335881 308335883
    0x10507020d21031401030c030206030910240b0a0504120602250204180803180a0804030f0b01060203030402060706020a05120f06010f02060405030702040c05131e080f10230a0504 78
    0x204000803113004010102c08203003030002401d0802803100600c01401d00340025030f0800071810440750661544581d2009940540b0302c003400b040b46440b41d80001440423000100034010640040342411405000102940130f140700782d012402c0740d0200750b414402c03ea4112584103954407070320a00000c41a050360326444060000300d00551401098440c100312203180100d64581c020075041c40c5440d004a6219510140c10039001c4900541d0700d14000100b03400001d1004500c903c40384845148541842000364005074485400cad50400c100304001030742c4e00c00c00c0341ca00c0c0d43d0100005840d10305c481c1c001c44c0d050207162003400301c0d003804070140440d01030118801031040000340d0f50310300c200c04840c4089844010681e8001d00300d500501220300145465003000f00032840c689003007070400c000406481c0b4a04410381c1304141e0300d0000d020b83c05900a000040744090004040102003078910810181c2d540c0150400e0043c0ca01e076109140c03140803561102285980044495040c114100012008000c11090318 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 308338381 1250 308337131 308337137
    0xf04080f070611130e0f0c0c030c0703060c03050105010801033201090309050306060a0e04150b13020a1d06031b04150203030610090b040b0f0702060403050a150218010507020d21 78
    0x21002401709054000f81d031003030682c50070448058881c411a508150000f0307058005500041c402001503500822481d4002c0d401420045440d112400d00030b030403a1410f81005040080e00c0c00184041400441002d04c240c0c002442201c01c0c0000000c228080107540502001039420902e03410145503210701c000050700d10480607a0055121003080119401e6a03124000380182860700003030104d0403102520410001980020602904c5080001d07404140031668000c15036000ca2250b0003039a00803050301b000c2c410715030709441b904070150021707003030b80801000032019041a03004034450b14856002d58004120071902c2020061a40c68040c0d141d420480d8400e001d41100400500d500384100d504800700c5d1840d000f814074143c10203c440d4515809803000140d4203004110341070058488100500007180200094129101c135031621000d981203100d02114802d0050110081c090740c01c09107060450b07000d0811039502c900620205a41014000300500103809000300342c141c00200c083d42c1076900301d0b076036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 308339631 1250 308338381 308338417
    0x801060e0103020d5907090504030c0b09070b0d0203070c08040602010204090509060105011b1a010f0302010e10200718020c0610030c03030302310602150f04080f070611 74
    0xa142c0500218000d030803045c0301c4c3c17901c2d00014a4035003080100c4c00050440e4041e00c4003181c9500d900826200c00703540440000c0c010342140028083c010050300c2d0800804030103007540754039103072000160f40149030100e08450b80c0000400c0c1440d010f21000c8119a6002000c60b0f1a04e0351006c001e4001d41083c4901d00d00c1a082c0301c001404500300ac95928103880058507280010317235110703400c40880c0e002240112202d8281c40407403810361603102c0400b8000c1501201c45d0417514210300c00181400101c42310305009940c2d0201e07040b0116001a4000c010702d00d0903001203a00f076213900800f89001c40707903030180b07034100b055404141601940b030300100300d00400c00c81211802c2d1103980d418103400d40c1034171001d0b0580c2c18064040c00003030301c6a0002c100840d80000300c4101c0d881d04003580101241c0c001104010f1102c2684104492501440b000c0e841110031100c8511501d400306e030945e040040140300500c110800a40c0d044902d0608040e1641075801400401034900152240c41b6268020f50844003000708071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 308340881 1250 308339631 308339711
    0x50f07060c08100918030503090f0319030612020a150309140318030706170c09031506010320030604021e0a0c0c0f03120f030605040207060204140a03030801060e0103020d 75
    0x1401200101000d051240f8030b00e40d0103443c07c03215a00090304e0120703075020b0500d006030800c904101a089412100d03018103602c1310412000760495001d0380c880290122003040c81c00c056079424600e601101e05c11404029044000d4100302c0040103104001400c4095205080c03141440005c050200341c04201140102070500070100f580d905514031503e00010f02440c0e42c8592001500a50741d00102a40c481c94185003000001030300304000d11424061501c80e8000f045129a8540520001803110341560316241007080c0d80110140300090132035000d0358000500e002011000b030119000700101e845191b03120181150b00820a587c207540a4a00260039200401e000300d9050340141220361100100c0c81003000d14a0a42d0002d581c0004070040c5669810b0000b85919a400100308051244000581c0c0c0c0d801c14131080510f81d800c01d80c035800355035654014400a508042c10b0750555581d03082445200e079180c00100c1c080e1054400001d00e890401c0308551000d00e41462a100008040d2840c040080c94 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 308342131 1250 308340881 308340899
    0x1504210203060708060904060209190b03150a050a090e0709021c06150903120c0c06120e030408030901051602041404021f02120c0102040905070c0201171006050f07060c0810 76
    0x1170f42c080b41d1045811012900103000d9500605c1280170103403666440055525a010403c10079501a510b2004000100004006c612048124614040310340065107400e05020038070a292502401d105541d585020342006c0100b0084407006200051040d0742e141e1030b0074812a140d0b00d010700106138042c01c00c10702064103584d0301e1a5400d924259030307410703240514503152a048034644000c44402e2002c002c1000010558400000c0b0217801940c43e12000540c084030740c0310860704103240b542d4413500248814089400084100c0f031240d00c00740782503a2904204502d00489011919000358042c0c0380c0a01c219000c514501d02c02c1c0f00d18002c43e1202501c060f42d51000002100f20f100950068001d8809140c0e0099440080c05501e86508001801d158440340b0b136108454040c0e5011002c500026540021584d011000b11b004e00c40c100507071400b5040940700b4441135291070150100b444004100d072250001824151402d85d50094018044819491270140c00100107581d0b04110b92003001d00802c814034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 308343381 1250 308342131 308342147
    0x100314030403020105031b122403060c040e0702031b0607090e101502010b0904061a1005191106040b04170702060d05060604080d050307030f0c0e15042102030607 71
    0x82c060311111b01d599078942200c40056090803c07021040d0080c001107401e086020060307441000a051042c0242203c402080005540b08400c1c610a922070b40c10401528101800d4408888a6884940d215110340c4000ea0642c0107960f01001101031009400c401a0380004501e4001c8150f52103650f507181d00c0d40901d00c00c045040300c8417406103040703040400c420b00115240d40381c02070080c40005003c0500100080e08200203450075a8840d4440c3c074000100c10b2404140306c00228104c07a50069608910380203000c501400d00c078501c022506508922603d40039002c4298220195403d444141ca41894400102d01054506848074412035820440c040f1601c0100c600c0607400816107802e0001c00703009407016250040009400200c1840001000754007041a000e0500c102d4a4554480c5001c00b4000d04440c1d40b4070840f06264223141c2030040e0302c0d0b00111101300d03140f02038582020800040f00d400384184603644c02120308144481038011401150414845414401ca0030345000da200d488041740c680d0307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 308344631 1250 308343381 308343383
    0x15060e0a061413181a0703090302061303020c150a0807020106050d0f0c3203060105011403071403090123040b06060c0f1902030c0307180e0102040b03100314030403 72
    0x120310b585405400340381c40e8401d00000110807501003903d0444c020421203400c202581101c9488403421000740803c8680b01d0541c0c404402e2408104120050700c3c029039410740a8121421084d41030100000e0601c2030100940109019240e5112081c0d0400c405241742d014000c000005880d0700080f071905403060207404202d601c010088a9180526111000c1000b04404201d4094558210004942b000d4148010606281400c01103c0c410034904101c550600f00021500c680c101c0300050180b0703078019254040c0402c1c1500740e80e4683c0d4821006603500203c0070301d5200304400200802c4103c0005410030b102c42c0d01c2d18004141c4108060381c40e05654201658004c1c600c1c44100005440343c20030b94064030785201030004440114003440d103444d0801200c003e40e03554a500c0c0007a0001981802c00a00d801030310203070300610140380740c40681d00000c0c0d015088044d0130b81d111900c1403903168094040c1c034083c00c00c2c034036900c0e500c2c14100030703a0700780c2181c91004a484510408031030300002d5000c81aa0112 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 308345881 1250 308344631 308344649
    0x9031e02060406030b01120906020301050a060e0d060b0f1206010f090203160f0507060603050102090103110a120b030a0507080a0501111222060911131107081615060e0a06 75
    0x2c142481800e6004c0c2c07180c09030003810811501810390706c081c950b0040000e418000e500059480d4100f4080c008103880c0c5800c0281480360a01410350f490b250400101c1ea00da030051400941d06020000092603819205089640708204a168400303001c008a840380c120344005040d19a2581d41d0f4900c44140d010440d04425440700c07a81c001c0315814042c0c0010890200c00341750407458000a581d4907811a046500b00b42e8841c0c1d070100c1d2042c030755600b600c54410300f102600c00305804c001500c030b0300400001d51550710885a03901c414000c0c1c0292010021244025409402c3e100d909864824041e41e910307455006036402d40c2440a54007100840c141214612680c0d0b03003100176181e50364128031000e40e03a48940300781805000b8a8800c0032810714032460801074401c5210340d0520580f0810450b10881044110070102d10300b00903840306108000c11102255404120180c890080403901040c0f55444d40002d80356074403130500c02010502580c010002d5500d51250a6182c1d141c0342124000c4514502880000e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 308347131 1250 308345881 308345887
    0xa0c17060d0203070e04080d0c030b030c010c140d080910022508041512060902030903040e060d050f0f1b01081305010e1c030b090f0412020f060709031e0206 69
    0x9418001c0c090500c0c940050102c8a81d5940c42504940c03601040fa4261361403000400d020075034840c140501d003080503141c5010b0107400c01641c00240c07154102907400b41440502001070007000204070380c1c10000034440c025181820f259000c003420000c000c0355003560324000c40d4400ba0ba14a158400e880d03002d00000a0a506030001240d034030304a064125040e12485e40a00000074000e5a407036094005480d56540c0440c0c0340900100d04041c0c1d081c0317420591580380103100b007150145000060f1001c840070707012107030182d455610102d070881901260180050294400d001d080740000541c42540c482120100d6004c90301001201c1460346650f1b00660001d080e040100310842c81e0313540d0691b5182c0c000d4000081140c46007e8140c501040400d10501c030440e50741c03003090b696070140f1a00052800c161011120352410708060072881b031000300001c00c501c82c01503180310301031300c02c0100d0001a00020102c1e450740c2001e0768080c016000d940300c201c4210038007101c02040780001d01072031301e440e43e8040c1003141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 308348381 1250 308347131 308347141
    0x32c06030c0c0304030c030510050c0d0b0109030c091e1b030b03031210092405120a0c030b040b060d020f0f0f130c0e01110d03020313020402030f0a0c17 67
    0x1150303201078419040c400e814004503003280b805100a10040d446880c00e17106051861805a040c00614100c3c0c080720343c501003c02141903900b40031203000b91403000002038000d036103900603101c4404a40001e04112003051000c50078224640c030058072289210407000504208090550585054111002188005a0170702010700c1c0203400080c111840107045c1d07070070003064004422220b0703c106c0303008552600303440c030822102100344501c00c80202c2a07016a40146c0c00c03180c24404000c140c1c440c00c0c0c000d4040c4503c81c4400c000078841c0030b40c529030220710180c145699003000540b0030020307102034500764800000304074140361540014441550140c1004010426403080102454245540c40e8110101140612403541d60354440409860329900020b4011486000101482d0000381001d060100341445401c001030006210001c54555103000b50352590381080c01c1102c0011200025041070011080c050380f040040c0102c0e00c10441800204031041400c50221a02e605075204450000302a1001c02c2c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 308349631 1250 308348381 308348389
    0x1d1b030c0d051c0c0602130e09030c0a020f041103150f01110d0828020705010510061215090207050c0f01090609030b0402030c1507030809152206060909032c 69
    0x101c891019400d044513400da01d03858180590b07010301e411000c030019401050003038400301100e44d0780000450009605244c4031049440d5503802010300a840f03984050342d0604959a60f03040b0781c0d8402144c0180c5a140e040021000c0664503403680b09070b00c55410f000322040a94400c00360540a04c01080c000c0420301c1000d002075910380b201400c5031002ca000043c04a2100d1101c3e030300140301c110084801a84e98200d41010350840b01c01400c0213208040b41c2700104200c0d540705240c800d2104003070f1740002d212401070b10b02c1c2000c03011581c041480c2c240085503001c03d0200c0850f1b00080075070b003690130081001d05d64004480741c0e02540075003070100d8014101403000c2946d4208150b413151000e01114441c0c0d0881c0009040c4171019010403081c4140001d40e0310400d0780c030440d91600070058000a01d03002c18400d09850503244001c050507270f20517014103041314a1070149140304c14150498801c00229807100c0e510303800340100c143c081e0702007114911a4842204141200400e03603074610001408084070710204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 308350881 1250 308349631 308349673
    0x80403030905012d0207020303071e05011506031a0a0b0a03020403051e0d030207030c0204050403230301090e06090706050304020109170c0405010918061d1b030c0d05 73
    0x25400c00d41c0c1c0340480c6001500034403454103c01c520000078141080e0220161918007030f2142c0113a80c0034018099140180c5000060300c0da031941c13040362040d00d1582001c5a004c520082000900250309000340c130040803880e8140b82d425a1080c0d41d051000540c03400a180e0011440b41c0c1039a040410400200b080104070380c0034101ca4400d078034015140c10790340d446141c540040e024001c55141240e4550207401c400c10012048208100d060941c102a41a140544504135030700000e80030300d0f120000541050720481011440f486086840140c1015071107140c20103030030034060501103916040d01c50641140c0015141d104112100040401c5424580121a07a0304081c3c0103e050000c961804a81c0c3c602e291140042003000000900e2400c4041c02004140e0f04180d000341081d40c40c00003c0c001c0700310303119100f030b200d50703007090002c40e074540052041180c01c2c2092101007000c0c060107071050700c554040300040c5003508084088841c205408820001051070315100103041c1d41c0a200c160580c540d0420740 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 308352131 1250 308350881 308350883
    0x30f070e030c0f27160903080304030e060f03160f2d170702030702100507020d0605091002070b01080d0906091809060f2c0709050402061306110d02010c0504060804 72
    0xc01c116504613070802025420007000080ca43c00351200070071200285030802c2c244095490326054081e43c0c13641d05d41100e01e100c0580b001c0d08120440401c50840c0d01e40004035249015421001a501e241c0280c80e8954000501000c1d400180c07444032101e40c0d5445400100c1074622044408407200e450f142c1d004d03509143c2c0070100414464980403c9400800c8081e0b424860b80d0643c01943d40e54155204009140455048440a2080600240c00561284036455040030f07807001c00000c440e01c03801d1405240c000080096075400380002411001c11200c007503014120740b5031070308880d120352008070181c032408458054100001c1442070100500c040d0486440d0b0b05080340794000501c01d0107a00c40307000382c82d15000e864581d51f80307449801402d03c0d886c2c0c82038407000303800007102e421690040d4051526603100c0c1c850000a180c40300040380666541e0402c8072011034010b550300d901c1981d81c82018200c1c119682044a8a00616101d480054010700407150420380c0c60303550625040c20300901b95001400a40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 308353381 1250 308352131 308352139
    0x1403010b0d0c060906021f09020d0605010605070b0a0b1005030406060b1204110d021e03010f180506010e0601080103021c0203011e06061706060a11060a02030f070e030c0f 75
    0x604410584545560091042c0201c580305034490404001074010f054950002c01154800a440984100d0024508150403161007000c91400032900006a041e401c10300003909241c0f40c0400000c95035040002008040d1065120305c8880d030b1001c991604840c1d0440200381c01c9a0110600302d50144120000c60f4400e02c0b48000207442502d403c036216031900704509200c8401803620501052124881550800e503108450301d140c0c40640794080b404c2c844d400309034980040d4815182d8151684c080d0000d0720f00c151a114100200c28400c0301690081c143c1c01e10540d80ea000e00000411300c0c00302602413034031904060b110750b0703d40c2c7d02c2d503424080764401d815460003143c9194088000165400c1c054643c0001070002103070300f41c28891000608840c0158014024800c0d00c909600030340d08003155080e0b01500456042e81c4480303d508098444c04032540b80c004090007610100148440381d640614061841412014004e0741c81c035505882001c03101410725403541c0014003514407440c0c6001c60400c0c481d00030b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 308354631 1250 308353381 308353391
    0x504020a1a0d142752061b11060c031801080903130312050405060d0507170105030a2d05070e09060c0301060c170703021f0b0a140301 59
    0x40c0c070500c12a12501c012002000000040c0b0440c10003101c401c143d4083c4c406007007014134066441c090307920a21030360a82400d91030b409400750602c01078110105220300c00c1c03a0a1000c00d900c4120080151003018603032501510341170012601074451101048080c20510201c3c149400544850784205503110704103900c80c2d42000344583c02a4240058107600084001003100d81c41140b0024002c17090040198900341e1060246004a1503504590401c0300c1c0c11079100c0303601005801d001c0303c10744075641107103030042c60028942d28490031396031189209000070381e00d10411481011000402c40800c0c4a15903259124008400208101850400c080c00d03064100030030800710508451040d850900c402d1755260030031a010030001d000d0f14001c0e40d1041e8000c02502e881e180c0040400d141d80018003800081085c1c4240c90001c00180740c13003c901e8580540040d985a80c59864002c2d520322020300ca5244000c556220303240d108001c1d00611a0320480200312070100c90900c0c14601903840da448480703905648503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 308355881 1250 308354631 308354647
    0x5011208070f1203020903010b012a061418060604090f11010306090614180f0112030908060c180a0b040b071104020c0d020f0d090501080403020a050607050a030c030504020a1a 77
    0x814040070010b443c0d40700580c481c034021080500319820600d007241031000320240000b03220002d066108480b250310002c020460341c2424100000c01d030401200b410001d03010140301c412540005441040e41105088900e960348450620003503411041c0c0c000c1a08011004e40c50008954000585e581c1e001850002060703a698181c034002e07160781c1c2e030102e0304007640c100c0842c5075424402c040e0101019444012540c90400006100850b041403107006542c44031103043c0010540704d0070807000100885000c5410a06094115060300c3e0710880160760580410040d6101c1c030305181e1740078422103020a040c03600345460a080803401e6800000300300c031040c0360b12038114099516480503002d1441c2c10002451a015010800380c03030000c000c0340d005140d51114602ea409940c0c131042d107005445003843c003004035840d01e00e4143d10b4003400460044c41800b9060410131505d078090082d10250303d02d541c1c00c0c000c8801898050303040b1b51090781e001c0d401000c1504240102d0030b410040f041d4200705c040341c4074900140e03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 308357131 1250 308355881 308355893
    0x5062101030303020910031404060e030c06090114090a03020a0b09012a020105060a081902040f1406010807180506030411030303070203040608060a210809040608060a0e0105011208070f 81
    0x20036001240460740c00b00e00c050460400180c1401c0d14002400d080084921414207400c0410380104014485031b00c4000b280140f64080c0195000d180c180300440310a81040000709010784041e140c003d4a1020140c0041c1450b040003494460058141e0060111101d454950110140006020110964076403220400c00500e0803a81e00074111460707400c012052034101c0007425207801500e800d10604c0c0c0014140704021010540700504a0130041b2848282990f00c04600500700010902a80a01e8a80d032200c0450030419039070700c240310999559030a036032015820784000041d542d04d0f0900d1407403603000b4030440c1030040003035401500400000114400b01d40000c2d00c1c0d40e10840d00000140c0011401700411908440c60075081402150400304150400701e0b090080300292070052004540c116108061146120413150050b0002d08140308040d10b51022a64505040d110301d0005485d00d0404082e0741010301c1954140c46108031806a1415503403200d040a41000c48147c40510302005c00c1d0f400202 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 308358381 1250 308357131 308357197
    0x301061701050a060605030106022a0a090b010207080105070f180e10080601080a08030c130906080c01200a03120204081005160f0e01030f2309061e010506 68
    0x50140c0042541c1c540749031031105481075944400c1c00e1150038030043c050180c000c01c4045072200c84661003a00c0082c05540240b0034044407941c140c02c6403000d90046001c04681e0070040b110380080c0c00320b404055503210703150708132513080b250200010003418402014611a0300300c1201c00f1511104080016294000c091203c1001d881440350701c50b108034104145682406058010b081e2100500002d04c0c6c40e407100080380c803004040105032180000c1c6010540c1c0381c0c1c6a5030019000000c01009899113400102d0340e214400030b02c0d1804104620205400315051a14135158840218090300801c0d00554080e1890f4105407001a2000e8080c0000f0071400301c10000031400e1210280041458200700f44603010040d03507642e8030310030041c0c1c01558030890b94001c185c000000d1002c1c03a0004840d040f103040796000b010640101a601340404052a402030f54400c082c0d401600020161201612a4007000d208120340302c4202d40c20031100001044280341100140c5004441004810341d10903001000b004440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 308359631 1250 308358381 308358419
    0xf060a0302041a0309030f030601050d0614010318050a240e011b0215011503090c23090f06010305041a04030903050d0e090103171615050f150906030106 67
    0xc0c1d40800d08005084200c55220038a400d0050780903d1420101c035041c2c0c40384070b03c80c0350500c03980300000030076010b900c00c0e0119945d00c507032608100b01c4191500484040d40c1c00c42c2030324500203800d20300b0720742003004007010081c100c40d807040050960131041d50b98614413500741010702d1038005400c501e08030b212803180034030800000d044000040c040c03a440300401c0d00780740e603086241c11540080c6250303400c100c00016260649500f4503a031400064640e108030098480c022005000c00c0c4c0303040740041e0504290002030000ea42520203840d401c0443e006104c074401c01250b078000d00b140c030203003c600194000d9016a4005005501440d50029041c072404034002c0c0644003140011034103c010030a1040030f1012007031107901881c003400011884000103000100600000d407803621120443c41e20414440b04a0f54020b24004000f4154072181c10301891002d45902c410b038800d403c041c0000e903c9254000284d05c40d04040c1214040c28403107406010300c50500500064144d9070310240490f03109079101512a00c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 308360881 1250 308359631 308359637
    0x50a02040323060c120a0504050c0409060609110f1c0213030308060108061c02132d0b03161205010f020d091109071e181203170705180f060a 62
    0x707001211001d898450002c0c8142518601800303005c1d8000810211186c01c51004280031031a600c81381840fa04058110440d940d1291400e0405001c2040d0303600128200c0d82041010000c000c540007200125100f8184c101010500801c1013502e4184108088440c0703011140380142070149094a540c1d00c00801e400c00e80115074403034100245503901002d40c07680884107852800f8001c000a01d140145002040d001788120b00101d02011800a10381c815000c015a4900d48801224103a601140c40005101c900690509100030780c0724078240016507020380350620b01446140c0b8a01401500008511041201c0a549614000c1c100e80d0306800a040c000504020009068215280c5200000166800f01d8000ca2001c4100b0500c150400010380803140c40c02142014003000b800100c450100900f60004899890040481da9881e6210442d001603c01d0b1150500d500c0418600004480212110000104100b040141c1e240580b204c0c20030a890280000341d000c084c120000b902504101165000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 308362131 1250 308360881 308360933
    0xb03070e012616060e1011030a050702010c02180402030708120405040902180a0f2a0f050d1401091109090a020c070902040e150a0e0a0903090302090a09050f1906050a020403 76
    0x111b40f030029045c07818040c01c2d0403d042d1500e84e035180d068880c0554082d1034144000440e0000a5901500129620130f0b4010000d955480d0240d011280c50403098600b03900911070504046680d04001a07040102c941c9000050309082c0383c001004060300341060704a03080f98100c403400d004405c0c00c05d02503003d00c8511401141070540d20541008582601c40d0300150410110031412041d910b01b5141f100360011031601d408014503114050314079104150401f8019803a15008460004102902506907140050140030728010900104100c0c010001c91981c07010790400490306000300d507401403114001000a8419195803490761000f20b03046940414801a0323241c00b00484032040041c0704e0003039081141d10404650a04080c0300580300c0c0103107184401a656a0440c1c241809001c82400a40d401041c0b070989141011600c0f0141a4140081b200c51107a080300d85a850404620106e0703800d401c004140d8222007644815010f0030010b0001e44501e6820800840403035401889021070350503101c2c5100b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 308363381 1250 308362131 308362157
    0x3c18071517040b01140303040b030f0403050c070315050c07110f010221030415060e0f06130905030c06180c0105030c04150203040608011202090606090f040c030b03070e01261606 78
    0xf00304004807117074444d0f0030030441440000c01d0749058a030040803840c000302d0103644525040c2c41d14892810414024850804000304015902e242c41d01200b100710414070003521020500c0b012406002c0d4024020340010035500c2c9181801071504106030014411290001c8614071030a201c0301d04100c6c0c0303090100d0000200700074801d240b1040054815151000c1000c00e150101101610001a211540c4400400c6c040b13021035407500e002c06031042600108001f1032134503280c07165032a03000708410501406250001201c107584001001100713007108001d043c1e0809040c00441d159480107101120910051001040c0324400340b070f02d081c0c404e01c15002199900c0c28000c01030049d02e0142c0c1f0043c00030300d100c12042c0c01070700c405220b2500001e003950f00c81d40300d4418000140c1400e1440780b400d07800504e00917940c8003603541500310a44107603096042d1034685860b4074109503c0f00b400d0041d402e007850940d0300c5044c110440001402680b00707500640e072040103040c60b002034008090f80700d2000540340c40c040706 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 308364631 1250 308363381 308363399
    0x30e0c19060810080d0f020f030a0905090f15040e0114070c1403090d060903111f060602060f040822090207120503090c01083c18071517040b01 63
    0x182e00456058410050103183c8110140d455489172011010403440d10980e002c441d000300f20151071101b81d2002c1d40e80754012220003c00302c02e03a80c0700d160701c0f94044c24045a01e4156001c070040c020a1140c10300c003424613009013803101400d040c0003418815940c8040820340503201440e00b41c021100351707032920350080240c1001145005041100c0f011600204000046541c0d5400203440c410344c0600c020600306154201600c2c840000004110140143c1d0124040a014071080040041200b00200201c80d1070f0203040340d0300c3c04125240ea900000101c041008201f019000d4401e40f214611140d0500c0800c40c1382c054442d40c5607224943c2960003054000c100104500c1c1010000c03070a151260451812021603540e84d840e610009050242c0ca5000c10b21002031503405e2000c0240303004038590510f10250144040007140c0003840340090000300400d0b017010500580700c01d400441001403043c82c1c103180e11074072030104d28410350f0213001c01e820600401204207409984228016075081c2030941c5007041d04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 308365881 1250 308364631 308364647
    0x30406050c04060f18170c0a090b0f06070c050a060c030f0309020906190b04080c030c01020c13020d060e070503090601140d15020708070c0f1e06030e0c1906 69
    0x4121412001d01c01400f00d070398001a040d2028019242070341104041c2da00342e0024018030b40141c580d4007422210712541c0500019202503085040c2c8020560503a01c4100508503903618005541c011906800342100d881c0032000307403000034091200340c80055034510008100d00d100f07038401d00204134074190440c18103410280145c0f11822a040901043c8043e9000a0040c10010300da41d05c51001840d000c2c0316210801424030280034111003485d0b442d0b4985030543d95490380c2100051103840707150001c030110352010403e40314608001e010040000364103080c810182d000b501e44000c00580c0e4940015009019001d018000e400c691101c95907424240402ca0034030005030003603403c242d41129032030150346852480c2080c1c19003200c0c442107044098880d06001e44140d003406070030800c0102d001c0062010b1079071480c00701d80d0b19454201a1607540d030344a03818000303c01300404050340740d4501005a207009070008074000620b402a00c03048181031001600904880640b0f50002240400500c03070103800c03001c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 308367131 1250 308365881 308365891
    0x9060708090304030c03020105070609021e1311030402010518130203042f0d0c03050a0305040608150f040504230708010b1905010e0303070c030b0609070c03170c0403020307090203040605 82
    0xb4602c0e150844e102c91070040282c0c0700003030401800003000c1c0b061003c0ca80c06549038540c0140800303152282001e040355440b99a440c0e151161149140c500b45041d2030b807003030701d44071421012801d00b50383d515001501c1941001c0c0300f00e0918040703294491000c1d0b0341c20700364602c0c140800200580b039040a0901341d03214040d621002410340100c80e9138180380d83d26107840c8490b4003002c440c982150a6245880d54101085d544000c12510425980404041d0001d010f8030950303a00f0b94171404503030341d24854103a200109660f00d54014080700300711f042034206508030350750080c0119000d851907102e141400790700c1e89454400c02c2160f00148010b00500c0700070f02502044072000c0758001d9003010317210709283e0050341611400303051181c1413400d1003240d1028800d03105c1e11a080740141e4540e95032030510640711032040b0349541c89580d5400011318014064101d1019090305175071070160326110f0b203503041007045002c1c0c85d1000448040c8000001030340c0802007900500201e003005a168145417902005841002d06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 308368381 1250 308367131 308367133
    0x11151503030319110714011a0102060c04090c03060803030703090203070609050916021c09030c0e0f070f02031306020a0213020c0a1502090a0e06031509120d0e01050906070809 77
    0x7050000000503d4590031111100c208002110a1154103a10351485003000080041940001035518920b040d4021380c40041407030070040b4800c40400c01261544400c03a5a5540c240c414001402070a1082d0310404083c40103040024038a500e410000307103140c00807148035000907115520b407011030a050051360000c08190900c00c00f03c1d802c00c000101510401402200034a2100e240440c1951080050440c1150403008001c801c4030314490080410310f450006031280400702400003030b000104008107100710549078500c1d40f2034a0f0b0510450315504501c20001c1144402e0000400c2020b0310204003008001e10780042c03510750b03001d00c1400b80d01900041c0d1000743e18414003064805101c00301d0246055540101107200300402c04166000074010300034560740041d100140854100404040c85004400880c1118840c14030919883d002010803241111a5081030380d10081c2d800340d0340050042500c8022000c114400480c0c44c05007100c8040307c1c642810740c4000e06001041750840500340c1c001c12010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 308369631 1250 308368381 308368387
    0x31805030a0906020c030d0c1115040306050c0f09090a09021201021b070b040510020106030c180e0624010e04020d20040302030636031e04030b04121115150303 70
    0x40000d80702d80c147d8031044107200c2c0e0170b040c1d8010070050364004c1d482c01d0070080c9402d080510340051040c203508140821100c452130400860740412a800940b0a04102c0703920b114a4454900706000f07007484003610340e8425a840303014000040c0e0b5603110200e8498541800140c90700050408900c850381c8035001007095420007481406021200f1040314240c2d4419140020a400c22020403030050075541d0001e01841d01841e00401c072580e0440c1030115222600703030144401c02c415140c09455135010303160302180d1a101c1c1140c02036000000312140c0400c030141010035140c8401c0340400e0a0b03901c040301c1165015540c148c00c88000681301600681a049150b0700f50416046502013642d418000e44413000c14503201051217020741d4280000c4400500000000084c103054a15095981d013041034040284c00b8118080300b11103c0e95002c0d40c0450360040048441a03c9945a048103401210002010442100410034021108200102c580107a49009201318a800c078a017102420110701d01901c00e0b0010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 308370881 1250 308369631 308369653
    0x31218081e0f011802040b012105130602160209011a04031502090607061a011704080f0903060f060913080d11160c030c15080106030c031805030a090602 67
    0x40e0700600701c40c0c00e200010500e180310700a18a4144030520402040d0700384001520f40304207001c996640248203690a0203000050401520340c070703000700400380441c205014024482885504015080000c0a100800048844e2298000d0341e0110320044900c40a09660404504101c403020b80144050b401c000c000c032642c6d01e19480c0601c6240b1000c0c0194040c00d01d00070054286604030359132000001d02072580c44065107041000350102c19059414581c0c4a00c1210349940100514248680c01010b00c022643d41e035030f110250f9400402825031200c0702032091900c107450802504c5c3c06040000320380c600d64078040c6c08011003400010038454031030004e4500c400008250b6800da604120741124085451102000c140e1540e006201c440e404948bc00c0070107000340441c10a00c0004c0d64040c103000c20301141c46a00162040d280c0107608000210000010032246120303520031403420080b480c010034448100269004c02800d02c4200ba1901d810001d2810301c074503080500032008003500d0016018403610 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 308372131 1250 308370881 308370883
    0x3190203060c0304290a14060609010c0501060f0815011d0105012d120b04110403120309080307090e060328140610030309170d0509040f050103121808 66
    0x805070107841e0b80c50010011030100507200d0390711001c0030a00020301d400c081ca00e13100c4020115096503440015071030240c0f8102e1200142c42498413802c030281109103008480b100448820040300c0c400c0d10b5035507a8000104600e41862a504000c1241c8c20007000c0070005508072070030030001a403200b041c0c491400d4500740007031a850070290443d502401c15201600300c0c00d000740101c00c04030b2201519454620054071085800c035030240c0c0340018081042260200d0903060004a0b0000c050140c024030042c00208001180051107042c80e5546250200700c028280c2d072191034a0700140d03845400706065a4040c4450022400301642c0100110000c0c0583d07403603c91040158503200c032548504240d046120b0050002c0ca159489140b80e034502241c0305840c2c8072528100101745400700700c000625203140003400ca0710392810740708514140805414400c080000644481d4000324050390080e880c4d02c2e01c00340d0b5110758440c480c0290b000344420703807020309114402081c130500c0d074480302c0d040304601c0801c1c00f580324 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 308373381 1250 308372131 308372143
    0x3140901083121020c2b060c020102091302090f01080603121812070e0105130608030a1205060a060206220c06050702010f03020301141e1e03190203 65
    0x10310140c2d210040710380c0064078445000340301d038101c403445018072111080000003082c2d180d2400d41c81003108610000c542080741c0315034500c00c5907907200e00310034008501d002000d080500b01016060003d46250859522075040c0d48000001c0c40150b5400306040c3e4150601902001d648903101204502d44003440c80091001c80380403544c2d03810820307100e002509986003048898101c019903114940c0300c03401c031120842d41780481244075009a032040c54200d0f11041c0050017200b50303042d80030001a80d03800c007024849015454011507164a07107800d00010130035000e200800203000c1e181e80780a50030440b05605000e03100050300f268040c44008904101c91540442d4a13a081024409a25034803e4a03544d806081d00386c0010251403160704440c001a0641c02000900086d8400e0304c0707144080b001203a054089001c244212a543d000640c0402498a01101541c0c240d02c090600b00d014000c89801007000020743c01940000d8000300301125800e85020072114070f00d000d00c5041c00303014040b194003003a1104 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 308374631 1250 308373381 308373391
    0x405040302150606130e010f0803032401050d0207110307060e010f031d1504061b0c030804020a0b040f05030c030303010807060c05190b07030f050402030613060f060b070314090108 79
    0x41503103011a540303544000880c1d00e4083d03032030040302c05e0b5502e0f01c840c10a180000e10a140604000c0c0341d00080c40720011081c2c0c3d1160007014124000d07078071880110b201c070210b62a01203041010030070041000030304070b201130501103008407c02010303c40c100044c135103404500c0d04000140030711542102031a80e032201c0310303406174001c514001c28180c14a550203d0380e0058900100c11031b010340d00c20480c080c2c10201070207201d41e000c0d404c203002da03041c026450608805d05400c1c00300041d12120041c1c0229000380380c3e00f600548040c10301c03a011741e076840c031074840f9802c01c0d041901e1b010210081042075250403c180745a500c411400f6605d95450192016500c8031a48500020300c50101060028420284403140c4441c045000c0c0b203120802e00d140c200780d08041111442c1c0880c0c86c044401100200307502c030f42441194090b00038031442d01d503c203882d404034200c04802c444258849505400b1170200780107460003080c082e90016110b602c1c9180103003058080e220101e4910b0024086e1106aa80c0320b40800c1d040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 308375881 1250 308374631 308374663
    0x12020c06030a0f020438040e06090402010c050105010e16020304081e030d02040f03060e0a1a13050f07080d021f0903030e0d111006080615121005070801050405040302 73
    0x44145030b8103c001074040c0e070b4010803241d445900a00e014958110002665420042c50355801044041980720140142c0c050070f14020000390001e00582003000d25650024014103244280080369500c107402c0d50001d800c41ca10000c000310a02640100c0b41500c2c808041c160b001450400342001c0e8421b6443c1740074248407000d85030001a81d100c2d917006004450b6040c1c0360500556445407140d02214046e6150711007140c0c10f91810b215501c0c1a0b90104010b17440582c4440075446041d0001c802030302c0b030200602403086081140c040e13100010420052003400005500191a41d1450501e00c5801c018038903401d681550442380c00303400c100c03242d016910800004040009204181418110f00400c0c01001c1d03064903100c0c241c0940075032034210a07601c1c1081c111344100c40c408038549180d00709484062141950700c0c0d02420218060241c04030800c0d100c440040e00e52481c40c6584041185001c10820351603002c169a03009004000d540500c4080c094a400d81d001e000c10300b00b41c0e600030340d0740401e00c4031903140c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 308377131 1250 308375881 308375891
    0x20f0d0201050d11091003150504140f0604150e01140103050402030a080304080717130510020c1302070c03081207080c0405010827010c120605090c0703110111030412020c06030a 78
    0x20844ca01d0103440b13000601400302e022030019203102078020700d02024504928209100000364618141c0030b001d0034009002e04041072500da0a1000d0240000540503542c8a85c603803001c054200c443c10000d00003009124031700f4849526098800c0604204110b20350f04050070801000301584000031403400c02540200115074a0b034407070170204071a0050b19401080c41e61140c2e035000c407d43d2090b01400c080381c0000c1d0440f41c4280d451003009408540001e0800c0541c100714281200c9180c01d400200c0d164505803805841d00c80d807540c41486008450f041100c40c4040851621007500810602c1d6601a2031410b100e141c90034840304010702401148a0103040140f07440000780016003071203014074000000703100d80c1700112040c8107450103042002590000508540d00041d841500740c0201000c4402c040c0203410701c1e0300ca516036000070764000350003503051140c21078000301505000d10503444145d00700d0640325228289407401111100003190f10a085600611101c100c07641c4070811250001404000055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 308378381 1250 308377131 308377151
    0x306051b040b070813090e0c010807140a030212010e01030b090102040518040503130e0105010314060f040b19030308011d06010f051e070b010906060504210807021c020f0d0201050d 79
    0x3000d1140d00c403100201e445e42c40001414031b1181c0c0194090f41078490544600140140c01140c0522080352404005000001d03041d035460008030003009040300b1850090328003100600109118482a030010035a04000b50040003485202040305411081c20002540380600d0000040c544d4040d0150180001f46820082810007000700100c820f840190400f003034107103a8820380811403210902c6024046401c007004003030300d030000702c10039441850300600301d0030340820b40d0381404007c0254052698100040c490f0042e00b0b4410401e4035001144280e4681d021903050070000d051040e50101202c0650100c03d09218160f80c1004848104011501d040d41c0c90304280015859011100d05501508000000720700c818400e038003c4071410383e68107240510501c3d640300350440c0c16124910604061558a04045044e01c81e000541140c8501402e2401e083c40740c643c0000d5821110040c501c0f508003400a010b40c04c500b000d2030f00080f2101c0c102e0304494900401d800103882ca10506000c02119503407948060 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 308379631 1250 308378381 308378393
    0x91e01030210030209031b0f06090a1502010608071512021206010309061e0929011208092e05040f12150507020d08010b0f0d200f040306051b040b07 65
    0x1500c2090010301f2a04c203a207034042140034201d41303107003000d001c1e46070107500310510f0070084115001210080e0100c85002d280008103034084060104050465480300b000186003402000518042e09400d02e000400542814004c0c061900c44d0b131540c08042e0050014007001172030b03070f026070703510402c02c3c240828580014a40580140392031800c404580741122100031404200341d12440303900744200c001403003100039043d014103c8042c0d500c0c0c130b50541135074100500124241000f1400014441c2844900701142c003400110307500030040100d4000d1040c0b11080025090520318a50f82111a007401d52504e420809003000c0c1c202c1c00e02a044081d102c800c0c21008000302605010760bc590400070800081c2000302c00207442e08840c80300b0b05c000400d2040080b807543e001c0c90480b09240740a0b05c07094900740b16142c291020f0320b20000f041444803608a8103032030003510040180f041076140303030409a0320303800c0d49130410403900007500340149001042a64014100c0c0c1c042120b040d80d042d1400192640300d589045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 308380881 1250 308379631 308379637
    0x1a01050414150a0314031209010b030307151b11010f14070f020a0c0e0115080105012001090b04030801300308041514011d1302010e030a02041a091e010302100302 71
    0x70046212450181700300d800210246c656440403c01c45c0f8103d494000c00b89007a500701075000c542c9a0800c1043c240000c40740028641d40030560740c0040780c41c0000c0da901d01c000e403081c0c400d4800481d0b0440c1e0f0240c10b9a10a21400c2e40031103d543c810408603511003110340e1415402805001841504444407015500030441000c185070301550f0082019210003d251071441c0c20b101d6118050080720203202068003a401c4d6174103840e0b060351000d803900c0c4400c000b40d402084250f00c900b1295620700384403010610100781644201c0c0203444e00125540750a01c0c1c00306017401d004590180d88148c080c22143c0700c40800844d81c680b41c0620340b4182d00e407190309000106c944510b0b2203c0d4045e00d4011080200501c030a105412100459062180d072003459890f0404210100c4100125450011414005600a42030b000001001404550000c900d507401703d0219030304444200c50080701c09107a44044c0c034152301d0b0a68020406224014480b241c0d0140c03401c0b211060000038440c001e0300021041d0749100c0d03419 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 308382131 1250 308380881 308380883
    0xf120102040b0403060c140f0708070203030d05070e0d0222141905010501080606071203060b0c0c101704030807030207080d090501050a20160f1a01050414150a03 71
    0x215030703442e590700000c0c81c150300911007250020305100308000503500912401c50310b0091070b01c01c43c0c9404000c10140301d166024030021291380c102404000096181040540010102d140d00002c0c2828485d0000c0d0902c0a5031b40414803950794038103500c0c0103032110030194280c000c8181c07502c41c0200140c6c981d0f0019041010761540c4480c0e84504121b00c560806c9840d00b090780741e55a00308034070790322203004560740141100d00641001e02002404000b40d12991182a603142d10301e0001141c0e601c1d03c080703004560202448a505074000120301c21a880d10501c031405001503810801400f0382d01801d01c02080d440203001400340040c0c02c00141e555806601100e0005600034030450350f440d203a60390103005003c82c2505446035881c0c00002462207616106004c04420000b140781c1102100750b008542940c440d5400d842000b40f801e0700880001c4e2420540d5040c64407551840003a0b2041c0040d0009107101640410b100f90b08110a0612030640e540d2425000307112884840c13000c000740c502040c2007548030b0744 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 308383381 1250 308382131 308382133
    0xf061808010c0807080708060d30090f080303091e0c030610170606060904021602091015030504150b060712050415090b091011011b030f0213050f12 65
    0x7006101941c803160140c45000349803181c03170003611910411224004111403188e00300e21549a9900412903038890000c1c03503030703013a050042d100c404103001003c4041205000300100d00c00035018000052030808190141020a0080d415841c1240340a9503d00f5417884564a000303008120f0000f180b8180001111581c0c0642203503410f0400c0b0302d109050705a644914100c0b52200c941c021880200801c41034080e2030000d01081c20010b074003040100079070109100c0f08020160703420b081300513141e95a40c907105412094410300070900d000307034602881c001280340b0001c1501e440100700000d40141e41420460180d000c1c00a502105200465828440d90002901c1051030811b00041198060000c105880294114016140050310246d50190050144010414003880070034038030305001d19903039988051890100c03540c20464446d1802c40700c805d221800102400780e403440303038250903024480e401c2c1c0c0e10320401c6140051444211030b940817140113541c4540c40c84141032016580b501d24031403d02007024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 308384631 1250 308383381 308383391
    0x30c0402031608100b0a0509011b03020c0108180f07170a0c09051e090105180f03040b0c120408060603190206091e0612060a0605030c0f07061e0b04060f0f06180801 72
    0x84011f0086e80107000c030a030004020414814480c841c000741300200c20f5058004018125014005548098000340762040e203246e42072640350354031000c2200079840050758028007822418040c45195003040300d2100701c1607a01c1100540700089403401d203141100c41400700081c0c5510b4680101219500700c11001064407210407c2c016086019800340d401040c040b288121491100000e02d5107030a220010007205030401e0108010342c85180009060f48120107003030f51018480d90007003d50541041d000320119038401e00c1084080d003400c100c040145c1c22800100010780416a000460f280710701c2d140f1a00426201c051429500840411908281d07001051291181902180f05003840300480e5140c0c4642c6140800052049c01442240d001e20036a415052902030060024500c0344d00414040b24915601e20310001c402d21494442013140403c20b20100c2c1484034841040161083d90b00022804403610b801086200c1d4910329030000c031442401d000d4811020000401d52268044d8015020b81d420a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 308385881 1250 308384631 308384647
    0x91206050604050121081803030a020f0c04020f07030507020103060f1206061a0a0828020405030d030b01050d0903180b030916030308040212100e010209030c0402031608100b 76
    0x250031081c4100c0c000c0c0c604000300da80c0c3d000c40e9082501c03454540e205001ca61044200881c0c808001000d11000302c0061088400451001c20300e10b074001d810301001030700300341e00e45e400c800d0080c0300c03c080500c800c4809509000c101f01304404c0620611800409110b400103500302164041e40041008008032591104001d68603a0720b05450000d40008403151454040b020036090107005070621100800303625207052200b10f81e000c0c3c441101c06480c40d112500d0084105d00003001d005c40c1700904040c0001c01603100c40c5404185850403e1035074000c0140350070550801d424be40c1c07000c1034550014000c0f2003c00d908409003019240341411011521601d8502a00450051481c000441c00340c24000200c0e884010500f41912001020740401800108031101007009460050b104818051401c03080d55015280701c24404200e554612050b021030350041000300442c039050140c46103001c0151400e41c6586000240c0c031014003a400320400611a0075400b00b40645040c2c20500090098203d02c180c1d56200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 308387131 1250 308385881 308385893
    0xc10030621051e07090e0604110d02030703050a060b100234030204020f0a090b040308121e0403080708010501110c1e13050a06050f03210c1501091409030304030c030912 74
    0x20740c050701c41c1d681d040c102441b0028a00144081c4141e400ca004131003080c03803e00802c10030914403032040e6071502c9420808404504144a09204c0c9849000c00180e0f504844050000e8594807805110954008480c030f40c210040304240c0c000202002d41301840703024441414484049580c4d00041c4d04148080303016180301d00d00702c000b00058101c64651003c2e0075500c10402003140b0840c000109044000c1c060060000c0081d030800303800c0400001d0707070815180d01940c03103103500608032004c4c4c000442c2102071100c540e03000041640500003c0c60401b990194021910fa5141c3c00c28042e94041e00504c004001c482840418088802200030011001c5444203502400038140548012451918041002603145805000103840070000340240030040030400c48500b0404201105074003501d410402c0404c0800c042c0441585091110702c516400e505181d40c0d603003103920300d181c440350b282818070a101d581c0200100396540503601d4601004000c00514003100e100381980c0c001c648454141040404100b1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 308388381 1250 308387131 308387143
    0x10e0f01030518071836030203042102090105010203131a07120503090d0903110910050a06050a031104030c031203090501020d021c050408091e120c10030621051e 71
    0x102c003109026000000c18031045459050a034406c94070420700c03450110b2642009046070f454042d006480c1020f90350401407050f45d950705014a8407182144c020070440c50b01e03540107070240400784000c41c104a40306041312460b982d28042c2010002900140c0031500550700300b21025543c2c031807071501c0c51030f4020714042c0c802c0c1c000fa00c0002c40c0d402041815180d0034410004071007140c0c2c10040340328400c0380781c400b0300102e0b50025240540c5000301900200b11502d40112100040c01c01e90340720f650303500568100800b165680420304070055030800082012583c020780d00c80070789400000030500300e240038005500800d515480101194000724201c0c00361041603002e05180148400c220840b080718a04500c100c5908480041420a050003185518100000002c8c0145141d002d0115514241c2000540f0030300b0001c10000e2652203403802c150141441005d2200303561150409200389420905110303c2a0905614140b0700038041c4020b80500c01d04000110a601c0340b03020003406605c0c2040501e0702ca0b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 308389631 1250 308388381 308388419
    0xc04020d05011a090307060f030e0f0616030207201c0507060e01210c0e03100f0608120703120204050405180f07060e04090204200c0705010e0f0103051807 68
    0x40c8580c0d0103c42508414401c50340d11000040203480f400303060800640b0303007103020502c00c1f0070160390341c964044040f0b08202c1c250707403401d1403001810f8500d0240b500144d41c907180c40c020000c150044c0054000660912403044900c0111040c45a040601c0b001082d01c504e01c410001003a403005414101c14003802055003003d64003e035617802500064100155000c6c4490f248980e2105030f155030f010780b54141c40e40a43c09004c02c518004412400c514006807410015401c019520369640402004410540c403440c80200b0301500a0034032040c1501c1d48550740d004092000e0103202d400500030075035000c0d6604980207454010010406800c01503007a80303000c0401d0409640e11701ca0125900d90009000440c002280d0580c4d0b1807000c3da2034501d013808041c0a803034100703c1e00952203074540081d4203e40c6100360082940d1100e181d0316141a1861a0f24210306a4410350501c072242503489003d032118004240588400e080214880c0c0324202c1e20140f04030f007904200124065521701244400c81070515031440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 308390881 1250 308389631 308389649
    0x30b04051603150c050a02100b1c05030919063002030405030c0f06060d020d0f0c0602031309060f0608131218090e0607080925031a07140c0c04020d0501 67
    0x14600d184c0041d6082d1041025550143e84541451612041c1540044894010182084030081480d80141e0103281c50810200c070301c3e410104e240b98107070400d109600c0004040210b005800b520b01417001e0240d8666940c0c042c07145000d24220001c0740c1d00012241301c02141c42004550341d10306402c1c9552079801c43c40035440540160340f483c0c103198000140c503900985009200e406145900da0070490100406c4200b101c602041842050100b03a400643c0c4004003600d4002d95900d05400050101c540410b805c1f074982546030034028003006902d040f00c0c1003a1080c80c00d090b52684c44400e148030a90207106001000700d56154108481c260b40403040e1071500349511a82c5407403e0b01e40c84640262412096400c58a84c04000003903416441206001d410248500a852090241408258104070340894201c105a01c040041082100198041018420601020440c4d0400ca50010441c0344d01c42c641e2030708400c001ca64102c50810078055190003000043c4215560042c403003905014000901c215160 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 308392131 1250 308390881 308390891
    0xc12160201170f01060e0f0a0909021305010e060409032706140c030702060702010507120806090a0b010f0522030b01090c02030c06040209220b010305061f030b0405160315 75
    0x2000032980b40c01d03020b20b19142d40d4050316070030141c1c1140e100c55202541c03544100190711031010b54035404614030143c08150408100c91450b070041c0440f00080b1000342141c64500001005650052810a500407008580101e4103a816090440c0c20100c120312201c0c0610080c02c1089504090514800449840d0b03151420302c0000e12801031502d008020b0813a07070b960020001600103180c80c0c4010300b1180d1050400d00d0402c00365031188400200058441c4010078101b4050005034039104010070740c801560310050000b540700400003401c0c507644c00c600070244030b008a20500001c404070685405641c8004040001994900700520544800e11503038607101c1c54076038414602440401203c5520115400070b05250b1610303800d200c05041d000707120100e40034540286034a60000c0c62030300200703240112810400c0f0350441c18100e0602e00080c0c01c5080740703914038140e10100c001240c6400d04494011f1014075556540b42015820701c2400c0301e181142282c200000302c20440e54800c01c12406540d46000c1003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 308393381 1250 308392131 308392157
    0x21801080718050402070305250506161b051e031c05010f03151e0c091401120e030906070c0801050901090f0f0201030b040c0f030b091b0c12160201 65
    0x1c07480c2084500c1040b000000c0c80501041c20030b41c0003443d01610a1601a15043d244012842074a0150040880c504141d5000350240201004059044494804000c00240401e0f0001d01092251031250400c000c3c00020003040c011705012a203409030190641a85950071701e1401501c070750000d003005055843d0320350301091040c0301d1312403941030b11200c980440c4c0d002d056807607101505902e1015000010b4666070440000c110b451078082102030b13007140200f112000c0d002d015005011503045007401248040000b89240c1c2d1005400803880c132044000a040702207a500a0700310f00ca01e842c1d203a040b440000e6060104a00d900c501011982528000c0000da01c034416010b080c0d811644025120110310001803000c20345a01c219040c40d17105040001e01c410001c0081410794114280020215000c08451030726550540110422004110340721881c51910400080e66201100d040000d016008510300304d484004014462610b05d880040b030f07884a0000c000254040294001280003540c0150044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 308394631 1250 308393381 308393387
    0x507090f090504030906080405030f04031a0a0507020c0d0311010c0806130c0903141c0509190e0f0402210a1a0403120c05090405010816080307110910090218010807 72
    0xa030051358140e44544480c0c0c0b4080003201c2848010b0015030f45030000704207140c05c81d04040d0050009602c2240001c0840088030a8174460810040844904504010401c2240740d80811601280071003201c0701c4c401248981030803a0a0320075045104034940c81c0100c80456560003022003842942c04480c0e810824050990349002c1c0c0702c8025900021903880c1c40c042c8006030411241001308007001040310001c10030b0248100d60f05a88507488004510009140340310b90800b00d025803908000480c85c090641c0c50302e0121420340d10010900c1020062400215085548172840c44c201100002100d8100145228403241c4030b407040d803001c40d002c8009450561080b40a000054812038041c2c6820441c0001c000d0030074068448049907204100e010843e10942d5981e520910f4041d00602006111428410107201d500c4900703500281001d82c0244134450006000940d00c00201e074050300c9544068031441280441e512568120001250010035405034007205c44c4200c1e800280d00341c0e0303012210b4a8900c825 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 308395881 1250 308394631 308394641
    0x1030506061c02010e2803020a0815040b060609060c06060f0a0506070209100810140f0c0d02090a0504050403032c0a030e0307050a030308102103030c02100507090f09 73
    0x54400c0504416040b02540c042d54042d107400f5005000c4200701440215814000e1950031904000c001914006100b0f50030400001e10103403003400010003210700700500d0304c031110704000c00c018480c280c1c0400060480d1140c00650361212400342c102c580b2092214402e9031a0300b401c8032000d000d0310078005900c1c034620f00401c0e00d20486801400f400e00d443c4154080c021140700090240340b20004000b0001200001001f0038100100d00400004444084d81000c40c1910009040803030004500310a210420781c840089400d003440c034200059980c81395101042860080c6e40c00164024a884100800d143c3c1581100004814401000a110410b003000c44c00b1003c00b40d6110f61240c1c0300825110000e4001d40c650014844001c00b25a1015503a00010350070000d540c0089001842000911040a001407e0240034000740f00000f0f41c403482130020b1940680c0b011710b026041544885001e01c0003402030211321500c1c4030901e001c0c8140d10f4102009001211584031300141c40b240054000303450380b038a00c16 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 308397131 1250 308395881 308395909
    0x7030e0705150a09170327010801050d0c180204030b1312030e01060305030c150907140f04151410031107060e0f03030f0a0b060915030a090602120103050606 69
    0x44005494002d00428806800c00c140c8107050004a240200c2c280c080000c001c0c40d9404a2801076540da004500d106a28400f0050707810080c0201000c22540d0345e800108040c151142901c1442078804d440c20001e0740030040c4e80c040a24034a000019001c55003254004100303590217601444481d4a5801c2100b0010740d404d0b40180c012100c010b80c00c0003081c0311303400c0b603509500300ca0008102d8680b261145400c5502a4040c2031040c0e10800d0780b030281403c0039440690041919000e000e4091030100b002c0e902041d0100b19074494841502021030580e45d550008101c0340b00d030580324005c284c980c040c00841d80c01640c0300350b100318240800c44030128401c0c001d400040d4910700185051000c285c1d94200903112180d101c100900030088503c8401504202452082c011084459034a081800c0c21f0400c9609010f0018002c1504001400d81c6480d10030500040c0e901c00d030321680ea00d5072800c82050040c40d2084e001440303d0700024101c5440c0c4407407403149040c1d03401801611100e88681040015415501030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 308398381 1250 308397131 308397139
    0xf02030c1e01060321080106020f0a0b0a06091a0a1202061b030403080c0601050a12080a2f03030a0609090213050601050f0a0804050d0815041a0301110307030e0705 72
    0x215045008601d040c0a00307002450000200e4816100d641c2c841d00c6032040340c26541c070001d101078940b5480c0d0b4031140301d5005001c1130015090f82c082c15140c0640390103400750041c002c0346410300401d03403542083e8000c0f0000d00034bc7c00c0030072040480b4001104503540900b0214810502154042400740c41c48140c0e585059004080518000915803420000701154950b0912404244000004600300030000c102803000303240900000d42c104010410220100d410103201036089820700000a0660822698060308034200094210715040900c1070407801c81040c546050001110411a07010000103103016000c11841071180d151900c04210803540230040281d404901c000746141c02681d940d018542080062408c2860701c0728034080d840c0d10798040034074100015540300800050000c01e0251501003030051400c0d00e81c81c105803911010741d0602107911403090399101000960b04c1010b0740c01c00140758020f4002e02c11510041c1d1208180d800c11138654002c20308041000d004054081010001e41d84010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 308399631 1250 308398381 308398393
    0x309270c031005010c0821040b0a0504030e0f041e0906050c030403090b0f070f0f0302061f1e170304050312040b16110d06020a03110702100c05070b13060f02030c 71
    0x1100c4400c5c40b45001c0e282907030200803015100e505100d0f02c01d62200300c1c84212145081c1881c00d4240ca903001081c0160080c642010301001a90050014110440485407940d40d09072404c00100244a00540ca0b80f498440c01c8058180645d00c0e0041c480c01d81c000c140030003050395040030b006070901c0225401000102c07250f005129041046020b8070503654403200d010704041940c0e48104180d0b0900d06c095810a600c0310403101016810050300754000ca10b501c0914a000200300b800c1c18840036405111280d103000b41e00486080b140c0e6100000030000d505104504244081c4002e03246e80c040e004050080c000c454514503c100f80c40c003110203c41d007024803030b442e14002008004159400c100c0c215208200405001566603030340c100061b806004560060350b0b90700d00c000140881d1030003040303200380f60310500000000d42d507081c2c08102540c0c8282000c0d40e00c0840d91030840e0500c030240d00701c507111010105149946081100b0064207503086525420700c600e031419000c0e82e8030701a0315a03881341d551000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 308400881 1250 308399631 308399639
    0x20703080d05090723090a1e021b16051f05070303111903150f0b03130f0206190909020403110d05010b030106081b090f07110309270c0310 61
    0x10b0744402d83c480302c0d140a0316580c1e621003061080200501c001c00c95404840e01e0f4400562804802c06500525190801c0041440304604e6001840c81641354101c103d40c04108000801c0181c040c0c11074a8100340240c4691000d00c4000c0c00600002c1e0245038003030f04440c41400c07000001d014141034006020b0300c485040a9040c2d40880281600c04089840750805020140c045006501c2c130b19025203950b18041068401c0c0190030200101a43c8a00d1110a121004000303980040080701d80100c4140004803030f80c00e00d81400c2401c240c004500030f401010002e00480c1034540300744040c040d40351564800341402da071034503070030b09a010701e00001c0c10380244c1c440301c0701140c40d041400c2e180d050b2260f80041142054400000c0c2156500c1e4410b103582c3d001400481c90207080a800b4185091040750703514401c2c10400041000003d0080c84c00e420300a00c04c03420b4408400030010380328406802041c040c0c031100d20404000d6034609000e0190344469400c03010400c001001c1c41641d00c0340d074812211a44140ca4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 308402131 1250 308400881 308400907
    0x4020403230c060d020705060705191b0807120e0409030e041505040501180506040917031503120c060709060e130609060801020913020a020c1e0307090506040b0102070308 75
    0x41c100e022005204001c0c0103103498079402d010748041c0300754050058440b65141410750034001c00421490030400100a107140300000076841c0d25804280386041c0003500f1b02440049201780244502800301c06010820000f00554002941031203022075440000900103481880309507110700e18000d001c914080c6403918642004d81c401e51802c0300d81d080040c10580c3d10b00c0454100c502c280c00c40780c03180c2c07400b040036502d1b030030039000b0319800c018140d600300920621502c2d000411110f01a1301070408000102148500e141d01d440e41c01c50443c0201501c150a20340b15003410700703074040030312030b01103005620008415a0103400718200311245a00e9814000c400c000270042850601c002c8400000c1d998600442c985c8042d109035006050f20a000594811190302000b041c1c8400352200701015004021448005c1d50110301411040416035031440c41d00724450400c0315201c010488240c245c8110900081c3d082c0c6e41d0380cc020b00407003050303d081090102c1c42004a85030b40560202614082c810002c462074800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 308403381 1250 308402131 308402183
    0x120f030601051603030614060702030703081b07090524030a0201030b031e0106030218160c020d021f1d06030412031805030a0305070f02061b040f0603140604020403 72
    0x150501d07000f0310b8120112241c060010b205102036000954440050103400000e58010324031102c100c03060380c01d02c24507500080e0f03144100e01008050344000300d49005494550107a078181a01103e003607540d004d1b150000040180402c0750100c01d400b0081c0310400c00a190398a1038080c103000038001c1c00c1c4440541e001075002e0240d04141030342501c01d04074001040001c60f054112115494400801c0ca0f501d18010030070101c4480f44108060307181c01c0c081c00075182c034102207048245041d041c40201c00060b80002402e0180f034140c0a500301c3c2c070399503d0001d0641e080d202d07400c01c601c05444140e900c0d18000e045d0001292400070040c1c0041c0200085408244000408d40214600d843d0100e440e42c4c1d1602107442c1032181d05811541a44041031901400d40c1501075a54003181e40d241228002c8600d200082d41c8403005040d005c280c90b0407000819121169604441c090000201e241441c0d82d41d80308010000c002a03110b140980751504c000c82c000b0301e02802190110b0750400829000141c2518007000501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 308404631 1250 308403381 308403391
    0xa0914181504020c010605040605030f031204030216140a090b06071506050a030515090307020d1401110a020a0c080a020d0201110109061d010c0c0b010b0c010b0405040609050f120f03 80
    0x88031500300035945070b40b2400202000641640086440b51400c424082900e444d90003181c032076000781020f00b00c030000000030390b10f00c0380342d440032000b0b16100c3d030400341e0400080d0b201880c6128001440891106000c0003080100802038400c02c80c0aa51003005500302d640d14909140e008100304507010200d01703000c940c29000141c40c1c0c00060751070358031070025408020a41c021940da820060240000c0c0d08154412613001003840091850301c3d1003503000aa501c0510a40100503420052800f01c80d44000d621803410b091000028030f1351107200c60400781d17569100c10811520707082880e80114480d000401c84414496000d4569401641154010742d100a90424015955980c8200e028003007500ea00808210360b03071072140b0f440080d1000103598255000691341c582031200e21211200014440c9041d40d0442e05030940c0b581e1580c801003072842c098030b00c442000f07038003900700403c0c0010701c402c99001d040c59a203c3d80807101103001540e0156212080203002c24540742082c4082154107040b00000e680c8a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 308405881 1250 308404631 308404651
    0xb0a090906030303060e180706050c151f080f0304090209060c010906090b22020108090a0c0f0801051b090609040902040c080a0f060b03130204090b0a020a091418 71
    0x2651903800d404200c0700e01d90300590001c1d840701003c000c000c810141365508070140d4260080004d00500d189540d84c10f0300d1281508012001402480e041018001c54514901d107584d00b4070607040194181100580742008910f0881d07840d80d001032030090005804664402c14005141890b282118420080d04181c0b02e80e41c1205040120500c40c240a12907280240c2c402c500c00100c0f4a00760030301602c0d900c001030030b2905414030307106100041508080e03580d0400d50b091a00208070768a0f18250381c28040c14110040c407800103111302161007440007442109444444008004951742c03400071010300500311410826150342001615450300b401c0c3d0041051a0010300045031010b0968049811030b148096443d0000300e41400f8001c0e441c1250103010b1401c007241c5010b000107828003040040c07600c405824200c07030039404900d140454407181c2240c2c8095070458403415075860400c25440107540003c0300308c130000c0c410150102c0e4000c8550640c5c0a00f010140413090a180c01c01c6074100c4100d800b1f0300c00050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 308407131 1250 308405881 308405897
    0x4060b2b08070506010305030d0b01051c09080c0a030809101b080703091e03021b0f010804020a0f06050d0c080f0402041a220b0306040f0206070c03080a08010e07090f0b0a 75
    0xf1510401a00c2e0085110700000d41d40c03080d8000e0b805d41102d0b00c1010705410400e0401c01b900083d0114134040700c07000040700300020103900710b20300500c640c420b885000c0814001c4070b49410034980c03c000100d120b41d0042081c5e0701c1912124003400111201481d448406101c2c41c0b1501c50030910070003941c1d1b449010b50800041c0b011316601e460000301d04c5456a4040c7d807000d1003074581055070502003241403e503802549a404041500007a81c00f0510901150400034009c0006041d5659100001d00030701c5050304581c2c0040d15014020700d18cc0c040e4540021440c00c160951010900c2a540148a4030101001021544940c2d00704009010500d00148006584a01122203540e800d151304c4200c21000e080e01113040c5c13056810400342e4a04030306252098021004000c0480d00340c3c25412142a13040ba01299142c10034a46543d0159441c1c0000c0c140c644049215400d05070003401c803d069810881501600380d41e00d00b011212042c0398020f50050070384500003000007078250005014100b0072428000c0c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 308408381 1250 308407131 308407133
    0x51e0f0105010909031e08010510170a090c0b0304050303221a0702070e01120807050304031a010f0902031612060506030a021216021c030906020d0504060b2b0807 71
    0x309603070003030700510740c5195285600010140c02050300464400807403010003961516181c09000c1000512600c2e005080c052070b04201180304030300395040211085201c044900b0070b010694024282024210f95140780102e01180e14802c1d54103480c4115445002035280d5560705c080030f86642c10000120400741c264a0150000501c0e150f524a0010b005444102003480c5c01507000749091400d41c440c0d501604030b04010b20112164103075210802e40c0150701c40b41c0e9144130f071802601d507114960005d843c1020380c0b4070f0761024481810821381210400e803e0103600c0ca071906122000c278072059440411000151045c50f00320fa0080266030740448802072b0010f0429038400104a4a82c0b04840d072885984c0e0020f40c558140c400d2a20541d0400301c11459640400c1c82054042d586242001140b103e42045103c3d40324602d12a0300045d40440d8005400e40d15038100000c2140640030946048521500b08400c1d000700e42890000c0e09094811402c41c0c084d141408804000348101f0154180c445000c2045020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 308409631 1250 308408381 308408383
    0x1101090b070609021c03020c1918050103021504180b04110d150602010e0d03050901270312050601120905010905031209071e030809040615020325051e0f 67
    0x298901400b4040352000491040009030340501003da04043c00910060011a50000d402544a0400d0350b0b0704100f0030103494440c10f010416840b0040d480c14100c5041780c260308030b8100c00d04a910a8850040c507208207140352060b801140500b103098032401d00882150042c0ba0030082c505039025100061818032003d5001e0640d1201c210040f00a071500d074910210f5410040c06002042d491000708510510100e0040e00c4001c07401806040603140c401246070000d00398029071000000d003646011140f950b0000400d81e659911041d4041002201400c00c03483e254001c01c1c1c0304900c16543c00c04240001c0501c6c00c010040c4180a454542d80c070b0000800084c800c00c02480003a070303141c581494510f4049156407801c9595084a0f080d0009006080403521070026203005503075100c030b0440e48078068000460010f29160b4450340c20000c054120602141d0040000c100188400b00b000b4521a80180c40c1704a101c03c001004043d84e001201001464800078a4164000c03914020b5800f44080e07400d103a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 308410881 1250 308409631 308409637
    0x501050c130b030c121009050412020114270106030f0b0f3301030b280b071106030702120706270c1a090d060c09211101090b 55
    0x11040a2000240403201584001d00280140a20a03000d0324504c0d1102c01c0c1c400a0141003122400b0041500115204100c0400d4101c05000d1241041100c0d2505040c80580741400d2058000075500c2e0000f01025003017080c14003480b6071802207003104d4084e10b407003107119106207080080300d4075543d43c0c80c04000030f100d48408468076401130402032030508200000d0b603d02070019000661145031101d1500380100341c180500c403004055095885800e005000503405001c4101c42c0c42e42c42050070b140b54005107840d507544a040c1c0c2210810118450b01c5094140880c411540060118050004012120f203415402190312191a20543c1c1e54400c082413640703600d03005080116405512007800004a40482340290325803002c0c003441a144110b5038030303070403803810481c0980502c81007070b03912281c44076a5107400c5920140c4041c2245ea2004610b00700800100290441100000e202d15000100e403800e401e800340c04100c1007058555074140545d10828040c00040b43e16040c085484000202e0304580c1d03001e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 308412131 1250 308410881 308410891
    0x1c02010e1605012a020d02130507180503070803270909030405030c0604060e0904051207051e0601030302030a05030601020a1e06140c0a05070f0204062c010608070e040603050105 78
    0x2114031040c01c1800141c012080d41581c0380c40b642d038132007030140410f102d41e080300803164050740c0c804a1490b490010480300e1418100801141e41001d081c800c0b015444125400b190003c1003440305101d40b50410140c460840d44107045a80d0300a1284030039840000d012500010400d098002c3c2d040040700115140440883c1c00c0c412a0b0400f24080005083c14024628803800c01c66003685442e040c120060140c1e0031480c540f500440c44100040d040050810007548081034002f011515000149009641d07040b24030f40258140660b0b130400440c01e0000244907041e03ea040d00a03500704020090115910b420041c18507046108235410000403030207400e912550030351031001c00c0b1103a2100d0b080c45816a0350800e02501550750000400030100c0d08d04060310b9900ca40c61070103903a2000a41440c10781c2054810002c4d40c401c0c9007100008030340800c030840701b5030319240e1070140180719980030b10104080c1c02486000c0c0410b68820001d1240d038801d102c10360031040020000200389440f42c8510f421144c0c00c4034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 308413381 1250 308412131 308412163
    0x1c08090d0b07090e0901060e0a0b0d0206040b09040b0a0308090108040317040803090607020d050d0e03090a0807030b090307030c2d1b21060506012007050906040507021c02010e 77
    0xe00100c2c113a41d90a5911070f03480320080c0320240c40d145007040d42c06402422054656514114241c4603501c0c505e0040a107a0010007054850b91901c00b403d886034410321547c0e22662922611032403506104000d90210f03508088100c1c00c000418005544280d030040c4100d003009103051305400705001a41100740214040e48005850703242106410349800005800c40065501410f907909039240d00000316038901c900118040741d1400021030306803850082d03140c140e900031061380b40424211000203106003128010425480b01c0d4944c010b003945c50388580030f0b001d0000b031074170410940850340e41c01401411200c01100c0b50302501000b2514034488292180482d11200c0300c050380c445202d041034104014046c410f00b854900070760291a0344601c0d4421800402e29500c80c0300040d126801047c003d207880240c4150313410001011541d07561030b8181400340c0d40c0300704100304c041035142c102031258038894800364000b84a02e042c003401030f07045501010003000440d920741c540d01840c14024401030504034503010b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 308414631 1250 308413381 308413397
    0x50906011b0b1f05040509060417040e1806060604031703040305041205100506060a02100b0406081509100e0a2301060e040b0a0905031c0204050402040617061c08090d0b07 75
    0xf65100808141c2c013940c8500e04080504c89207202c08039200d80c226032300114111400000940d00c07a220b009070b5000c001c8040c0700328104000e81c902150031700100c0018600740c2c0d2066a52a00304001c0e40601c1c00098601d8950b00312644030802c86da401540c00c10300a040603410300381c0c1d40070744004c1500307011021a040e82041c0700c000512121801800d401c1403040300c0250034a00ba90f04029681c0310054883d000194458000403c1078807180e001402a010f070310140c9001406d0340d00c0003081c400701582c030301e982803144407580c1c9000c80d814800c200c038802401c0050111908240c07943c81c0c001c1000724907900c50380818103030041404001d1080500078501d07080c21142c0752925081070400c4440041c002003c080c2031840d19400240c01200f01c48016120480e050f03484d401080c240e20081c011034211540251001a0109030070f500040301c580105c105c0d100c0c1141d2030b03541100b8084c40725039203030302c0c1d401254080f0164030008504e1300c05815203d102070074813a50843c0300d444800c60400c00380c8500000c10341c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 308415881 1250 308414631 308414671
    0xf0503070c141e0d08030a0603080408031201060201023a0501090e07090504052113031103010e070509060d0819110f1b060c1f050619050906011b0b 65
    0x708181c4000d80501c054a40c43c1040d00f2408a00d0458030a50004c0080c00004009216070400d6400b0a024540103982c070351700c5035240e0642a5590388034100c0321116900c0c0500004102c0d10500032200c42040c0415004080d010b543c4140b02c10324851083c8001d103000550710100d01c00c3c0c107481a68001c0090110209090f10041201420b0003520b0300011400d80c103040400020450000b00c5000120250090608036030455945a2042c090308000004411581800005004403d0445003031544101c008222244c0454003003540c4400920440e90086e0740b40e80020140e00d020700184100170301440d1072510700101c2c0d0f000d40709071410240c158804180c0d0951310b001d1780d03101000f000314484040030090280c914441881820308000b081d40701d204c0e9200003003512030300009100d650326802030090740c4d20340d03e181410000040c1400711032482c003581980360040504072710100b9800484401800104d10347d1140d60046800310f211020311122464400b201400095102c0c40030351280c0108644401c80b4100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 308417131 1250 308415881 308415889
    0xf0d0e030d0b190e19050c0a030501080d0c030305092107120c08040b0313051c110706090e0903071203060609050402040e2e0e062107030f0503070c14 66
    0x241c400d1050082808550741c89448003081040c0055441095a1401c03507528130031855020780d581c0000150356402d0009020403070034074402600c68248c0d00c3d24103002903a01d40110709d45d50798001010000040c02d00304644040381c020f0340100d401240c0ba400780c52004001250f25604510206804d1410b10307000034104040c0003e1340708680810030b240c40c240710a00c0d0187c0f1210301034004d900521580c04000004110b01c1d403144a45507445681c0034041e500011480c2582d401c100381141030341c0c008100540034003411200d01041100950711191600c00f80300d4140740c40100001e400826204451000b04013920100300d04841520f01840903941c04100d050034154000c202040c00d0744414040ca0041c4401d00001c42411005a4450505003000c41d50078020700148078102505800c681d00321600044c041118107113450102d101c0c02c002c0d6a40d0844000b0307000001c00c1707006040e04003060394110160900000308041644040180503000f20b0382002c41c035458251110445500c58108000c40d40304040481c18 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 308418381 1250 308417131 308417141
    0x1f0b16060c05030c0f0d090c1d0609100e04020f030a140106320d0803090c09060609150a1806030603021f080105040b0d0507030615080c010c03050f0d0e030d 69
    0x44500d080b0f41541881c0c0e402550368000c0d031040c03020030b040104401035000803540c01418400d40001d00c0b40310305907941503030340b01030b40500308011003401c020800102c0c80d05102c80d01074000c0d10782d201040c0b1180d1602c1b0020210000150007264848404e4003194010340d02049441d5801b1300a46c51082e24414103480c490071140a036001e01c1c0c4461000030720104d02030880c04149401c0b0950300c41c00e0716018403900065140ca003081d0f00204038040c04401c0c001d82d40030010341c03805141c006980703c100a85819080203414040c403010980d00454640700c60350241440000303411241d290342000c0501071040c094624455016400100000b030b912036040042d40b500803290b000105010500040803043c100d4028035110050041c036011788d1701c2d03026648164aa408210070200d4100742900c801c02d480346026800b03415270a85900b03e8894001000c90107080101e441c407600041612407103029002d42d5030503a13003900849928502010b051002080c022224000c00c60f6481800c00610364521201c020b400c1181c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 308419631 1250 308418381 308418401
    0xa030e07120b070f020109020d0506091203060310180602040305010c1403040c1e050a0e040b06150306210105041506170705060c120f030906011d1f0b1606 68
    0x405000500d10100300102c9001d6000111494142e80300180803009a01500400300025008001d41580301306114001c00c4043c010910383d8150784942151018600e241c2c0816907907154160000d29641d20b503113069a011300c10f403c130141740c01e1108107001d44a0303000b01d8004d5402910165194480510440d40c0500c3c07a8808890071b0f03407010b00394201a12940000c1340e6900480540141061940b00c91074000c503501401840000c0000100e591266000050b105e8152404c03281d134414203010440510b880402c1d0f4011501e0310b5101070840d901c450070001c1c00c9002410444c982a9040c10460346440c0a001d114401c41c01000c201084100000101d8100c50316940200300c04090421060312110012807001c04030f9104075100342d00c0344810721415040c4840d060441050100006005038881d01113000b07503110391440400d42e00c0580e0b8a805040395400030300014100700d04001e00042c40440100b03041d100441c9100c005840082d280c02c0700800c65030180142014289100109008205050090140103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 308420881 1250 308419631 308419649
    0x5070f14010318080703080702030c0a11090108030c0a0b040614010303030207030e0405061c050f0f0714060f0301091a030708030909060406030c06051c05011706060d080f09060f0a030e07 82
    0x140d800e490304c641c035002d000702c02020008014007041c2e00c1c910800c240d440000480080c2e80c81081d9605e030004983c403540c0b0407540544540000050b5001c0c021003070b0303803c0d1100e03040070b480a00d4540daa10002e0102c014000c6070070f203594410041060044540030342c042c40c401d03200142c3d6500c11303040c007800940e040780384103100e18244010031101703450f101c000c110640c0d0305000800142c074081c5002c80c1800c0c03002c00c80d0300300340c811012100a07114001400d5011518040540b5600030f040c0c1c401e02c4a0b1b071042004440e0880003c00c010803413000030703510483c806400408020204010103000034144603130341d80070b4082d07a40080f641450b586484417401360810021502081100c1c03031540e86401c104600d03c100400c0c000e001c1a0380c01c400c0140d03410400c12003102d10007004290f8482da113403000005410b000203500e01c517605c0000d455027010009000c0181d00044039a050280c403130f0164440b9030010442d160812020b0025165840c240c4021b808842480c1c0c8000ca0a17562000846180184a601000325 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 308422131 1250 308420881 308420921
    0xa110610031121010504060c08010b07080a0509120706021b0402090901032d030c0b010803130902090a12061b0207060816030902090a0e0d031a090405070f140103 71
    0x14a00c0003550a600000f9140380c01c00518038001054101d190090f510b00c5542404104030400c640b0b6848040c40801645272a0066625490351440394000c0d07103030081101804001031104580603034054807419034010240488014040083d5062804503803002000d0307032050100d0000368945075603a00c48003905070340c08c50a01c200311000880030b54040c840984403025107041180c40b880c425014881040200400040259061130000c00c0d5002c02b04003690840220400820030010110444e28124442c0d000441c6086c2484a071a00035841030304e58940c000404c0000003040c421014448884a001c1d10340090004002e0728900c0c1c01c002d04440003000c5400c42802407010503001459240c00c180b2200c2a45074502c60100700360001c121000000c1e501002500c208644c540c1c003500024403265028080e1481d03035000340d40581c103032007072041100c40688040d02c2c2076000e82080c0c5201e5521500800444214a0b556002c4203900070b82604003508042c0c081114141c02d50f05801501455044000301b400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 308423381 1250 308422131 308422133
    0x6011403160306050612030304050a110405090a030e060d0c020f1204080307081c020d020904150503030f0d18051c0503040305090d151506030e2b140a11061003 70
    0x6400214000200410ba440b40442c4844d1943c0104105290700c1004488c7d8904103130510301d03501c4503603001c1210a2243c10844201a00b8103001e200d0007182058001c0100400c540e50540380c000d52540b080e600000240300040c0c510b6502e0140c140d294070907401900e0002a00004207007407034000f01c1850b00d127035001c200c100448640042103801c41900900e00e1074480c4d07132000c00700782940000059201c0750b0740085146000c20308668020710980d641168100701c03070009181401c40b4041c5a01c81caa616410a110318810a180e844c010b2030050200c0000050810354130301d1440c0803640102096480d40d04c20314204855000083d0450328540050a00790f00f185070990f401061446141c8505000362001101a000c0054240710b4144208034031505001600c1c512202158800080c0b2800d40041e00b0181e180180c1b8201080004445500511105030304050528558003e00340402c441c04018540c01405481e2820b98040e020700c18150792aa07041a081e200240e1034084050140d604070051408200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 308424631 1250 308423381 308423413
    0x306060607030806010c0804051e0f030106080714011b1109010608090a080d020c0d030203090c0a030b06060a0908070b040e0105010f020d1d0904110102060c03040b0402010804150e06011403 83
    0x50303001c1c0703003440d110f07030746ca010b0b4a0000303018021680503503004003410340811002901030000c41c01d44682995065112180311003094242e03842c5c0e219403400c41c2c0240c40c00307101c0d403844407059108034001814019282e258161108500d4100f42d50183c44112110130503041c146021040580102614039082100c4d00300742c110076803100d0140d40024030010000a0005503501207405a40400c803a4205803101c6010507240074010b540f00311020703401400341c2d50030340101d40381620202007681d0700070f2000c070110f40d500c4040c801da039840100c40e5820300a0b05100011100410443c5001802d24080b20720b4546251030001c82c20403c040e0045810301c01032178001c000c0190b0010b604646c504407858a06503002c603a20321044210660803840b504602c0c00d00c03c010500400b80b11202540c0001c0e402c0750241d54440800d12150302050700c0081120009102140240d0720500c0350540250094881c0841c415032180748108403001400302007015004000100806145d9007030800031030009030b0203082030441d100014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 308425881 1250 308424631 308424647
    0x30c030501150f26061602010f0c020c0f15030408090a05010f0806011d131e05101521090c1a0409021c0905030c0d050f04090905011401090605030606060703 69
    0x1200501d103a4168a0107413111030b400d400494808420389445003030050705151465114030094000d0740c20300054202d02c120310f101d0380e40305101903400380030303042018010040740e00410000a544200e504024403250580d1400840c00780780b0407000d01d81e5984511040c410300303140d16841355050007550402c500040350045101940f014017440e0040070351105081000c2c07241c48160030a9000012003981c8800030b00355030b101640c0d880010503202250409982c2c60015a0000c451055503108940030420140181d40101c2d0485013042c20300914855000750f010101c8041d025001d040a0784840d03070132091203005002c04024040e441c3c916020503013034100101585c8540e01c035959010340d0003e0042101c4c0160038480d41d15544c440810300c1441014107105642c2d40150291948a001d0b5042c80c601203400380c01102c80010303401620307609042c40d20035444010404c00006951a54030340400c40740704480d800c036280c060031442000051080c03c5c90245441c200004110074040c2c041003003840b020a804c000c0c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 308427131 1250 308425881 308425889
    0x310060302090409170a0801140102030403140106030506070507110109061b0c120501050f07080415091b0f0807090b0609120f0a0503251104050c0f04030c030501150f 73
    0x2590b40e000503404640280300c80c000250064130a010030700f040d192243d005003814002a680d200042e62540d5004507050844524540540d00c02c020400c0010700200c0c0005d50041d081000148480c0e880c0c640500b0f08400700d44050004000149040030002c440041201008007843c1c0f6450090602030043c1103807a519a90403400d003500301e0300c0e500700702c44400e06c040034042041d040060f001aa0be03015010f060700b5a1b800f601800c40c540043e4015100e00041d5110700e42180c5074001d02004070510600070b1580020668407a12086003c980c0740d2580c510315001000c0400ca0f04601c1440d00480702e050014903004030807100c0c18890003020769074507072050f04e480c040103c0307403400c103000d055429a250405001d8500720501a003034441c000c0c001e002c0080c28900442c07001d02c0c103000c81085010320301c0000c0800c005041d864129150f1030681002c0d8000b560002180090903d020b030070b50070401c6150069031085404d44c002510500421100780034100c4548060003a80c8a154202818503d00000c1350203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 308428381 1250 308427131 308427137
    0x5160803070201030609051e1807030b04020a080d0c060f1b0e0108060109121401021c02270102060a0b1c0c0305010b0d0803040b0a090602121806071d030c09130b0c031006 75
    0x41b40340e403921801382701059801c9030304071340e44d1340d6507441c0026030000204d038140d01c80c4010f47c600281c000c030007040502c1c45034001d90314030021504699402c1c0060506627030074945203a5a00503422014558882c4035072100c240d84903200c45d4100031000501c201e400800c070360304010205c2c0040024062420800d44030304d038000309548a0480e0803480d24020b00402d1038815002c0340c21a1032882c0216258000c200c40300300d807100301000322480007240589028102440b07006030b01010004a420440707030301c840d003403100051802c039a000d42c0e59008c2075951200003043d140001020000c108106003407040307101032881a5100d690410060b200e0311500c0c04010409880c0100500c001a01450130b0303440029001d6002804646440e00307440a00350030001140c59841c1803081c01030516205500254a074130a41460307454042001e03030040441b5a000500601541610032400010920f55a12000c01d101c1c041d000317040d80d50852281400988020b000d4800301812908105100c40302070f68411040c140c0b241d80c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 308429631 1250 308428381 308428441
    0x10c050711040f05010303090f061d0603040c03021002070603051302010507080f091305181f0b010504090e03031f050603010501030507050c0604061d0102031e040516080307020103060905 82
    0xe0082006850b8a03001d0720011484d01c0000300415400c09507000c242c03464101c48007006c98541c0415203c02e40c8207c00382c40c004a10002105240c508400210340c0548100c412020040d965404aa4005002c040110158000080c2441026810b00c81d05038000803c0c0c00c4200080d655030000380044c420508040c185087c002150000a40c2c0102120070007d40a00350142591076031312035000404e070030380f80418289100800002500b82c00610155000784001c40094a1490441f215009283c210006814403200340000034107503c1521031940440a19406103903030b45403000340c1d45811107103000f0011910501400500440d205c40d015241503074030030300b40001c158588040644460203524821660342c402c202c1080100301640c0c1000d01d84241d107a01400c5402600c0b150030303090f40801c64240230a40026401e00c0400444411903a400c1401401600c01c0c0c0103044106080d03581c40340d000024141d00025090045503414842d840040811140070415810041c4440b0f00c0c0e6a886115102500e141c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 308430881 1250 308429631 308429663
    0x90301231806150103113603010203240d020409050307030801050d030206040803190216021c0f0602070303021303030207080c041a0405040c0f090b0411090a0b0a0c0b04050a0c08010c0507 82
    0x4542111f1904030822005188101fa1520707640108400585080f064644c0c403202100030b090500a59010302c508444085108010410200c083e08090009540c400c030401000c401580760782c425010b09500070005155158000d04001d001b410060340300a010703030a04501800400c0c0d0125035035800a91040d4015565107034210b11031400c02100c042c41151500c00240014206e5044200d10f040610a41d51040c25a149029403040781d92002c6003d4200d405030a651070000b82690300811090744282001800c5c031190341c8082d00c40500781d42040707001d6031011109000c5040c042154007440b4038102d8040c814200714900d0a405e044000c0c04290149880e08085010031032084a40405000c50580703000d101540d8100380000b42400e13842d041d004a03d05249555045d00880440e640040701a04010015260151030000c550000540d0400c00c8038031041c0500142d9400039403070007980200010040703402c00307003040c0620000316400301034070340e140800d28581350b40c02c001030f540344503004401e01c03151a42d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 308432131 1250 308430881 308430911
    0x60408070615060f0e0a0f1e0308120103030201050109090305091903060f020406030b03010903020307080f0d05040308010509090601030c050f04090b090609191106090301231806150103 81
    0x4500e9084201c00d401e00b5001c14040e82c8407040400841060f0383d5890700c0052042808400101800354030900c10045c02c040c003010f007107c0c624014020301d01030140d24040d500d03114402c01b60001c04190540070261001003062590900940307015160101e42001101001e40c1c0280c00c0d17201c3c2c501501d0207640c903846800c0000f004190717640002d40c0c1040003800011420000b0f080294004d0182c00c010a00e480e8074103203d810140700c0c0b1038003907a05400541c50038a036a110b1210541100709420b1407450200441c03200e03003806001e203601641c42034559449075410b180401c00400d50040800b4040c2c2e000340010030102d0130b04200c1c43d00315002942c0480700d8413400030201d0098445401c0c0036104207c2c1505002801361700180d82031013a000d280c1a6040e000b0480341d441020140c0075009410441001c400781001d15003000102601e100040c00056024012601e0380c20303c13009008441d510034580707402c000c40c0080c1d850b103c120001e6450090102890700d610300b0784141881a017158101130f540c0710441d0309031003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 308433381 1250 308432131 308432141
    0x20c060f150f271b040807030803060d050f030304060b0415170f0a0506040209070207030b07050d02090d0501061a070839071d0f040f03030b060a030902041a030604080706 75
    0x5491158411001c40065076540290f805075906a03e080621211150803107840c0240c9003940d028402619a042c03454880c4241c0e03400107001a980080c00f11080d0f030008008011071360003080d007000510741320b20381070031b0050444480040c514010390a01b110200b0001c8404442c005a4034020025098001104403243c50000c007100038071010302c591040841400800601c1c20300c00e034421940301c0c07110341c2c83d607000b280c8035100d51100809241c5400e0210340071038007a1024002c0362151003001404e2240c6c00002030343c4140303c3c450948a90b503480e130040c8024011140e01c0d000445a02042a1030005a0b0b13541c0d0409104456548140d94121009441d4190410100b000607280c0014081d0401a00144c46d6846000500c54001107084012103e610341e041015018801c4010085140c9a40d40b6501ca0103070001010034210205503481103014016600c80019000600260380e0003d134a69280c414001210f041d02e0344003260074411402400326650005406a0269105035555140c182078a0401e01900b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 308434631 1250 308433381 308433409
    0xb03010510080709051206010f120b0103060e10050103030807110d0504120c03060c08071215170a0507120201020705030c0d140c0307060c05060a0605030606060f0c03030a020c060f150f 81
    0x52480c0034046c04039000192940c1641d03140308500206594801042288001c0b030303200144051004001000070442651041044118060684d501703010070680b02411244e09800480100781d4650a01c503203d940030b008400c000340c20100078080301081e0b1030040c000e0b029610425803e902c030182e84108101d5568000402154011414854444001c0c800707440e02c28104c40c460001400071080c0d0413600400d0251704c40ba8021403a15522845c1814071200191844080384030491050001c44000a40108008001401d400d901064491550f1000a0412086501c124820b6010713075020320713080d0750f91410010019400b000e0342c4007000b0501d400c80c1c01c042000f08000d5141c0244000001c805400004000109108505071440e596851342244219030503809000c1d050f03800100000c01c542404801844100701051005081805605200d440e5901c2202c00c074098540102e1882c480d000e007007040b41e40001039840120028030700760310000400061446028490018500b03800d400e0713150401a44030f24 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 308435881 1250 308434631 308434639
    0x7020a080d0e10020c0a031206030807031101021c0c140c030315010c080c0c09090f1c0c020409290c071502040825080a020108040204051b0d05010801060b0301051008070905 76
    0x17802c125101c5500d03441d031480c1c1a0040340382c17081440d5003c485803091105480d40000c509007410f200b914100d801a54a2100011075942080314000c110f41f1440034035150410040d0102e404201e060004021500704001900658020710140103050008000c0d2580f12401d11034900e80441400d0040350711041054000d02204d400099107030711481d0100d00000c40e90f0041d9181c03602a1201c07d4102d83e02c400b2114801e5460f0070421038034041d02200d80c02100c12094600e8070750b500780d0080c0c0026084418500003281c0340b15800f2881c0c0c1c00302c800801e0004621051241c407845628006c1d48900341d174460058003c110300c8012808000e81240c941c141d0300600720380c4040b20004400d08103002c0c42800104144800501030f203000194603100054080d1840d6810b80d0740c0d001c0d60321507500f0300010700009040c01c44070021141d1402e140403040d0014260101800c50042a29403400440508441e41038000008001080005101544034280d40101c3c40b0410314040e0b00070342d01c039002102c071203c558118944c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 308437131 1250 308435881 308435887
    0xb15040e06010318240608010c08090f0607080f0703091202031c050106020c120708030c0a1103121903140112020405100609030816170a0807020a080d0e1002 69
    0x5240410910300c0e01c00c1d8020b80781041020024030130001e03c8940d0400041042c881c1c0c1d00044514030100c080001c1800e0101c0e0007086158480050324295800d0425030800503000d00c00b04901d003081044400015001d440242c003075403c200c00d00400c1c06d4030080081c565803002d4004110a58031035404003407a56000741c2103001080d14500004e4503903100142202410784d420103d902c10b0707500307449513604a6581d41c000f802030014442c24041520055403c16065009880740066000828801441500c003044060070038016076150031580c203004c2080240c040d91010800509145120003200c290030f035062410714021280360704c120003170541261000f48411040000203a5010510102d10342a48200d505000c20341c0c44001103c200c146038420200000e088400c20400311b1136544c01000d0a04d41207140d0104618103443c2c65660b90041e035010041348000180c0501750030b500202064010075a4409024108510f1305d61080170302414003c002c0c04c0b0350f190840c103800081000312031040b450000e01992 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 308438381 1250 308437131 308437139
    0xd05060403050a121d1c09090906200306090c0c06070c050c03010903080108010e0f0706030b03070f03030804020f040923010608070f030c05090705070f06090602030a06030519020d060b1504 83
    0x203c440c00000d08a040791096111b03048074441b001d1003903011040c29564024409190840c010081d0094032030540d0090340c1c0c2d16070b181008a402c0b05c0e80080103825600c4d90341e242444000d1280034407000b40b44084030300c000c0c4000303414020049211500907810b40b9080307110b010381d418040d0400da6000c41b565031641c80c01a44408040d00401c1385ca0499040307200070000b4010038880a03444009104a000c1c0c02e42003500c0600644d4020f5000f19503070f0102408540303101d80c5901d030f4800d00d07080c50340040e00400c88440070003046140c09803c03204510415241440f100a46580350019a00d1101a40c4600c1c1c0d0071600342042d0ba0001d50281c00140301c2c10048421156603495503420003400344c0001d0b01e1640401401050a091103c056800f81d1031964078586800c0b2252620320b14500043d104a4140ea1240740e000d02180060001d14000c0c2c14010002801c90316516107580303003540f0481122070004850a22300056034404160040f101d800000c0441c086800340f0004901c00c4600c00c944100182c003040201e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 308439631 1250 308438381 308438411
    0xa470c010903020609011401050d030203040b0d050105041503050309041a0618040f0b0616030201060e0109140921030a020f2a060610030e0709020c0a0b060d05060403050a12 76
    0xd07039414026000d40315562a4240c80f28281c400d5080e80030010010b1100410150400305603c2c0200b43c06803045ea403c06403102503140f2281d101a81d2148242d40342e81c0140042d2415220758001e082503001c017040468590341e103240e280e00410440d240320b1a0303500141941300b0200c01c420b52403148020801075840c030403200e5031842a4500c1d10201e0041d860700074461800c3c1524407440f900404001c00c10303030070b14030400100c140508405000b2001c5548030b01340040d40181c0000318034013a04da4800017040001050059140013072000341903101940c031507040c50a0f010742e04030f0324041000300d4800050703407039583c0342020b406882450094003020000160380340200f030307102204404011001a211590604039800941c2e5040c3c00d49090360300c0340820315140801402076002030310440d40c22041c0c0c1c1103180d440030054200d81000a2055845d004151a002000181c590385544200b080f00e5003c2114610344070a40d48281c010001024030600091a0801c6400b4400a00c01e51401e040244480624a4251 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 308440881 1250 308439631 308439641
    0x801061d09090a1a15060c03040504050408030f07021c120b090703020c07081203060d14060103031d0402070c0605071a0405100f1a0f01091d01050a470c01 68
    0xe9030000e44c20142a2079203034800382c205004e401c40b10782c0e5580c80841c01e420043d05502400e5811440d11080100181e161a90301480d842103001d400d030161a4600740752001d14102c1c1c024004800c54000031245284c0b0b00380e002c020700101920b0f140446c008404140b01100a043e40b81c02d031a4032030400001c0001c3d080c0d05400034280403040300243d595243c2d0300c00e20b840c4e0b81c4140454a80c0c1003a01400041d1140c02c00c010400f40e828050340f00e001c02c0000e2000c005040050030f0700b081d000244900c901c0b070088a80201314946002094504618002076a00c8034604074a085c0921710401c000013030044140400400c200d50701c0610900015040d0a041c40c21659a01441c408d500d242030030076800e400200c40500c2524031503901007540240d56840b000130440220301c80d840480c188003020300d0109003106840403007203480a180da0041401e504010801c001e44d00c050340420303803080302140000442042065010700c101c1c1d00000150900f10002003401c085000d1000000403d000400d0082002c0415040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 308442131 1250 308440881 308440883
    0x917030d140703060b03010602060a02030406020f16051c051905040f0603020904271b18060306050f04020d06021e0c0c090a0204140f0402070f0f050c010f0801061d09090a 75
    0x81018550f0b0b03074807444846c0000d20580016800071000150700550036001180d0285c842c4000600e49042886080041d40003100c2c04540001102c00c41d03001c003c0b0030031441d40f0074038150306400710030694240001d002e07100c0d01c41921910454078104803100b6000f41c05480c00340141c02c0c601c1c09401d0710b031f1000030025009500c640344520308113801c2e0b00340080743c00704000404004c010016004241901c2d11004a01c0a40c0929030f502e150310700000e409200c1044800c080c0200913000300d00303c4d00c3c5060000a0342c101078404440100301400740001a555040e400c9151070344480c0140e10342c0d54001e40c031528048103018078451101c0004c1c50403a03041021031200464841250009599121008004100d0080340605000c0c111120041c401a140600e440400960300800c00f61800101d036070b843c14403501c0c1e400201d5401c8a890b903607408201d0140f041030b003001c01c20319000718a540380b500c00500082041c8039100601a00412001c80e10200c03803044e09030b2010107000a0340340d00b01107028964071821128 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 308443381 1250 308442131 308442137
    0xc06130b0a0209010e04021605031c0e060f13030311030703020a03050702060103110d0809060412021201020906070308180615100507020f091806070c12020d0917030d1407 75
    0x504000d030706200fa0f0750401810b175901e080300d0030a0340034007001394009510f510440401c2e2a00000044040005000480880900c1140a5129400340003543c000d1066041c0d00d4000130100311040302c821142c20b9000200c2810a50150303541e043c160020078080c440816440d000000b000340c000d070141c00030810380c21196020483c80e510010100d031140380a0000408011801007210040c0c90710004003a00c1030301503d52985014052800134105502c50392001203803c42520f650303019480d100101c3c6030a0010100258038007440b54000814a1051403401418008400d003ca00205442d02c4032010104c6400c1c00c49956042010403c005a21500100e074411020901040f048901c50320984212650141c50050440411001c0144283c4028000d01d0064100340707100884c804100309150290940307440b580041c0e803e50402d08850784061040350255840024001b030420341c8a41c0000c1200e044550075401002400c00301030031071162007914150720f0709141c00c00c8902106007069600515280e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 308444631 1250 308443381 308443403
    0x6021206010e120d030f020d060f050301050f01030c1a0f03040b01150f08010b0c1207030305071701051305060f060a02011e110d0203040f06060605031b0f07020d06020c0613 76
    0x8042090503840218480c3c0160002c90103000054020f0b0880852041100300150405a15203603a10440b4500e501404c5036030030782c000c1040203040a00c034154102e980090b01e00415819612900003159051084810609d80300400d141c40034484030645880200410000c0d580f410541881c0302540801c0c01140141d00041409003001c5020b4045d11101d8a450784910071982e2902555064035041842c00380c210b4050a01044145400c4000a00880c0c0c4a51800200e60410b03c00042c030b0701d4002d1b400000324100c0c501c0140040d54448140380300000350b8000c0403c0d541d6a0401098008508a215642205010400c0007070550103400c514038190300031201d01c014401000410b0b080c0c4800f40c0004000202c10010a00080c086400075540213004180490f41d02d41c060b5a0a0100c40e030342e41c8014001034000c024040b20018032024108880c04600c0d490f030030000b03040c06982440c444d40301d0081c401d9400c1d100305020400b80d81c040e50401d1050b90f09481d29464034001d85007460744903890440c0d003802d41c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 308445881 1250 308444631 308444657
    0x818030106061b050f070e0103060e06133201060e0c09010c0f0c120602040e1305030d180f0c0303201b03100e031b03040b0a0e0a030602120601 63
    0x144038040031103002da500da11030012454140e191078285800f0982e05030240c1050800c80c09000c215400050908440807040d40d13243d030810f41e08a86404960710059040340e018858440c10717003140f001d9039642010f41115010001384000a2420f17002116250350825505075003410306041d40301c40d00701d590442c59079540d6502c4c01049102882070760592804180ca45035000f0124407000619008144a081c0b0081429114000d08034400c5081004075a041c0e0006018400c1030115080c842d0800c4560102411407061599040e440380600c54540d4035030350383c0380741da0814503000306203603100c040c1c00081e2001c4000c0a801e11015481c99404241d02041d2580c003e5007030b25000d0f604001038040313858090110f4035410584410010468000e0651501c907034540c00c100189103102c0d40b0600c403c54070086548101004003800344042e4100910f039550030900c010050029190210360b80c1d084a890149200c0300d1600004224042e1600301805562000c00c0b802c402400000c0d5180c0541c8007601c0710b9000c6441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 308447131 1250 308445881 308445883
    0x209041b0e09130b09100f15050108070c110d0c0e010609050a0f03060c0c060c0f0801170c040c051b030901030f0b0d1b081f050114150f0d050103081803 67
    0x59503c0d100450000003c4004a40c200785243e030803207490026148003500c0e00440c50709071400c1d24040070126a48090b00340d00102249504401403c0c28240802e091800580241520000031400382141d01c4090343d0205a940e40100b22040c0c96100002c40c210030744400248110034000d01804021a0b1200d030007180ca8a0140904800c483c00010890612810755035444041c000340f180c0c0d80140b00d8041b451000040180c0a14421584280e880141080d4480d1005204d1617041e803107207000210141c60a8081d0030041400c1c460980c00313580200b010728242c1c13401c45192007428002100c0c503862210a030682c0402000402c81504d00340d806005400c00d0f1201707403040368110700c185640407110450090010381110f90720400d1b80e0b126131062041d03903a02c0d55010305202800004000000114803408881c091501c20980501881e40001c0101c680d21008151000d0260585000000002c50a60340c100d0407401110f41002d8104c13014007455035079160001c03090b04502411000e214500c40d0a07659410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 308448381 1250 308447131 308447149
    0x1150807030b07020313061407140d0e01110304050103050c07080319060518010306050a0b1e0102010e0606100503130c090207020f0312160f02041103190b01090b0d0209041b0e 77
    0x3c0c5e080d040811487c07910304180c60b4651407a44a9407200c0301032105901044880d20680c034403e114a0140c149045c210b140107014100c1141c8160500c8410542a07901031000400d81d01680c00a0800040b1901c030780e92070110038082c4c400700a0000c940003040090481d1480440c0e174280c42e02d000144599500c0d5000c000e03805004000b80980c1480b817000410210303015400071500001a01400108003036000c01141c256141e14810b03803c950483c07540c01c2d04a50f424411001990a9000a80400d04000000503100c01544400c0c004000d80440861035500c0203150058020382d0028860700c1d030a036268000c01c0030f0b405c000310591242e1007022500000b400c001c107aa480400c02c910240f072600440107a148800c0c01001c02c00e543c00c0c0514411080142c03100e200d0328514001c02010503403030b45050100407514407011403001c80d1490074408420081e03600450910192214160f1131601c6030031952540c00240034200e2150303403150600038005030502d0f05144412801c0ca0503038030005401c40e40e10500542c56 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 308449631 1250 308448381 308448397
    0x20a092606010e060d150209040f020406020d030b0a0b0702060f070506040b0705070302070e0912070c030c080a080d0207061b0f08090118020f010c05060f010e060d0308041401150807030b070203 85
    0x7104139001c100000e400c00d0455029211b60725401401d1a4181e400f041c100c40c0301c10114103065600141c1442040e40401c60001300500d00e10b42448030010f1b030808078807415568451643c03107041c0070401d001190760b18400d840c144110400103a4655070715090860391040701751002d882141d50080454160b44c401d408070340101e50190010554031785445c200f0300071550f005203810010300030901c40e51248030002c1c0041101c240903c00851406046013840414036920354441043d45c2c0c0708040101c0041d01c0c00c002d03070f00842c10680300161a1a042c0c103051000d460a0002c038002e940011b011400b0881c2c024410315a03a000507074030b400306662601021403c9a007000c0d01030031140045200c08006207000f82c40407030350100604d02000280d5165503904e1800c2400d40b0820590742007040140100340710000705542c0454100c3d1540ca151010f03883c040c080080142001d092400c5801d000e80e80c003e425082007104803400000745200541e5030300001d4984000c0d002c11140043d11001080b0a24400401d4603509 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 308450881 1250 308449631 308449639
    0x80405090f340c0c050607211704030f0c021c060f05060a03020d0f0804180b180114040b030d0f02060a0516050c120301030303020702030f1f020a092606010e06 70
    0x81c2902c0103090340d024201c0c600c110b03200c0c2041c42000c9500d485200c00b0382520b900c11104451840c0b107d0003a84001d600031011103041100214402240d0a07003061150380203909424044d007003600c0c01008851510300c541c00650481d404203100c4100e140341103074491001e030040c01d04000388000b50550f401503e105860300d9520580402c001c0c03016292000d024031070280305402070a540d070019074852440c0c1e005540075a2401c062032407030400648040c040c85000000884400380d900018442002007250b040c000c000310741c415000d402403280c0300c0d03500800016900400320382001061807001409541900c04c0034005028440c08140b620245000350787c0035070311010403540150300c0c40f80100c1e21500500b2844d10780b44699003030043d046102d04000d5010714020341d000340e9240b6050040c18034000c6132018064a03a13020040000340c085500007400203105a511000d69034001070001158000d92603000201c0c43c00f0390341202200001020f280031b038050052421707a61944e903182c01d8400b11b16000c80e242904 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 308452131 1250 308450881 308450971
    0xc08040213060e071407020a03060b0909070e0a050705070605240f0f01030e19052d071e030501061e210224030f07030e01060819080405090f 62
    0x1000b40140100c005c032800c1310b04846d0403e2902d800203915003e10340e0099512580c1c5000414181c144100543d0340b00d07001c00014800c107440c200322034400210085c0100000d550721408a140340c0e02c90021941c1003904210144201d0510440300d4410441010000284c41940401c842950070306c5562000c100300010200042045400015006050854200380d05802540b88500c40d403100d2290482d030042c0100d004081c90040c0201c61000754004d000d900c0400c01c906003443c8543c071000240e42c01600d051615035800143c0151030301c0079101450b00002c1c12035003444c0c008503a484d009180e0041221148c128400071690703500d290301c0003100c6840d40120305042d003c0b03c1005424144481100324040000c5005220842405003450741c0050710380405500c034081c1807100d0541c1c54001c00d045d03542c000000f00302903881c0c407004651760b0303078a02442007a051000d00003105106c1550152402410040c0c0001141d10f46510aa01d10000c03c40c0c0d0891200320701501c00d4095802080e800c0c185899042007221 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 308453237 1106 308452131 308452141
    0x3030114040b090f1b0c0d1110020d0515040b1c020303120c030907050910030b150406080a0c080105010b0423040c02030901081b0304140f010c08040213060e 69
    0x410040244426407012002051036100711100381040350856141700c40c0e113800c0140031080510054408200d425181c2d041d9080035100303c00c2370020710450280e80040104660041d145d80390007103501004141903100c01140c03200034500080403682411041070468141041c2110024000c0902009018403c01c082220001078081158601c51500c0d02c0344080846d000d4070700c4040e0403404400c0108625658020300c3d200890b10240040c00800e1312000260fa503800590012204801c183d5000111250184513260698400060192402e1b2419018207904a840b29402d074501402c000714403070980d06d610850082174850b4003d11340354040d2800140c40c0380d00060540d005503c141020400140302c40302180d51013644540d03a184103481d80c0009500d0034210b41c0404e40c2035031a11001f094100c4d00901c50b2441184201c4401038010b028440c6481616141d110340901d4002c6000462 = true := by decide +kernel

theorem cover : BRFrame.Cov 308273381 308453237 := by
  have h0 := BRFrame.cov_init 308273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 308273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 308273381 ≤ n) (h2 : n < 308453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
