-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5312
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:27:15.907602+00:00
-- url     : https://prove2.me/submissions/f89205e3-c1b5-4a51-bce3-a77563ad0dd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 955215827 ≤ n < 955395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 955217077 1250 955215827 955215847
    0x911130e1008210304080d090f020414041703070507050102031e0603031303060f020c0f0f12130509070e060316080a02030f06040b010221090906030718020a0201150806041403 77
    0x41c540301061480e200f140d140e58032070608010901682c0d64044296040a50305c8c8204250f014258903843e03c00c031000c02c039420000903800d5001404850041001111100c0e408001c03800030059a0b0000d0b0610784a860200700e641c400b400ea030000d50360b025010503840f500c0d0a1600b06042100c0d48503c040d03000718200003020000b5915246244005031081d40d8540403048000100d40480301e420302c40b500dc0315815a003810465030f07102c80c00310b810b40640c001c8041060303a0840180072198030a814010b03e0001c2d606182c100205030002414000c20302800369082d074501c0d00c6a0020318810800b590301c0302e4a04080140242c8405801071041000602c10810445007410b131301500b6400c1402a100040c1e1030f02c0d118010f0b8506090728041c665412001051070244460141c01440014001e40d411032064075108281641e92405014003070500c0d030504481c4080d0f401070350160503e20450b2001048100c0d88040c83e203505542074201a110b41c000c8404c000501540d288070705072490001c401907250040c1c0f01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 955218327 1250 955217077 955217113
    0x4051e01020a031d09090a110307080703060b0a030b01030503040f060c0c0e13080c0c040615091503061a030901141510120212100914010911130e1008 66
    0xa002020700103901322148a0b1007091261000200010700f00340403e04050560781c3d99012191130455070441306011546a608011a1040c00c4419100041103414210354448c8003070956181559013018121400002180560b64072034002c50080d400b9650701e40c280045d00300c00f502c40d030300f103201400498880200004c10841c420812038660400140d999110101c4010152600a01c050401e0700301281034102d030303000410b03040c02c030744c204680800c14140c2d01c0260124603035044000101081503003c1c200000304082c0c45102d08a01d0740d180001d07907a61901c40e04a0200300d40749115840e000301104000400c4400d1140c2c229176000305002d1165441d01d0a80368107c00310b911083c034007540c0180d040c500c0b5640545040400c902d800c44081d5218040c102058403961000c5422001c4c038044500e001495440c0d0f0720075809221030000341400580c0c00d00302c02e40301600d801d0020103c400030411021803614100780448000d04408820041a0305009039a400300141c5600b1201c8140c014540c04184007201d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 955219577 1250 955218327 955218343
    0x1509090d0912141c0f08040c03031110020a0503040314130b0c12070605071b0b010509071110060302040615050702131808070501060e0c161407090204051e0102 70
    0x1800500c80a100d185091004580031007000030f02807142074001c607002c603c40101c0224028550380d5940c00c1d4050090215240401030740d000d030503140741a03000e01c04a0320030380682c8400c001d010f00301c0c0c03000c04012441004982c8850110000100080180000c16a000e8584100180b0200c013450030030009244a000303c105520800002802c009013080e200002030020072144804500501d03111190b9050000142504580080c0081c520200e42085900040e00403d0440d402100d4000c407607003020180010b4170f0005d802101440602003026024803030030814101210185040802e15030319520500c015144650090542244055001040c083c2d00c40c041c2e562490301103550900b0345008044071b100400d04a001c40c0070b607000c3d9201070300921103d003000b070110742d200d000200311042d03444800d6915081c1c141c405c5d19400000300300030008003900310b002d04d45081c0a0030084901507103d00342c4c2c03031600c1d20650241d5805a004601007082e450903004e400c000c402003102039040c1c8100c1e900000e40b86d03090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 955220827 1250 955219577 955219589
    0x2090c1e0d0f060e09033109060512062e05060304140606011b030e0609090405060124140d14161107080607080a0603230d18090c171509090d09 63
    0x601c7d81d41c1c0d0703545103803101c56000c8032050740e5150034450b41300c4121001608042c02102d014510300000c100c4091000250580700740940400e40380360340041c2c00d034202c42c0120500e002181c0300c0301000220741642d803940254040c0780314019044000e11592111814944000c1c0502c0c180a8517501d06688440c0380000c2c034881c1585840e20100b04000c030400219240114180b5903040600c4008201c208080042d185041c0d440c190180c9020f40569210a490082c020085500082c4805060805201d0450192144003045040400d03840190411074000c600121443d0380c4c01c2c00c00b402c18820483d04100039a42510824024109080c206003605a984401605820412030040001841103005521a10145900000111141258200c2401c400700c4080540b442c40c02023100070b91031280280340d440c1650828840c00c081080c5480b528900030715000f6900c5040c040c1c01c0c0f502c560007001519500d0311480710070085444064000c018401c0c040307801844000142e105a03c3c020300181c00080704001c07600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 955222077 1250 955220827 955220857
    0x1091a0a1107030c080610151103071b17030f040b0309070e0a0c0806090618060105040f0f0f0f0b03040f080702040f0b040e0a02090c1e0d0f060e0903 66
    0x4655241101c40c460580d055240d280503041c80401004059031801003114010011514103450f038007104089082c40d8428040302e00c0010b441f00d1036a90140c0790700400501140c0a490600c09141c40315030018011006880303800381c1e040d0b01400001400004940c007044014011401d04030504020b90561141d402400406000400021240701042000d41c0140c50301c803c034492642803081c1c04102422442e060000824081d00002e105801c04545042c8071701c0303008107207084181c1904c0070603502d0703000606071034100300d03042002142081c21070281c0360041610080e08030149140c00d1000e01041442d42007445c50780c120343c4080001f028458203072508990020312a14072880103241c41561407107007903030080d082418520b41744000a140c2d48155041174083c3c0b03040c4000b003164014142c6503401031500a500400d0600801c140703010301d42c0900580751100090405506480c0c1c003514154100034031501f581526800c10304030302e800d58000c06000304140714807000141001c034001034481c060113080d451141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 955223327 1250 955222077 955222087
    0x60702040b15070302100b0612071202040f141201140103031101060e13060f1b051305040501030b15030703121d0a090902040506091b030903090303120a0b01091a 71
    0xaa20b40b040380300e0301d002205420303659000d9450040d40300c0c00f0041208100d180b81c101c40826a0030000c0880b455207030742031144a42540d030f404054035511a81810700070340399401d001c003103841e410030780000d0068030700400c00c1d81c3c480e180705003008000d50101192203aaa41400c5510f40c06107140c0c2840b038103403039150400320b0180c000c2d00002401421a988560040301483e420303c01d47c03032250f180200a09000d00c03418400441d41500b024141e500074059002d00849074002c00d140e1a1140003c0c0139202003c2d101803810035550400a03099403400c1c0c205035050380030780f002d02040300c078058440009084140c02802515155454003601581c1c140ca15005000c1c6982040810403248014030007503100080403841107e803541d25260081c140c0c02c41c100d020ba482c0c00d0204025203010f2224a03c00c1e035400240f1080c241e040c01c1ca0107000d41019050720b4036440f05000286d6039030f40500207485480b5031103ca60b040307860009009402e03100c921170581e0500c2002c1e030081c0a440c250b03810500d107441e00748190a03603403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 955224577 1250 955223327 955223329
    0x50a02010f11010c0c050609010e0c0d02010e0901090b0a0806010302090f270601080d0e150f04030f0f06061d180c180126030a14040302060c010605011d060702040b 72
    0x20a105811800b81940380180304a90250465030348100b117030140701250101e0307450840311401c032044403842c081143c0c0202c222255501d48650680b0015106242040c441e44400010a020407800c1e0040080320351a103040d0003c0f402d00d0b820001c020400b2000600d8594510340110b00c04d00030203883e04646055020001e0070800095003c490242003030310013020341c401040c5526464400a02400c10300b40a1300f00e002c605140b2039000c9caa000320340141182c40525149441d00e006601410500e010000240000004102d0201030200e5650242034482e1805009103003400c115840e0741c000c03903550307036a405802401c007075841c1788198402041809010251403d54a0a14102096070074030350004c4d01d0184614a0b1641c1da040504840150f105185140c00703900d1074200b4101255620b580550082c803155450030f10440c8242e180142110308640b80c181c6a1300882c0c156805160705111588d19030702c00300065640f0890a511b00b07000c03980c50404680000380060440d10071610080e105d90703162400300c807030b0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 955225827 1250 955224577 955224587
    0x406080a06170c011202120112230c0411031302040905210c010b03010915020a09240206010f050a030f1509150b100f0f0c050111091c050a02010f 64
    0x42c00c080c500e03481d04111680c201c0307942d40341e03040400c600094805c0901d0491010034000c0c2c2e001050309045558003030b07081c440f01ca0002c0303003e51425a4019401d1460881003136850101d205510b0424020b020f21043c001c0c20b02c0190b41144a240c6014501041044154400030791900e40c03241e4122400303c0c00c0d03120790800703520303100c840500b0f84110b00c00c0f00b8007039201958080040060840500c000d00c040c410270000c1508071381c40c01001421301c036480e51482200310120350007803c858880d800c0044096803241850110141c40c2e0617203001c0d0502035403000340f065804201c01030040c507204402d0b600032070511010079038071492840010504200c011060081040e10301c5003450009031070108000040040c106801d0041481410241032803171321000050a05101d0000244c014564441d000080e070705070b01c11a40c04525980d82c80400c80d03040c0000001503001e011b4400b51101c600681905c444007501085000241c1003030020b100c51805c1d01010001d5070206210310411380900341038200020985003554 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 955227077 1250 955225827 955225829
    0x801181505060d0204030201080c0903030f0708040e10031a22020d0209070c0b070f0507111f08011422270609110102030a0815010e04060b030711120406080a06 70
    0x1500840120f4200c07420500c03540603004690013669150841c2d05d51065003071b401d200d100305a44d05030700100310310303159170705044010148a0b10075107103a0b140c00d9480f00140c070050b000b501da00c2301d107582c5801c1c104144094076402c600c0d51340281d01c00d0b20650501c50346003104d42008602481d031210380c51150744107568910007103400e610f0300542810101e00d080e4034010000000684112110207603030000c208942e218412600200b0b030507440702842d04034980c407841d140c2c201e00a0700662011000408a00c06a10107009070490401e50311006040d50512101e142002c04801c2e00307a0290a0351000381e28150365003c00746030b400641c40c1000070311084000d8403200e110600d424503110603401010901c1085201c0d8414491240180c030054801d000b500012a104d100729140000011240d501086268000e020b0a91000344141040250001c0101c041000d507102035001255407540801000a240d0b00010b2504e01000e24401030040b60000400d081c04d04d00450240c0b01c03c200b8180001180c0319040c0d88510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 955228327 1250 955227077 955227079
    0x4090b1c170706051524040b03040609060e0c0103050601181a0c0d021f021c0e030405041104051023030c1b03130e062d1f0f0801181505 60
    0x10120b841c01c04100600b10310600a080d0140d091b5110b03081484c0c03101100603012209400880e0714007440c041c42000b55400140007a00c18950360280c0100198062080100ba602c00350017400503c5508000503084520042c840c5040c00903400d050501c4c4003070900124291640350103510341c1d00c100c0d90900c010302d000d8a0b82a450740d11480803040368041d00055a810400300860765407908000d8040d1500590003100c08050256000a01c4514032882c2a0441c14080e4400812241031569440015080d140c00d000ca00440c0c0c800040c0a020504012650044900031030801c0260600000381c88010743d0000494803a0305a030100203e10307401c5a034001c655912385503450103404040c004004589940c00311008d40c20020a031300340055840312000c81c181c46040010110241c042003280c44041044214120094100c2e600004000c103980d11380c90900044030802140b0403e8035030a102501400b5231203495014441d0340c00040201c40c175030022400960310740e000b001c02e440800202d0781b030140107160011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 955229577 1250 955228327 955228331
    0x14130e01090c03062003010308092d1804170c1c050c0c01020c2b020a120203060705070503190c05071e09060806041209080109060204090b1c170706 65
    0x1000c0c00b01c9854070009881c000c0408012058003e490900209101e11007a0b1a00e181070004101003680a0042c140051b00500340101380c59103c0d03075521018034206a2010911360240380a505810328070003c019a01115031508c080781040d858550761b000b041041e54003407800c0050b5410318007074148100c0101c0800240f20700008000c509019003543c0000d8503096140c401d010344140590710010340041032880c06480c408100c00e81c408038694000d4810500783d060140ba400f10001030b1a41c86804000740110031810b82080d10350f10415091002c05008901000800c1c05071401140740801101c00307880300c9980c1c9494a40894505a45c2c500d452100038100f80038126001880503140300d896415080381042c081902900d4001c000c08840d014050149a40e02140010b80014102c00000b10200d950f4107210f034a040e41c90010500703580c82c0d0b1508a444170707008503042201c1f4085000e1541d5005048844138824044500004040b0700b070030700c001d4628040b409600e140c8000b440200d42e90310344c200341c0c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 955230827 1250 955229577 955229591
    0x120409020715141911030910050108070e0c0a030b0306040c0905071103040e0907120c0305010b0405040b0f0712022d040b040b09010e1e0a0f14130e01 66
    0x5440094020107001d8482d181903208400700e06540348a01000a50710410204542c0c844c2408845010f8819a030380b20040c1c5e84c3e2030010008a4501c0c0614410200380c0024030000165030b07200015100c041c0d1002c02c2e113a0001d9407c1c8070b000d042103c81c0307034041c0341419110b4032030000560807005880b02000d0280c050085500b40010b020082418800340e60501006002d0f58690020469054440c01400001504144018440304101c052020340058100048800180d29a140e265202e4202d01040307503901581082041000801c0c013400300b022a08a03401c1001c0c0c507141c0c4a01c40c3c00b501c02020200014820700c00621541d0090405803060207450b0b5046403542d000084d11103c46821440145556080c00304401c0591207043c111010350f085500f885083c50300d0300c44280940d03000000070a052046e240714540003521180440504100b4650300314401034160320138048800324a420951401d01004000d20405291240d4000b0400302500c051510f410441003100007400c3c800c40d03e91055081c644 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 955232077 1250 955230827 955230839
    0x90a090b10090803090405040507030203060717090a02060906030402030111041d090a0c050d17030709150f0e1e04060303050702011b020306180a1703070e01090305030d0209031204 79
    0x4481000d928003600c504580c80c100d1441980c0122182c8980700e035a900c00c0202601d0f42c20560002a00a841941101c2e50152281d001a04141c011a130540c0002e4048440c04803100011007600e0304651444060044500181c002c034141740f00700c01c1c1c0213020f000008003150441d1000d41c03246131050344e48800743c0c0e150354841d80c0d80700007a600485c000c1404c29508002c54450140407480f03060b503031ba020444501c4a89002c0500c858800f02e07110a851a40a00290004480c0e40d440114841c0c0c40581d00d8020650a0806810409103404503c0003003000d007002c5000d207950003603a10100010111001880b4200302400d0801d0351080340c00d9580c010b42000703000010160000c01811005100341c070341c520310604000e00e4420807915507030041c0d0b01d90302820220324030f130800f800018103124048040d209211416101c00712111302c0115440e0b2000000010010529840b007280729021030700346000c0600c24910740301e0b0396980c05901d90000c0c0740c9900103408401d694003001240c400c2100081c241e80c03600d41d603070b0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 955233327 1250 955232077 955232081
    0x90302061c24050a050a050d03021e010209090c030f07050903070b070606051507170a05160b041707080912031603020102030a18030507060b04020d1103060315061005090402090a09 79
    0x194101408807809500072030a450301503401015218094981b244a614210811030032281c40c60095041d801740701322101c004014a22501c290645800015170b80314005410b001409200a004070885481401488100034186c1d0080340c000e0702d0703031a180d07449802d0040041e083c03950540c0704516031200080c11004000d100d400107001c4500840704001264080703030910310030f4030401c2d100904071228214441b041e00894000351802586601d041d5042050b458030321285680d00c00015900318001c03000300420001c101c0d400d80a21440ca4032510304120003561004418003800d403485200303282618503100d5036035041060720316041c404d02c4078155280c101c0c1000ba000794002e845554485091500421540c00383d601240919a4165101840c0c4400d0303480e514020f040100d40d160b40702d1b03000c104403003c800741c0740102440c801010320364036500d09040342014541000d20004900d000068810810250780385104800c0400c0030b820801c0d503410715000002e0081c400d05864a91142403560007103400700c203035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 955234577 1250 955233327 955233371
    0x70912060f05160903030f02030706021b0106060f02370308091b0904030c11060c01020a020f06010617100f0e01030620030601120e060c070c090c090302061c 69
    0x40c01c1c1002192502c5018800791000704040001049034041e0400010f40320f0403102c00f80e1070b61481a81e0501c40c16a48040c10303a404002480950b140a01207005009402c1c4150b0740217000c282040003080c120050003940760f0400705105902c0c907401c0d14070500d501041c21004051040030b52000c03049440c00b0319014290319000c2e1001d6000348229040b010704000c03100070560641710f00a2400170715650307076541124550035a031000c54403824600344004d070035128000a4640e00b038200c400544c45103036a40c4001e2810208503110303031159220000400825420807010181005840369420380707641c80c070140c403605901a80c005503001041c071a0008407502010201e505a922a15082c0403c0c1240c104004607200c091021145980d0108041200d0358004c01007442c4603050008080381da800e110f0011800c00d401164006040d200c0015040c0030020a0162900500000c071010003d01985503001006003c00c0d00000f8080d81c00040d0201155107d01038164040e99001d0090005c1c40090800c20f02e111300d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 955235827 1250 955234577 955234601
    0x203031008150a020a0309060908041e0510050306181510030e06190902122508281209050a1a0d0c050403020306070c0b060f0607030807091206 63
    0x800c48021960010201c2c903018a0301d41e4498030490b030b03120700b6000c400a40c0618034902c00d01d6907a0044100081903401128040340c0100405900c0d030340742100d203800004030aa000110160801e005106c2c50381d94141002d0916000d01d409a2640c2d501c9000c0b43c0d42442d1065020b0049051500700050210201112225900180c404260000352014268192500841e50401503044000020041580701d18003580c03140c0c1410700270500c00419000b0605103203071000502d007160401d2000001280752139500c6c14082108024258125250501c1180c442e52403030668800421640c4103003980d0418040d4410307419400a0004078805036180e0090000b210b40d1007090301a02111800051051110800030903c104202c020351402551214031402407109403207a2041c450144408405a01e0070400d0301e100396240d444000d614009814188055100207011900c503c0c090040c1c02546e071221000d82d4045507250074901019211072405a40c052440e4100c80607884100c8000f44c18404260014090024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 955237077 1250 955235827 955235851
    0x40501030c0f17060f04060303052203052107120e01030e01150513022b0f020307050d0b12061608160206010605180901120201021c09170a12020303 65
    0x81d1414059800380d9140300038102050800821004148018012a502c80401000750340702c0403261000030115141c5070000d174002907001c210081c44032340e00c55907a10041035142030021050b2850b07891551b642b48000600c4401030002e0000b0701d1005125090b03481316a8004400f4070750b402034a0008000c000d00414541c006400c3c4520581c10f080d062040035100401c0b00c0800c0115401c00302400110b92103600700c150708a900300510902d601d20489506800c210305002c00002401d80c150300819140d04c01200c1a4080c410024804c0641e0040308982d41e110607180003040c1030810b000018110180f1041102c07190103151300f0043c0100e40f0b121001128a100d4581800c9619003146100450450300001c80c0503910040061284a00610250000c48806051000368229050100d410075400380d01456009844914110841da014088481155042400d01c180010034810042502d1580e00c070742c04d2820f9000c1c241c500310820a024802d0b50640010399050400e00ca060000d699900860394035900a03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 955238327 1250 955237077 955237091
    0x50c0a110301050a1b050a0203090d0506040213022a03071a010f21020103110d0e1f05060904030e041113080106050121020a1b05060403120e030706050a09021504050103 74
    0x900030384118a031002c017282404959080000d03066a00394440c0c4162020351109000f08950b507510310a141070010310410160039103007003034414801e01c10f0384d01d05002017090040c08548400048181c0e810388bc82d01010100f15401090030105003544100740f4050a440282c8443d81488004544240e049030008180c00a10541d156009450304445003101400115030300f1000c00598841c0d04a500d00124079042032b880c040409d0f64140031107406400192141e04005441b5403403211071240c1c81003909083c503082c00145056000180314200042008050003281100410b281e02d43d58044108070001080003036881e00002030300c00341842c00344602c80c01982401e42c0400d0a5100f1b00c40383d60707521681844034542c022440c2c202c07000780d00222019020051617460924200c210084054001809400039195900301801d000704200600c001010100e0706109034001920fa00004070307580c440d0008400502c0c0c2d04c81c0c60140015041d18800a03500064251192031014020f20041003143d000342c030100868 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 955239577 1250 955238327 955238341
    0x603070305010f050607150f0e030409140a0c20030c010f021312080a0c080f0406032c070b07050115080312010614090906040b04050c21090616050c0a11030105 70
    0x44d116086c001818001c3c500216003030000550031440768a42074040100d141c01c07000200703502e10b402ca5030041036090785480d601c03025440d507045040e4012801d10800d1014110140001e0581d000390348004508400d104952596640d0a00a07114800c2c2140020312400c41c4000c1001c01075000726a800d403880040300b40000300c10420354503c00c90760b644052207608004a0702d00a84040101c5802529016820401c200d100c403a814000c1000d419143c4001500040c400f804003460f42d00004500d41b42c00410230304008116000502c10102c1300c03142c0b1b074603a030b5483e00c8c0b41c05805001c1403102c040929529540100d200500400a020031f00500008100b8a81e0780d01d50444d540c104004030b41c030141d0400c201c0c16580d4140200d069510010190004c207122210102060844100300e5200000c1c500104100c5a003500032101a800810760714514005810000411921500081c001c4211048180310001101d8024020fa400152003d02546d1140c42142402c4084115030754503d8400c0d46003100051030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 955240827 1250 955239577 955239589
    0x2150d09150c02120714070b1b070303230415171f050f01050c060411122a010c050a0b070f020d020c01030b06040905240306040807060b0d020603070305010f05 70
    0xa4002c160f8014030055204800120700c9510500b03064625003882d070010080d10004200c034000500d0359566a5940d4012803007001c0001401c03034003801c017940001804001107a070040200e40e203603045030600140340588a28171081e61041c1d5200d00654600c4d544141041900942c03a14600380b080382080d12550307500c3c05528528103403260804035100c410f840c01d208505100c04507014040301810298a00304c210552149440f0b001c03242180e00c100e0500516007039007458183c9080140c01640100401140b0070790349000c0004d040002d1901c00c40c0d195840960ba03110302050310080d50090140c440c00005c0e810031707800445084500300c01041d05c91120550f603606c0010030041040c001d034003418000c002e01c801140070301004241c81e41d1105007480041448810b500c9500d0142d80314200000c82030000402554681940300049413007500500b0411010442c84000c84501d81d500c00030004040120000160b6030900408002e03402901c0401001041380d0198040d03410382e10902e10036004c2c02c5e80c1e43c0801403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 955242077 1250 955240827 955240841
    0x2090f060312070c0e0c040b031006030606020309010522030f2108060f040e0c0613030b0f012601180f0501060f0b120c0d0903120b19030f02150d0915 66
    0x100130390145100b04003000c0c81c01c60064101070704850061030305584055541c070341d40069440414110144408100300c0d50140300e54402018140043c504000d049800a03255000b41c43c8004410a00c404034011400c2000c00f0400140d42e10246540c018141403c05a100c05280b044400b0751840e0b040341110014040d0600d54420713200208003e201a132400e06110180001c004c00b81981d20440c10300441e2561400c025000c401d04000e0074160244c0345d03090005c48100302a004941d852103a41c0103004c164400741c1983c1c2d6401405140d0240c03901c0700700480340146070001c3e20350000c00040414004011100810000c154090002408004c1d01c440d5000308910b81031062440695081028890031490100415070080038071a05c1814004205003201c25a0781d820003c80c0024150010540d02550910803c0d85052050740c0420103445800b22000b6030031038030701001c1c20b4910000141c0045682d01070140b000c000107002c96645a07180386003407a01800b0b100c00101d64003401d89441c1070b09107503a482011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 955243327 1250 955242077 955242083
    0x2812020304020d0f1505090a17281404090615020609100e01091505091911060313021201060609060309080a08130c0b03060405070c02010c021c02090f06031207 70
    0x80481d0f00d82d02c80d241c0352107641085692100e0400c240090300000d10a941c8588080b0000e0044000a440d0900314043c1e00e10042c0da21a80c00e021240700b96220311814034640c1003030600010440d00e120402d82d040c4c40c0900c60303a10b50003000100440c3c000c0882d041035088034141600e05908100e03602060761103440407250100203600040d002c001d400c105421041603822548000154000141c82e81540b41c080514614503450700c88080c8402c00ca0104003031181d41c40070080e0541071060b81d41d034080c851018114054811900807003c98950400311081b80c0405900820813070b04042c148114278040e194038890113020030400c0d100065641d0281c002e0060056121010621304400d4840694003054098010714070b8a108071a0710300014040d101403000707045101c0d806522454000100001c0d244010100003c104103024080c0c0180d81003c03c00d200307160b04035a42d503030840812500038010302840c00d000e0744c03280004040c4200414030209480c0182c40a40540d0054000c0b00c1952990340300c0c4040007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 955244577 1250 955243327 955243339
    0x10060e03010528061706040506180606090a0219090305070b131205010e030d020306100c03120f2909010b0319050a0b0414090f06010f1208281202030402 67
    0x601d14031003071034800f204181890740006400c5482d8080307641001d51005c1a4001035010b4010b00083c40030070001300d507008520703266890601c0d88100030710f82c440340042c040500a500c0c440101d000c00c0141c0d01583d41d1400e0224004c1a14a010500103109040a100565a82c0a52031010078042d0101084407998044491000c0d045858021140c000c3d4035082400e842035540c810204c140b060061008080e0000f61481c01358030380c01d14800300705400c0c80b0304800390180103140d00c1081c00682c001b5041c1d09001d08141002501d00c480d020090082d241c000303101005254078055100300000307a002050180501558040300980c7c0310410907034180310541d01186010300c03441000c2c0140c2c003d904072a0b404202c000c0007141c031890720804a003d440780700d445c00c0220614038080051840c030030001c46528113440c200400080d40340c0784020200d02540d026095000c200c020f550414060180c044034a982552600d40541c2c9c501c0b80a56010301101030f032a0400940c242a102207450100e000343c0e401143c0050003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 955245827 1250 955244577 955244611
    0x405270c030307200904080304120201020913150e07020a030305060d1e0512040b0a0e040b0f120c150c0d031e0b04390302070f0b0c04080610060e030105 67
    0x14007a60404c414120340407582c4054104071558031031a4075180110b200f030840329241d05191801d0b910a41c51000d860303045a1040c450602e866036035044030200a00c40340340000300d80d20083d4208600e860503422482e01c01d48200c092000481d400030b00c1100c6540070703980410150319860100401c0450807540584548070301280103101d0045000c030650613a20a03070441e551141d02d81e0a145050b005940080c81944000c142e2803042c0d60825810040e41100f140e003085103040f00c0740001c1007607005807500b50141c40c0b040d102a140c0c10081081018484001b04520390140c400c49040c840340e404401f54555234001c1c1100d0412260007801003680c0ea441d03024405101c4072110544000811040140c641d004e03884007c00d03082d83c0b514114080b88035006080702d503250a42d40954401030340c26075000c18109841013200402080a44840c44819540540d9a92817900c421039045180d0040d40c018460a00800c024058030410030407030001100c4c1c50b62a50214200014205401ca4004896101058a000709 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 955247077 1250 955245827 955245833
    0xb24090411182403180601031208070c020a170312090304051f170c040909060902012a0809040e0708010501030c0506041d07050d0f0605090a05010302010c030c030e0405270c030307 79
    0x9154000caa813806030710f01c85e8045165174941003084c1d009544070a0031030b124100080c0d00c50440d6a1202d41c1d8101001c059996601058440c0d0280c882c400c8c01040321900d11001d08018003c60302c002110003078138001070814008954495006200c3c041c881c828030102c94403400342c0c0000300315107410340751a00f591100030149450a4800001c1841c1c880040c03c000100c4d02e14001c1c451001814000c4000003044039003880094108002a000043c1c9001c0da01c0005100a08001118003249d60042c540380d03c030350386580800c0140c026045034030f030140190407001c0388000055204c40c1c102c0b8014662200903990711070a001861242e80511710301b111040040c1c41501d2094605c3c650000c10358640a403520800301c6400701107500050004c40341540300d0900700700c58500000d01d55000300c04c0302c078100401d5165500182c40300b00c12440080c240b01105406106050058a030030006003c00340060290346041c82d00d11890650004240791038001c410322001d5082800142c1d090031400107001145070031180d40b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 955248327 1250 955247077 955247149
    0x30c140d11060901090206030f040321020d05010f0b0417011103160e0d0b1f1505130801021305010f0e04090303240e06060c0a080f040f090b2409041118 67
    0x4006400f80030214cc052a6240c10140701410380c41c2e0340450042e12407010200443c103803403040c1e1101000d589040001d04c00010160200d0b003c42d06070b20009402090f0310880035024061030318614607000702c00b00030001005410000001d0100c2c490f40c031103854841200801804d90107c42c80038005140202c00180030b20400e01c020507070150b2000b030a000c00b80c3d944044151402003201e0a1001802c040382548000811416500c0600309650003542809407824689110b0304203440341904004081c00c0a600a84c06002001d400320760181c802d114140031401d001c0d0244c0720454034000d0100390b5800400d940d07180003400c2c00541d11307101d44441d042d48650042102540101c000c10400d8000c3c00c1a460008000e00000e016008807000c05d582c40368a0708072100d0b40b400407540310429003810141c4a0380c050f074030322440b400c1c05014010821408600116049440c0c0948205103410a150100d00c80302c00c49200701400b015031000c2a8104a492108180145000e8110845444d00c00c1c156490b00105940 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 955249577 1250 955248327 955248331
    0x30f0708030a090f03050a030b0d2111070b090a0e04170d0b210f061501031104030821060f031221010b27010c030c140d11060901090206030f 62
    0x441c0100c1c02d50629240c04d160500781160407004503a00080d8a24460307014052501030a0b0101e5602da20680c10340c0321441103224054420840c0c0503c43d0400d002c0f01d0050040340400f40300007045034440d03515805492100d42c02884520320412803081d0000d400f480e404134140c801d0703520404400301545100c403071406641009850301076098584221508a40310140d0503038424442000350071603805200281d42c101128410b05041c03c0c5c0101041215124241451404205003843c00240c2c0210b05044240c590140341c00062602400003091100411f0200b840c00300c0307452002c6a26040d0b02d0340c104019521078440b0042d41c040d0809092110340130401c40183c040d40c00c4841440d209003941003541c0d501d401090300058007102d40442c60035000c042c05d50079a28444603403285a10034001348800038051483d4150b00408004c2140711507810099581000c08000380305a0840f8190903122001903d0807001103032111540c840c0100148030030a05020b104641ea4014054514680f642d90402400ea440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 955250827 1250 955249577 955249591
    0x30f020910050402121602010c020d0e031e0105060112061413020d0207030210180c0311010c0b28090206040512010b0612240102030d020c0c090405010b0111030f070803 74
    0x807281d00000c00b40c5460000701020310310150174654a1400d0041106000907650003441160b03d00031402414980001e54140c0c00b50843c00d0134800d05401000082c0f40141d100130455600600c242403140c2e1803c1508504e00410342601c0d4a40f00154801d84070084800902c940c2260389203d0810401d5400c1560217180310080c0508094a8000d0806061060703a1010004900580c071a0301c44500fa00c52610a5400c05607036200170040410981e00d07002c40110407800013078075401030360600e801e003a8040c071400315015a1021701402c4500e400c00f20400c50002880110204240b0038030401ca43e007095206407003a0b0b83c2e0007041d080c2003030300302001c1c444149686805042c0b950f41e11a03070036080d5515100980f0030440121100304207443e00611407541850125007500d00c42040c03001106840c0e03004425181d2405c0d040d000143c031545a61411890101c021800396000910b0300203100c1482019001403001b000b00b078070750400d089260545659a882000c60115482d00140450000514541d00440d08005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 955252077 1250 955250827 955250851
    0x14060109060f1202070803040b10030b151c1209091506050c070e0405060103020a0503010c0e120304050a0f0911130947010203090108060405070216120c0f030f0209 72
    0x82c0710040908981c4566810303502844007000704800c006e00d058016030f11030804181c2c001cae201e185559590007020040c10030350810407001c07541074444c1c807a07404030340270324003000103d4050581c181415220040756540003030000f0b071f0003900840c0100560062030740301c0c2d802e180f65201d02c501e40902103c564000d214401e8090048100006595000789450790065000304041d02aa51451042115420340742d80702900030b0f41016180f40c0d101e42c1003003101c040c1c0542641c45540c0714241415650451040da000194401c0308000c2c04100c0c242003219910a482c20034200708890011020766598038000e844c0c0c43c2c0803000c2601418003015019030810082100e5050000c6551450301c280c0109400c400d14154490180c18622845100075a55400e0320450080c00514604018080003c1010900400c00c40c0529105d00100319201c0c401c20502603d0310031050101d0400d0f41714040d100c44211011801c0d2040d030051031000c01c0c050a91030311513049a0307000d03643d10303000001ba03800e104280714010700c0380000340b03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 955253327 1250 955252077 955252097
    0xf030c100215040c060207150c0f061e0e160509130309090c03090c0504020f0a03020c0c0924030c1f0201060f0b0a1403060a03080d0906180614060109060f 68
    0x1c4211400b503402940b040444005140c10a5402854000c19a101160b0700d820804044822504400c54512254018110080340711203030500c10054403007a0b003240f024402240500c41036160301c0d801086840c850310145e80301910000d1200c4012211350085650003c02e20012a81c92548180c020401c1071003401d00302c80c040c1d03580e00c0701000c40f1a03e0100304007117500c0f00341a004103c203681580c1c0180c41c0031501141030104981044481c3c2c000c41c1d4400d0309142c0d00040303c9900c0c03d406c03c141c00302c90f07000409429040c5000800951500d0140c56070f285000090000c040030b900d00400c0038904408040c0c01d00b00d0168128001e840c40019100c111000c2d9543c3c3d06002c550078504d01d100c507001d440d5092071950348001e048001441c01e2a02d07048042c8542091060140340d960380180381045a070402d1660b03031148807041580c001800d40c4000100051f240074062110000600940d0001900440080201030300c4c0300c40000c1a004c0c100d4807140015050300c0180800c5009145900da04205458206c2d101e03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 955254577 1250 955253327 955253353
    0x2030d080a1e0e0c090114010e060403150204030b010f060c111906111002040b0301030609080f0d0f2703080a111b0705101407030e1801140f030c1002 66
    0x1031010020210b81d029101c0b00d40d842d1076502000140d500c20419030b1800100c2d80f50410742080d00402290b07142c10001556a43e6000c1e90701c4200345d601a40d00040e00b9101d10440148110080d407151004954a44107007000250f12100010203604985190700e54a1402a055031807440810008044d00c0e442910601c0140c5051403030100c003030280c0a42c1e2285500034155502462503c2d1245102030b0b6041d00402c803d0200300000000c3d42c0c1101d500900101e8500400d00d070001c468014030345401100d050100e0400b141e00d03104d4100816011300304108101c200f00300200d40003540e1014a03a0002c99818800308400a8440d1818030340c0040d14402c001103400d07103029186030a50080200d0041040c01c00d0100c010f004050080b00c00400044402ca00d120308048400390002100b5000d5000038000442c1c080203140c01405d1107009440001d01d04450241211070310701d01c014007805a401c0200b0310700c126104c9810071070fa050001c40802401414413031a464200405801352454400841c041c0c442d1034400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 955255827 1250 955254577 955254611
    0x110607031e030f0e0a030c140f0312060a091404030e0f060703031b02070e01030b150603090a210e060f090603070c030f0c081801020111042c010302030d080a 69
    0x18241080e0780204a00ca030000f03080095410701c03030405695030031041302c660009400c0181c1d0440142d000728106010082451007608000ea0501c00b148513001c0011164039100c48070035007a00c00e9804950084440d1f4580c0b01c80400c42e0503005c0040144c0e1134040124000c24001c482003101154000e1614940d0100c1c0c50208259410200080340829140d964036018a0740712800c00110030220b10040901924042d0400d8141006210281221038540c000c550700021b08031a2842641001d00080d5036410009485a950305d10444281d0b41d8134040a80d94007040042440181d00d21540d40e02d81401c1503000b8200070503603111502c005007c0300c00700a2064140c4074038014622501d0180c6981c00070f603102d400c02910203158054000d003000200b00d030110001b40c0c00c1064610101d1090710b500c440052001c0141d00500801110155071040450002084410125200c1c1c4910f0030300c031480b000241481c083d2524003000e0000079032680001c51101b040c0c1d0310502c1c103160b003d8050035010031038070003490f14070403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 955257077 1250 955255827 955255877
    0xe0a060906291305010f0e040501150f031b05130320190803070809041d010f060902070507050907050708030f010e0c03070c0204050903070c0801050610090311060703 73
    0x544208404465140e44915902c044a41d94104045140c84a0100200752440450103014140101c030059030003814811081e000d04008081e104010301e5864507504128100001140b400080100c00810b0705241700740140d056454800000e09052001c0b290107480c203400c03081c416008450401c0c80000031801c1447c0c902a0851402094094164034600340403800e81c0701d41003007003024070b050f80410601200000304c0d0701c141d030851012511b8400c000c00080113000b40741c0c10081d0548080c4440d540305001940071600342e040c044c01c02c01c4403540c0c448461007a401002c80142054200000411160400794120340d4808120300d0258900465542c5200d07080d00b0076514000104100c4005000c0c90341311201c413940051030310001a01754074240c4802000f14038012402400b0f55102c00100c1e081c04810820707184035940c0000d64008140d210744406008201c2120204d111b600d4180c59070640c1401070721000306407504074045a01c0c01074040d0620a940c3e016220460810203c0c0c440045120841544c0e84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 955258327 1250 955257077 955257089
    0x10e151b030a02180a12150f0504050c010305100b07080a021204090f050c070f06090206091206041a061315091806050105040b030304141f0804050f010c090e0a060906 73
    0x613115801c42221030040d14a1040070344c01200d031150700340f02c84800c41d000d00c01c925500000c800d401521200c00200030b008030b1070301c1504041c24030341800108040810203944039402039038200041d41d612188100f6104007846600d0520400b04043c034040342001d4000d21203540300b40111501c042d405071440350180d002d030744007000c3e455840040b240010070074001d10350801c03400340300f00c0d0400f501ca4494901d03108007001c0c01031599a1b030312a2441151506010360340f5000d40100b0300289440560301443d22001c08a400311380d15002101041d0071840400006070090700068500300d4030042c070081e02c3d002410301110300c14046080700000280e4544a010b000e0f203003444070400c0039800d00075250940680310107800c1240714500344076140031640c44c0001514101c955401c06a03c030310380348030080750710490f041050034121304441c50050602500541d146014030b115200311a0940d444800700307822101210500400564240d100300000c25201d4956a000b54a841c0005010703695411488e0445010764440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 955259577 1250 955258327 955258331
    0x103080406082503090c05060a120f06060804120c0b2e0b160314030109020405010909020309490207120506041b090903030504060e010e151b030a 64
    0x521419a10814054000a8856002d0700404120a4a0001d001c80f1200901010b664010b0301050000000c0c418006020141805554880300c18008060094603d80d001100741414100d4803e54454410441110001c0c1e446100d65155a900d5a078140d213021080005c010f42c11441c00089449440002d000324000c00c82c42c44090030f4440203c840e00300d1034141286000142108001e0300403031104690128500c0c4400c624146041e01e0180ca5603000a490302050110110011a440301c181d402082901c0d02629440341c0c0a40d92a2010140d01c03080341d14403100c4d000409284040086207404103440110308c84080720014500e501c66091160b5415080c0c0c070252100c0319000c4064042c066003010300720001c848000100350f03454090365201702038001044100c8400c4240c020a0b0781c64506405450214004d1001c04000d00b0014003070701d01580e05503a024900070301d01a9005c014810400700d020640f01610700032041009a501840c0b0050101d9101c2e0103190b1a51106a00d180080d449134400801c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 955260827 1250 955259577 955259579
    0x61b0714130b0901030b07050c0601080c031213030f0c050402030901050f0114090f1b04080f1920280311030a0305030c0a0504051807110105060f1903020901030804 72
    0x801c0701e80000d0045005025151801c880c1c0039440d080041815a5004081800d0903103d1140455051288410302c0285000710000824907113404114040442411801c5401442c3c0540304030305580300d010444540281c01a01c200002810b8044040b407680c02003e441c81c080c0c0d983c1c0b0100c4d003641d0048480505a96540c410061240c0d0210642c27405000c800ca410721001402c0030105402c51409041030428500d803000281c048000380301aa030350320074400c03210742e1100e80c1c03642c0e80f6039942c201c2c131040c010b00d000e440300c80c2c41410420b403003e4000030f420940940e04100e41080c0c00b1a520524440e4a8016250000f0000e1048444003904c02851990034010102c504e50305008030f5443d460b1000b940300e5000b800c81e0501081d445816290803112810301190f49080c162000d80d858400ca03800103800c4005281282c0004021038a150311800f1280c50b000e403032107080c1c2e1400b401c8900442d865580128843c541c0c0500d4100b4100e00051400705120002c0542d8580d0005403284c1000d900464180b180054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 955262077 1250 955260827 955260829
    0x1a07020a0e041202030a14090a0b0403080d0605030a030e0409050a140a060b0414010e15030a120f0f02071208071a0117071215021e0d15050906061b0714 67
    0x10407100c3d40c0d01144040c6017010303101d000040c111a880e000040442c1404906807103565540310b0700300010401e82c403041340e0322952461b00303030900d82000038150407013450324a0000d040e04011440c0308407264542d9900c10008100750030070008203c9618240d807644076450012000074040a00d5161140652000305038629091078840250ba0303c1250f8640a50305000d5506110464803420790f05450100800880c0c540d00c1e142d1104141c1a00c0c0c41e000d5140c41403420303070b40501001d00003500d000c50855403100b40c80b4010315000d440c28560300b0400001a0300010701040804030503032038110600d120b87c000620f0300c1c110b034448038807e841e040c0504215a00d82001000395999000891345465026805401224500b00c2c81c68103040880380080c00c00c50780d29000a200791425230403942034002c4481149040c00310000c241c40700c1d070071400090114a242a6260f5141d440c080310b81c030110f4500810a00311a03591500b4000341d80c014040842d020401700c02070b01c1c1207034024082c94024168182105146c0401c1c64 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 955263327 1250 955262077 955262093
    0xa0b1804110d0f0b091501050c010207120306170618010603051005010e010e0f0103020f01030e0105150102061014190b0d2c03070b06030708070602150714041a07020a0e04 75
    0x303c0303c1240e2074a0084000c14503210740c0342055019086015904000c0200300040e6075a11030341100e040c02e07510004d41d1904200d030541c80c2000d101c2060760308018171615070085c0301c1090041c02c8600b07010b50007070000807101c546071521600c55110510011801e19640c0c2d0304d441c5400c81c1c1401100c4041e444400621400d442d0202071030041541e0031088040341030144c0003260788007040c00301a0144c140c000d00509140d0190b0454808402c5c8240200074911384000045840714410348a20f00500410012610718102480c0d0031054078100409040804850310400858403001c00300c107919244040800100b407134100002d48241700240001213003090401c0082c0c61810f40c2e004101c0c06401c1c0101c00040540e00020541e608640d02c500c00000700e446030000640303000780540c00140c0620404001003445039000c510400781200d8800c0c118110b840300712007a80c000340080704010107160180000c020070307120040b04940181c50803102d82d2800c241074001c070344503002d542c03c004110170f03600d414041045800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 955264577 1250 955263327 955263341
    0x40b1b070321020a0507060b011407080703080601031512150507090e0a3e0c010618060602150a060905010b07051009020105031b04080a050c030d08060a0b1804110d 72
    0x900302149800d100020180c4107000b50704007c1c101c59520483d003149a4015203102e8003c2c0744004800e9116206880e00c0317010355001000031000510020003043e0954041d02a031401e0700f82c9100004e54540c101440031780c03102c008060580304002000c107440904192440b40500902e115900c04220504000440108041c00342415519510301805644182e4144801031400c480d0281c980410040180c01802d03280f401f004d14141901e400540308903000d0055002008450803450b840b075400c51580c1c0303a0300c100c2c3e1551203183d000d42c00c44910034150380e20550940d07030310070580750b400116582c0b5010000d0440f02c2c240c0240038001400107408040c00402c01c0000905660740360180500032160780000c040740405403044c104803030550104810080c098007640c014007030b2241150007141c0907090241d55003201d004880d01030f020b81005601e020340b0480d8210b109100240c604d04440d850700010080580c40704140f40d10003003035030540031403a41c6c1d503001c0e803001e0340c142140564031b584115008030121144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 955265827 1250 955264577 955264637
    0x3032007052e0c1107050901050a06110f030307023901050d0e030f03060114040e010e04020109170f070b0c0c040e0705090709080c0d0308040b1b0703 66
    0x510110000580c0000c400c90540042068560280402d00c2c0c1240300c0c5441898030000c0314180901c00e400190720200c1409103240501c100c6103000c1d5610184408504207015413900134040d04028408036025000005544c0e91003405c641c509058220300c1d031b0860304241c50410040c1c1243ca08400c1207400359004607004246500071380905410215840c01101025402074144840829842240441c1d03034054a5480c1d8010162952a00000c603030803c0c2e6441120424046100310043d072200442a000780d9041c2c1d00f00002c082c040784d003018118140b40100030001c07410004641310109110741507425a841c60302c0c4400060000200340e598007400c1c40d0560b001045a04405d04c202015010005901c01c0100c005079800180c60b8480406941821450f400150308142c45100b40689158460000021104080190364642401720b003004000b110041028002820400110300440c2007603281e26004507c2e510760180070070140841c1301d095041008107802040300f041801a000e04800002405021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 955267077 1250 955265827 955265891
    0x7021f0306050117130809060c0c0a09020c10050a060302040e0d0806010219081303081c1506051b07031416091803140d0203130201030b010314150105160303 69
    0x580f641034071911441c0101500c5400c01c00013480d45c03c0c00404000c0700d031031042c05401e6a5480c00d041210550302c0300c0c500c0443d4014100550000343c040824070a980440b511800600075560440507044050400a040180c10b603179201c46c0040180d403075100b400c11043d21440501a008040c680c0500710381d00c010484d0741550044079480c840040503040718840d1a90040f841d0783c640f441310f8144580c5082c1030700b00416400b0b0004460103800e1003071211349905030b407a5100340b001e200c0080300d099503e82e140c400c110110f82d0a205c3c0300c14100c904c09040005050031812621016504c0c1c981d16038084441d4141005500520304000000100090000140800820512501d118203c568052001e0410040c3c10010300c001c0c4505d03000180303800c1b200d500284400079902c1b41000c1c04800740920000b001280400e2030110003500079406070188508a00111442544e41d42c0c2d00801c40b110030f140314006134100101017121856000b05003480300711136030003580e00007411a40450805800240c1810b9204010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 955268327 1250 955267077 955267097
    0xf0f11100504030e0d110d290105030601060507240e060420031f05061f05190e09060f031f061e231c06090b0c0c0307020f0607021f03060501 62
    0x1828140c42201c006c0c0e0180c0381c1c9845103250b802d10700109040b183d40d80454140c0c15040594010386001140c1c181c96003201551880d0741c0e5104d0a0b80e551250031001010a0043c1031610706810340340307135242c2c10804195000314454120300401802d1602c00c40e01103a071a00ea407945401104100c066103c0c1c0600150000c0c034240174010318070844052012240050182c50f00c0002e986034507202584c2c0700b50000e4040780c460080000b000078220b80c02032910303111032812084030200118880c10200b040c982d0058404003d9840d00000d001c02c510300e81060343d4140c031031909401410402c995003050030040190b00021602d06003200c40418425140ca0414802c0300e40c00140051040c001c2810340c1030301c0780d0088900e6030000102103000855001100d035050342c0c4607507941d802d02003a600308045481c0700d80d004006656a852200e0440e00034071840070f42c00d510034003031b032801820a42c0d40000d003400000c203102d04007101c2d58002030205030f002a02164620a078940d0506082e010f0260102070103090078032031054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 955269577 1250 955268327 955268333
    0xa0c021c0c0602090409020d0c0306110306090708181917040b0d09170c0f06090609070e09030f030705120a0501240908100b01020c09070f0f11100504030e0d 69
    0x84020000701a0a855000807051a01c2c3d64640c06500010b6003e80800b881ea1041c1c10014141c02c200d10081e2075050404100384001c9030b441d0200c0b0f1140c2d0f4000c01c004620349504408540c850360060419180e900d10720441b092030141001070354601e904072030580c150301c6924602405d41c0d25141c0e10184404a0a01c0309000303100a6005848800c40ca0340c60010301c03401c5a0911105446014170000c00304080061540d080b610086014cd00784484c080071208a5221841c01b00d03a01c0000f16081c0c00d1940007030710140101890f88150750b42100110302140e0501c1003529005d056648262182404030300700041e01c141e40115030102c1644040c800f1020025585064840031526080c042c141444c09800303c02000c07007900909041c2e01903c401c10850384001d03d0b201420300200b02c1d010902c0c0c050300c01e50705112410301d0071081c400d00c14200350b92584201520f0f610155010018a081e000c18403804540040c1440e10801c10b18a80301c107010b00c04107a41c04c190030301502c9080c2c1040514051860703101441c3c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 955270827 1250 955269577 955269587
    0x3220806040809150d0510090e07180c0201060f0b2d0f070f0c0308090f0927120c07030303050a0b0a050906060702040213032a05040b060903060a0c021c 67
    0x1010205139a841d00000080001400030310031554403201c071500d17000921030441c455400340d1042d12040a802c214a8a10700c1c41999101160b00ca4403250710142669518960301c80d8000c43c202f03900900010075a9626880c0c1c00b00c0f11070b01500078090b580d4020032140742502003140c0c504003051841600000c3c210040014506500c14080c04503a03400c03000403003008102c1003000c81d4000c42e07003041c11106240d8480c0744c080305035449480c4582c455010302c0c1303202c0c100d1701d810000c01d802440001c050391070f507607180d007a51811041103070036a44aa01401100820000200c8001d1003031181c0039010300501804c615000c4e0072110050141d0300402d140450002142c0c0310b204545040d41e50448800141c0c0e42d0705000521288030341c140081d002800458124400e456003200142178a10510301c40d17000010001c642d5082c440e201059981010011380100070307501345548805040d0780301400242c904101d80c0082460800c0070759600054a03a50700110020507414400c43c2d00c404480c0195008800c2e5031100181 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955272077 1250 955270827 955270837
    0x504030f080405151e0f010503011d03040527071106130206030609090708011109030d08130b090a020d050c19080d0e04020904060623030c0a0503041103032208060408 73
    0x40d00c04c0b1a40209031110412089030030811002014080c00e46080b2100700306000081c41064000d600700103240e0b50406c40750709440092024140154146441d04041001588007282d0100b0212090705a002c80307880c40600071031003800f841d101d0900144640c200c05243c10300080601e14103101e041108001680c80d170040340c1d00601c04480f0001c050b00e034101000e00702045640f10307826540c0f034038000d6008021000301804e0000002c41c1038641c000d00c0401c090f220070108032808080d03411903202c03000c0000d40304900507400007a402c0407120405041c2e030114940c50520380059410340d1091100e0902407a0188031111400032010058200501d4a40c40d16659001c2070300303542c00d01c0b441041c03c00700c0e41c450b0b0f41a070343c200500510038000f5a55400703004c3c112640d545c90020401c03401c0041d100c05c041c032542c200d900070f02c3c0400e4014031745a00803200301d90701c0d00054401c683d03003014142c9070780302940e0420140601c24040e040343c4c0340c04126114030810420103a805081590045420000410558800d0f59 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 955273327 1250 955272077 955272103
    0x90f120816230706021209060f0a05190306090f0e0d0c02030f0a0308011503020a171e01080606041a13090302030f040312080c16030f03020405060c010504030f080405 73
    0x100d40c24030701403424505a02c0440c90b9032545600502c007044001464008a850b180c095070010741207592520014480d0400098020200300300c040c1c070040c02c281c01041c040380b5503e003581c105540c102541e80100490b400c2400002d072960420b1020920600c1144441d200000b0100008009080324585400c0080010400d00c440c0c0c64440d800d40d201800b0445000c00c240c0d007070b03420000e11441d000d41540004e01640400b4203090081031031a40c0a4804c4405114164958407281080c0d01402941041c009156051225081c1c4c0c800a41004170003859020b00343d5074018051902e44242407000b1200711154440b00e141000050b5407050300d0740300002149003803600c0085400c2002c0d00b426440d41c0700d0000690040c000001300001888500c100b4009601c000c1d5a41100c1915164aa0400741c01411882c92510140134614000a409850155503030503c9042c090708040c0e481000840a0300214000841a51110100810168041c1090100c1c001c14240043c46007030586915940e0700442900c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 955274577 1250 955273327 955273357
    0x6020c032e050c121006051c020c01022803060f0905220309060807090b1209010e07090501091508060103120210020c0f070e090c1915090f1208 63
    0x2640c0e035100504904038071101e00071041c4031909004a00845a40c004010000380c5070550020a0f5400000c40c1c07410129442e071381d10503092910401050b90f006800745490b04072180e01b0805c80c08980380c00c3c00680001600300725000c3c0b40d1110000303801000303c144c9003c0c1d405c052a1000c14800c43d02240100000c0c0d9200d48400606c07030762984240312501589500c1035903c001d44204a40406a01070400c0e425200c50380da41c5922601c4100c0c05a4002c1082d001d00004920300344203e01c48050b41c4101c0d1a0310641c1d910005c1410443d40b00580c0c00d14070203401420384240c4070001448050000c1c0500610b44004501f46041c0c14900b00f01d070380e1502c4040c00001c0082c200121324440c014800c21a00c0080385002ca801c55481c04002c03000750b40ca403d06c0281c1c400c0da00807450000f0f5249202c90386d6510480c2d400001e0410107520300d0401c240c1e0020b000c044841c80c40c0312000440c008034608141449001981ca4004140d424548040702c2c3d022182d01c0340807850304030030540d00003a0300301054603000001c007140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 955275827 1250 955274577 955274623
    0xf05090604091404050c06070b0601050a18151e0e1203040329060f01080106110a050102040801150801060326070f11041416081b0307031506020c03 65
    0xd00305114640c030500d80181010015401541081483c50041e4841c404982d8109220301c00c0c0800e500442e0700190521101c503000410650262008015034080303454509640360801c0b103d50301c2981d03560081019800f40b00707402d9100d00c1d0003411104011620103103091043c01480e00c001c004c0f003103000c042402a00011f290203400c60013041998041c5900596104014984801e55901d201e80fa00014442190820120b079050420622124003140c0680d40c2002e40c4c1c0c01d05200342c1c1c21307585400f00001180b042080c1000443c00a20117000a40340c444008101040c00d03500b1044c00c403c41350070040590b4505482000016005e0281c004028001141803c3c0c4401e0210450b502c3d0150703031009468000c00b407807001c1c01c01080441d0988e20440c201c0d400c01c00303102d81414403c1c1e013450484039600980c441000c00a0200d0240440342d500c603030b41100410000c01040f0f503850003a0800d03103000d0046912140d1208a03600002d24540c0548564401000021940c2002236500c0c01104c000c80003898000e44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 955277077 1250 955275827 955275829
    0x509040609030516080d11120604150e1302010305070f08041101090b0c060406050c0c1009020609030a0b0601120c0e041a060705031222060203090c0a140103050c09010f0509 76
    0xf61011844200407a035100c55280c28006615404000d000320786e140f03441c07810b60084111000382d51b10003003209209540365441e40184001000c48044001101c01d034880002070160f081400d41d032082040540703000e1004064030024090301c50240c030074018055200030b9402000d600256081e0310541043c0b440ba4804811001650110200d4004002c22600000c04003501e00c1e002641900541c480c1004110550b2050310a00260050801c00901c0350481c1202d00030070002500a540510b000030412458203080100191a100062404943c041607400806c081503821049407101d0030640c040500014143c04d81c01011510410840c1d031103240d03120380783d120792480841c12145540001e00455520400e0b400e0455a0b900500100c01e40041c075800050100c051800c0b40c01c0109801da0b890300b0880800d9a248400303500010a200d11a110306101d0041c5540c4a40300d48000748107020072014005a07a900060584000038850010584e040104c0419640d0202d21424581c28074a04182c036801c0ca00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 955278327 1250 955277077 955277087
    0x60c0703091205031c06050102070509090705041d0d0224040f0602031911040510080c0702030a0b09010c111b0409140c272e060203031807050904060903 67
    0x34110b100248406100501048400001031048000f140b04281000740030406103020b66005000343c500680009800b00302600b03203503120682210204003642d41d40c64456010404a903200ca81404004090070f98a260200741888041c003500801c1c400b5040c080c07402c400f4142e0920340c1e400c2c0c0e451800c4a5100040c10b1000d841020340350303d40c1c000c0095581c1e0402006400c0008124880c1003c4540303440308005604c030b00c1c20b08a5003243c00c0903103d0150b0481d01c0c00e00769010b08000344010644d0800304843c0c0010703078052102c80c00d0103106400131501400d00c2d6050500b15158513505000f40703382490258005540000c202a000300021021001040102d0118014001004000f49210031803000144044800319058039440c006644445225801520b480c0d42d020307201082003492007030704001c55561856080c248105040c3c030400e500030612035400c10300c00d41011358005001a04044244000e01407a646001d0b003001004004103440c41c20200010210680600014140c5039142a044101400b074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 955279577 1250 955278327 955278329
    0x20070f020f0d120e0a050904150209032e0b120a02150c0a051c050a0509011b0b042607111306031b0e0f0c0a112e0b0111060c070309 58
    0xc3c4031501d014084210140100310074520643c4500280000818141001040346100f55041404150850a9410702c00f00a42c820074945406006034109003400c0d061203d2144c0c2c081e4840390124005c021100c52107812076032031840c150b10032031440b00842041c0d500050f0041141e6011180303080c60322245051400701d4400e947d8403103980d0203554480e41c14028080781000c42403044c0c03440000081c03150042118103100b081101030224005000000c41c55104403051841f80140f042c201412a03500d486152418404450840720481c664505040300c0390030032000d58020704180001810700001c0d9440e50580ba001d0300403203005480340b44010310221903903004580150341190a00c60b0341402044214210b052a0048070494040e900c0494081094401560302c9040151106030034821000c408444060001909081c2841402c1c1440b0985408802c07c42518202900785695112400985000e030340c400400300341032240800d6502c405400100baa1035120580102c2035560308090300e0140e60040403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 955280827 1250 955279577 955279583
    0x3053909041d0c0105250201020c04050a0c0207050f0a0317040f0f0e09210901180620030f0f0d020c1009020913020a060c1e030320070f020f0d 63
    0x400a0600035141d504204900103401101610b28407000100103580d0b82c07060a100d5102c0341c510300c10f40001c0e010403041c60b22506c2c1c1b05105554102480000003400e03207609980000c04180c2d0b07860000044c0303804010f02c8008040642e0403051340c0010000040d5071752903901c005844000d00d40b00a01c05c2c00d070b610003110041c02103640c0c204010390b16014151600100c6025144001011402007185081d00052800715421404001c501d5401401c55a580680080c030340c0038140041031101800d0410100d000f00054540d550f24440124010440d00084240720b28040003107401c02c011840c0c0381c0c03000d102210900b150140c00b040c2d8030300c80028810006c1c0f04410b4040801d00030810300c00c001c04400d1b00f0201c402070003110040c5054441aa540c40c0110788010025440124264108180c40c001c1303441e81c1842c0d000d001d42c1c040d04240901c0b000d66464000c03008400195030307004243da0144203007060194540c2000e920754201311581d51005540380c0b00e404064895141001030161581e0340c064100f0b510f5034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 955282077 1250 955280827 955280831
    0x5031804020706141b030c0306040915090b092406300a0c090e06190603050604050f01060f1415041d01090f0917030a09051c0305390904 60
    0x10304d0052100d1001d40544040c0c20440e20380c900541e0401c1e41d00180c0303020f6031100c420645961035401c200401450912421239184810130703811414030034248a0311102034080d4448150600c0c140000d2824452540104064441c45240c0d224101543c82c101030b51010068400c0306140c207090001e401540000b011980b40b000c030800300103041060100f00314a205116420644000d91150340b00b805980001c0005855030744580c3c00a103502c406556441480b031800403000420980300d88586081060031a81910326500400750194108401d200d90401848055203000e01142403104c4220b038600b10944161168950004018803518407404036030090504061548c3e10000004d080d05541900344106000b10345001a04a0031010034025400c01c9640109244c0c010040c00c28200b035030b80c0001e0100d207205a9100809400107070f040191940039000b0040e039042c01c0c0100b080c001e0a03036500401210300c503280e078000408030602c03a55200c4e51640a42013101c0c041240b4000018071409082c0c011a4000c4c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 955283327 1250 955282077 955282091
    0x103080a021e061b0f070804140910030f05010219030b10030203011203031a040e06160e06161109010b04051c030c021207030b15190305031804020706 66
    0x48840020880c1000c40d03029280d03030038181c1c070b40400345001400781280981c0000e0001000c200ca59081d50404040d0080310078103060b000e0314504003980001c0d20455840b41c00160512010440c011500e84041c01150290600e02d0a40c41c04582e04045200c01003101e02c01c0742092040140a4060702d18251404117080e1420410a40080141405c1303411580540300408003029114400d0007120305030741c0c0c9044034000900030b60b503084004280d149841d9400002e070514050456882d03020b01c0c5104c402500c0144140d041c405a80040b8070101202d50007401000790000c40a61078503026039030100d1300b218440c16451030a0a201a000c02c103146500c1d44026540c00105406c0d21000162041e5641a03403003850042c06042e202010001e05880035000c0785080040000504c2c05500007842030000000750f4014990300e41d5200010101660a03104d020340d145c034941e046062900040c030190f145c0c1200302e010f076407071a103a1980724810002c80781520603400380080201c0e1650740403600100c0d840701c3c08102c1d030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 955284577 1250 955283327 955283333
    0xa0605031c2601050f120c06090a08030c01061a090a12020d052b09050303071704030b1003110102210c0a05060109050a05060904080406050901121d0c0301020a0210091a0103 76
    0x400c1c09004292240241d403000e05003608104003840342540c440001018041c7d80402000503a400020f00150701c240d41d1640030030581c1060010348403411a200010403020b0400148481c150300f01a031a07400300105206c001d1450743c9064007001242c0a000b411080e580f21400450312030781c05404043c01521038085001700904020014604a8101d01c00d14007440d2112001102c40040a100fa030380d056009105100100b100140300600700c035a00e0740d809107000c2d82e136a203803420150700715606600c03007080034020420f000d0414868401120244050034000860040301000301c0c01c0311103240c09803113001c6505003200c0020000803100c950041c041310a9983d40f01120b81c05070000310b0314000300c1424900440c0580c01c10300b1140d0f015541c042851410242004802c0310a82c10002c0700b40c0c1000f042c600d4a100010b41032207441040001503024a4108528044c05440c0903025001c003070080e807040000c4071003c2d50100d5014210b020429011440c1c6a0604150712101c3e80c040128034901e207050000010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 955285827 1250 955284577 955284647
    0x1020c070828020f030304030507090603050d03020a050a08100b0d020310091b050d0f0c0509090601021b0607060f0c270e0106120f0c0504050301050a0605031c 70
    0x2107400480c111445005280218440412601601c101d1801c01656240041c944000201c949000c0a0200c82c00c00707a03603480d0b031490486d0560003070300e032256600c0c000d1003801018811f0460006503810705610b003401a45009080e4401c02c0c0c0d5440030000b0020201d80c001e0346860303612005042c04400d131501c030075803c402c28000707500640700c80d01c580405e5803002440c2d41ca01d000c1e5000028482d491400011001041a203243c0e00c1850a449403583e585180c1f0100c1e40b640c400c4040c1404c0682d40e164031500d58009015034180085e0410341554003000c011400c240104480910142003694041d443c2c0e501407070403d0140c984103203100080303410072004101390f6601c120f0b452400c940c010340c0005040940b012200320b80080f4007507000c0c0224000018040a801003001d181003400b400f000080070000550350004848901114400080c0c0c00141044549801d000703203500144118020041c1c00c2c50400000d560714000c01d004440f00605444e80c420050086041e51480c8481c1d00b10107203405154200c0f540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 955287077 1250 955285827 955285829
    0x50a0f05160305090d05091003060e070504030302010507080105220f0203010b03191b0302070201020c1504060f080907060c081309050a0e1c081504020408100e0d17060d0501020c07 79
    0x20000c1d190400113881c0c0000005d030441803080988540f40780819031028403071902c52040c0c0076000e0540319040010110608405a845420180c0d1103d44031815890004d0a41e000900b000082100400040c086680d443c400102c1030316010000c0c0c0f040c518100b0170302015146003030010b5880d80c4040000541e55941c48020762046065400208000040da1034403800c482e81d00d0080b42c4046050f00c2d00a480600a50041110320300500484080d00e0150000490b81e0b864008104407201021500b04421904902628041d20060801e00c1017032400308001036441d5114801c440800001440d4841444010011503401c25100c002c1d012085440302c201802409007918100b040354641404e00c400c004012500b950020540e540641d240d070303030300f840c2200c0d0044040d0408070720054208803082c25503902e04c010310041001c600600007604030301c5210411501001c00d81413068110b030b0604400142c2c080b802c607100791600b0314107988940341c2c40c010405250210b28004c040703600c002050a80450300040d940 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 955288327 1250 955287077 955287121
    0xa02070f0e0a18080d0513052506020a031418030321013804051206150303130608090705040911030618120f130f06171009050a0f05 58
    0xc44080c004490700c450071078056502070b1071184207001d10744643c8046d4020a4110068902c16000760314207481e628100b0000304e045072900d91182c042d414058078640c034040020700d1503001a019010310f40d100502001c0880b02e004160131000606007270b00f00001300040c44042d00140c100c1e51030b4040c0c2c42e11201b40303056220b4071103010345166000154000c4280740e0a816004404018480d20b191003003641001845822480b4480005000105280d19025580224000c004c4002d1200d41043c20100d1689100c12080034080d070000c200366824402040c2030101110b10610704406c1603525140070504103005900034560240c28412440140004070240b1070340e40c4c20403000d49000d916414030410904d003440302202d00503040380d00702081d0100703a08050021401700b0081546030882150b507503a10a125600540180c880701d08052000c2ca030300c80c9202d441d00014800800d038604001c804400002c0851041c0f14801c0c0e02c80002920070315098021300240d10302d40303806004504101d0002801c40554138100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 955289577 1250 955288327 955288331
    0xc16020d0c0e042f0609040e1b0901050f030319020708030f0d0f0c0e10090b0705061e0609060913150c030b01020c130b240a030b0d0b010b0a02070f0e0a 67
    0xa80e8016103180750062020403004041c4d000054440e0a1205030b401c460903d070703400769407070182d020080006d0002400e00310070241c500c1d1494145d001081003150303060b00102c1c0200c0c3c0003130f07000006807400801c076010540e804178440341e444100c40e4102e00d0003545800403101d500011841e6100641c008019040280945c0c00c240b1095861400c054215260000e0140010724582c080320681e00301030411611a140900d4100c10b82a15454600d0450380084011201e80e8028030812140c0070b03c040340041e031005c12a80214003420110f0008440d842e0141189100d040200c000c40c0380b000740846000c0b05194080b842000d80002800500c005010a44a0001080c02c214400c80298400f081d881441e8100034007107040f44203116420801401c000000b503800100c02103125607454400100034201304c080c906001c4c0d07500340030325004044d104406a8540248c5a0565080010300302c0c00d50941510600c00403c1d44406042804a2a2008a074084020401d070004c0101c0d454501292061180c0c90314101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 955290827 1250 955289577 955289603
    0x20906090609040b070203041e060216030f02040c171006031b021b150c16120f02010e03030f120412230f04170d1103030c16020d0c0e04 60
    0xd10014890440c1c907030707900c80785807000074002448000d401900005944104e0342032070f0701e0342e040b80c0e006101c1c2240c664414501c1c440403c445941044a600504010002c50b049c0034070315924111038000d165002880b40c3d80301c500e00c1564500c00c1032110b45c07840011419680900300011780c2244000c441c010000000c1c20051072450702c0d0001030450140c0f641c254001c200c05908440419035203409444510b52200c01102008100d002003c060120b0800d10005050300ba6051051039002c0c20f4554030501032400d8100250011a10101450840c56020b09180640000400000307040d84501c0c003441420f0040442e013107443c041c011000354070587c1f00c1d01a01c28a50500a03041e02c000c288a001c0c0d4a6207184202644843d2060001401c00840000f0806080545131049000d140c07031a5401c00070568040d050604070a80c0c0501c90001d045d0680028501c0c50801c2c0340d031400703280300f401c20701c0401c074244802010840d280d0901c600070443d080362001300d03010f0b10740c0c240c00300200b0296016100c6607541c0035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 955292077 1250 955290827 955290829
    0x5040510020903030d0e01090c0e010e010f0303120e0a15090b060d080910020a0507060503150f0603011a070206070309230f010f0215010620150708130c080a020906 72
    0x70803507100050080056080544410340980a880040050b0300155241c00d42c03c000521603000d03a0003c0c12200c0c3c0400125810f021950540b600140d101e0518a80d5030141000429040f031910700700401840c6000c28150550001c01b4501040312a0081a4040d10388140c0401c00303d0391312070040d46104450203802d64640c01c040103100140c04030050658031301040594601d00e0720400140180507140165900303054583c444604040c5254004404a40000108581603940309002c09083c00b08403101c0b0010112000410502c2c04140111952109101e04a4105450040940d0207050303000b000070350345e10060303e401031400009100d203000c01800b401d030003a091403461034215400540a4a01c03100c41c02c10100440e4020300000c2c8800a5018910300405580f040e28401e07806081e05031200c5103103012150b40e808441084080c41d460300e4000c400c101d004040d00c104059082101450318900a07210014541c1c0450303103c04000b0900a0850700c00101000c010504051442c001c886400b041d81d203483c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 955293327 1250 955292077 955292081
    0x80c04090206030a051009021207030c0219080310030c0803190c0b0f0402011b0c030c0f0e0f090c03030304060c0909060b030412020c030f0c031e120904020708070605040510 76
    0x103200207500c244144005034001c4e01c2e584c04180e010f4026900217502594802800040342e00420182403005c08030760410108035054021610b4000701e44c070080c040840488207060b99002545d0004003096000000320349030301d80a072640304c00340d03410030394104240e03036102051540da034000e200e65030000480d14402401c15014002800c2c0e413035080038000316950740d032a2420f0700020300184224113200d4403040103424150008416903038648180b1200c20264294145104948403a83c00b42604080400c818070140a401040710341200c244668801d1686800780400d0400c0621074200e905072001104000600240f03400c550701e00f9084d0344030072202546482c2c284050301d05500510f142094100041400203c42088982c1100041d1050b1030b9040000000242000c0303d5046014040c3d12401c1041c906140c140300c41088816140b0640007027030745024100361038a240c0c0040c050500d074081040c416035156601110401503002d8601d0365a0149440c3c10b20050105075803d480d42d1040c01071204141040d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 955294577 1250 955293327 955293341
    0xc13060e07110a0803040203030f040324020a0207060e060c03071a01060c080f0a0e10030e0118030e010c030507060c05030405191709040e01020711181003122106080c04 74
    0x10300081c020600c0070b9216402e0a0b8401b400480e0944020086202c42e074800b079010b000918800c031102c15004000d21445018090f82d010320404180c81044401b05081c0c0000340101161504d080442d0199584400200140641c1c4584030160000050160800c80e110358a0541e6505020007090543d0729440111502d111500740280f00590800c1003070303000591a800390600f8841440c04205280104010641071780f00380d4003280102c1d40711a280c403c082e03000e000c3c6188bc60340c030100f42e203804811030b14010482c80c010700e40c003070500c80142544d2040c10f114400f00c0309015004a4140412741c2506002041d9910890b400d403601e0040310b104042c102c0d40c05200d0200940c118880c0c0d4200380c1021281c5819a10168040350b0040c0e41d9285030404282c280041c18109002d0350000b510700e030020041c0581580b80084403490805500c04200d001803e1a907580241d9400c0500d00e400c4282c9648181d0b010034401c10300b03015030504ac80d1030b80e00311103e60304241c05840d420000d41c0c0030118184e060100b5100c00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 955295827 1250 955294577 955294607
    0x908030a020318130912021209131d03030106021e03070308070e0604080604200603040f060f0e151801020c03040312020a0f0602030105041103010518090c13060e07 72
    0x104290501c01e441c2c00403c0c81804001001a4404500d600d5400211403440b20111071080404200343e60064050000036843c000c0c400c02e151816180c013000400c80c00d10f4400f0000125a20fa0004800d0401ca400180343c09041000f203955958651201942e00c1441488041c4040003d6295650f40c403004010348034041c0d4142c1b600034994480300000e85e804e2081c030728080d4000d0420710001030744032820002d0501460003002004128a06000444041180d140081d4000c0d001041880001900341d01031082c4d668208000081500141108001511040702c540c43c40b07120b43d42031240e00a071801c801c1030048415440d504c1500c040742c1c5c0000d09034001e005091020341c00a000400129000710092400003801e4415544480800d80d2200103039403c0720340954165902000510080c2054400c0c0c0b40450214000e05095601d09000510a807003010031140b06074450301c001c240b2940c0c0401c44e891155000424104415a40c0c4540030010402c07072294032803055025000c1075450b030241c09501203500fa = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 955297077 1250 955295827 955295833
    0x306260712151e110d0b0409030909021c090809040b272a1c09080702041505030304080c031c02070320100905120c0609131d01020a0908030a02 63
    0x1a103240c42c1006082102c0441100e0700c0070503001d000d240e650f04c00d01016605483c01151110b065104410484006821545c05a440c04811101294210300404102c604082c00541c2d40c550545084011010b50040440d043d41040e0b401410401c1c83c20281056080c156400c00103100e04800b00103407100c0c084030300441c00f40e84400090400d03881011803a8482e8034800f0040d5041c030002c0000d041d000d50000c000c0c0501d0b4001c00c0341400b025881c444140c00114299092010b2102615410414402c0c03020092190741d4481d1072456080a6220200050a00400352600c0303580e1082416240e01d8403040c213030301ca40203c444c5c0c60340366a401c0d607031102440125401056504d007181d503051a445154151100809002c80b040005075884141070700010240e5030300c1d002c0301403401042c800d822207100031424094100107200301094666400342c0d164a00105d65080700b80e1f1980442c0c40050118103c2c11000c2031104080740c004d204150020018416255030312030b026079456907440c5d241d001d00041c2e82c1c01a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 955298327 1250 955297077 955297103
    0x1605012f0a020a020a08010b12030f0d0506040e0709060515030408030703020a020a061e0e0303250302040503030d090507050a18050604141f0b040605190306260712 72
    0x6481401401d5210703034600443d07030003c0c099000140b81a01070b5000105d0f40c2c1d1030b01c1030800e031402c2001c03207010107418040003107003048803c400054050080350900c044c80303a582c90000d60f9680c1d80d074101d0300d000c943c48000c0e0f40403d62540c2d2a140500b405000701402002c4070700c03180050142c1c0e0700849100310741051642c0e0a5841d400000c401070b6110400c0c8804601c0b49070455008a0494441c0100c2c0c10040c100c4500300903c0c0d0031040c425a140d059480c902c0c0d40052042025500c070510f0f2008004180f800c0000c4c0030741a80e00f098000303005940080d5003521021803405404085507000001c0710b8041d80440d40029621710401a1f06a25805901d20050b64001090404030740c81e048150800700c014004a0f010940c1d50810728141c504507441d07440c078091006e10240a4203800d0703c42d000761000598051800781010000f402c10b00c02c3e011a105c1c080a5420841d007068482c1d444a0082e101010010203a140000d008104406d400c00c3e50384181c1c0a940800a003060001070705c903000701c0e806030300070b1010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 955299577 1250 955298327 955298411
    0x21140a0c080304030e06160b060603131506090c050414150d090503070b13020f0f01020c01141204050a1406010302090c09010c02120106081b010512091002160501 71
    0x5074001a008409108010880c48202c1d1b07150809086201d001c01c465900c21380050038101002c00c80640b44a001d04070070003d000001e0002c09003025038035008a054035207000381c2c640580c020030040e070060116a151007000d46500340d01000410846070202d4910040300e00841c2001448217500740014249002006210720b092115000141264061b1082e6402d00440f40c80f008001501150307140200568070704001d0851600141c0c1d480c0b060415982d08200942c6800041d503141505a134042c18041a0710442c07094101c65822aa980c04d41000c150701c02c1d00b800c1c904903640d84012481100c44c0d000d4031180140c0c4000005106040b250010210201504d49080d10089540301100142c10420121620740250304da40c0100a4031100b071744000181946000340c0319041411104010b4510070702c10700c5002c4282e0340417095a85102146850b85000e4903030340f1100340b810302400308400015001248002007445d0300070301e109240340150000d0042c0c40c104541010301d030500300d00c203400781c00f0000309103510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 955300827 1250 955299577 955299593
    0xc030c031606180506040b1209070609090b03030c0703050d0818060c070515010b0d06080a0b0c0a180f03120e24091c020f060c06130c0321140a0c 64
    0x251420280c03400c05985840105c3c20301e07170143e00700300181c0500255000c6070214400825500103034610182003010300f01000101080c0d2503104e5403a00030b4032112900e2555606004940714824214111071141e980c80c030304292200038030318110010510b00c000140d000060b40c60b200302c01c1c820b4072000e00401d41d604070600c40c081c1c000d14000d90703e92041c01988511403445095040c003908c5204c40c510b40300e00c0000348031019a100340d00540100c1d040b03d002e110021300100404d40d0019180c0500380e48441075a04100c1d03099441c03902c4980d5620704401c2c0000c82c021500203210650b401941003640f0412550b1060300c0740c014075500c42d9080307600f40400c1080e4925050720a44143d00540110745407001e2000010904030b0000c0e00980040065695441146041c004981316100c09a44c0c03d81060864000b150301d41000410011a1200e0001c429041001d0348100001865015044203510050080100780c0044480741080210344040c010b400c0141c0f50001b0b0ba069960345907500c4c41d030b0540d00d90310f07000307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 955302077 1250 955300827 955300847
    0xc1110030e03130302130605030304030f0602160609030e0f0607200a0602100b0102150109020c07030807060b01090b03101a16050a1b0e2a0a020c030c031606 69
    0x810981d030340380301c0703015001d05000a0943c440e0050440010f24103500400c519605c43c0c00039050005e142100802031518080f040d42c0c02c80340c00440d80d601c3c0320380e1810808040e20035221500700c42c1e1240d0303640c80c00304105680312040c214025524100032102000074805500740740d6070900d074451001e00c60500001c9032038049040b0744a808564180b9001883d011030240c5010b070700400c0250304212803404440700c1078495005503080034402000310b6071103600c5643c000b800c1070062500c41030300010014080e1000b000070400850f400310f415030b611070440c10010700401d0040314560014034802000500c081c03851301500c1c0505102e00d40e5240c224501404032003400180c5c5860f2501d20403d004052605580420f00500280101c010b801044124603140c80200d4004280c9502c01d603403d1028000c020340d086400354040d4024200981400d06584041c2c9501c0e03503810300c100c8804000464102c80b1b64003144070100c00b41c054040301d000100038030070580c4500c508034600103003080d10340c1d04110892151702240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 955303327 1250 955302077 955302109
    0x60607020d151e0f0515130908040605030a05060301090506161407080a020706090b0d0507020c040e0f071703070204090221010c0e01110d0f050d02040f03120c11 71
    0x164030b403420445800140c0300b541d41d41a00044543c0204600311019000d003035815150100b00300301d02e2910780d030000c2002c040300c000c00d0700900c25003045120b0780026502040d09290000070a64455503515001401940200d1f01c08010714148408203180342814041d600c4030690040c0a015941d540c00c0d22140c03051851032200b4100f208015103800d250312032100404016015506050761685024006450908550303c401c0403c08142410410717402910203840303020704800300102d03280e200d4a0f4200c0c604440c1d081059406032625030320a4800b403000900324020350465041d960a0342d070700c250b15035915440114401c10703038104210b208010b03c0c150380b00c40a014801094032a102214802c48a0041003440141d00144e40d41c0780c0e48850150440aa444a10424a041007000070ba41360b006894542000d00e0100780030b40c0c0818560702c035010320140d5200f4580c0b003504545450792035108440700d0071244030aa4802114081002d216441008003460480c4c00104000c02c035040c0c0410302001d11591101c81c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 955304577 1250 955303327 955303343
    0x10020f0d03051f0e04031e0516080d1515050a05070b040c08060406020c01050f13060b0310090503070b0a02070c27050a1a04060f0e04020301020904051f0e060607020d 73
    0x1041c40c083c02208030b4082c0c41444d00044040c60145000752054030004105d5552104807003880e58525403110032204a040429488031180040d460000d0060164141072400d050a142c0042c0321104130020b03603001c8542c0313404526140031003c042a1107a115240d01d03100010000c010040104aa15a03035503081403090091004e10742d9910141820103905903070844481d90009140603403a0405d000310380e003200c4210a02c0c103080c2460080080d1503005078030300034421134a55240d15070540d0f090007032024405e00c0040601c02200f0a02e002c1d9200e610000044035202c3c940c5010440d40c082c98802e07a01042c0c3d0051056000604220714070040c4009016405940900d100c1c203504518918010030713019005103000401d40c0a103004201c1441032403100090301071460410204103606000d43c0b1780382121103040d645846902c66002103406841800f4103d41c00c54200350a0100c035075030200000d40b0701c0701c0d82c0c03010106490319401d00c207d80d1003003a80c4a1382d0210050010001514181c1d00c5200c240b4811921 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 955305827 1250 955304577 955304611
    0x303110a0c0813030507330e010305040302070e092a0d08030a0f090f060b040c1209080705030304050c0102070b1c1a18091b0a03030e0312030c030610020f0d0305 71
    0xc05d46441c103e40c00205083c80984901e80c090800d44034158400c0d030b500070115034640c1c0007200007858244482d402d9410542c40d07402040901d4001e02c1654003816400d1101c461515040030b485540e400d410b40c1001c5000741e410710200c00c1e060300d843c28010020000f0803043d45142c0d0f0703031035080e001d03023016102040030360b5546403082d0a00c4262040e12600c0b40b168006191500e035a09122080311002c4950a00640c1006940b00074540c0c031441804480c940071a0008000015042c010240d0107627400007052480000280014401c001448480641c0264200c8180035291841154240a82a01e140c0c2107020350b880b1256000941e0000c580364a002c2640405d6000305200041151075002070701e1000c41001014404c1d00142840303100340c54408005500d28507602d61000c580f04e00541d100107000c000b002c00c4a800569000c0c840c0d060940c400c595040e469050015800407a5802610414414980e0401951001d4008501d1008080c45030b0090400007065181c2036018100050282d64070101c8154 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 955307077 1250 955305827 955305833
    0x103050414030309010618090c050913020d0b09210403120309020612040b13020d110409020d0c1d070e010f050f070317060906061c02070606080a0303110a0c081303 72
    0x4040d5204404d10400072800c2440c100408128412400007584040d04242541c40400c1c6105207082c2200c80542d180390036581c90320451220040c094000a601280201c42c00c400c0c81784010390039001c0c0d064403064864090a420000945c6180038081c2403482100b80001c1011418402060743d5032241400c1c0810301300203c0e0b00080881d0f02130904812140d0250051109201d070041032075620001856074210220496000525546201c10707000b803a60402594058003500c0d181c00840105501a024035020034141c5860803114690340a8580d101e000100c0f190240050703e002c00d80904c800f40c64071285030591000440d00111006010014403034100003d0044507200d10041210078000d9946000b05000341030340e020500c1010b00241d2040400d041448010742c2c07200c048402902c800d14481e1001d00001e80481c000c0c1c01282ca01600380c0b85080c40c005001103000c40e5107840c1e2803107a90200480d03208400d010456000ba0300545000902c5000320341c0000308620000c0803c4100c0c1d81415014540c1c980d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 955308327 1250 955307077 955307083
    0x120904060e0708040314210a022b0513150c0908030c0c03251509180203070216150e1504090204080723151201061107081b0103050414 59
    0x794940d00010100810402410340c44000404446c8034001080e140028940d460f00c03810340c00f5039030104841520808a11401a030b079049424190141c8286058040b02c604a10507120100005003405130400002422868044008001d060380c07020642d075074200392050200080c911002c841081c40003164001c50794080400c09030000409100003044413502460071702d414594603000e00d20b2000c80c110b41404e039240102064a05443d4107083c030888840000e101261002269800a400c00b1511400c074400c0e0100d94008610507003103902107030112000a45007100d03220b0f0f6449101d140e00190140820018400e586580380940002c10501059030f000600300d03210f501c40d0380012a9541c0c000340c2002540310601069000b00551550b16900d40308420610003c039144842142c41800c142c2010702c0e104009500352642c642607441000b04a42e11480301134141c00300203e010515126800d0000f9103030600041d941d03183d92024103c144c9809401c0c006402410300540100c1d03401c000e8880b0485044020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 955309577 1250 955308327 955308331
    0xd02070812101403030306030714210a0b01050904020315060d05010212040b010e010f0e0601052205010305060a18050703290406060e01081315021309050903070302120904060e 77
    0x95981602c81c0d2914400c80b002c01400006940203030401d1040040c266008140141110f0300da00da80700441d07000100244071072040f00364064002c06510f0204040000018031a11524440c040c841400d0342c85104000242c9000ca40080d032690007815600140344400c044190400300c0500034800c0300300c1e0f0303036100d9081e80c0041002d5034071a00c10302c0c03c10082c071060400c05801811341c900340162035410001818001803050040009102d0040f0100d071450740314004450302022100c091005450402d41c0022185403244509400030781008041101e510b4101e07200012248103142c490601000d43e554480640302c000e140c1d109042d0743c0c000300400104202c503039800e481c240c40100341d08030140c20300704402c682d020380103a01084500110088541d0700030382659005000d200c211800c908013450705e900030314001903106044600100301c3c40406500119048242d9510003002d01c0280d0302c00c1c0005549015034400640181d0011541c0d200600190b00185501040600046a899142c200724a190102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 955310827 1250 955309577 955309591
    0x912030204121b2c011a0a0c02130204080c100912030c060b04060f061403040c0b0702151c06050603060a030b100f032d03020309060a020c0411070b0702060103080d02070812 76
    0x20b651307501108a02c10388090313003d04000d011400c014070749401c42d491103000d440c11500034442e40030364804c20f550f920643d9200c4d444041c1c10566a880e200d010580d04d490400500030700841012603013860180c05601c024040e101c0c5a80210000709094400f1a02400d1841040c1d5801b651a40000368036129402080007610304503c45e000440d01d072480c0280803a024810302c415034003082c0140300c000703050342051174100e40600c00b005844906500004100d26400501174030002e000040c00c900c3d88240070010f4040c550344000402403a40d40710144186403008585555124840c07070028030000d040d0650507500f094040340d00540c880d0321348614a20079110380d0015540c040c0705185082282e0102c00416910f241c8200c441400c42107a554069038074010b10014a11a01c0c02140040e4140e20070448241c10200040092107080c0107940003040590200d02c051f00e40c0c5103400700181c003080c000261141240e81c000305003071400c44025042002034020401c01c81e081e10382040160b0b0001c41c041d504c640220b107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 955312077 1250 955310827 955310879
    0x23070807081201210b060414010f060f050c210c0105010612060510080a18020a0f030311030a05070609080702270a0e0312150d060912030204121b 64
    0xc07441054042c81005a000e01024a14101c441840e0303103030041c000c40c1640e8003414a110355100c110005014044030705e469103c106241c1c0000034990400d0081000701e482c00d85545408007200c0c0d204031818401d003d0314494940c8503103442004c40032102c24000070561043c0341141007030074000f000c03801e60705c0a0344a840010b19070341c2e50058545c41032042e80014074085483c80c03004031183e60090302a40d4002e10704510290703200000701040c0940d4003180039455000f45281c1c242d41c2c40700400c00c1011250300081e000101e2115485158a100104440c5492201d0319610f003041d40076626840905001c56003110602018810b1070f0042c3c55046106203a02400490404800602854000480c20003890b07490400e00748114215060700c0803080b5003141800c5441c1070404c0d80c40345017181a04c04e40f240c0d825002041e044206061100c1648002e001c0d9214800c0c054034816a480120141d010340d0003110240d008150300071001030f0f469081001400303400c401038000386544081c00c0300c0c140303084004925252 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 955313327 1250 955312077 955312087
    0x12d170403080109051e060f01050408031611060304020109030816120203030702010e010605010906080a060503120307080108070b040618090e010605090a05100b0c2a03060f072307080708 82
    0x61350602499600042a00c002c46c03910341e040001e0f00c0440b4010b020381d409059400540d00169110300100c4002c2c0641074112a550300225a001240108180d01a6030f11042640488520300e811030461340100c0c0c0595801c204503086460380c1a20764091204c0101040100844600003060b40b0f0416000c0e1070070790059903c03840c010314040d09642c58058410f40c1645400d405001d00d0f038100d1004400e031003032460880129030b00c410f4030700000d01240d0000350780b501c15054103090222500b0002d5100c0d52003a40c4610312a40e0713444d0051f9441199005480351880b0034001031126902c0b55a103900d8070058501a6406240c0d03500c01041290202c00c00e9a1a694503035006100c0c60801e0149550800741700d80b000c110074644009002d0a0302d20901a5401a01c40000c2c00300060030100140b4030b0307070460100c180081241c035071001080301000d02551800781c0281b00006040d00c0e4000144c0d4407039000c40c4ca8284c3c0c400d03103002046040c1007130200f410f032940009000703502c0404c0e5588090302c0c90300d07c1464810360360 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 955314577 1250 955313327 955313339
    0x1e150902101e0e01120905030918010b040303050d1514150f0f0a11030307080a050a020a0f0e1203040920040f0e07050403020913020f012d1704030801 66
    0x3203038840110030902100058001402c80c01c510210541446490151220020000101d4005010707658803000700c1e003400d10040922101100914a943d401ca803000058400c0f40d4104541c3d41d000d20031541040814842040880d0064008049241011600003407001c00c1200410904520b500100700e00409950300e6041030408500050001d29800005414652034400c018024410b00c0c03a8a207828201060a0310740300d02842c074410104084030140c0380c0782d01c0c00d40c90041c42d03103100300c9668130010f091030045002d914061007104c0210b80942d4405900640d0f1502c00e030380c03885020005641105020002c1580c196050000e0300250054801c0458260300d10304000d8143c50142d140360030103e008120810401d42c501002c0d2088403140c050a040316941d4030f1098819010ba0b0380060f402401c001c04000000c0030a81108407507902c02c542c1d83c070000d28904011540c00c1901c01e543c0000003041500c0c4d01d865058001d484560381c21300c1c07804080343d41d06103051041c00c510503202200403414040c014404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 955315827 1250 955314577 955314589
    0x6031104081606030b03281b060c05010b0402030103030c06050402060c10050609090606132403080a080f061309050c041103010609120309060807110d11120c06041e150902 75
    0x105c1d4022001404018000e400f461a103490b40d02c0901c0e180104003901c402002100041c520803c1c40c180700c141d00140da9440040d08444010000712811751a00c08204501d141c1072080d41e060326055070f504031841034a0f90781d9000074000504140d030b010a00b40301c1c444100700c0411400c00e00d900c8080010440b810700c5e000b0b00c22042d00180001865030040801c0040e281c4566180c070b085510840404241c4003850088036003035114400c2901d0100d00c00030408000c1c44548801409003032025500d042c095520f030702003c06465003c0e1440c41c1c1c800b07240b444400401c03c4d20f4200c1a0214002d07c15550304484241c005801c1312480414003004e0140803004200740b42e040001e007001820208020041c0d000c0a03034005003811424080c0d81c00f40000c10700450030603807041001c2702201c00841c085402c001c90150002d4100418801115032911510029000c0d13140c404080c0e6881001e6840103180c0394440383c1d5441c1a12007042107003000b40f4141c11040d80440d00b4654821f0b50b00540541c0000c1c52092070061210b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 955317077 1250 955315827 955315841
    0xf0307021305070806090a0b0301141617070e0102010b060706090b16020a03050a020f16080714030a0201030926040906080312010e100e040606080105070f090603110408160603 77
    0x49007481c042c20480c143d42c101008030b03131180c0e0840355400740c1e07502c0b03c0700d0b44c1c02400c01c0048160990701e400c61090210380150311050082040000726803540d042d02000b19595035034044138411481207200801d81e0701d4003c011000340c444c0f05000120f0008801000309044e601301200540e0003684178083c0c4018002d000c0342207074005140c1003d40400043d0f01c84069625141c41c0001020400000380031800580700381f15459031195402d00b91941070141c4098003800040d580141034040c0140d020000c2c01d203120712182c2c0180c2c5405400f401d00d00d440c9400542c010400b51505844001c01600d50340001c1500046114440310b0b0041d41e151641e00f0041d0000454026070804000d903441000701c08841c002c5568018116003046d4502c5401d6641c80090a41125256205020142e03412042c4801c0104c40d030042400e0390210030003003003075a4894000b150603000940710000441c0921500b4070003140710340c00c03a03000401000e82140c542980c41800b140790882004003c2400e841610b07040c40f0b90313641806800c0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 955318327 1250 955317077 955317109
    0x10060e01020a1106071104050712060807060c12090e070c03021c080f221419020a0308130330050415260f091002030103030509210f030702 61
    0x910700440b59a1008242d240315103441c40f0b240b01017810410007401051283d550326010700180030500b044070002e0100000141c0c0040803504000c80481c0f0003c000407100100e074219913030888244c40d5511104240c01c1e03030800031030070071501000114440042c50308250003030081c0e076203041140003241030003814041c601c1051880301100702c0740b20314910752040c4c0d6a0780160714100b0142113511070102c0c0401a0201d00020703015040d80140e0340041c01a900310200104600e10141d901c3c01c2120340e042c1e0700f0100091320095000f4030004080c00480d003504080c1044542070000703690b07015100d031509e00311483d0810401c0d41140800c500b5090031813030340b60411150b081c542402400d1a091018000b40421450180c608028a4085450303001042c7c220060301c5038900c4904112606205081c000d0402c800c4802900328490460b00c0044a0076038801c41e4101c079010b545503410070001c58100a02114046c1140c85407920100301d990803900280000d099080350b05009581e42e00d2541305002da032070440b01d024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 955319577 1250 955318327 955318333
    0x3120e0c0a1e03050607030b0a15270503030313120309050c04090302030d021305010801060206040b04120c140d11010b0901050603060d080a0509041d0c060903070e10060e0102 77
    0x22089529032820900075202c11100c21001c2d024200b105001100c0c15034030190082c0310f180c06015580e0b40640c07000002400540c1d15101c01e9031a100c10300d00e400305640c00d050020b2560403200980a070b800b005c0c90b400b0300000000304015a0b5980020303196410585048080c408000008001c0080b0128036400204503030505101a0ba4244c440d0707034481d40d415000b0350140303031104042000c240c800d100311390741450f010000315110782001c1508481c00030a0f0003910301058041c1d00100b240341c000603080e403149510040c0088a5030711a40c0f8810b6071880d58807003200b4840c100700c000c00003d60b50a0b460750080c6050700101034207004210028404100c205906106074940f40d003130b10f4107496540c000303419120260341c001d03540d80f40c45000c41c050041806001d0108100450b2160310030358064024442c1d8807040b24280f01011003000c01428521050181448030781c40796004841030b0814201800321414020141c1c2c2005a0b0341c0010080f080c006c85880388007000c0507800703102d00d80d0460f10742040f0703800070b1000b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 955320827 1250 955319577 955319593
    0x507030b030f10110f04030f06061a040b070812070804050c0f03061b0c07090603020a050609060d110f04121502040b030f04020f060708070b0105120c060c03120403120e 74
    0x912074035038016103d100c00071622640d04c81580400e01c000c40c0c100c0312128441c559925602d041038031040d0944a800c5404c41e0600b1030002d0040740703554441c2c080e2050301992903d810326001c5102030316407060354102e410002c10b000c46141105c0500c6042d205a546485040d03d6107801e1a010f402c0120918170a031145020001d5144140c6000511a910114403601001c00b040c00d108141694003841400140d58400d9034008102c40720150400011203209490045403151074000f0810300e401550b4105070440b01c14013a0000d44d6003240c00548c01e001e03124540c1480c109681c00700d90b40680c071a8005070f415031004c0e46071700d081180340b00c241e4180c3d048500085080c1420807a26842500c806004085100280c1c0c01007420b5640d900446042401d0052066a0354455450001c0040d0060302055030140320000001959040014005039042da1490103400100045000c002d10382d007040c0c80304441031106111100303002501c070f0315175401140680c884807050000c0311000d8050710201d0342c00758526004104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 955322077 1250 955320827 955320853
    0x906020a031407110c121c201b01120b0418050712080301033f180506031f0315060305100902010c0f0305071208011a040e180f010e010507030b03 64
    0x107200401c00c0c1c012120040c140d01b1802846190026182c49030004201810302c101410383c002e5880d07146410314160400b40701c562104075640f01d61f05494503070940102c0b171141c2000d940c8074860a1650440032800083c4800e42035000c41d00b07c0728981c4240c1c078081d251040141c180b1504108004c0240807661101e615921150b945403141c0c0018440240307490746000c000030101e40c658004240030350003c2400b07200c400c001c02d0003d004600c603962008c04641c003610941d080e80800a42c03042a40ca000d80482c4c03031a01d814840038890382c040c0311003c82d036090070b000100c0002c1d42003880a03624103441201003a0035096007400c1e400c04c400a90f041002c0d074500300d0fa200050341c01130420341d59180c000000c0f043d00041810180c030a4424180d00901c003450031f000540030107400110b42d0b4142e07080021700081c0f1010703010700395440740f0641c0100000646440001007680c1c80214030080e0048180c410341e0602502c0c440c2240c25604421513214813a5150020030100d076030b01d442078241410303049008005100c5481 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 955323327 1250 955322077 955322083
    0x9010212040521190c0302100206061e1c06090b01060809060103030815100906090807031104020304020103110a050405090f07080601030b1c0804030203060916060c05010906020a03140711 82
    0x510203c80c50f0344080800c01d107608140700448220130b9041541d80c40740e201d4504040d0100850000321300c02c0c41d808514120103032000441510556010700032980000390078000711408448200e14580c0018001020304024210f007000c400716078400c10001c140a010341ca8000e05040c0140c0085041200c210208512100d00255650440760141411041a00c8080300c500c80108604000c42e00145010442d403a02903011514078100c90159a0300100140c4030201641c80303090074800602004000600c3d4030b102c1c9415401581c00c1403050500051003082c0d295401d0711034020705442c1003c80c4c00403c003041281802404980d104016054110701450b101d00054642e00c005441d20b81003581d2480c0c4800c594940400d0100144c0c22a400d60350442c00714074004141d40d1050004a00030301450300880c0740c0d10000144440c01c41c4817500c0c0d80001d5810103204482c8520014402d5803190348514590b0045015403004004a1101c1d40e400300d040c60410640810032032016281d141042100001c4007a0740b0004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 955324577 1250 955323327 955323349
    0x100f0b1531060e0118030b040201031a030a02190f06050a0e030c010f05160611071e0b0705070503040e0c031501020703030f030e0c04060b0a020601090c0f0c08120903090102120405 79
    0x50400c81c1d401803c81004075140d9541050166080a1400c40403081c0800e038515688118401d82e42841240c8180025174080c07000303c041b180c1c240e071010000100501c0d1560f0100a10f10078901b20310000c82d0b58541101400300540d01040100340300081000300c151b803001c60039071092410750061000d100c41c3c08c002801c26030034001d44010020080307502c0000d0303540c90034000c18141e0001001c0c040c0f0744006612551079400418200c86028180c031030b084000c01800c440b061582d8100c038180d00c00d65121101507405d0342c800902114140000c01c404100d5240c01144103004003843c004640c0c407880e04040300b00585040c082100d05542c803811040000070b0340120001210440d5141c04a12031610403081450070a0034038000f0391113401d0810201d01c050341580501054241a1308984559076102500302c1156810f10445000640b207956500d4210301905004c04154030507440f161070100b50030844612818191842c40244d04005032610843d80e04202203600c000d444900729241c1854440019000705203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 955325827 1250 955324577 955324589
    0x10b030106030518070b2505150c1903051801151403010b04020c10111e09120609060f103c03110a0b0403020102100f0b1531 55
    0x260700028139100e86070313038540080b925040e00f20707644a501c8101c2038100b6041030003070b00c0710492940840168a5210b04010412a80080c0984070038210f003d02074080d51002008825a90410058118800000001840c250f0500d950001d42401c1a88612003d9240d40200507801c0c5e05105ca048050360000c0c40c00000c58681c1c071004200a9101800310f07001d0b196250400381d0040c404500882c0c10308010403001c1003813005e858108450104d40d8041d04103405002d04109a1112400b4491200102c84005046030341000f0000c0104061840d5040d01e00901191a051103410880920880c1e01d001c1c0c4d001a041100e82060b04803180c203103220200e006800d540d80741c06045c0380007104101d075541c1d40d19080d01449110b880059450316810300301280104840d50074000d001a52001031114510030966040d298160b000d002c80f030220a180c0c1002e0030241e00f240d06040d540382420340326590f841c240d141109040d0b2400c2078440603411081402035008081c1407001042444d0070407408403d90000c001a540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 955327077 1250 955325827 955325831
    0x11d030d061d06241314040e06010603020d060f14010e0604080a08030606040b1911120d0203150a1814010305070308071407030f11030c010915020f01090c1706010b03010603 76
    0x600e0b82e240b4040c00b507901240e00c0113100004051400e088032542003c180d0300b00340842c4030301d8400e15040c40212075803140706640e0b40c3c0001c40140a4188203400030300e0244484100461713400d44030b40da50102c01c00e1130b0f4458103420142001210055802881091802c00d00301e0760141014a0300744110b4a40100502c001c01820740000050702581c2c0c2c88080d9409444a02090f0b07445012001414542e0408054210003081810031880c0281c0000120305112614201c0c8443c10040d2049188019400140040d48000203c00c900c074a103445403139000004155810010406040ca03a01100444031420048014560508010320115100082c000105c81e48074442c0ea03560b00315070130201c0c610440c00d600d50940d401566000020b200480340c0d000401e0f4003c0c01e0a09110090f802056680c0d248080d0090100700101410440903c07800044800420540181c403000009007207694215900010210b0f00120b240a003417094058004010074000a000300500555040c80f0214001d40414410803003055 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 955328327 1250 955327077 955327099
    0x9020a020f030307031413050c1011010e1f05010806040f0f1b0609062102180d0f0b060d08070f060b0315011e060c06020c011d030d061d06 61
    0x14801c0244000012012040d00d4a82c1007000e0b004000d85440410240c007000d1020100e04010600c01c0c003010456404070080084824100c18400c405200c90030141c2804014180704200040030b0054040c0c140c00000500070150044079480381d40743d0000010309d00740d450100103000c1c104000400307a03001034000d032000124114528014400d61a44034008100041d2410034039641000003a80c0310076150075440e0102c03200c3e25040304407010020280c0c10065010b0a140040b84a241507004095586c001e00a8801e4414a40042840c6a1011000b15081c164004d90903090012100c501500940120f0f8101ca0152080e00c4214060148071000741030f903d0325094210410009074400507984201605803020407540c1401103030a40001d120f8012114180c3c06604a041101c1d222074050710001e4a4106810300c65850b810300940140d40402219036170b812860104006003509948082022002156960440700c3c005050310f5150b40800d80140c0551000c45007081c00310411a8410000e032400d000035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 955329577 1250 955328327 955328347
    0x813030e0f0d050d0905130506011e021e0708150709030b060a090e1015050d08030a061a04141c0b090703080a0306170d053c09090f0f010902 62
    0xb00c00300c01c2e0040c058420019203190700e40c5c002c8490402c072002207501030341c044c40000d0035a0548104840144c0041c4a05c0c58a10001e02c0900c2620300100b43d0b44100d880d8001c0c02d5801f5070742c03d81030000c400700a0307001c00020803440104200c01d5451201d00c1490000034207000d540602054042e00009102c280c0840000300300f5100e51484500515a070a418052401c09414203620f0b402400059000d450400501c0ca2011040a5805003213801c060710900a4440c1a2a180000d80015000141d0951109000a246200c4040038105030105c80c0d64560780d103140078040e000301107000304524002d42d10314051a03a01e12495448840c1150844002441c0780d03910111755040c108540c000a06121005c1454801035601d41e0080098074007000d0505d0743d51400c11141d641e16003684d5040000500c0800449640d242c20401c142100c18420040704003016400c114980901550201c1440c0b000340820f8080b407500c0c0c501d1030603401881c0107000030040e0030514240500e4010502402040c5900016080d5070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 955330827 1250 955329577 955329589
    0x80d2406140c010b1c0311010e0c010323090706020d020f030d0c0c12091511060c0903070f1e0909031d03151305120c03180609120d0813030e0f 63
    0x4401000b0b000021030b00c00050301340420717156000305a00003501c54201c908002414403400c0d168440e02001845c40303518060046011f0a41021050b106443c1180f07002c0050040e9041230f401526088042e01c291410725000a18100400702e400045500c240c0c01e40c0b50010f000300c1129844100405d0202c0d042040d05029660300f10416001000d102607072407216a26136115204a00b52800001c01d080701c00c0d600442143e1034442108034110035000714020507011007600000745800030f00036013a40c100f5a61000403100342492680070a2518100c1d0302c08500b02503803803c2d2800603150003c410014001d1540b0001c280b452120301840307400302d180280d1034481d80d04104410300301a005280c60709900e4040128504070199640459841c40341940000050344001c0540e4494070b00c0078001c5041000c280314007850728145210254104c43c0801110201c0d44600680200d40a001e500400417060206c0d0020802c3c07100a00400c0104c80068410000990120740c159600c401191700c4680c01000740b0005003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 955332077 1250 955330827 955330841
    0x40603050d020f071401271d0907151e1209050f0105060103140a0209060409090f1209062304050a0f0303080601080c0a030e0a080d2406140c01 63
    0x300900c034036000010300550001e0064207030b11842c019a000295103503440112007a03180d0020380800c0c1414403501c01580d80400a0280790701c80310b06a00f01c242d8403000c840d101c04010b0540c001c03c1214a003003041c10042042214000e10030181e0086101c610b4000c01804180c1140010108944560f9010740f0a4030464250510003410030041050b509640b920603550001031444041e594208000248158068410310190800400c4121400c0e83d64000c01c2d802035200480343c03035210400b440042900d410f00c2c40342a0142c1e12481030701c0c0802c455070900c440301c0d580b483c05071000c2290152041c03141a42c02003501050365540c640464451f401050140418043c80c1c00c59038020764060000a581c07140811054110390080e01c684104e0746520b0011281440c00301c0320b402c0364607801c1080d0401d0364030a03400b02c0e242c480d404c800c0c0e41c20866144c0d0b80240680c0070a4000c100283c07181e00c45050248400e05103000120240b11010717840d072030464061715000c84a40c032100790314004a04070b0117040c0d0a401100c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 955333327 1250 955332077 955332083
    0x30e07090c050a031a01081306020d090c0503011824180605010f0906140108070c0b01090204150509130e0307060c051b0a03090b1e03090a0b13120c02040603 69
    0xc440440812001040b9030404403070342c0d001a08040303403202e014002c00800641420181e40390f684584c0c1d4221080740c40303480c0c29401c0703035043d1382003100c903d04105030b03c540c48640d4802c00403500850315142c01c0509646a000d0b114a906461101d400000746499092841500600d03803030f41e041c054103117000380040c81a80008a400035a5022840400c05c0951026050300c44143d0003800c00da846401c00011681d16004441900b401d545107600250301a01d040d1b503100405151200da0901195104000b591081e0700101405401207000d1000da199044c420b010070300c0d00c2c94254140301c000700000b020441d10420301008150380c3d2243c4a1002014000c488035260001410310080803405030041803a4030000740030b104181c201210004852010500b050041c0d0907540b0540079905148002e411a40705a02009070400690b051a14411040c0081c0d032040d08400003800d0025140d0900c400501001008a07480d4400c600030b10000489401c440d510200c1d40d1328120f500ba06651000c240201100c0e00b000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 955334577 1250 955333327 955333331
    0x504020f03040201091d07051812100c1418010504030210090816120308070519020c0312090603070c0302010b0a090510061809050c160b041a1006030e0709 68
    0x3540105000950140b8400e0307840540e619641c00245243c81ca5802c0d8402801e421b1a0100f44c50354450f17005429040101210030707880010300c40c002407040d442c0d1601d4144ca5000011244900b08443c4180d40803507031281040e00d450b1a220400340c00398441c1e000442507121480d2190080e59100b44180c1d4040c55000d0444c000200f0800b0000d000322000340700320001c0d80302d52010b01410b001040d084d101202d03a6025000081581550306490f4682c0080181040013410f2140e1404030050b2a01c1c0740b41104650064203022046c0e205040c00c02201040d414200c0000f044009219120329049a511051610f41306014910318038089024252072484140d1100c00c040d804164000c20ba40708601808000408540070790b03a5140648110844c041512200340364218100f103d49040c5c1c01003540221a8615985017403042d0446000c40000c00c0015118072582108000030000240841e00048c03001070900c44c1c0300d25051b400b40061304c04600808003050748855a40d46000402c000020182c2006441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 955335827 1250 955334577 955334587
    0xa1502070f1b050a0509070c0203150c070b0a0501030305040e0a0b06070b0108060f0c09190801050a0e12040b070f080d0c1e0908060115090803040f17010e060f0907050402 75
    0x400b003422000085982a4000011000900d610300404410212100907080c608030740d403070150640b640c004000c1c050b6018002c641d0717241035000c4442c0380c9a1046c02d0411000342c498003d0b04054100400c003d0083d034429151000600c00700c0e801c0804e440858589840300c1c440c903513886491001800981300e8180d00700f01c0c00300b038040400400d1510036058600c2407045075610369a800c03040d15112010384011080003030402c61110702e401e203205200700c50104220444425541c2d0501076085a0007105c03603052207980c555003405207000500020025282d640041400e1500b0701d0096125072242c11802003448141d2444401000411310a40c1c01e5041049410407004411030f0001d07081c101e1002101c1c0307070000001211203810340201c0c110416210840002c0207180e0070a120403043c40050441c450900540d00c0e00040c1150041008101908014042c4d0f5076042c0380c282408407400e548090100d440c0d041072488015140002030390f0798002c04000c25a491030b251886110301b414030036088185c0050001507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 955337077 1250 955335827 955335833
    0x21e030103260306240c030f090102010507020a0317060103110a09090f020f030a0b034b19020f0307030b01210b010e060609120d020106080c01020a1502070f 69
    0x100120b100841d50030640b88429241120180b00403124541d010300c450420704402070700c0c03d8805180c0c0781e101001a2a0004904019145800c60902c2486c1e080e0001072160241d68280911500500c05000810700d00450b50f03409401c2d141400010407440140f0000524644c1c466041f0030b40304101071b01e07055030344c84032040c0050040d0341c42d02441c81e032103040c40064508809680b088540079182012078030700f961104d01004015165915103254140710b64500c0c3c280c2d00c0c507815a60f03010210440c05020070541c44481e018031000402d00030706000340c551803840b1081c08010491490121451034060844480361001503074400340e0111003501403140036800300801103501d00c040d041c1c2d0344082240c2e08034000207420b55a5001e06060041c10901c03400d00400004643c850025040000202010b04020001000c9401780c10800049041c0da400764801030b54054081c402e01d8003420028001d00114600c110010350b0f501c407009002001c0c43e500307030314135040c00a166041d10000d40d800a40401c6d0410141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 955338327 1250 955337077 955337093
    0x314040b031803160f020d020925030902130c090306050109061403010e0c0d030903060903091e0e010b070302070b0d090201020f0303010f030807051507180603110d021e030103 77
    0x2100c2ea0311100b51240728200c0014008142c0d44803201480070584404e600d0380d90101e4054100a040f80c11006000440340180d403005080c5101d4481d107010391464201d006180f21a030b007031a0b480b00c010f0620344681c0e00302585503414070648088400ca004207810b00e00000032100d22400d6403025005920b800000304061045402c488101e40540251900d84030070402058200c56030781a46002e01d83c030403803074050103081662030351b1620390203403c0084032181c0d252120380070b0304c105220031000240c401c80c00b80500d800c0146c0840548a00c00190701c181410240c00800c60001802050840400440c980003014070070003d03000602004c1c908140c0703a040010411001e015a000d00f28003500400b01044241240001a80e04031040f815800030a10b2540e241c20b20716a10807102940d0b00d000e84140c01741c041c1d110388001802030143d5a56011242d0250011a410702c40b0307500240d0805041c801110941140001aa00c2c3c000c600c1a0059031940f039020030b05100700c1c10405014907080080000000d200d550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 955339577 1250 955338327 955338331
    0xd0b060d0c050c121207031806020a170a05040b04021e040213081c020303070e0d0f03020601095004140d171605090a0e04020a09050f0705070314040b03 67
    0x3c00c003100e1a201148891010714010601070808007080b4000040d14944030380c212070307100e0325140541d2149a4494030b5a8041ea40601e042c440403403440201c0b201100303426000c00d0340c840c01c403140402c03450800c0e0341c0303e41c0d00002c045c2c0064030903c05103140760358544040e100c1c11401000100308640e80c180040c40707260908014031a2140328058481801c0c1c040304610f58131103c0c0301072907001d507266503078021094450f024844622230300880e40d1011075000400c03007041d242425009400402a030745c500250441912071818881007510405038680c2610752000c0d40100c56440f8500800540c00401c0044915448201c51002108140007061109200000c4090041840c00c0c5096030015a05807000390b500100400012140d00c2e07691000a0800c000044070255a014524025141034020400034444001c20340016150000b6034042c0011860106102001402c5a43c014011031501c3c5114403040000245404240480010400d0402d031054402d120f00c0300d03500d00340a4030f4648415041c00141c2007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 955340827 1250 955339577 955339597
    0x90605040b0103090218070912080327030a05090f030a080c061f15030f02040906060e0904020907051803100c0f0804050601121509080712090b0d0b060d0c05 69
    0x1d088006403155100b4040c1e5404203402500d0210701c071010752000521018020b20a004010101c0360108240403041080e00c0e1722402002c00e19220301701140390103044c2c1c0401034051010300d1070015070100d20001000b41c5010544038140162255074101c0401c0b8000c0b50060b210764076006074003441c0200081030011b00070f400162022203240d60f03101e035604c42d0446010071075220032205c20101008184000024841d4104180c98040340000c1c440d042d00007640c0250b00003e11035500ca030414004150300803499411090211405503550516401160205070b01400c0002080000101c0c802c95032000c1c010700f41c00c964040d085402071565001c02c60000c003840b80386e400014070030710002005c09108500050242e5002000b030b204a074604034402d0300703d0029417002c84212040d2411064030040501c541c4030001e01454941d91307110340724580807101c111080303490800d00c078101c0c0080c00503840314030546000540380d10002540f10450000248103000d4240030802640c02c1c0f00c401d03565103500002400d41c005d0317 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 955342077 1250 955340827 955340831
    0x918050d090f0911071a0117060123010521040c080c010f030e0c150408153304090c05030115030503073519080c0d0c02070f09060504 59
    0x400c0c850460386061148181001101d80340c60500602c44503601080e241076424003160300c0e02c021983c07a0b4048510346900e9000c40c0b60070200400132440e2049440e02101d09201c00b51120b58103281580c01a40c0da8a000301d503a07070342544c000c500c3c43c1c1d00910860342e0046801c03501075030b89004e003c014240807000316021948100c042c0390014240c2c000082141000300c05840b11240004005411401403001d84907003d19441244041c0210b0b485100b2054080b01d5484041741e990390420308024648a9406140000703494854200030811001861030406001b20102420442208000b05801e84400c4410380d03611a02d000c0c401c1c01005201d880300303006c0764001d031700070710007180c080d40e91038480c004500c00030f031894100304000c00001340c02c1d06103048040e05074000d45154482e5021071282001900c90740749100381001a903994140c9a90044c030b0410a8145405a8603180c04642a0303464040c20b40c184041603201d422b100c00c071600a01c0030308044e080305490300307070000d58400845000d0041841034500840c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 955343327 1250 955342077 955342093
    0xc1701020a0216050117061c06090b070203070f03080915010e040c060305010503250e070c0b1312030c031b03061715160309020409150b0108072304091805 68
    0x343c44a000a012604141c40e07000c201c4603100782034100d1001c02002664010315100c8503080d110000b520b01c1004600500000440480c9481d2a0300c1040e4080c0c00d444c10b5510034880507001444200c030510240b070340341c500038000d0f40310300d09664a01000c180825401040d154008140645242d01185c81075019140545690307035544020f40455030280210f64054200120071020b5000564400340c000911480c4200810b41c1c40324949501c200545203080041d5180c000c0d481400305d0300880039081650b9200120b0010013a54a81090600387c840000a050b140c039641c81416010b40c0c850202d24401781e105405440c00340000130010440c0f4003440402c2d1400590005c0c1c0d542000500c48114840600140c0345911092603100b000b80c0c1d501380090401d91101c0f2282c0042c1c4480c060002400e10a11800d802c0c803207159458426106401540d50400249004208a2a501041c3d065107404410783c0c00040c05c59883c1d203010a0300c1180c002c04806424482c0400d4400c00a81d01c1c590807034050415581d40d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 955344577 1250 955343327 955343353
    0xc02060304110f0108010f140105040305070603090c090b01080601030f0222061d0f0d021c0b01090e06070c02100c1703071806090902030a0f0e060a110a0c0f0c1701020a02 75
    0xb280203004600419292520a00c01d049150602300084901414079070b00700b550781e0740c0e1300d807511055410510010303407540c0020f0100722903940307803a0240c070501c5010f0090702a0140000c00084004115a040589400200580041c01d038125190940034210b42102402403040701c030007010b02840b5040001d803810583e50308488030180103481c50080105425900c1007000e08100030076a42203416a0301103401111081d00300b68001c45229040d01c105840140356142c840c03948211020810080c1a42e000706042124a9a02402240410303504a410451102d0480c40c1200d0b020001c0c80300500000400f0140404080404040c611820030ba0ba58400401d9100343d0100c8c0c1c00c0c006104e800045519981d06004810b8642c020710743c03000005800261038044000d0540540d850341080b80e40c00e40108042c42421140c2d40280d4211070882c1c0501c0d071803c1a82e15000b0300c41006001c3c0a4041014110340390700700588080700d07800420490b45070f4000d4900200e2061300075130208a1100152060019440c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 955345827 1250 955344577 955344587
    0x3021b0409020904020607060618050717010308030a0e030412050309040c02010c080406050411041e06050a35010c09090501050306060d0b060102100e1f1406010c030c02060304110f01 80
    0x780e59400f0300440920746450382801041c1d000710b0301c125201c545529020540a945900701c2c0e01002c160400802c040c1400d24010b01100302d88089849040c42c942c0050011a52131800c0380c0d0080c061640010311380ba00658080e003540502d820281034281c40c243e0150610000201030040c070b290807101040b400b140344506a08850241d140705001c101d03000c00103804103e1725402260f129003c0d49001c6158840100080d084640000c00c40c815000e18503012711031307803040e8802c100c00b030401607035514009400e15030007942194502c030003040041002d00402340204050f46541c03d610380f030f1400a0122008864025060300047c3c010000120700e040000200707072a00050090250b0406003040b004148a43c6500e404c0420040c9698194407034007002003100100382c0324248031100322101403d103036140d800b9403282d80007442101c1c40c2024101035078800901c2190008a80003802401c20120340e0a881c641035410500c00b4078080c2d40944084104024010201e660740c0e040002161204403c0c01d001c401524 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 955347077 1250 955345827 955345841
    0x30b0c04060903020d0809030a1a09070b030a150b030f04120e0f010f02010e0d0305090708010e0c060919081605040212061c020a0308090406060c120503150d03021b04 73
    0x38005402007000d400e019845480c3c00340142815484c7c0f00100f00441c3c84c102c0d040c50112100701ca5002c0b0381c0d01b103041407100c4603001101039019008942c60014142101c2c0400b0703000c4120140d840403c02c1e01c551441d031645008144040d407072600c07442c0c1104151403c02d41114103840d4244001c1001d01d40901c01c1814481c0840014060301614240000444200741303580340400c15590b031025903a40d086800c0100c80d42c060001c0d50049114601003e07028103214036540020b03910b80c103000020101c1080400c050459200075150703030703840b13181800c00161050302e441c2c0072540c40d1a25100c0071403c203030007007402200d4030302c1c1e1180c1c0c0c101640d69005002c201d210700718070146044038501c003081d09464045610700103a0603d4508119190701500042d802c0c604a0303000b102d1106000902c040c1034240b50088000400e12424a003c00e0072007920707902c05180c940c16184c01000b200000050406030640c4801900396800b03001007a5801c7c20b0314001c0c1d038030704d00b680b11031030741c01400b411442e82441c060007243c0f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 955348327 1250 955347077 955347089
    0x4140901150309060605040e1614010221161101080c160b09070b0d0203040c17070e0603030d09050a0209100f030b15030f060f0a0507090506030901060807060306030b0c04 75
    0x3101e5080010049005018905003200c2854880c0000500e6680d00e000b0303210885284009482d908850303001d075075240304090344494169000e4820344102c5030b80110b00e10000d20010180700e002c010141075550030354450303c0315850007004912a00c4060106181180c88140800c0e00c038401c0342c1d00c5901030680355019070074158942d2403082115100080e0b036504241c0d008010001140d00c12926201960f0030b64000c00b1003210b9555000c0100000c9c0205801030304000d08002c54001080d100c50321410341c40d59081d000e40000c8004d00804110347d52070800c216001e0101046c41040740040c90b00e00f103a1500760381c0b074080e0310503481e01d0040303603008a070715905004031194030007054803107803071030b55075043c0860028454100f8010490f880c11443e00c0c140401000a40b10001903e81032408400c03085030804098483c80c1401d1404040143d03007600a200ba40035030700304413809a16660741501290141400e9044040d0b1401512000213900d500b5030018403c0d02d21651550603541d5440c103608181c0e0090b84200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 955349577 1250 955348327 955348349
    0x10c051902062e0803030a0e071d061c21030b090c09010309050a0c0807030311060601301a040b0102010e0601330518030102032401051e04140901 64
    0x21816004a40b43c51500b06400808041c1400c3d0341c420f4901e0440c3c1045820440485d1602189589020244020406030031900c0401e0080700400301220320007000145071601072114900364404c4064125490740006501040c00c05106908942c501140142081c6100101c2e003080b840c0c143c00d00e441c014052245c0d030b49114040c02d21601760011070262000d075038155100d01881c04801c001c0ba1040b030954010f440110010300b01c10b891450010035200190300180d01c542c010805200e203a0380c0c424824442c0092080030329078003c2c010000741c05010080700200d2449480d04191114000c0c0e000d050141c0c0d042c0c2100c0030800786841d0001a400e03108062007030312080d0400720042c4034074000c04e800d10494003d180e80000f06564908402d140d00d9a001c112140442c2010982d07d02c0490036001102c400b100560096040d03042104403020083c0e9004508038402d0503d80c0c0d82140e030303440b54055401e4180c080fa8a0a40c4040302c041403412035006024108002c04040b01401c4242007001040d41203038402086 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 955350827 1250 955349577 955349611
    0x703030f1812051b0703050c0a0f0e010b0f042102091003030c06050903041503050402091b1902120703110d02010509100b01050d0905010b04150f0b030a0608010c05190206 75
    0x22030340e030b50007134006018410040c0e48102801c036041064034065441507008040b501000e508114111110b9440501840b103850800d001506000c2d0860b8111000c00c000305440d2401d00a800f6414003943c2c02410105250a00c402c905c041c0c0c514020202a009840a4100d601c840c6405a500390301d40c04041c000c41d40d42d10509000803055407155a01c8000340f0113603410541c540c6503d620302e82081c0742c000c0000361150140015458030f00d20071508942000c0e41d40e10b0320848080c0ca15003070b000c5c082030011038913125212520140d00a0000011000d80580205e40e9018945000fa1075180d0001c00501d1a114038502842c01d40e00501c07030540283c2c0250000c2148450501000020f0030316180c0646c10000103001201d805c442d68040e50034418401c00003c00e07140c42e03030760510003240c5220001107a01500c1c00410490000c0c07440b0a00d050f160941100c0e40c0ea60366441841c0042d140503440311206600c1c1088601c803003903100e000791100d80d402c8070640b41c1511000b1030480c3c0d6044103443c1203001c1451410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 955352077 1250 955350827 955350863
    0x50f060a0c1e03020303090d0801051507060906050109092006040e130b0a29060a1805100c030f03021e031e100f061d12030d020703030f18 61
    0x70507521001c0c4994207041d08201089060040240d400308101e0150740080700703100001030248041d400060036881c21911303640c940b030006280105031100d00d07070780d011001034048180051ba0300b103040c0c6140c000c0428880e6594501c50341700202082d140685041c2c111400401038856000b05500c0d007110010201410241000880d9446c18005030804078a00c1203410151300242040804134821a00c0140001b100300e21403510700301440740c40780072034200c00c04080b00340c05030f41d181d50950344840b1441c50210414240d850700c0602220280d0001035012440009480d10780742c0c072603400c460052107655640d420076000c04056082c0c0c0500c06264402428204250800300c030450040d5500507111200e601031007540004e034070401d1300b0543c0c8015121f0030051050000410500b2140001c059030b00d4800c1d1034500c07440b107040f4046d16039841d4520400081e1410703004140108169030a02410407000c44da10445841c025008050038000d032100c02e41001c0300301c14040b1400a54081003904140c2c0341c107003000f50903 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 955353327 1250 955352077 955352087
    0x6030b061209071a0409051f0b090307170d090512060c09010c12030b01110a0c090509030403050304140a05042c03040f0803040314010203060a03080703050d020a0c0c050f060a 77
    0x40041d0000c1c4a210800100c80e885004c40c6051012500f074801e603103d09010043d403c1e02c070014030044011101603052011692146952411103078028295034813545a40b0000782450090360010300a411080040030400c0c5020030000c0d05204030340c80b100d14040d501d0082c402914104855014030340c01400006840c04191401041806014580351070089030954420001c50400e96a00780000d40d0382807426039a5070003120071398502e0300f640020000c92483d9655103064030b440f4001d0448003a12400032400c2c100341001600d02540e03100041d070362655100e0402400064203500805d02c80c0c6c054420014180c180b0b889010a071185c2d400c0140781c0c00001411608101d00d01e00443c450713503c81040300044c03400356441e60501a01a40700034603603d0f8034600703141d611401d50b4001150180d01c10020300c0103a42d203401409046981c0400c16a40344e211505042d2043c0c0100104c024a81d03000180210031144d201920001d240e00c2203040c5000c1d19160f07814410a0240103008070b8204030204504d2002da40a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 955354577 1250 955353327 955353331
    0xf0307120f17070c0911250204020c03031009060605180f04060b1b0303060f0108190609091b030210030e01090f03031d060421030f150f06030b0612 65
    0x9403074030503030180c1d40d50750030840c0c826081807038003030420108220307040240c2250341c0d4008102d00401070011015001821290384134950702c0a2100c2d101014285514400600d00220181c00500844d00e5480c0100010f0f265407089800d042c0e00c6208800200d1002c03914401e00c4180c812a541e1141040690300c4d958103002c00515a45508c40030714002c1314126036880c02410050004540150345804401d001c403521041d00e91140d20050b0014000c209243d1a200090a403450092030080080c0d25030100e0301c01307140b000c140c2c00c41149052010204a5200ea03030007000b0001d1180640030110500358900380c2c144903441c00003d5100741c450920b80071580c030a82001200c0c45024000180c00b15481d82d5191403041c20f00401c030046038544120b9940e42ca550480c01400208513005098146400d0b6900c4002e49040c9000c040125081d02413017100c40d01c6a4065482030000f480100251f240b03002c1c1014105910384501c0300300f0703810440c01041e224800d0140245c0c0c00c0e80134080a0400d0024041a0145070f00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 955355827 1250 955354577 955354583
    0xb040f0b0a110f0102042111090c16050a020f04091a09011d0d140f0a2a050c0405090d0203092e05040510031a0d03030e070f090501050f030712 63
    0xb00c20b6500d00c02c11018002d5058102c110800161384920703025002c44075400302465200a19403540c816000f095400d8140041503600301c516160b81e51762008051101e004034801d861260660034440800c00c0400149030381c5c450b000b112000745916001c03040100b914419400100f0140400308400d0b015945007002c035070414141360012614403103030f00d1080c407203019491030f0410780d501140e04041407039001380b4000001900742c6030007450400365030009840391282c41030603010800186100c17664943e10400002002c5404503071650102404c2c14850b0361416243e4200340f09a241c100410f040140000e0702d514641c840d0b8000d941805c001e07808000350069440101c101540803207890310211461041420012141c584815407a43c8c10642803100070a0f00c5503012044c076141c10802822010040f4908a4641e01152007200f02c04162808a02800d404200301c8480d104400300410710b8460600c00c00152904400c0c100042da90b150b0810019604103421950950130601080c04000e0010f003002c86200c0c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 955357077 1250 955355827 955355837
    0x130303082d06031c0801090501090e030f0f1309140906010f030305072907090b0708031512030c0307060f150501050c0708120703030e010903050f2d0301030308010b040f0b0a 76
    0x22910304c40048140099003040020088801800380e144903204080c05000000000c00c0741d91841290b9035500d00c604000410b6801002c0382d11088081c1100031120890560306400c0d010740e0355082020302404840d150248186060310014545c0308000840c00c1c100c403d0180c2c4000d209103581c40648450b030105c5401e403002a0002c0e00d41c20a860300903500041c1080305071250203546403414004010418a0f04684c03501241000390300c0c00f043c0941c05894000f0756a60124405000d1440021005444020001850f0102051042200c1c40110141c000280642070521200408200130f030121202e0441e0865017001007402400154400e40140a00302000d07002c41d4000c58540b40c1e028586a4803030b1104546000020f000000c00d64540969a08039064600a01c8451601e40e0040d2080c041e5174140721079103202003220814000181d041d12100440c8c4080304c409148180d080c50304907842400154081401c4100004104071854110713000c4808a40d50311083d1803c013400c01170f55070f00c035603e0402000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 955358327 1250 955357077 955357093
    0x5072309031501120b010815160e0a0806061201061203180909050a0650190e12030604020d09140106032001020c040509070b130303082d0603 62
    0x1800c181229010b440c1d01600d86940e941306140c4045e102105070000700c042d810a9407498403090521001075040801240e2040c10807008030300442d0780310100c0c41565440422640000341100c80030520500030320b402e9030600806032414965600307072b401d00e2107200b0700300b840b2042d40d001003403162800d0b44040084a0740c0c40c00b05955000581d0039982c1e1810142e54039042030310a403082003050f214691451448000f0702a400c4803c80c030601c81c0401121415120300303d00c280a101c0c0800905034000074035113040070f8015600b0071655500020000c0f540500800e440c0004c2d42d041c2d00c00000c0e81c03140c140001d11f952840d5031784030000e000294202e00072110b492030300d4242003c006a80280d03c851419400000000c010b46942400c807001c1115508205000f0407240d104455079a02041040c5441000d650208954a4000b000c03071505100358001e001d407a9002c5050742074101d290340800b003228001e603030307102c0c02d5180c000850701001000990740c43c0030000302c000303525500c51010503103901000c0282681e2000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 955359577 1250 955358327 955358353
    0x2070201031503080d050f01030f03181d180708100b0301020f1809070806101d0604061d03071d090c1905030f0a121407021504090507230903 62
    0x1900c42c6070001c8604000102d410841c205c41c0d403041b40da020305140b4510005500d10f0b264102001c0820902030b042000c2d10087c24503184c3c008140342c0c010f00385100c501d40700e186007816032020aa4103075403441012041903005901c40320009a902e003030303031805000b400744200d10b040243c00405c010724205401d0354091010702c2d081e0510304060034410040080d2024048842c10030052452001004001400901c60a000c80c548507101c030f4099805107814401c0b040101c140d17030070030214500f007801b0b94014800280401c010742e015101d010ba01d2a203440001b03280f0310395010503807510881d001e40b00340340440350160001034000101d429044118241a1a0201c10000c0403036441d20544411110000400c2802c0110b07040801c040d146100691019110848040d600c0342d00d52588002104100200450b19010700022041219805a8024015400343c0086054103d0035002485040c1c582c1d460803000441e400c2c020340300322000080c1170044a88020700c540078944c641c0c110500c1d940d0544281e015110794 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 955360827 1250 955359577 955359611
    0x305310605092d04020d020408010606051e0301050105030c07020f0307060809070902181011030c1c0e01140d02090402040f0504111c1d0105180c0303040506030a0207020103 76
    0x640480da80e0180c1d203140030700501c591410082da42009600e2041d0412203034185851915104403c21100541d5501d08445c0d00c1c006030003150015002546010000a00d90750040028003502d8080c1500f094494034428282d003290009202d0980402e9041001134140c07400d02d0010698030380300904140c0300643d04000300386003050070703000880030420b0441804a0071104225020003002d0b00101075242c100c3c40143c1c400c800c11000d0119000d90a1030900600440c09043d000340a0704074034049a4a0321641000030350754000300320a1295490455800c0082a4410107800c2c14114068407401460342c10040c01002c1640146180c1040550902c502085a962800184000d0011500c12071689041c88100b004aa012103159040303420100114404000030310101d43e031282e515400010802101c152403112410a00d0640840d5481c250070403c40000d45c8404100e203100c0141190103940e11402030651780d128501030f055010340c0030310020315400d0030f0782c00400f04944103140100d08102240c5072249 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 955362077 1250 955360827 955360829
    0x50408010213180209010903140c1237121202070501060f14011b0c0506121e33040c08010e0601090b0901030509011b020703021507030531 61
    0x1540c2c00030360004010350b90681052100c1980b500d9811480d100c141000680f805180c0d01c0014150010b04844845c619001d101c840e04041000d4200d04c0011034181c0543d40710710140c810070040c000c05e01000742c41003000401c00304082030b090600081040d9240c0b40c40c10300c2c11f03500940004120108212109500d82400540348a85c402d00002c6541c80c2014049031880b002034000b101c22100440c09030b15540c0e401100034050900800c2071a5808550381461620315640381c01c0160014000078071090b038400c19203115845000c080341d405c9000a02030042d8044034909440003d00c0c2d081d60f89a1400c540d0140b0303490044041c6490811606640813004201a00c01102c40311012400c80b0004000fa02c84c81c00d00310354008024a4501012400e080c05133001340200c080c414101903455000402d016825030101c40c581d80400e00c11403205885200003035a070601c600049016517070000c0309800100505007aa031045905880702810041200703103c1542c00004122022071103070f144605038260030303010b080720 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 955363327 1250 955362077 955362097
    0x117010f0e0d090b0a050322022718030306130e0f0105160503010305070909060b0d0503090a060302120414030f030106090e0117060408130308040e010602010c050c19030504080102 79
    0x424805080c16000d4000c0d0325503800f61304014030030001d9a8010381d100089950044e0103000c030007400407603811917000540260740f0080d040b86a40650328500782c6a00b0030150781c014000006102503440040c41030362610141d0340813a0a500a1001c00c00601d044400c2028009a0680010340f000740320248a240c90150030704198241d64800510204c42c3c0010b040154692403418045c1c650351443d525555200c130207201d1580080da48215140c1006240d800000c1c0b4a00b008010302a0700b2040e00b050340d240e90000c2c204a00c030b890300d5800001d4040c040d0003a15032103200c003420615607646585506880c800c4c4d07004600c80f08e0004025600b45c2c1c1e4910380c0554080c1850ba640e00e8905400c00000d0061202c068101c000801c645015140c800200080d44c0c50b40144d11894541d15104002000c0400b158940c000034108400403c001c40d0104400c0f44840c102c1e40641c1c02404800c07820842503610348a811113440103a000300c4400390b50690a580606251446880c086160a54803075101c0d0890300301c107100c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 955364577 1250 955363327 955363333
    0xa03051606061503050105100f0825030c0801140f060c030c060403021005130b0a1109030d081b0903030313031701031b0b0408071a0915131203080117010f0e 69
    0x1a00241d9450311441e0f0143c501603030b03050300d20350235000c1c0603100c1c2e60106441402c2007840b0001a22508600c0001c0b2250740910410300520040004003402a00720010480c002800d05800010f44062140c1d9042204802512029170000100148505a44680c0c28400e8070b11041210800b000f900300141845507009a014040c00e4080f45910340c1590341c0603020004146142a003040890707203400c10f072a007010040c1d80000d200c0c1c1e15403462104600460400c0d9503d8020000c1d1082c1442d004040c042c400d0743d410225500c41c50018410034424084c4c04800d54140d407040c0b0001c2c804900b028000c0c003400c2d001e410b00600c117207440e9100e02c8031305400b600704039078031018a0b0b11402e60f04441c01c1c500024029020030a41011708040074103944520a20031030451510030300c02d401c800800b500481350312450141c40701d69103800789428021107a01000f800d80c00d07071200d2000051100c41b0f914100308956850360311001603900c1c1000c0821880101c2c2e6141000e5540c9112135003030401d0921949420a02d4034001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 955365827 1250 955364577 955364609
    0x130312110426010b0f010302031b030c0409051b040e190203010909050c0108091009020d2015070c2607030c06020f031e07051006180c02010c020a0305160606 69
    0x1070154140b203542c2944010342e04080c0e038100e039591211100031034110b00303190061b01c941e1440440c02042e006100c0304c4400700300000c10b1140d1280260028010307104412010f00454540f400e660030100245d414a80c0d21050510041c0328400620500316001510181c00c050003500340b0344600300302d130300a9000071206980c44668104000042c401c0c417030008400d080c441103034038211052648502c2104510010140e5800c00c403421552071079046010140c10170100c00b07002c244000380c00b40306c00080036140d04c00c903140e2a03900204050745013102c0030254807000c400042403900604c0e85d01108450340794921381d0702c41c10a146151804000c590000d41c0940c020246c0c50b1715094010b801c220440103070880b0398004204002070744e158030300c3c01c0f00072010703120880369944240d0078060305110f902c000b4200628100b000005149840c01160354000c0a503110030801848800800e900326030303980b04c1501c0580c008002400200b40580080c000c5100c070301190050b050902d81e296800c903561034101001c82c50403014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 955367077 1250 955365827 955365869
    0x10e030d0b030a0c2702070b060a0806090a061104270b040212040f0602091305010e0105011e08100909080409050603030f1801020312090f06070203031303121104 71
    0x9002150308066018200c50320840e04d0b00c01d4440d480780103001440c030641a40050070404001d4111070400960b41c210744480e8549040c075613101c8142e0f0003a2003031600960204480d440401c010740541c901600800c03141031a9a180405001d55032006081030b0001d0000003942d504c2081c040d4100c03a078808110194409001149089403030341c0070018000d610500050800241c4066195000780c1c00c101044281016450500b01070f204140352903800024100c07000b200d00d1420780000c0d060362a011082c207a02e0707803220011903100720406094039030701c1c52001380100c0c2c050150400341c0c2c2000500302d45090700d503150a90001642c152000c102c50103e00040e040042410501c6071540040c022005507240030003001c0719850070701800d010740d0100707042071035400e105031700820854032003c42c580c1070000240760540c13040d610780e1569607006405006000008120b60701c0401101d00c5100e40b01d203507801d170b245540c8044400324849000c0c2c074400c0c0c1e0384500d10222591441c01410007000d1100705010103900c140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 955368327 1250 955367077 955367081
    0x60a0507030f17042301063f0b0901200a0f2312091606080a09021c0b06102a0c0e1006050a0509090622230f061908010e030d 55
    0x61780202c5640350840c07c2c8a01c0341002c1c60500300c022820f001090b01c100c0c100004041c5000b050440b5442c42426154030100a10701440e44c1c03050700300324020481d50542c031000710070a0f0380d0320340007924842c1c0401c110005680900c5080051204624020f0040210545081c400c16001d000c0010a840081011000b40b21880981a07010b03a000e0090302410002d44189240744940b401010203000036035002500d01d0fa0142d00210380150001c04138580003c0039141003111440f607a030141c4a03801070000040c014205288644072150841e80c80082c0042403554429511404019104680249185c19030200b00820001d2001d801880b0090b031079410b181c0d0340c1e11400700b180d1303000d403042c010244a401045030300001501d2203100c0c207a07003010296985200240100390f404004401e101e40d0001c104280c0c60030350317000d02e10b5030b051442c1c045032001074420034120280040310710180b041c1c0202c00080307090034500404c03805041c040b4103101109890b6035455094035800c44402c0e26507800810600c0d100d44543c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 955369577 1250 955368327 955368383
    0x90311060c2a0a060e1213091a0a05122d07050109030c062312011e030203060402062a030a1805090402010e010908030a030f0b060a0507030f1704 64
    0x490005101c0e5a502e80d1407030b00d801c02d40a018002540d1032146000707800301484110000b03038504110680e070f071400c20351031030341030000d401143d140b1407800c00c40307203880425004903041c0484000e002e80d204500c0c0600b042001c2505440e180c40c64000c000040140c540e20f041000502800600001c83c21000606e21030326042059026504000900d142040424641f90694043e030329140740030300140b116030075004000304070049071150f11800041e0144051840b401003a058617518004219000c5500b903051a4100140c04003a503d90842c0000c2401031a150000b0724400722050451801c50010000c410040c42041344a10459003002030300300c0021303500591141c3c0c4e803502140c011448506000c0815861000104020305201c415208244903a01072803191000701440012aa9145032101c0001c018100c10b85825010604000350740c152441c2c50003c0c0d403403c54940d6601428504c1e181c80c01c82d840d0395600802018004610b82d00705400d170100002c6031255014a20740140078404107100346c821005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 955370827 1250 955369577 955369627
    0xa1202160b120c0715150b0309011b021b221107050c010c110603091018032c0d0c0e0a05150405010b1e1b011d1f090311060c 55
    0x104250700000d00c5c522000b404103e200c400005500c004c484629014205a4010b0b0403a82030100030040c4020381504000008550720100381d8483c85020710036079880c1c6800e0108031480c590145000d216040000384050840003a000600c3d0303003000c13120f00404492240900101d00c440000300d400910a04201c8800810400c1c80c201005001544a40c4241401c3c00c0d00c081c070461002006c90b42040c1c040001040f031421085081040181c0c030040501846070b101c008801141440c0a0b040c0411440c0700c02c40104000d0403086600784d074101080200d902c00c040c0049800c1c1c0012080460b02139500c0781c40e0381c400c5440c0d80001509003006001c1c00e203080e080129183c415230034038006000c600b0200c0240c80518203250004e5030f400c100d181140c81203001c0c0d0907415411a201e64040801500305401c1000030240141ca0400804d8001d425661180c0071a07400c0c5480c0801c60b501945020b05540c08800300c14040e00d000d02035001c004003242d04182d410b07110312520078004205142c113205804880b030002c80c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 955372077 1250 955370827 955370851
    0x190905090c0c0705091306330f1e0909060f1107240e01110702100f050301060c020a050607030e0906010c051203040c080303070f090e07020a1202160b12 67
    0x2c44504aa62030125024440c02401800e011450800d043c281d0100365540c03040d42800b000038602c00383c0b81040310040c210004407001a101900101c4c941041c001a00c0000603040c40490602d0301c0d24402c91207080c000325a1500601000841c982d85100b00c081c114802c0d203010521002c5100706406a81217485042e80103a0b08020440008045540c0b41c80c02074076200c03401840242c908078080007880018140c9a055003403c64100c40c2c545e03064024903400e2310072106010204082c6104a400c2005644070f070010400c10401402140c1c010585842e407644005c1c02c00107403035140d0003c02d11a401411048021031f03804a401c0c22640351a007000c9a000c402840c042104c014161103080d40c90900032041c1c07401300c0c00000807409008440003110090714140c000c581d541c0c01c1c044802408242c028824100040c1c9182012a84c541100d610398001c00d035a5000300009032690301d580d41c681180c039214a080d8810182100095030060465800601c01c0727000c0961102c4030b000c010115244000c181e204004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 955373327 1250 955372077 955372087
    0x60702070f0803121b0f0d050f091b03011b120606080601090302040513050703080a0305010608070905040c11070611060603030901230c010207060203040203011a060d0f02190905090c 80
    0xc030000051341d07004641d082540503291295044c002c0f5102c4c0081d070010b5000c8000a03400301b5860003100074004040380000801c05555400c00a99102c08203441e016040d400c0f03802000e0040244038135448000200500008031031200a4900740041111100305001c00d801040003100b0f607419118680003448a8205100e0074500000002c0401801e03000081c400c550301d01c0406c0d2642462500300e203900358410200c540082d12400c002e038407a003100350200f001034206130011070010700c13541546015013055100c0c054007506100410001d05034002003001005505142c000044200f003104400034140da440d55400e030240c404203e810424000c086a01aa2040114443c0d40c1d80c13048410391400001303d40c0c608411600999800e5601c1045141040b40d030021400b4000d2000310790043d402284210000c001c003800032040480d40405c00c1110341d41c042824405140c9010707207500142c03405880140c0051800c2c40351018190002e0400050074009000b00e00c0601c20b905284c1c0c80c4d96003001c3d040b80014141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 955374577 1250 955373327 955373339
    0x14030d0201110a0507140102042d0608040210050706050103030509011101020301081c14030411040e1c0305070903050f060f1b071e080d0c03061202031015030f05060702070f 76
    0x51080300c500d00100300380005d0003000c0c840b446040c01c8801d40e03c1c030300941d41e95913941c400340c1c0c084030922080140301e880e07030520504030006103407244101d84064541c68400d6880e40c080010303400550301a401400020481c860004000744540c0e07010710700ca07882e8070b51030b00d80c0d071000102070b490a0252030350b07168810801440005000a4103080000c1180c00d0803508100354081140c0c2202941a03c881c044008024041001b400740f140a00c007241c143d8040050034680400030ba9511604171825400b002800c10342c02d20a8031a400c040d07802055400c0480e0700684d00d6030f80c1d41c074000303002400156136040141400032500741e5034042500901d0400c905003a00368004122a02071103201c1000f0051110341d01304c100406407004002e4001a0450356030f58652045100d01005410031040200c0081c2c0341c00780102d5a07101c10a1004540b036005401000141d1000c000385004001d4640089032089443d40000009040e4446407812140328070081c00445c2020400030340b801e240c0b604690b8243c80c0038a03080c094 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 955375827 1250 955374577 955374611
    0xa261c0e0118020d0c21021c030f1d030a0515060103050402010828020703020c0f03160302090c04090e03040e0108190b1302031213050f0a03080f1314030d0201 70
    0x505070b0115200300c0c500c0801d15020064040641c002e0824414400703094009886c1c4200a0003e98000c3c1c40c444156101413005c125071107514a00200072031040c026900100388200c4900030109040407003441c2503615100000c0c50940349140c2180d407940108101588000001240f5820200a0a041c4002d041c00ea0018000c1880100a0ba0117070541c2034803140301c2c1c4001000b00c3e0410700d02a40071550340c401c6007002500c85030554410750003074610001401c80303400c000810403a518000103094420908660030010901e02c0074081502620007884081901646031040200011580008560780c1e4501040090501e0050b4024907980e044800c110f10b00380c040c201107158441c0c6c0405044800c0d0382c0c01ea072460910702840310203034040c0b150740d102040c8111020010454000d4400700c007094140c0d52005c0018800c0c00e103030300540009075168100005203070040502540860044070710708211080c0850170844070140d00140d00382d4100d0b03444441504043c0300c95408110584001e200e200354481040b49 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 955377077 1250 955375827 955375871
    0xb07110603100306180c030312090b07080a2910020a0503040902091203030f1915030c080c030105061e01121401030b06030102030403020d18050a0905060319050a261c0e01 75
    0x400c0c00101c49c10344010320003540c4440c06650344809600440d040000c402050700344210744a0419070300e021104045180c040440d5522038001028440041c0464000e108039042d100342040705500c43e18041c04000380c020702c081c1002d0700c480741c0300507207400d0a0703400c001c0d00030003400d40303c0d595420400521102c000f40f004c0303440d4481c09805006c4a2040310308a00e80013404800301d160b507002e80030403000c0200061007440c1000c403001041100c00d00189070f01090b08880342034071400e601100502d13510b00400b2110f1045c13034403010305060820000300a0a2840c007550114083ca072181c18599006000300001c0d041d1072a002141900214150b00d090ba60195851801d02600006d01001e2942c00e492000d4000c1102c1c0a4040641030000c25666484204094030341515841c2c4240201c207103070340900140b000807080c00d5410400804da0700c4026254070105040702520f09200040486040c52480c942c9400dd004140400000000d200e010040100403100800c07001c050b0307641491412406927030b03800d0301c2c11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 955378327 1250 955377077 955377083
    0xc090103120c1718030708240405070e0406021c05133804050f030c031c020405060a0c030815060a051c060e010f0801020406090b07110603100306180c03 67
    0x1140342d0150401c407070b0f0b00c88000d02d00c8009860024844216041091400031214000d80407501c046483d00d0800f5214031440c0c17054407215800b0480c05295091140d0718980040c003840c281c030b0381551a0201c41585160440c2c00b0340b01c03141c000414460010209001c0c4401c4030f40554100a28107100a01e00c1031184a0400a0103004400346c0350082c1c007484446406070400c030a00040c20701d0415a40ea4004203604440540381c0d80100c90701464a01030220480382d040301948007443c54861110121900840c560f054094095402e0202140613110301009000700010740d19001500c804600e0300511180c0300900c28010701c0322510b44141640c1310003040e1050300109041c2652201106148a480c000508004201340da0502e80005420300b0b0034103e45050700c100400310002c0c00e490303296440c242e12540c41500001501c0500410170b41090344064810940301d80d21806075120b034030780080d8a507042520007034601020044100200300062080312240c0320030035016038500cbd41d00c1d1165440344820348405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 955379577 1250 955378327 955378337
    0x203040e070518040524150313030306031509050c0102010c1d060913021c0902090106112a040b040b03061b070515010303080612070501050903030c0708010e0c09010312 74
    0x820f41d200019241d11203000c8015104012525103050503a105214280c41e100c0c201c20506410701d418280f40c0c01d4180c074540c145615a04c2d5807542070360381c1ca1003004058103030105507071804040002828201c00c40b00c0c200005401282d03071070341170a1044c01c3c00980910f45055a14180c0000142600300f0885000302c0d44403e03d0750120300c1c0c0d1901081079481111101d651001910001040281d0f0a9018010702540703406803000c514052011501103440c540c0000e540300360b5400042000ba0310801102011200620a40d6400341c65103e0410800210703c80707a201c034140c2030002d08402c4c01c0911880030664811142031005c0903900000c25140c03507024201000c0d4801c0304007003107005800340c400c0b01c40a5178800100c504428107016070111900084c08101c0c0080c54660200c1c0c4a468404142451880d5500242c01c1b1030b480d00c1c0c01503a0070b81c800c586003038144c0400d020b08502810240080d10003419204004545402e80842460502e96002c01041c401c400001c01480030415105005140b03c580d410700d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 955380827 1250 955379577 955379587
    0x10c021002010e010608150f01031a06010c0501020d06080d21020f04150203040f0b0c032703030a0215060d05030a05070c030b0a090b15010c0602031f0b04060f0203040e0705 76
    0x300301d000d4040c0800441c043d6090420004081d000042c03010600e8105040d52403131600da0142c2c58819180c03e20001e04101c0701c0300b0450424020741c002580d0030400c1410000440720b0107640d00c90176600b19549004c1010740d1018100f050400c1401494000d501625000004907000b00c04440301c0b03070925140084c503540c0841d40d00b50944a5108503006050b80924401e08a048240001d40d82d62050240d940b4402042c60000380d0008402c082c2c0d002001c640780614106100f40e04d08403d203000340c0c4400110032074510b84001c0c840d2020f000802000d1300c00c0e07015000c08034610308c01d02021a00540194080e55115a000000c00e4010003039409040c0316150455840d159820312800c00301d4a50400b401e045400303024404078810503400805080c0c4a80d58550146c0d80e0300c2d4035111500000c110369070200b010f040c840d400182c404d900a56110000c14000c0401c80c4000411041400c8180c00410815034005400d018080c1c000e1901180f09039244019882c1c03a00b09090000100d401412040a01c034000c55 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 955382077 1250 955380827 955380859
    0xf06070516110a031506120c031e06020c07050411030c1b07080d0f03201917010602010203060102122104050a33050405030306090402180115080a0b010c02 68
    0x81942d1900c1c01c0202203034683c0b501ca05000b0100002401d2100c0303424074240c000034030040300380240e01030b03640c10003d0081800e19540750024240c48403121120714622002c0010000303601071000d051380182d4880289415420301007440200e40b0350070141030f070308101402002003610714a000c450f5000d401c001e40440c01c041c0c803012249003040079007083c4494000d200000007200d6002d4007801c51140c1d04c0e5000e00c68407490f07002400300800200c1c8400102407003088000301500396084a161545000c0c40e006841d4802003003003107ea80000e07045440141d40000900c40d01d5079040240004a0006c80e0b0030380c0c1b4051481030080c003490060380307a01c034801e41c110b00083e091050a10903100078980000250a01e0107040140d03d1800c40144000244000d9841c100300c003006862042510955200d0011840d5443c0c0104120f241c2800800890b440143c094510980d1000c6c074141ca402031000c180c140f010030300c100e0409440704100401110b803180c039094001c81c241e030344103054039181d613010341c0c00325000c001004c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 955383327 1250 955382077 955382093
    0x50609130b1302030408070201171b0f0d151a0f030a090602091207052404090e0c03070603090312051314011b0c060509010c050703032a110f06070516 66
    0x500780b1800c1480401084144000c80d0010300b1005e01c00d0703070f618103484049078143c103040704c0644202081d2207880c3c48400d20700490000400700030405011813030030b1115981d0700030103445405c0c44010468007160001c010006000546451034248441650300b882003240c1da044690100405c100729598507441e2050920690380d0446401300c6014144200c8003000e120740d5a5122900e20849015030f503101d804015480417680c880d0469504040700724541450002c181002c0c080c1c2d13400c02d2b205d900502440300f606035000c2020700001d0007641c40115480c241821b010303040310003461b558a07405092200b0030034290010000500032075800400740c02c0800c140182c890040205d5602c0f0045041c1c881000b100b45c40e00b203800e0400d0188141002d2015596001380c85003078034001e0158001140041c0301d1312000038004d0300015044280031031419a107800384010408030b44ca0728151000480d09200036154240d0081c8408905601c4800042c9503909003007500074440e200d80c180451588003400003400c2001415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 955384577 1250 955383327 955383349
    0x60c03060e0109090c090b03191b1805060607030801090c0908030a020c09093706020d0b1206060a0620062701140f091011090406050609130b 62
    0x3941c4050395a1111009002000c0f00b40041c0e500c0321700200000355049003405540d003940c1c0c010b405041800d0503d03030311003071002c0c88140403500701e1110200c841100300c500c001c0d180100a404000321000200c03440301402c44102038903c5008074010850200402d400003201341c11646c2c41070b00084e15005040c070845801c0c1941c0c10604907404002981688554000b9150010f11070481c1d81c44d60310b4490f13224180c2d9800800030007180c0484d01103011203865071040b102d00c50484488006001210159403404100e90085044444040d0360780580b0002e814608000300180140b40018491400c01c0c80000382411028482d840400060070f482d140d283c120104011202403010f000c44415050240080c4105028080710301220740360820300d20200401400b8803156520707821b90058290315600320105903948020145031540c418074010464040383c42c0302d145008128000c0580d251290305007000180c4a482d07000d18801c101c140700494090b610700091568840528100059440708080818058109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 955385827 1250 955384577 955384589
    0x307031523011106010603020318071d0105010824060c100507140f040605070c080a0f02010207060908060c070c0b0a0801140604081e01110a1107080601080a060c0306 73
    0x1a00085111010245001d940004880c00d2640320181e0011a00c0048040b000c0e441540008010400c0c0350080d401540c100304d02116850b243e0a040d80754a24140c07281e0300004e04604800a002e000005410040340506400d20303218085090203010f010300c00c106100301c2012103141400c00c17001d075074401c404c443c002401c0109654140316803841c1e42004250482c8c029001c9610f482c050017181c03129004032011030600d2003005041070306003001110b494128500403510340300840e80219040f1020042800018800d814065503200688002814550035a00000c240119820b082c0b005075808100d0f2540441c400b00c10035200d0748c2504000500b1015544882c2001c1c00c00200d5481c0d035540705648034144c4014003404e20381080c1d9802400107d02ca584644507064008000350785d81c0e244100b10929040c1508400861822440e21848281342c2c00740c4603e03000f0070400c02d04103107401c0d0309100d01002407507c0d0010b08269894042c085884800d61040207018039035038480b02e1195400380c2e0021003e496 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 955387077 1250 955385827 955385861
    0xa0309212a060e1c0804150e040203011401031a211513031803020906060c0a061802040b0a060e01080408040906060c03020f0a03050417010906020a1701080a030c08030703 75
    0x40d903050302811407001a40102c4c0138555016400089840790041544540da1064442d40ba25203010303402c0c0c82c11040c60030300138108026100485403543d5030740007a6010344030044081740e4040d00e040c0007408a1303603040c080007480030511070142160350b035003203d10590346482c0884c0303041da00701007200d14182420b40005089010b060014413648101c0e002500c00003601c03a40b5422441c561000301e4100740e41583c030001b07500480190000c1c409050003006090003145600c211180c0c81d460f943c404065031003601c00300b000346581c20003820035450302e405032441301c0c1c10540701914600c0c1000700040215460703001d070320b040c8071070340000c20100304404e8101d034010100c5841c20400c49444034002015030880c460280d0051103910a0911500404201c040340c4942c117480302e0f481c0510f0106011229211188150703425540c0326040d10105e0b0b8907000600c05c408070303070b82c0e41408440b5080d00b90b0128801a04040030540c000c29420f030019401a00200816401c4660292a42d40f920b5040300500003c07500f20f0b8840c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 955388327 1250 955387077 955387079
    0x27140a030806090901091709010201020c0609011505040b1e01120e031e090901050f0d0b0a0b12030c1203132a090b06120405011d0a0309212a 62
    0x640c80030801e80664000c8405142c10f0702c4404180d42600d02c4001c014220f5a9044900054083d100c0010b1180b0342c410300025003040810882c407400c01404a0300c458059440b021041c40380c040080400c1c018003400c0740c0c104100700c9807101241c002c0031018242416004803140074102a80900d403844d0319040d0815080c09000d24000703034603441c4d1300700542002c0f004040412544136407007a681602c1941d1000b80000c60303168038140801c5a2802d040344001d41045030440e1000101d88080202d92003480b400c04003260b44030140042c0400e1102106201039181c0003401070103000e05c0045100840d40311310201032502e903221800c4044083c04665002861407a054017108100903069062000c0c1c460340d2070074020100d50740c0044078252414100c004c0d03030143c820001d00d006407000381d002d240c0043c012000001c644944201d00710b120500302c11420300e00e03480244910101176016a050018040080c0d116440404440c441c0c41a200004401010031020030b01450802401110f000415040c03044130030611 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 955389577 1250 955388327 955388333
    0x90306050a0912051210060f0e3f0f0a0b19020a08062107050d15020a32040e04022d010e06130b1b1b031027140a 50
    0x41d0312120012444400580001b00c1243c2c0d0380540c4012204036494a50380135512400864642d01010783c0310398001502404200b807104480d210340d03529815646101c5c0d82e07280c1300131511100165401c0704031003584800707807500c4025004034051034503035070050b100040354991109541c09042c11108041000d4800f2565000b000d0780180c80350b0203800251011040322803071015060344600c45030140e56840c0d01030310003049641800580b001165024840c9400c481841e0402001039034440710380c1500080c0e260400c60071038075280b5154071100110b00e450303000030b0345a281091a10300a0780b252401086080001400b0741d12040d42c900c10743e060b80c00726088480c00081d610148944140e41d040d0006040f60846c400500703100301292980001d6007041c1e40d8461602c28018200c2e404801c0b448903141d84289080620101000644401c1444002060358030201d4010f151030074022100b614411820311900d1055018014550b20114400164101c1a00b603a802e1a010444031900c0644031031041d42300d00c02c14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 955390827 1250 955389577 955389587
    0xc080703200105091e0705180702060a02190e0609090703020d06120b0a0c02120a2006150105090102190507030c0e041a060f09040309090509010c090306050a0912 71
    0x201d800e501c400000030005410442d00300e80c02225890001d07400f41c104021740d001c2d500815107111300b252003111071264444021403402c5010401082215020b40d040c080710540600841d98440c001c0d103421400c00c101c0e440f80740c54000041311a00140105c0c0c1d01d0200960722040d0440c0c4a208018160301482d0425507030003002540a6941c01c1050f41c5010400304207101a00500c804a58000300b140440c2e8541c0d103035250003041c4108004040d40700d00c00140422070701d514050100e065098480700c6500c00c403100b44086050248810841c10b401882c02c0010740510540a00c02100081c68550f44860f04000183d00d068010344200c1c2841c640310007442e04200340080e14109a81c8a10700208102d6520b40c080f40c400c07a01990020007690011111903081640003486650011000701520760640402d03000c540c8003901074900340c1c000b8985000502072112503006141d0040c031808020040202038a60040c24411207000c02048162a0004107241d1881604104000d54001c58034030802201400b002d44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 955392077 1250 955390827 955390847
    0x305010b030115050913020307120c120209040b27010f0c0c0c140301020426010e2e0204051914010c020d02040b030a140a03080606190c030c080703 65
    0x116903080c108508001d04040c024422803203c1c505103040094100420000e440800038240c0048141e010401805070382d0401c814401000240100c04115149007040800240310b900541550245030b0180d20068580c0504954030641004000000c0d460351041d070841344c04007941c01d00c0701c406248070518006030103500a80104880d82d000b0072031101e034510103940c42040150050071280c1d60400800c10820090f4a400c2070250003800146803980b102115490201c1c1e07000c1c0c00d5101c0000c00032031022040301b48955490f1207003250081840054140106210101d20b8800da5145d58551500c10b0300c044140d01a0303409410014103036940c0440606241c1c40d020100e1103a07a80d000d08500c1c0c0c4401b1540150075185410b5005492602c0b82001a02840080c2000f004410f8251040740e64980c0490300207008014003502d504040c142c007940da4100203210010242116104500803c0101c0104050000102e507808003410484d401c0699410250760116200001401c50200000e400c01056401002c440d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 955393327 1250 955392077 955392083
    0x80c0102011a010207050d050c06030a021c09050627062d0103020312180d080301081e100c090f0b0301060807030c090b160807050307050f0303071b061b0903 69
    0x110a03240d00d036a015100b0b50384659030340075030094042407209080041145400314058021690091016000709080e80e00c21184a0101940421005130040d070401c1541c2c50419880c0c0284900380b81e61711a08e07152600035002c600450f9400e99401e00035101800c44c0010b050b0070100355a554904070100b41780b000c85044030002548040070708000100111b80c4582d060303a4024005101c480c45220507651135900c178207480351480324054100d2295907560031080a11a01c1f27000029100c6d4074144241e842c05460040c004c10f000441d0550103c0d4000c0011b002e2100da11110022907100d420b15010354100045401c05019200640008a110a031040c0114104c411580d5111110780e00c0c101d0403421610146000c1000980c20070041041c4002013020b000c2c50303401061032807118005662440c1d010b1b400b000d002c69140e04086001c10500205100f10003100807488040e40c51464400402880c142114143c10914000c003000076050141c0c55110703810594510b0b241780e0a50403105001340c850902d0384001c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 955394577 1250 955393327 955393331
    0x61216153018080c010c081303050d06050306130308010515070605040f0803100806130305072d0b04060b06070c09051f030609140340030308041b030c0b180901080c010201 75
    0x203071080c0f240c0f41f2144103580c2402e10300c4482c5d507207a500300d43c40c1e8414102203551549502c0f006c83c107070380d0902c15140921410f100d9907002d161140b80181031004c05034410f2740300c0c040c03046059100d00544021180c401ea0f2150340050781d03540310328000f503031948200009008420301008020002c211f404c4003000380d8041200721207081d81d80d0040080402d684420003000107505000c01c500007549402c42c1503d1002c000210283c1c81680c015401e0100d80b40c040c15a102e1820200380001d00140c0d100d05513410909482441c50480c01c0d803100040c0c0c0340300c2c4c460b82190035514000111066000d40000b6509051030050300d242c6580c038144407000e80340a44041d956044c00000c40640244000100e4000551a00c44010001181f4030750301108420740c11324803114039808911800c0007241c40c42c050040d40c800e45954002d400c11741004c0110304999044d0340700d51141c0c420103102080b040c400c80701c00c44140f8a0304070381e074180003201a4030410000386e0b4907420840d00c03000071941010203d96140e01d00b00a03802 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 955395683 1106 955394577 955394591
    0x130f02211c030e0c01210902042909060907030e03040503160e01060309171b0609010c030c0305150108061216153018080c01 55
    0x8078001e104088200710780c0512405109101d00401030070f14400500c00686040b8001c0201406600d460750062140c40700768000641095003e0814000f070b101480c29400c4006042810b10100d14840c00e4921070340c10b160300c0c00c0b44a8500140366412680f6a4082a8001e225100e03402250340000c0001103800c1c2c9040140e03020038030048518100d550710740b01040e0382144040c3c10400c1054100308024001c00c850142940c100200200e40c140d95940d000a19202c040403c0507000f010f000304001c2259078032042d44030040c2c20403582c4040c0f0808410501c21401c41d0310441c1c03201821001c1038090301895104a01d15503020001030b05581588042011080c548940303003000c4851540703010342c140400f40220f100c4245c402c455051140e5829800401c21100c8618a02805600740e1014003c545503201500802c030303500b4044078240031140c3c917400c09140b1940708005241b800d41c20402 = true := by decide +kernel

theorem cover : BRFrame.Cov 955215827 955395683 := by
  have h0 := BRFrame.cov_init 955215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 955215827 ≤ n) (h2 : n < 955395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
