-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2608
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:25.142889+00:00
-- url     : https://prove2.me/submissions/fbdc88f8-a04d-4a6e-94d9-1865dae17578

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 468884892 ≤ n < 469064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 468886142 1250 468884892 468884903
    0x45010207350601031b0e0103062711180103080405012d050a09080105160516021206060306010806090d1b060c0905040b060a05070b06030c03070f03050d1b020f031207 73
    0x2c0104108030a40d002292225400c04a8568840c01c145c5165090a01403001502d540d03207596a0340c51a050901d0034140c01000420402d900050b5030400d415526403030f203000d13402a9038040c4107809810800280f03a058903808820580f83c01d03d0700004442d00b2141340c0d8040181240c406031400e11b007951030540301c1803941c03d80300c2d1a2952890000030b4500c1c42c09521600d003070b9051a081084100c1c40c440303000300c0c80b45542480c0da1141188450981041c84240300290817240034142ca0f80b40c031100084240c440c039021022114a6a2034000701c41c0c8904040d903460a55501c40e80656100900031f03035140020341d6060840e807200c030a11703445800c00c0d06c41c1180c0b0300010980d1004240414242030152038503920081d906c10b443c0c0104004010309900c0342c600046c022885660100e00366690520016042000c01011500079544400300f001e0b9a242030305c400c80d154422455030341d0525009214802c3c24506000078144104110340920041841024616034180500405001c0124200000d0301c10f1500a5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 468887392 1250 468886142 468886153
    0x1e051603020c041a0303030a0f11070303061701020703171e15040b06090618041404080c010605010306050109090905010b030f0c01020f0c150f4501020735 68
    0x2c9041c032044515049860181ca02e1820002025841c0002166081981c40e84005a03e11000d46904000c0c070355021b100200440002c0c0b0101490382c103801100658004900c881844055040003a01301d10078100d0084c0490a6103c8401c0c0410340780e00b1055100300d03040681d0841c40c5101c902c89107940e030110b80f4100b505400b0401444c1c01d013054420300c1003805099448a10b00981000060050b01801c1903482d0000c113600402031244e102c036003184406c18200d085c2590542402d280403d200e8000c580200d1840d1318002d400203031503200c0d00524089410685903000214117004440c4060420f03007405035041e64803042d0b180c3d80d91310200301008041710341c030020302080291607000900b8011013504602055015240a10a1360340b500420030240040121083d51840c801e01041040d00481e0300c44890100e13440c519003040e06150261081c0e541040502000c2c013007010060400030f4001010040c0180d02a0f641032044005030403268410000300303200c98010040105841d01c1032400c8021000c100d8118 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 468888642 1250 468887392 468887413
    0x12102040e1512071403010902030d08010509250509010c14100c0503150609010c0c0306051902210603010b06031003110a081015170606011209031e05160302 69
    0x40382c202c50080ca800c4501c03810010040c0d190301c0e0350780d00030700400c10400d58107450300b0701ca55402d5100c5440036038040c05550518060800241c003200c0b092041074011001d10b000034464800042003101008250707101d28070405006a01142c141d00300c049254141724441c9030b880301141ca444d0b2820207010307041c0300400f43c04c0492800c4905545150401105000040c001c0c4810100d50010724942c00d00705a5510784c503001d41400494456003107100240488941441c08000e0100c43d4200b82c1c8200c01400d039030404200e030000c0f00c204030300c10b40b0110000c9110404194009051404071a1381100c0014000f244194811000030b1095100303070740485900315840700810030480480f0741103011050442e607030082e0342d1606005e10703140c082c6007108084090713403004d885d045402c6482a010251611001181ca56000c020345180d982e10140c814a010038000c400c5a2521001d50246a695075450794510040c40e005c000003d140c044514981d20a108062080d02c850700001b14603080301900941c000c00c1561072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 468889892 1250 468888642 468888661
    0x1005070339060b0d0b0135070807060c0803070c05120d0f050a150b0706140903070209010b030613020c011b0f08090307020d0b060a03060f091703011202012102040e 72
    0xb070410a540285894644040443d00d05c810b0703241113882c003804042c04181c1001740d1142d190b40b41d110000c10304403148000c0a280780c0004220040d1440d9008559131140c403070a00781d41621141000800c0080b0400c00580d899200f0400345058030301c104200c0d101c11489621041c0142c00c28002082010340d42e400c4030460100c503004980c1c2005c281002000f1640c0c80b818010442d402601505e40726190000c0c80c5010400680c3c01a145c4d04c8181520201300d0406541c1152682d000580691248024600100d29050300b681124050b8000914696101008041c1c01c0b012f900480700a41d0595a2412507409809503d81c50140b40320481e928a2140c410300e8401401d25075028040e850300350b00600c051801a02c800d503040c46c04039045400078040d0354a140002c0d02c1d40326135800051145090000045100c0066000840541e120307503e01c049031401944800d0705030100744031703107520400f205120301d015501640945903030665032a6440800c0100741541810b981c080c0d407002c204003e02c5010803640740d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 468891142 1250 468889892 468889901
    0x20a03090804080d1e0c0b131a01081014060d080408102403020904151805010203150d0c0306154101020d030c02030909040b010501030b100507033906 66
    0x2175101006006808405c00a10501c0e0f00c03600100703070b4441d04012034a02000005402e070440d5200c0064118082c01043d00c03158240c00780304451551240381580450040c1070f020304c1040e400c0c0c4244403240c66175040c00b084400743d02c070441171f60400b43c00c100100380a142400b80d010441610100401c010701f40e410070f03100b1502e071050305100d900c000c0385092006a841c03008072a00250861001158171a99020201c010022001783c2d07054141c132401204100700043d00070f0351017100107501449501085200744450003001300e00041188648800a00000d00a5446504042513102c0411030b050f8944500511840c1c2c5411040c66042000c21100c91082e2040c101c61424043e1035003940c4030350b0804001070754405030850003000345900d0300c0c00c0c25440c920804c16900720601c002c2914005081c02d06194008600a000d0980003074101303c500c0c09142050b02c1c509002e085a0794449260800e980c0303040b80e003a0181d810720610070445404035031080022110b01113004c0c8002005400400b03451504400303d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 468892392 1250 468891142 468891167
    0x150e0d08090a0308060a080d020a110a051302071b03200612060409050f010c12060b19031a13020306090a0b0f060c1005040311060717010504020a03090804080d 70
    0x48215010402001d03004681c070741c1c40a80c10306002099031194000076000501c582c01800481c82050034030204198002080c4092034010403a840c01081c90209101c3c030f00c8031034003445421281c00d0075540c00c80740165004211060298241c4624041d00b107030028440c8802d1303401552452401c50594075090030803001c2e80304c0c00104890142c502540241c00e8520024001e142500c0f65689402000c10310a060140403845d48650f4000c00040403982c4000c0c108240c5024110035007840d107040400e0000c0354070704a40d0303501e081d8205150701100c5294100c000d044070345103080780000d801d10101c2c0c181e20303020b140c00e2244c500c02c000945c4030300d8198140060700e03100420100d8a10304204041f01c2540720307804004200e07039065500341da4800d941d214280c9401040180f000780c203480c0c4010401410340c0320388400743c1c403180101a42c4464441c01401c40741c4680300340700702c1e401c0c0c8502801000300c1c0c03600307130b005100758842428003043c2500030352141c09840c2c00030751150034260400404001940e502c540c840000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 468893642 1250 468892392 468892397
    0x608010614060d060e0c0d06050a08030304080a020c06120f06040920060f030f04020913053307020d090b0c0d20060106031b0e030a02010806010c150e0d 67
    0x2240ca429005036074501500c000c103000307440c00544080340e40c043e900728401130504841c44901a00780810b1041c115480030700700100c15031508401180300e14200035502d046641c254010340c00d686860700e520741164004603100d001c1d0f2041c1c0151143c02d03211140500842c3e0040e801600e00f524000c00303040c0d00d15000420140c4074a24080c0c2c1c140028411425552203030490010700d002040f01140031500300c2c41815a4034580e000e005c01005210190008481d110b28030a40d9440300507220810348404001d0616002403462300714180030f40c0308280595000c580b554500190744440311403044004040001940c1080c0142c0092011000307150b0400035403001048070821441c45c005110241e40c0e1100b02c0ca4001c4820400044010801071440c101c40c6003035425100700355000c55950f600b02500078801c20300362502c4124611403403440305005495490620758040c02a02d103030361141d1b004481003040240040d061040c680302102c0403441032621445400d125a81c0000c6a0301162801d51625400c0c2c8000001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 468894892 1250 468893642 468893651
    0x60a0e1510020f121b060c0c19080409020d0902040207050f0d0e0307030602031302060f0405040f05040506131707051609151a070206160212061b03090f070f0801060801 74
    0xb2803d07000030f180c0754a0201e1407155440c2c1c10030b18105d0b40710039885051481e40e0311500c010300610140180080c038402005a0803146404490540c3d90705002d10703e02c020b05110740c140020070201c80c5540003000440c20210f40003460342810f5002070100e8118000a507a07030380c4a96114030481c0070400c510013000300d039414000c0349801d80c1d500080e502ea0050100a0420703402101203031303800544140c400c403004e40c01045587c8a008000b00554180c00c548100c6201c1d9007028402c43c44894030340328040c0129005005050155940c251200002e0312015048a0205903100c041c410010840c0c007801215100d8000f91043d5512030046c0c00e0b080500e90003030f0503050f2401300f20040ca0a100001e0350125411900a0360340000000e038400002e02800002a4110a00050448629100020018030540300300ca000c510456103000c016524041158030105507880034501015102041e0040c56000b10108121000190100002800d0800360f61198984803c1001b040c044d1042c01c0c02a03030301809000d0001c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 468896142 1250 468894892 468894913
    0x40b120a0b04050c090d02120703150b041a060304020f1504060806060c06130f08070606051f120b04060807090902030d08040308041e061a190803090405060a0e151002 73
    0x203038880d66417502c0c481c020031105a0115210b22110280b0340b054101030f2540169242004000c01c004806103000007443e00c0c0d0a5032040c50540300c2e0580d2144900040e81c42d03c14032809110882c0d102600590b40203c0c4084480050390300c107000a058195158002500d0b28074040c0302401010f0b0140199118070014080780c01024000500c076580104001c0d01c212030708445040c049140e481c41c5a01074280100041d8a00078011103400450480f14140c6801c5483c01d00d01d0206034405541c041080c001404d018000000c00d01e075504041811880140001400c03681e40c82c00e540340128a034060010152100118001d52070144642400707842a0b08250015280550f00206000c0c002000101400c081e840c0c00300240f0108001c203ea0250301081c10001c01c5680b041c46030b00042d000204a108251000c0981440701200f4481000c98014400460504004030200801b400c0000c0c9100d8000204400014442076000ca00c035028844501c203600d4044d1030b01d4180910401700e183c1500c01cad94003260284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 468897392 1250 468896142 468896161
    0x408090916020d1d2b03260402031002031009090b010311060315060a0c15140603151302010c02060708090f041107060b040e0f0304050306070801120314040b120a0b0405 74
    0x82a4040448600000614031440250034880c00c04021250305800d039044006c041d00a9000c000d00707054400c4d00903c100042c1c0200c0d10640c41218029010340003240c100300c41c1e80c034a4001c1c40d0802c00441908414549a6000c64100c9011030360540d049504034004000b0f002c40041a101241001d841c4140b843c6468006102070701022602580252000542100320501c2500b1070407655602c10303202052041024500f10140940e1088040700c08030150201d6881d00d4005008802c001182e41e6401059580c0c5103045003e66200e1400c0e41406100c80d50340d00160394541c02000081e1080c00700580b511001801c0c8400050441000c600a034039042d0556003544d10642952134150b0300103408194801e00002040c040c2c41e103051041d040344601107022843c03000c00700280040c1c400a5045031802d5448a40444074042c0038410403c421317003079030100c0011a03c01c140c41805080d4002c1e50303515080d6900410b603c180e1101645051000f8180140100090180a00044a08116014019814074072081e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 468898642 1250 468897392 468897437
    0x30d050f0306030a06020f1201060201150e09070b132103080a05060f03060c1206090402010e0607050307080310080d030e06010b07050a0804090b01171308030408090916020d 76
    0x3003600a06012000405503501084804102913126105640380d50803400641e05070b4105424a102d201501000450380c0c070700c1442440d03020f00c3c6070544250b01a1800380c2000f0f10f2140032341541494055064003040f41d0300c501004000702c04003a55400422403402800005100704542da1a007041c4000c24000301103584003c151f600801050f0f4000f809446a41c009940c00c41c404124641502a03c410001c5202403c0007a01044205003400c01e09a940c0d481040b043e200e00b2540280422081c00514060342481000b50107058030907022240340286545480b0780d41c0d0400c4910031101000792109101090701070000d8100700b46241814400c00007107103852a10b881c0140a003603954040407840105101080000201d101c1d0844c032415030325920758010601a01d00842c10901044030040d844004504101c261441040004941d501c1c2068940c1c4144140e030000d00306454042080c03140c0f00782e80d40d4981595000c2c3d4a000000c178618204e610740642842c2c00e410b0b4003000e0001c0038002d4294624080b52 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 468899892 1250 468898642 468898657
    0x503041a09090109052d01090b0108040c0308160b0a1e0c14090a0f030503030f0c0a0e0603060117070801031502040e01050d05030c030f04050306101d061f030218030d05 74
    0x2800320380d60361141081e25006d01200c0040c2c01c8409034500003815001c41141c0b05042c0c54503142d090044440c1e0400550b4420401d69004003091954141007000c2403248014000704040400500203000454980054120054272103558461380d480305190400300e180a030b0b40c50031264480a12081c0c6a0b45006480c0c0609107a0b110300061000461103441d07542c0c00d8000000e000098422016079480b400e00c10f540390022640969210321350fa0102718000c02c0703241503410040f080c3c0e1350031300e41c035403c003003403091680018040c10b061140b40f0380440e030070f158180c581500c02c5015648881c9a0341c9181004c010801c4c00150b8214514410001804070b0050b224850b4107503038003501e1100c9030640d0384ca40a45140314000d243c100c03d01005c5041e40c0316402c1c0c680140221901107049484540341e50707040300b040c8011480b8004100303a00e56242c482508110400e59070049000301401100da84074640c403225502090030040000b9400518124085603500d0b91040d072500a81c000c014040040001400304c4c810440f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 468901142 1250 468899892 468899909
    0x902180d1a060f0d0c08100207080d09030c080304150b0f1e0a0e01180c0503130f11060a050a1d0307050904141606030509010902210c0d0503041a090901 67
    0x1010743d11044084004144040c01c001c0f8400060309000c920203d9601410200d03009503458003075074419900a607150941c101044502d401c0c600740c0544008d0030100c80c01c42c144400c585c46500420b4101000d544030350300407464140301004c01e00c0c014003102c1d0802100c92169810742c40c400030036103800080d02204842942c15a408448401c00150800302a82c410a4005440000480e0440b2014694030020090742818022580c0c00d91003919540011503050419802103024440032900f806550310045011b640d0300b11880a02d24089001503005400300c40108100142100800340c3c4980d141001d4103c50000b95803003c0b100001940b290300341e03c1082c0c03040801c8000714003031101603020f403044c03148810129803200140404e048800d5045100c0c49000c6850000011807030101030007a0301c5001e500a00c2c03400c8020010041c0b28003070600030060f400300c2c8514021a81103403600a5405a924056401907482d5440c00c1c42005a500b84401e00c00786614080c0002141a01d44845e801e040d5100758 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 468902392 1250 468901142 468901193
    0x2100314010b0c031201030311100905030a08060607020a030b1014060307030c11070f030210021c0f0e03120304050c010c050c090411060a12060911070b060103090c0902180d 76
    0x83c0c22510794020b00103820000324284c4000000c058124080c41d50050619040d03541d140c001c0341210040724203201000d01241c004104d20818540708c1c04a0b28bd03c0b0400401181c00e042c11500490560302040e00125000e104840501c901010309101c224001c01011582c40b54030031a0b0404a999800054548000d1684540540c0b90480c000d0460292150000b001c84161554450103c407511385184002e078000c1861080e400318051001c0749502e8030340458250440d0b0240311450490303040304c2c2407186e00704000c0a0320100400c1d40e0144500b540195214001540b00d003014103103107041c03581040826050208451000d0000340d000714512011403c00c1b20708176200e40e52820f0855010301140d6a6035441000051580015a08489101281201e0000803c03189032a402c944044a00008091003403040504c40500001c210802c01a80485d042c0b40108807030542d6603417180c1010316a00f10025160f0040ba003180040310011502c0c83e051000c4807042d2501d8450b4482e020350160790140e0300441e0000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 468903642 1250 468902392 468902407
    0x50901181e0219030b0a0b01020d18080708010510060201050601090311040207020d03080a05150f060c010f02031e131a0603011b02010207032d0503181902100314010b 73
    0x41d54101070401d07802034030340d9014401e108003c03041054580800c0700d03c451104007154121521740314080c0424010780040600442015040d920480c000300d20344010042c0050101342c1140c14440740303008040d044004141802e01e0b0220a81c0c80c400d5412a070116858441080802e80e070108218084907000400e100360541360303c2c049006131050500280d0031100c1c84008604259000f07192510419405504001c0ea40b68010214540401d40017456805030424014020314507000000b82900d000140c00083c0f40840c80903a002a600b08032100d810802400401c0b42806903146c0465034003070500c0c8244240d035a2256a6081c0c0c0044d0458010011440c00380050001d0300d00758428038000c1d1117100c0e41c421000300507200034080e601240c41100082c241b4004400c111803010035001c1802800581071000303016441003202e03541c000410507980110050749484030039000344030387c00210f12541c3c2c4424075420103005000c6200040f0340c00300c0805240020028401030319101d40c5045d0341a034843c0660700c108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 468904892 1250 468903642 468903683
    0xf150f0a0608030a050a0e1002280c0308070302150105061603020a0203151e04020f0906030a140d110318060d0f060e07020105460504030305090105090118 68
    0x1508840c0b001e11001840900050300840640303090020365444002e440001420b02c1740c40240c540040d00540e120003410020102002184c0c040d800042500342184006501c9030182c48086600a0310323000d00014901040c180e040c49a00e030070724101902c1901c0d40d403400700803c1c0b09209441c1c6105031940c02c0004070b03007014400d1110002140e0020207c0e07401c0100e03c407645030070301c0c0e085c2c42003000700d03111441c00320003150f0606030a03105680041400e000070149d5002e020300d40e64000d0100751706004452003000090050800c1da200700c0305481c02060703590b1000e84040e1403983c580b4980f140e190305c14045194102001c92010119820030703610781d0340722200031074244080e00780700b9081c1040d0350900001017030b000a030341111481440140c0c024410354440c50031081c2d0f501420400c2000e200d20b44501140c0006e0010302c00350341c00c040d89203e0501010b002040d0b00407654141c404030006a220010300000c042c3c01d020380b60300325084c2e500030818117070f403c140026201c01c2030100500c3e00012852035240c03040b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 468906142 1250 468904892 468904901
    0x2b1d0604031e2106050a06090b09120c030601030f020405182509110d0501050409021e1c0609030806030f031210030c06090e0a090804090f0e030a0f020f150f0a 70
    0x1d900f895802c00300f03680c0100200191850b40101e500a4202d0000094114400c41d800fa0880d00c124502c1352504d080c500600641230181c101c020168812400b282c001c3d61810030000d402140100d50101d0310b010725104210940d0700140c04c05089143d00f041c5076900490104410550344403c0e1402c204052440d4000d0140d401c080c5d004001e414a00b16080010031b40802c010410580d4000c0c0800041ea00c2d201007100311050118040e4101d028039035040c001210380030090b0656078006282100d0111202183c400d03500c000c40d000c4400a445a003040e0406400c041540c2d00480210003804c4070700c0c01d00c8852642c0e8018020441c1da50441e00c40481d52002c441d076041c8005e5a0000008070915031900d001a10607403041c0b02d408400050000064021400d80c071a030383e042035000c03084070f241902c0c00e000344c230103040001910a190341d620742c14041560401c20061201c0b041546500b041010701c41c2002c3c0c109103071100d8800c1c140d0043c0788000010304000c0c0000742d001850300796000b03d945803264440c0081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 468907392 1250 468906142 468906167
    0x3200108131a09070f1a03060105070809040c03060302040c090506031504060518010e0c090109150e0904060c0f1404030209100e040b060f060a020d052b1d0604031e 72
    0x110b95010510420030b00201d442019100400124495180d94501400500c0100c00076103010303000c14000300742290310034002408040e0141c41030328104410400050110f54410351540c01080d0f0303800c8200114101f0f4080e1440c002881e05042240b02e01d00710200d01c0e58070008015604c124085452908940d40d190321034805030102030702240c1c0600d00c402c410903c0d05028058403400016400005464120280c1110103025041e51403014030317482d207801c4224800c0d00280e6a0140154607281d400c0d903840f4401352038070903400342d10042020704070000d01a00340c2e61142c6400c002c0010480c4041ca20100d11002c0702c080b251305a407001c919aa540c000d0010000c8150070410001c41c414052109000306201c03480d01034841201e0103025110740104005052046109940158004802c100d1005020304080c01c00620441c4501d4456005008082c400108081c40c0c1079809607550003040058440130140c06034200588010302e40c5060030b4070003500c13051540122200b2016006c45400031184141c3c40d58812 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 468908642 1250 468907392 468907433
    0x603070305060a020306011106090c0d03030e011a04150b03150409050d08040318030b160311210f041709010302070606090b0f010504150e0607120203040320010813 72
    0xc0c1003030380e51980031790f2007594041d0018100c0600f20920410128089006d155075000500402d40342c4424010702e0703044504103401f4580d0390501d000c4001406c1c000c1110715407106d10b450f41c020340000b040000b11a4013140130300180b41c142505204a03500041200d810603006460702744c91b044064005406041c2da200010084d00808400d00b040ba5000215507004600c02e44802d1001c42241030381e4001d1035070700d210150880040341e000c550148810710519410b03182515001c2a030400148500d00d543c1e204034103c000d480c0c0c04098001c4880c81c03c10f03846811900d815029203490505032941c4c0c140c4190041c040402d807400080a40781030780254104c1e50398076800340042c00741030792b917000c900000c0c00c460507042c3c01219030700b4200c0f405601c524112400d482d00c010000c8036501d400e0308200c07110324055403007a420003000c10043e0b010560002d003801c110340c2a83d000703690310b0707055242c0341518040e4054000c00009039044c2203c0282e030004681540503040c03240d02420380e800c1d170908140b007003002400c039880b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 468909892 1250 468908642 468908653
    0x22b020d050a0203151504050402100e0d050f030c0c04050103080912100501090606030b0d05062208070b01051309050d050a05130608070f0207050a030f02120d03151d01030201080603070305 83
    0x14070317185203c20710032080150400b4105c2640d070103000a0b900c048070700950140030100b4001e8854007503002e40803040b030058143c1e803202c405a540c0615050780d070764022000c0d40c00071820208120040000c10300400007074509000319490742c0d40d0344149010b40741013140704000514200820903020804118052800d030024072444d656401c03840c00030555401182c0000e41460000022800e26070700c0807842c268000000c11150340c407446642c003980c2010703c1c8101d076048c3c0070154001040c296000761000600039a8074a445514100c20800300040c0f040418a40d2414802c01c0c5001c501c01041e129200e01042c00c0c05a601e50031840115020310440012114261030100c0220712142d0140005e44a628140c0320300103a4003040009aa07584482d124083d800500041c2c107000207844983c12960951010300424111108900c0b200e04002d40d03411890300003903440381c00c2d280e00541403200800401e000720092104900000b04403200d960f05000180c14425a100800d00da920204076482c0150b070800107492 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 468911142 1250 468909892 468909913
    0xa09080d0618140f01030b060303040e040606172b0c020418020406090605150a0216060305060f0105030708070c0c081207020406090c1b02040b0d0b04022b020d050a0203 74
    0x2070400301c151090507411880c00f011606840700803d101801203c620003050456840c540c2c45404001d0700401c910303010701050000052400c040d598090055205080c00300d07000341400c011088150b038041c1c0886441c0c2c0107100ca10380c811444003114007020024a44008040300c054400d840400c88594001d4000e881c050b1039890083d4044450100075100700c0d030074082c086d41e50300d9807800d8070703007900a25620440105248128030124002003656510b9030058404115022081c000e801e0010383c046004603032200100001071900320344414060700c00b42001c505506041100801c90312008045400340110b0510082c24840d91200b154002c04c4200d044407900e1082000c23641c40c64100e1001240268203188000c20f450025000720034010f8540c1e40c1d1300a0310340515450000202c0420030a80c0c000e07580300707540c05442d00d480c40907076001030150220074440d04003403040c07018603581081c400c1c20480d40c58913940030703a0f08260041880c80c1d0f0111481454007400e418024240400305400a40c58880d840050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 468912392 1250 468911142 468911159
    0x40f020909060411060903070506130b040e0a0609180b13080a0302090a0b090315040303180f0311211308010c080601121e023006040c0c0503030a09080d06 68
    0x110301c26072013040c440c50285821010712001740594500103a040d080314400780041c2c10018007405420420710040a201555160454080e42c05a0800d0007031101c42000c002020f0304030700550009052542c000c01c6078040c02c0c0294440c0071240035005000b180325101040e411045648102c4525402a035150307590000420083c0003580601c20007070203284801c0e00091140700c04400d131190030384040e000d0400d640504414400d46800100100e06065492494802d0300c03440c031099080e4540b080a25840e1a9001e0034050042d602c81801880b035075012554018030b0300b20a5082e56035074500505030360703115024003114650b400c0003500245010341c030f00003036854000e0384950440e020306c0c0c0c283c07110039552508a0145040d1880701081e20300d917500d241d00c0c8040e0341c03195900400600d9450b114010745c1c59640648110713000c5095401456520501080c42940d18143c840d4140d400f0039801c00711210070342682c0b2180c80380402082d0f0b0201507540d803824000e100180c8121508031503003160800450340c0300c1020713 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 468913642 1250 468912392 468912403
    0x303012601020c060a36060c05070f08090f09100506090f03010905011406060406020706050a050c0f0703020922060e0a0c0b0301080111180f04020c010f05090d0905130203040f020909 80
    0x80d0740551151440b03051ba18035204403d114000301001141d18980400d44407800175243c1c9074204400c0003030411001005c038011483c00038200d882020720039910182501088441c001c3e00040c00d00c1512804140031f41044400d000c1d40031a00306580040e2164a0ba03800940050f401c0c440042c0c1650030300314100d04000c019882402e00b9185038a00b03c10175100c02d001c1c031006018034007408000da407040600f0b111003400b5070040d0607030110a1a00529001440100d141030101c450006100c80d402050244110b180c0403102c50350190708182d101c10801c403034500740702d01c201c560000500a29642d0f5180311401c80203100b44200030b60001201c0c01c109a88040c011001e03882480b40c95125440c1c8400320074814a0b0741c0444201e140c45040010016010008001e6004541c0e03d00aa00c55420840000180701c00e0040d284108011500018645400005582810914046101080340304801031010b0307910b60700074541942034554016243c2d82c49240c10310081501010103136003c000070040000c03041c40047c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 468914892 1250 468913642 468913661
    0x12060306020909071e0e0d170309011b050702040f020d05070c11060405301006090f050906011701140f2d1306020913140106020303012601020c060a 65
    0x942e00082d40e18898210b5065004000b0b0400c00c4403c0c9082003100c1c1c6c031945100801d62030041c28011074813203980e241341c0c0700c20340108034100c491404401c0280c280000c0c481c10b17020300006000f080900c2540c120042c03052160401c02849240e40c1c2d1800d11403480581d0540300c10a1b8030041c00c02c202e05002e4070240003404510401c48121070f80e07140c40f042500b40340e410741c1e040342d0380a802c4e5a0761007230046081c1ca42c0c58070840301c81401c1c5091020090080b00411948002010889001491a007044c00ca17105440400a010420600b040103000e59800700203070850460b030302030f005014440c0100c0030082c0500f0a041070240741512200034004444280c58296020303040139068118409080c001680d0a445070f5101aa07100f0910300020341d0031244643d040f2001486500300600d080841c0c400540c01210096070071400995079040312a200405210341c60140c2418002541198503002e03030b400503c1284600c2003001101240d45c0220b142003501962044000d42d070076103a1510b064201000140846007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 468916142 1250 468914892 468914899
    0x1090f08120a0b030703171603030b0f01090e0c03060d080403032a050a1b050904080c071d01031211100e070b121f0305030c03030106020d09060f030c120603060209 72
    0x1002c1a11055a84184050400d000d0081c00900f4a96128036508001a1010882800041103c01d5402c02c40c01001000c462103514001030608450003407180080c03000e1400d90604c012010b0610942d0344024100343e100c949400c000743d4940e55200843d00c2880c0f00d400081c00040007050110425401c00b1800101200400007440c01540c100c1d104002c007100102c0292a94208001c000c0c0801c081240801d180c4206612200c0115512700101e1134902040794141e0f11201c000c1013401c01c140c42484240c004050041c50002517070708041900b0320148040c03100a2484545980d80f00301ca5003e07070b07003071340740303102c40c80d01760355000544130f583c04082c1c044400002410b00900502003a242c0216040c0c50b01d440c508841d00b81660781d9002d00644c2003844155940c610780c41c0030000070014008000418800e00c1c0040a03585079498520701918050388072524134184407500b41c1c20b02000e0b5000740b003481401080d10300443da01d034900c003040c0d5200200041c0071403010300307000b40071090007620b0300100401e900a5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 468917392 1250 468916142 468916177
    0x501021c0c12030e03040e04060c0207050315060312040608041a100302060d02041203051201120b0f100e0c1b0105070e0607170d060302010f0e010f1101090f08 70
    0x240c922065203214808804503005007440c80200d481c00003801080c50321800c000031440304c04018607155811551089150309131850400c030030003170107016054254401c0c3c002003003220305000c006911941c1441103508505a442c0000d81c4590301040402051240c0e03001056440703484110003410060222400d0340c0016807c0d41d44a101c4842804a52003401030b00a0a444941540e0800c1703059404020941e01c80c0b0780a06c40890302415200c0c64168080c884e84449649504104420a9045050f405040d202c2d089403403030404202c2c684800c43e802101141034450f25074a0503150700d001da20301d0700030800c0c91010703404001c07801c1ca0140003480745250041005801d020b10610160a8030030440781c2e0f4000500302e55110116081c400040e2044621030b1044842e0001000101c10254021051500010f82ca130340d002c0055580041100c12400000d26154101441060019021030030350981c05040101945031096504000e62000e00410707448101e003903011080342060150b0b50015405a81e0641d01e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 468918642 1250 468917392 468917413
    0x17131406010312030b01020708060f010f0806010e0c090d14100f0605060702042d0203151c0803180f0312060102190305071109190501050d080d050907030c0f050102 72
    0xd1054100c2c0e40c0721014262040507400100e014050300305010781544950100819070b8602484980c0c400d0310b201480c0340543d0316000881c0700c03240c2c65502c103507595000a40140400b818144e2156401140c240089a46015500200d40340903000e1001030046115903000c25410755004c98508442c0180c0d5006000f840c0d140801001114140c2c881d190b0300180406c0404010305040d0081000e41c91681d07060094010700703008079405441a444032440705913000040041000c040303420810703c52016a042c03c2030303c0008180c40c8070a290508086c1c01d10601000255908075004540000f00920200b5105441880484c259603500515401201e20a4010000d08154030008036101c56404004030340110300c105840503125640252000d4401d5545c1200ba03091540300e02403480c4c0902c1030f00200f86071104001142c44112601a04060301c5101c140075000080759101c03045d20141c0306014000101904c1300921145409043c0d0b000506403038036031900045aa0400200c1c008540c4282c099503291600b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 468919892 1250 468918642 468918683
    0x509060a06020c091f0e10170303040b04080c0703050a0501060504050709120501061a0a09151706040e0f060403080c0708030a0c140409060911090a0e071713 69
    0x3114060301c00141d0212940c01124a0108403860300b0851040d10b440c10b0041c0b071a14161004140d400c03c0320b031204540309004114000044010080094031744030541d4000900d002d603120300c009000a09602d040001050902101504440070001000110307608181da0380750040d140c4d0607015054800d0752070a0b200140600b42402440e20070fa21a582e0507180300c0c10400c00401c1100c0019003a2002c0d9655900400e241d2407508002c1556102c50107019210604054000c01540c101d0b000090151015525840c4858110f14006003d9a02c010189504d0340c0e050040380061500520b00c0000c1c0c815501c0d00202003a0209803640190f0181c0d82d441181e545401c01003450740f250000050100108200194030a14180e00203d050740040c613100ca1035191310800390b1040c0e04903401520480f43d03903040c1044110350610030030305080e0b80307a40c420b070600c002e21000400c1d41c07070b8a20500c201c03035240350300290700b10381705082006112001000c044401d040a14000d5070110303024008441c2c500910800044011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 468921142 1250 468919892 468919909
    0x712060e0606040312050c0105040b01170106050a06140f04170f0304120303020c010e0d020304080714061603020709140717040c0303030e070e04050d0e12030909220606050906 77
    0x42c1001e450719103141c0e01c20910407501104002000f42c01d220720241490280a502c0c002ca016010000e22075042c0288018494000b02c41219281e2504000300a243c03034104041d0300319141401e105c031a28803021065172040c400d0040c050024500050040b48542810381d50f845a00884411540e0711000398032020780d60300c143d002d2820b10b007058020301400240b02e0340040c0000140c180000c500200484241c1d0f10301500005200090382000c01c050040550800106e4006d00700f180d1001040392940300410160b220341000d40203500f9041d0310300340a140c02040300400412502c0e4041007480341182c4801d000c0c1c0001e072860000100341340130360441d0f51804175080340200e811041600c40ca0b0318580c0c05030020a00c044e1500030728050381100003521a002c04195114030300036405000e02004081001b0000b90041e41564032801c0c2e0245000c0c41c52100100380c51010b0b4003038502e5403240d181c00e01083d03144860401c80140c0c0c0c42443c0515420444503030441c0003181d609840030400c0c2e0311684100324220 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 468922392 1250 468921142 468921151
    0x613081c05041409040f0b04030215060d030804022710090c080103032f030c03040306111306030b15160c0f1503051f080f10060b12040303060e0712060e 67
    0x4001c15000f601491804010198010748a491059503200082d40c0d020383c0c0c1d50f4125170540c007582101c00b07030038480710481540d144c0c801c00803076420082c034183c3c2e80e000d802c0d6800604064047e15500c98402641c59000505034490780d01c3c1104118149092102c1d07115004050103a4840d0a080c8900c400881e030240d90501d050329899100e81010710000407100a0380718140d40b400ac0c44015018103005000e0040c0300074035040901c000550b43e42c0d400c5060070010743c1c1040341c0c8420808020040d1002c83d40c0b240246d00143c1c2c0503850040b42541c510700006210f0b44202031034450412002421001d00105ca40304040014070038000380031829941e44001601e40310a1143e00300030502500820301d882d1203548016400031a07240388560303688440684030700c680c41582043d0f407940c6c000030904110a008020308080701c410380360188070342c80c20303c10011114003511041054109102d80420200360094002d200504450030342c0f000d8920303109100415071049680485101440d1160224000484000e43c0d07219 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 468923642 1250 468922392 468922409
    0x51c05181b09040318050a060e03010506030c01021c27030b060f06190c0b0c07052e0c020c190519050f010e0109080a060b01030507030c090e060613081c0504 69
    0xa5600c0340c800b17503203010251810400d281e01e1180085003130341d40d1400301c4016190a035030301ca000042c040103050845001a02c2248a0340c0702e0004080e4a0382c0c0028100c0c1074810000d0840e004081c07548040d1688039070300101d144083c160b1804d004078506203075801400c83c2d0044c186260303d0b40b00c6409000442e6511218150401810000b89403410340d003200c1d0076100901450103811050854440d0b0074020025100045031000004001c018003070108400544081003200b9a00b40340d65842800c3c1240e03044005140b03246480d40c00300000f06000340961280c1c80806011003e00b110b91680c102c0c030703074083c40c000e80e8407481c0d404071100e00095140c10f2034801d4400c050070103581141404010342d5200300d00c2002c0da042200d29100443d0804091080f0011107210310070202d41c80c280f60002600380d40b00207140c0380415103030503041e110700b80d80205a40d040301e403000441c1c01c080e1035590200d180c0e44104001c0c1ca0342605041000581c010002501e40301c240f1144406a80c040501c8800300c0303980c4030354413130b9148 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 468924892 1250 468923642 468923659
    0x1d01380a0b0310170f0c030d050d05071103030a05040302010606020712080c1c02063c07031b0206060f0301050705030f190c03050a0e070f0303051c05181b 68
    0x296411903009540003000e296015101c10f650f03d009024508131030622a1490f000700300c2820110508000350000319401301d001c0d080f4100b2405008241d40146210440802d0b04c910100f280a03001e003052444640322801500d9880ca0010706032005017405540440c01507103802070006056101040b15030a0790365405603a0030000f05900d81000c10b03000340c03140d80340501821154608041000c01012855200d80e0041c10b400e00e042143c010003a0081c08062016004d16542c031000d407100b05114660004102e02c105402c4c0c1c69204003180104800d0f40808045012560300741a034a400080c16482070004444041d01ca100210a05090f900192400000b0803818008100c051070402c45c1c06070f0000750424001c840522010b0f9110a540e845200324012a40e00ca0078400c0036030243c05420046e00700388000b00740c50351900781550344000c0e40d440003400f003100206500803140e610080c0c0200549081a040c8034500700079451403281066050000c0303552003100d66548880c100c100003220041d400900495 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 468926142 1250 468924892 468924899
    0xa1406121020030405100605030d09120f0803090304090515090f092b08151507060915020322030813141006090e0303010302131d01380a 60
    0x5400002c010740d00c100000b145a03003640d000d82c2c01440c4a180564010403171845c0118440003216201e401440c066000701d0707007543d0f55a400118010840c0d1001100aa0450309420f0001c030754200d142d001413a2641c00003d00442200020140c800d54000c800c080110b41c60712607900c43e407011003a50b6542c1018110001440c0c0301d54207603c00341d011810b20280c58400f035049507881701e80c0b0742000401c2c0c03c030180700065a030030a81c0080010781c401e102e20341e00d800040340d200008501c40001001140e45c8000021801c007048601c0c1c001c000300c10340c01445400f060321101d42140103508201d48202070071240105a40e00020b004072800c02058241c2c484480503102c04078021480c48480c20240c1e9068035610026030b0f040d404122101d02c07a11003003000648103044c4036010082d288001174000c41c2d030f170080c001800982c0d24030b986206030480061000800d178061315861048058442c48030300182d40381c10f18031550304100c103810740c0303140c0c665611070381c1030100d50301c0310581c3c50251011603034018400d140b050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 468927392 1250 468926142 468926173
    0x303060602072304020a1e3519021c05060102160f15140c01060314010606020606040906140403031a04020f07060b0402040f240201181511030a140612 66
    0x410403000685040d00c26401c0c2c44000000c103000c00040a0005800342d2310b10800043d0200540165a82e06914603410070607e10707002c0340e0448084c10900ca00c20712401d21110f0843c495040302e0b803101d040d408402895400c0491180149001c4810078054003a4092043e00e0304800c0c1b580c14140c1b4150540610f450b0b0800101d400d82c0000c044a50b0184019841c9061500016001030013001420b440042007507411458850b012000d080c0c0c0b8800a40e04000c0140481500407400d16400751003510f0004100300542800c9000e000c0480344080307150200d0091000740b540c10b420906030143c1421911003080061400d2004a1144240d03015400304103000c060002030303964000c0d184400c0010000340c1016140c503003803500080c1a0384103d81680109012032446d05280310301d0503c0e00010700080102400355041d598940d0400140142a000e810071f02030081da01c00d0348004540301e040d42800c2d40700d28140014000400500112101034a0b410b00028041d103082d08400c0c40d14008a03024040c07e0a003403201c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 468928642 1250 468927392 468927397
    0xc08010f03030503100308040306090201090b0901021b150a0908070b0f0a031508120703020c030303010f05060c010f110c0c0904020f1e03010c08041b0302100f0e0409030306060207230402 82
    0x107485c44845403900001c0880c0d0308401400141d8050280000da0b03215501c00501b5250041e44106083d2106110005c92aa0042001140341d007000c2e2a03070a141c900c20002891109030303075460005030781012592a007015440450740060394071103030448205546407180154036003d01d000d50b46960000304190040c40c1d103c2c2c1c102c100550020010080010307182d00700a0b05100401c2d11840c0c042c140420860300380366041081d800181401d401a6246505182800c20619624028180a45800504c001b034203034007584005848084103404101350010014180d02c1d40d070205005107803030300c140400659540751020106028590040501c40ca41102900b885003450012840550100c0311400044140c0c50a0040c111441e003076550358450303031030680f400e400040b104541001003916081400e2005032622640c000248085062542c60f09014681c01c441a000c1040c415412508180100c0704254064100da0180c40482d020744000c95203545c40294103800e007a4410300740e603a40f0300344c0100c14103180e1700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 468929892 1250 468928642 468928651
    0x31218030403031b050d1d06040e010b0702011e030501060915080a0c020709050108030912030c060c07060b180402041a0307030204020a090503031308060708090c2b060501090c08010f03030503 84
    0x4446094404e40d1651030070603031020340780000f1032946441503d0f040701c00c1426000030001140c4940c1403c0c1001c0d001422807074140214080c091002411341e040d68021002c0030785070f02201c10b28100c240300d2400b004016010030700c50f56000c1034885d00d02140340205041d0020069030140d44000d86523440310500350141c040940c40d01c007507006000c0d000c1032035041070103800d0181422900450b44c5015090902c01c1c41c012000e41490203030403d01000c600ca620200b003e0780c2080c00104d42585900e06400d1040c002c0141c002a25400a0200c01c41041e845c0c04076030061150f80225000c01c03406070905001e07039410108583c2c06905401a10f03050005107001e60143c1030201103842d11600035a01d0300f0100e480c41c1d000d90069100b0408103041040304507001c04c0300b50750041c1c59240400050802e824003a90310f4200407042445000380ba07440c2c03002458500c103854013080e0020100b0a02d1041c5003000c5005103400c5c01070002a0b42002e80a204403405030240e14100d9a0f02041036a4071890760f1000c407542c0d00041d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 468931142 1250 468929892 468929927
    0x605041b03030201140702070806010e060604050414090c040b031e01020d0e1006060e0f06090d080301090207020315040503040b0304060e030d020405030c010305061c080d020c03121803040303 84
    0x803220310300300601000c0002a61090700001420410a1280106000028594001c543c40540207200c81480400c0007811071364083c00c00d500c41e07219034002400e540503a0f041303242c1041c90440288000140d145009000d1100d0b80162410b0050b84e00c140821703100342ca011035406910038111591500d10301c008121904c500c01d0001030801d402500b5980035a44050b4a141c5a91f0108a1800c4001443c0c440d4000410142c240719500d0351080740881c170807180113598144a10b00c045186a8035494089045441550044940d41d5960312406090025040300b0000c0e03000c2d00c81e6000704100d140640b0140e178000c40c0c114000390300b82450b00b00c0e2010f80313070310060044600c2c1d92100b60084101000304007400034a55001f4000d0380741c90030441403510386070300380c21424101070800e024000180c941c014021a6541181c0d0030a071105032a0a000450f48103141d41300b13901520000324181544400300c054000054000192052512101c9000d0f01c0385000d002065901d030020082000024000e4036510720302511b14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 468932392 1250 468931142 468931163
    0x1706090610030b0616030801060c0c05011101020d0c0513050415140d1202070515340c03080c0c0a0b0d051e070809010509031e09180a14060409020d060504 68
    0x94000c10b404d034000e5030f03415000c01c5e40c41c854141056000350041e8003400c1c1c103140c20300b2102490b44961540250610500d81805040d9250800350b110030b4044520201000c803040c4040c21049074005c146501c40c206800c0c1002823080c02144616080c0520002d0620012114144a050100e00c0000412491146c0c0d4401c0728010b4100000c3c03400d14641d5846042c0d50094042c451a001c00d0049051042498002e004c104010409204801e4221985010320b031042c01c2d280c07a00342d43d070f0a0700e203607202c5c03100034050040c05200042001002c0009081010001c07041d50050f023040b0f03044c444000304074010301041c2c101c144000401005141d11555110131403200601d4a5500c03103000c8900e000e0140c5a400001d202101003001a07602406800cad00110385000442c46c0c6a922001e01c40240c5100d82c440c603a071400001c080d407403560303523009e240300803240020300302303080d003407404008000702140201405031515400000d4218a81071150451094000d84043c081103401d0351120002d100c01042102d00144a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 468933642 1250 468932392 468932411
    0x602031003150b0301050703061212021002040905061203030405070320060c011a0109180e033f040308060d0204110c1b030f070b0a0203040302031606170609061003 72
    0x10300da10b0009050440008202c1e0090b01071609581008180310f092505180d4100310040304216030030b04c0c1c00c1d00090070a500c0001c02004905003601100325001e1207001140c0030401144a0f84402c0c0038440c110f034140308070070082283c981c5038081110043c0441d005070a00f000481c1e280c8007403607800792502405005d035200c81000150560801310107500260b6454082081c0d5100e803a052031b03200d003800d0030030303220f010300d003011541d400d1101c0c10003070081c2529413081555104040040c1c4560031f40e00100070031140c1e291400c11880e0008142c1c0050480385903611038000c40520042e46000745d0b09070703440d034905a03a0b44003448034005624004070380241d40c90122000b480c008102130300b050142c1602a241111880b4581e001069aa07403501e4821342007100e081c002c1c0200000d0b01d00c2140c480c0314440f03442c2c00d034042040c0c0c00d500072680301a4060040019070310100040304800800d40d25035403101005460460030607420410f04948444d040250280400c3c12460200450b4024504038500171500c01032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 468934892 1250 468933642 468933653
    0x9050306162a05070909060e0c0a12020303070501181214032706151005030c0d0b0a0f0f0608070f0f0305061c050d080f0c040501200d1e0c050601030602031003 70
    0x20317907004032034050340c038410030040154a008080000d00d030100204280a070020000d002c0c410144a000f04042c450100c000841d2028001d540001d40c00c913000300402c1d403002403103841144a4044c225468032a89a140016902a001958a40d9103510000d400d660fa8400303030310303401d070800680d03811620010310b250f01d10702d1070070814a48205908400c856a040711441442560010490307007109110f000d00400000309041070a460110440c0a404202c0b180041c0104920700200e0308480c03030001404801084a80801c043d030301c2120501e41d109122035a03000d0044a851580d8070154000410071100320140505c01e0300440e410800003800f00c1e400c11440d401540031900100d5084820750404159003075025080000f040d44008103000054141c58120b41c40f024511450040c141407240404030740e8034204124041c51541d42281d030031a41c10f90503c2e840905113202445401e42091180510041c42621408810142c40e034020008d18450f400c5070354a10103504001c1003145030b15114500040401ca = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 468936142 1250 468934892 468934903
    0x50906310f1b18061b06091406060a09050433090c09050a0209090c032203030f060503120a050c030c0102070305030403082202090415020a09050306162a05 68
    0x14014608008940311000b000e0600e2042006880010304011010045a9007180c04411004082c01308001d9070b2220f40340c5140240010040905804104155001c581d403000620b103014200480390110300c4c0e5a1500b411041d101d00b2500184968080c0e02001608600e42c0d0310702c032400861031480302d258450b100003041201c001001c152103024182d10208210f0800d40f0409800c090fa0351401d500c1e01c1c1088021500070302c0080c29031982c9240020014650843c404404201039004140c01c00866645040090103041c0240380030110501c4d12400040500e0300261850b1b4070304a803200709040c49234040c401c0d146901b003204008114041001002840e982c02e100506082c3c1c8a038580c40d0f12410b140c2401091080c00504644441000c0a010011840e240c02200034580e411a0000d18554071403500114a01103400030246060000c102036260942005c06841500c00541c202c806030350302d03000e00150845424540101013184101e04010b80b1811024244070b07081e43c0301d17140301d06181695403103242c00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 468937392 1250 468936142 468936161
    0x3050720100203040306150806011206060f03030806120703020f010e0f0607030305161103090402180d0605010602011109100c030504030c03080910051c021819050906310f 75
    0x43e0000581401000014420a00607000005602d02c12a04048046684000600070350101c0718504140c4001c02840d5001103018014400041e50015920724001c1e010140a440c00c61003020a40d40a54010340300148600c1120740003840981c107501c0050041d94194400e00700740b40c01410403d11401c0544511000740b19040c860340c2c00207601d190156a21400405142080c810040848440080c1107000400d543c44510b0840740140c3d6559050380c180c5215840460b810340181111403140148141c036400107040701e21580084c0454150b48018600510980099650004407107050344011442459030f4035407148281030082c5082c0c0c5a46a11045d04031541c822125858006452041400d240800c080700840a090240c180b01c04080344504401100031840082039001c10400003146e85031140301200c050262080e2112030000221801426803030003810b0150b64020045405400c0c810703007805250740c40b04003107010050b079100020945510300c00740e9003020340c940c03002170a80f06d0300d0f03c1503070b414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 468938642 1250 468937392 468937397
    0xe010e0a0303060f030f080d0b09040303090b060a050603010909110d060614270721140606090319050a0c06030902090109061404050907030b072006040305072010 71
    0x2541292030020103a41e00d6400c5400c6104a1070703c1040001c0c21b000c0d500101c2c690281c000b54941100c10301a41c000c04031103400c1d03075000c1092002d00041c160150301268940b0300500c9000703800c0c2d0350481803105801d42e030b03c80d0a0704800c0400041140346411b51103c18641d1203183c02500c0044aa400140c000600080035262140d035407e00704002d003074981ca40e10400d14142c82090b030010030440240302c84010b511803507203624a008005201d070307032107007450410721045089012000120402c0b4a07004001c000c1c21a00b100500d080420464a01181a15404100207005084603504d070060039941000030b0208580da0310072030714940005182c200c20740f0b01a08117550300003036844650040068006040e84400ca33030f00d141c400d040c04414800400d55007aa0000d88000c540d6440340d441642c0360030040d07030004d0b20404110050200c915400480b504132041c00c0480c03408648559841140c0302e4600b0390b0000c01141c405c0114000180880c0314100745d0b01715000002c01d240f081c05001c80c20804104140000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 468939892 1250 468938642 468938653
    0x2704020720010c111c0b0a090b01050906060a0f1b0b0603010b0405090c0f030709050711070602030a171e16020f0102030405120306060c19060b04021305130e010e 71
    0x401507014035200120002d1804600101c2503880f11041c5100d4030007064000c07030000088004e102030000c200c00e040c690101a80d00b141ca8010b40d003800801099400b121034045c4c030b40001030340f8070301200d6442c00b540009000910340b00e00003000ba221564000024002c1c00315440503c50706107480451007009a000f800840000c4c903118080508407032118010310711482c904401d000c0301d41346c006002d8040c0c0301d09032180c1e03400201940c0000d1411038554411990305041504104406600001c002c0c2055140400c485070320741c0b18603050740c480c010040324400242030845500f04942c04080c4040c1c00c10341c0b60034085903a1322100c02583c0500012a00f83d50099401c0721075400e0103074100120f600b1103064000071401c500b05a41c5403a00c0310000320484208910203c003080059444038121502c3c1003000c000c440100c08208020410700c3c0d5200c0c0305031803203440c07c000100b0504141c0200c4041c1b10040100f116040d0402040007280c010304080468116030b034084a0310043c20920900c82c0b0020b40800811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 468941142 1250 468939892 468939923
    0x170c010b04112b060b130801150504020d020403050609150c040303050706020d02070218070212180d17030a05070212030702100903031b0c060b0402070b0106050a17150907080c27040207 81
    0x81241c80e0687c0481c0650303150a0214040c43c22036606101510701c112400340e5204014003003c00039014039007020b04640254001c5c04407403c00064440c0d2048001c203201c0145a03206451000d00d0f014612016022030401c00402001039010790050200800c8080010b00341082ea801280501e564080145903464002d01030007400341e010480340003182c8150030300910b4041c25021030184040706c2d841d000d0003842c0130360501d8100840700c0880c12030070048403811902c0303140080880025240545605000d80330341802c0301c641d085c140d003c032840307603486400408042290001c000010900c2480a40400d1340d6950240071028480c10190fa80300f18a540d450380350291800c00c44100e84140b13040ca03100e03a10402c64400080c4081c4411030440c0c006041c620340307624071142d09440001d0340d14000d0601440301c0302040ba00c500041c0b05100c0500f411f8856207848ea0340d000c42a100550269004206d0120a0200380b8600c4985542a8150007034064119031020440d0086020780c1c00c800c0d422034480c8524003950707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 468942392 1250 468941142 468941167
    0x100b0409020a0914010507061a06030430091211040f0f0f060f1a07020307170c04200a0c0b01170f06071d0d170c010b04112b060b 57
    0x1000d0040301c2c06904c1e00c0d600b02c800190081c46001c00052003282c82d210801c001c400d250001c0e010111010b03007503d58a00e400d1805c00a01c03503003080da00f200d032022400d080c0702216912108007008200358a404501034205121021441c4074004101d4480340f141805150b5501c0e6405a045080c0d4a000e0100350707002080c000b0030680f00600e8684078141d1500c4070800c01d422081840d42d0480345407414205108101d181a4a01885101c502a401d44180e041c0005c09513010f002d07078400c03c0742c1d14003941c0c0d4130003c1c50200410b131015880342c1000d1084620402410b03204400041c500200c0b90b0600c9007402c9655500c00e000b0500c264014500c0c804e0103080058240024824040c903032403401c0240c0590325041d0005400d03d500360034550020014110040d800307894510703204d40040d03005101460701c2e441c20886807141c0e0344200c4041501c2c0d401d2049801c518103181c09203402d1040307200006403d1812621440410001100c542100030320b0b5503000103000d5a180c0300c1c11010384002c880c0181d65001c0d0b403403503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 468943642 1250 468942392 468942407
    0x15060e0315040303020319060b032d07052b05150621060d05010f0b12030906090f0d0f05070303020601150f0c0204290915090c03100b0409020a 63
    0x80c003941003007481c0d0040c14000051240d00c02d92501300180c990310b0702d4000e104280c4003425811b03006880d201010884100c901c001d54415000c444014100011150780c100c00c01200807100840800c894020483d00ca01030b601a2041c9500e100c1e1006018000d4003001542d0403445020311004c540e21310910402c9000010081c400c0041610814503249040300e0b408032407c0911071155422094102040c1305a40301010a902542c22000a029800a4050500c000c0200c030444610500f010b0320300b540018400310586150890003030115041c001000c051004040f0343c485d45a601280107008a400941b1401000484034001e800030701e905400d624000e0314014040e0451851662082c180d00c40d02c591240a03a88203038502e00d0300348400c0600f0301c08540075200c0d10629800c84400340b1198006036078205020191070004641f17510168580440811509075a2418240c200700107000158003141c040c8000c5422003440c071002c00a02e5500c000e0f8041c40d4105401c824038030b9400141c6070300c005a00c40304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 468944892 1250 468943642 468943667
    0x70c0509060d0503040603050c070f03320d051e10140915010509130528020304050303010e13050106060c0302010b010905060415030e030a1e0203030103022d041506 72
    0x622554600b49a01c0d019940c2c003841c880d103010075403a140010011035a15050350581a8040032a8584000034540944040e00742000158010303002c4845140b03020800ba4816103441c40c4070201858000d40000c2d8502808000b04404070f080d1350031030000711099000c1d5009115980f81c2d80c001855604001c11011602000227555100e0104002400302000c204060003a0a000909216560300c2540012441120200b00c007200c03810b1600f81001070355a0640d214820040e80c03031000c4a070346001c2c401c441003240019500600035900a0005000d42e00c48113100c60f4008606004240c104a0280c0e109030030f54210340c004034005405821a84101502406100701c0c0040c2424100e0310141001c01240e030f01c1c042c034030410301001c104000d101003090090340400c2c0c951004100356039803130440c3c10010b0000c1a400650ba4203100046c000301402d00e10100542c0e041e80c0d4010408003900ca101075090441c0300d64034101141519103050f055070180e40705e200303401c55400800110070240d0324107080a42147d81096 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 468946142 1250 468944892 468944899
    0x303060305010f1b0806130218061b0607051c180c0e0711160501081023040b090f06060a0c020a121b150c020604052d010c031b03020712050106081204050d060b040f02070c050906 78
    0x115030302c0c565407050144d107102100160001000050403001c40d0d2034480c0708101402050403110003003641d16440700e031144500c10680380e40d0601d507a0910850780d038503e800d1801089805101c03042c0f2407980f0030162030f5003040761165550007144c4c4a214a00400402019402c1403410b0703009000043d04260242450380b510469400b03031a880e20105500040c04000c0c1124450f8030300244101c031443c051400301214036005810b4801e015240d00019103c1c845035002600c164a2009004001d841c1d036840b050160b03495112019110b44e0320403416a00d0b600000c030101d07402030051002140704e40f180c6d00049640c0e400d0042d0f0100035800e0250540442c2d60412035541080312154460012a4010081e00c110b0281d1103910b50780c1c5181c43c10101d007808501e400003800c00d03e41000d00720510070f054000c03500f03841c01141518802c00c100000c086980c8624801d07190800070704030141001c140254042ca2440901810125810441c0328445040342c4c80042c04451809240505100700d003850365040344e0080c400d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 468947392 1250 468946142 468946147
    0x10f0b0d020609010f052b050604090525031502070c0b0405010507030c06020909010b07060b0118052205090307051009020a0308070303060305010f1b0806130218061b060705 76
    0x1a0045072281c0310f600103160601c02100d0328510514441c0d4100c0f504c280b949482021187c00e24003185904c1402c20460f00c4d101400c000106400340b44c180314184030280c4c024001c2005403405001034000d03401000e40c103855454044030000124180c1c0e0b4071600302c2604000010381d620160725041440c101260007011407240c0a010038021a60000101c40a940d014188150080300d43d10f043d4010b849a18546a08000c00074000900c05483d03902500700030384505d01c1404195542001101c02c446d9001c00c0c8410305400ca002040700f41490b15a03400c1c01c582c2c5030740a50000304100300f9401582c8060b40c00c192168000900740701030040c00e004075448108842c0c0280264403041e00002e107011550700001d0f003110800114441098003c2c3e008900070b40cad210000344100750f60380c01c60704000e2641e0030045030150185051520181d00c61410765201d080000e2a1b2840790406e1000c0340c00139000f06441c0782110001d8400700e4100d40d2041e01501034600300d401c0000d41030420f4801c0c1410300134003510800900509 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 468948642 1250 468947392 468947419
    0x50d1404050d020a12050706020f070305090a0b0a0807030e21090109090e030307260c0403060506040c080c0a0c02060f0a02010c081003080904141302030715051603050705060702010f0b 81
    0x2e0920445c00120340f4103035895a04c1420280c0080c0300341d14007100b03540c000240e88004c0540200c09004036403c11111000a607036940c09402c010710480614000064084001490760340c06036202406080411040b240200382c0501c4802e0f1082d10524030080c40d15000c2070041c00c0b90b03402510403026058004081c040b00c44548001036981c00301034100c50620041d585e900448200c0c0300da01d00640003018001c000181004408607126a20900059400741d04200c006000707400c01c0e004408030a03443d6903440035168bc8690304c03400c960304905055020010004040e8000d44c0d60703040544240b44201d00881d5843d6075200e03000e0300715600181e0050610807a03208201c403a40b43d01d4400b008072a0011030107555001404c000400800e05d10f50311300c0c038004c0e50754288141308890f80300c24180a4401d90840340d00e0382d00c40340c0011003185040d130000006101004440d0021002543d1030640b581709003803044c01c203d2581d40d507030b0510001703c80980050399615203214030340c03030380380100640400d05481040545c5d15 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 468949892 1250 468948642 468948653
    0xc050336150a05130e01031205030405030a120e010609020d151203080c0f0703030c0809160b180907111b0607080c0c0301020c010902040506060301080d0f050d1404050d020a 76
    0x640401c0311005020400360910b6015500f220b078400502c40407030380c100742c4a140424041500380011744840d04a400004407080c020f00890b809a5002001182400c8811744c0846050311b8400380b44409a890b60f808003101c41003401014040c001c00d00e0007581310f80d585500e0300c08852109d0000312102280c030008010300300f891070240700d8107034043c41c007802c0a03500d01811240c45e00c14071100183d5044009800c030300781545513111313020004859480c1b01e525120040310907a01c44480388108620b182d000d1007000800d024400401003000112070703a0000c1500e400000f242314604030351900102c5c2c0c070401001030014060220f40054000e0040c00ca00f02541c50340403403c0c138025808020070f616800141d0184c5e048007003008070702600c0020001e543e5110004502d5010741050b41003203010701d041c00c010420740d141200640341a20b00100c000c0c42959020792085038040351003040309081c4401080385002032030b894005c0d5240901102c102c00d100d810319150552034003101000000440d00490380c0c2000184 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 468951142 1250 468949892 468949909
    0x70902340209010509220c0503010e0c01050d0911040612050f010207150902011701230102071203031e060e1504020309061b12090d090803071505070c050336 69
    0x304140e460000319940c1010f00301061520784103da4003241d140a00364208211201c0847c1650000d80082c012809048012039580c4504944d407030101d50b00784000c540d820019442241d02500510146000c4100c66011808542080d001601500103805006083c800100300500309410001e000b14580b4256071207612810004812900000741c8800300c80c4250780c0709400c1c080b03c00d05600807451981d69105500f103e5503031021041907118440080901c060341c00800c0040031141070a200303c50a4609690860041c00788070700075074243c02c2d40d0000c501d40d00100d101d100040c2118200c8071145d810040040403007030480c4905584034500400410038125808610035804c1a03c8180c4d0340e12001601e0b8026045000304188500800c0d0244200507211200107110f000408490f261000ca254440b0b514548a1041c58000b070700200c00490100c0300c0411940c00581c1c081c9035850719104c3c0f04d2481d42e403103066600404018901c00b03450420100030307900022000d00360a0702c41c05a84681680707103010400c0790 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 468952392 1250 468951142 468951149
    0x91513030218010e0c1b010c080604050714160c1214010f02090607060e070b0a090f1203020a0305090a09020403060509060c090a170a05031318020a090506090307090234020901 77
    0x1080c0124261b00803180484030503500c0320502c0000d1011381c1c45040300505016046074440d22990408001c103001c40e0151444241603280c83c0d40003860000d40346580d440600d8249001c48107c0b000003c0082e120000103501400d15100b40d503151514110550450b0944078400e0a00702480c0c0704000c00c0c052680c50700b041f25204e035070106002c2403800502031080d08041155000a1420500048000318668001c0ca010f094445012504101c0c03926400310204201c6200d40042c003680c000c903002e5005c2800340010340700404008041701030080d2110307203010a0b07030081e03401122040d07241c1d001d2180401050050300d40c041c0c89010107504109403000000d00b02c0c150340c401c0c0218030b140840141200d140c01d221050b07190350445d048942e40c510240700d9180603501880340d40396280c5084460002503415000300d4031101010b40d514102141130000f00101c1c0c0d8060f00165500d4414900009400195800500b101d01c641e80031401c0d0244100709015220305014414003514a60030404034010707546c022940381034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 468953642 1250 468952392 468952411
    0x503040e0a14060f01031b0302091807050f07051207060c11010908042d032618040e03120708012607060e12030304050a061803090506091513030218010e 67
    0x103400401c0c01030f0300401007c2024a151700c041542a40040e4068000300807110f42903c2410384001c9041040300313007100644001c03000680c100004101800c1d10300c00790410074000d00603070b030751000e144c0b100e05580c5c0d00040c0121000c2e40c441c1d160140e21030b007010502c068030148034002d0203003801c039030b4030a80c2d680f1072401844803054901c0c0c000900c0c015105440c905016000305248440c030b8603410704610f9503501051141081005103a9404204e492070240ea201d5007036800450f680420010410010703044004842e01d65220611030b0800795165007403024000e14080c0c0391500301d94140340d038814240401200544442540781004c80c40c0800010b008000c0300c0d407518001d509860001d00086455900c3c401c9110180701c00f1092105101021510f0210544513801c1000482c89940c6846044410401c0140214030701da07000708031604094005181003000180421840006256650f55079002008a0326101310031200a00450418002c4410072280881c4241442c0d03142845d2031110483c01412400c1c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 468954892 1250 468953642 468953659
    0x4050a0201110106210203070518010b030c09130b03010e1f020f070804151b02090604110c01061e0501030204030b13240917130e040f0b040503040e0a1406 68
    0x100100a600003800381c17894120040c0340c1c1100c510714078034001480100303034481c0c0030315400050189012003a8400700c40065146420503860400b542140b90802895103000300c50810a10155941d01009003d00201c040070004210000c0c80c28907013110074111940560740c0c0a0000c8510120a540001c20190050080584e0300c8000040340c001034050381070300034480e4001160224807099a0024550500d440d0390f1410440d007164040500303c0a0812006034114500c0f002081150606420400c0c0c10036003100d41f83d14000e03507006040d0031156141d2040e02c2170480701080d100c46001900b178500c0103200c00d107010b500301411900c52035200c1c407000d001503210003903040c03c4000b01302c0441c00c00070078104003807502000da241c9004903901030101105e04403651211003a4100111403110162819110345000b540145420f00400d05218000600140d60005220001d440020f026214041c071441c46507000c1c5440d00c0c43c00480050722503001d04841c8075a4103001191446040c5032801641c420422194800e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 468956142 1250 468954892 468954917
    0x2040906110f0714060c160c0f0f09050a0903020c0108150409060c022b0f23120a05010608060f04232212031e050a1b0804050a0201 58
    0x41841e1034011031540700c04a018100300c0c0048000e402014001d01a0301c1551425007803240c1c0307074081100d0040b0720786024080c11040e10b91208040c2503191240c007000d0310703068403856913840d56000c6a100141c410322089050110480c00e00405030841aa080203110650036a47d02a494440d00d400702410801e8900c00610300058200081318803000c00390041014010ba13051280180815001c440058840c100d0902184801c400440030900350120b2121f8840e40c03094011600e502d2129566800c115505264091985451600d0007407013100d070414a9131180d40200d50310740600014040f5480600e00700041200701c1e00002250f40c0180100c40d5500400b01103400a001040818040034081c82c189200d0354412505204175400342d0300e460080d5000340c0d07040b208402c04100215000f045641031a00341c2440740c0c020b03006070b0700d01481850041405100c03504504129032080304c415815a481d05010b60345240c040034100d010020a20300105980b800391140c56079505c584030000d041000c8200c101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 468957392 1250 468956142 468956153
    0x316020312270a200a080f030705010c0503100b0306060c030a02060402091308040e06010e0303220509071d010935061611010b060f0d0b0f0d020409 65
    0x120a600d4072020307400341d141005540001d0300b81c0029040d030301a20305000690390151000030300d50b540c9540300b000c0f00f01012411103401007000703ea068007a0022441580826804402d001000c0100d540700000c5440e60318078101142502c020015401c2070010800500c6100c03081000213500350740041817050360f46d8913002e02240700c900c18407103003545070301020075000c0c0c00c1a40420307800d01580c000c0b11402c1150f00c405002038640884d070b45004001030350400c03040080070801d15856602c0001410410000c501c40008242103030300869a4501948071391111038440610025044042c00054884d401649040301d00034200f401c1145141c40d0941588800c3d020702e80c0724084003006090741c81100d00340900141010070b40078461070009208440c010b5600042031100040440c41030459040411825107142c0c0e09803500b43c45010400c105540300c403140b00540e1a00f01c02403030000f4070051070b5903131160001004400c6030b0003903050a101c1d00e03005184000c10368500c6034141030f1a8040310f0003c7c41d4100c91505 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 468958642 1250 468957392 468957397
    0xf0f13050409150e06070f0e0f09070819020a14180604090905120a021c0201090c060503060f0a05030c2808030703110c224d03160203 59
    0x2a8014185555501001406140243c411580d41c1082c000c42d2420b0400c0c0d500e0700402c8455a001070700000300016503d110311084514004040c281d55100036110000c54050f503403c07243c040124071804203101c2000100858581c501450f4001181407e0810708010400d034141c02080c1510705d80852180d00d18030402840e031124a100809603640c50303a0710400b01c40601140794068506002c1c8001d0444130b11510400c0310062201a405030100070b445603048507140034024043c0f0210340d81e4440c690006201120a000541156200e5585919104c41008401c2900308001405900742140030032071900c0004070300c0420002102c85030101030000b0030001140caa50807945800c40200700c00060010780100040c03075010b01a45e511110001d40804003580c51410100040d085400314071442c03001080b902c0d282c0d1b0401d004000105550326030381d800180d40b0403880c180e02c032141030203c40441030a034400080c110342d9160002c50b0b40b441c04c031300c94800301e1404020050215a48024414141681b0a004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 468959892 1250 468958642 468958649
    0x60c010905010507171003120c0507060804170a09140d020a030804140d150908090d1109070e0105030430030504050607030b0907031a060408010e0705060f0f13 70
    0x2000026000c1c10114040e05003500c071040803030402288049400580e25101d40f19105424040000901e1030f501d240840514036010010455042c4a003800542c041c42007400528140e514000700382041e0608001c130410031254220310100400c4046400e84d00880b10904949010018407210928000801c1810103a080001e52100e920100441005515405003064944000f9189900000c0500703004807111007101c042d005024030703239204890507078580110010a01c5a2401d90030076044a0200d8011000540e0071950315489040d1941c00b41446d541143e44404036141c603507100110f100001e40b4910000c3c0001d44080b80180e0354100d2000d154000402032040d41a44205064520748001c0c000c0c0170543d4102c4d26030042001141ca000d200b070280180303c0c140140086099140d1080590080c00c0580b0703200313001c4810b114000d501d83c0d200400340004042c1640080340c22592111900d0411509803c80ca200d146c0c02d0042400480c0407000780e80000018036949961400c00980410f07030641d4950 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 468961142 1250 468959892 468959917
    0x70c02120715120b01020a0804230405160824010c051501080d0207050a0e010e0a0608031b01061d0c030709050904030e010e01030504200a2301110c0a0306020906 71
    0x240c044008951103100c0140d04000c0703c80c04c011011102d001280c4030b1100ca031010b069100c0030300003480030392804034100005000405e40751301c9242012011074161441140c520a40d40800303900c0d040e400b60009182503000c01c45e0301811401c0941c01c1c0398000c0f50ba0340481d1031070400c454080880c0c00c1010070400300f003c060301c40345460001d6075907000e07403a6140c00c0f8908210050050482c000741e10b0070142109401d45a0a002c0c0c00302030f031b00b001035612a145005210100b5130b625000c002540d42400c0c001000740154511030f0004c800014414a82950020380c0071101d000a076480c910102e0394103903c0580c00c80500001d075690380d15440d508942444890300700503485403101d814007040540146205401e503000381c8603100c00403800401501200c40440f4064580b007601c0c80481d00c00026641d1282003010000c00d062f2407180c079560801d100c0c44681a41840c0c0410007010000e041d070b08001404600404940180031402e02e031004500000c40e40d101c028409900400c2141d0705036264425580e04031311030b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 468962392 1250 468961142 468961169
    0x12020702210709090b060411070209090717060c120403020a061b09060201020309070b0f040803030c041703030c12040309050315070e04060303020a02150708160218070c021207 77
    0x600300e644072140e40c502040c541c8600300c00042d2000e040c0c00340d05407036500301c111380c15542d540005010207444000c00c0c0e4003108000b0084580180d58502c2c0b614090300420008001450910328502c5c0d0341131680d81000a940e00c02010455418440001c9030101d44100454040e5a201c51400780e15115400400600c0c080c18201c015100c40501115401900641e5544005082e40c85500340d08030f10003590341132070913080907105019481046004003240078405075050324082d81c8903622400c2d5002a0761511001e41d001030104264400030f407002e80b000c4025030195203142000c041022247c81032030400300401882000060034103004944000091a003c0c00b61110202038054400e0b10450844281000c40d9190584214a00707051041d0410741307905400824421140e80c082046690b490155010820000c124000002c0c04540107004101c2524a040840c110b4520410022a0114958075200205a410009030079400f8007035600e015015626440c40361038a94095003000820b403ca109802a030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 468963642 1250 468962392 468962419
    0xc03110403030c0b2212050f0c030306030f06010506030a0905030f07110a080607090303081f080319020105060a140301141005040e070b0f0309160b191e12020702 71
    0x4000100c0701c60303110b41521011562026103000082c21404044448800005c0301c0400190301c0710400020103a540c00c044d07080407540b1203404040d03130040c060500780e0f42010090103241e040812040f80049401400b41c4015810035000c2010313800002d0000f890075445d80041400d009003807080301c01c445594842c2960301d61032030901d5010341981c81c00241c020303080110006880513000c00c3d00c50080000b035440540e15895501d0440d070f8520003808460a04a841c2510244404031003541401800000081c646505140208038494001920100d007035904020804c166a510342c0e0486060f0344c00d00c40101d10020341c0c400402c0c0180003407c41d40302d42e440c41c2d1040c4101e400000c1e001c81d089401c111424015041450310b61a1546960301c501c0c1c001d81024052080b90210a0025650005e0f460341298400820304005540f03482d001d03405405401c400051100d11100c40f1941c0c40100461400d150345100e2608489802810021f01c1400c10030240401c1e1310101d00107a012a000103400078200c4c44607200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 468964892 1250 468963642 468963647
    0x151202090d0614061e0f01020304050a150207082e1407050408012d0b031906020414040b03100b04141005040b121513060c03060608010611070302040c0311040303 71
    0xf4002d842c1980b040010004125142070315402401303090301502030f0502a42c8405111180503101001c6056000c1031202181d140c844d10250030050a903000f01501c000342500d0040c0c100310298000c88025003041c1c04a040040e0b070b085a003002c0001040b50120342481c024a020f00030003410790300c912503111680600402caa0700c10054016103001d8002000164091010209202c4a00c0004414125003c2c801010324603d540310441c0d680d0041e0940d000740f08441c1d94020400c10b580c004640c0c59901150500211285801425000350240c404001c1c03070309502c00080c0c2d0380701d84051020099864084009258031541c10070740214582c00c011401da0308146414000700c81c100c2c080d190140d840c0c04900d110503e8100d11746103a2142400207459031900c4484d605000e420f0040c000990040c0d00c1240074001909442020895116541d0000f450b03810110020714540040e440142004a0200030281c010f4010031181e0403280e0468000660380300401064000e0a0144600040101d000c10000305054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 468966142 1250 468964892 468964901
    0x60513031b0807170a1502070b010303030212010e01060c02090a0e0307060b13060b0f0a0c120309020f010e01122a02031c0626161e050406151202090d06 67
    0x4807420180c884a984407030503500c0421a0800e00d14241c2d01610a60340440c0c80401ca0460b69444580054500039075602c68403050389c0c080c0d00441c00286d00203140c42c1601034812120707002d01490010030b02c21754076005e401807905c60b04c0c1e00081c0c8a83d0241000c20003112300c65101046082c031820980761640d445081040007450001c2c0d41c28001c1268610f104d00b03907005441143d041d244c6414140741446011004480c0c42e400400035442070145001100022803040b43c010403000e103180c0d9022070544d840b48103000301005200076550500c0255501c0c1001c0d0707a08007100f4403806d038003000006001c03810308091641c2e100003c08103454210130a00b4241c0a2640400100042003d208150481070700307210f07151003201c0140c4035104034008104003203110018542200c102d0fa02c3d04a0441c1c1440a0095004c0382c003508907800b070720041880c0e030340c0c5030803020002103c1c00040c03000301c508000e118070340200540c0c07a0524550b54000c02c1030301c0031500f52a450300d5060b00c2c000040500000b16240c210b181160090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 468967392 1250 468966142 468966149
    0x905180d090801060e100b0a02010e01050f220215090d0b0405030c0708070302060d0908090406080d030b0402070507140a08070305060a0b031f0522050606010e01110601060513031b 79
    0x43d42040b10108101e8091a01c0c0c2c4d000721803c1030f03400c011600d003a9180c0c1c1c00e60440b0104c0030440d500c403044101d05140034040d07580280309602c4031032403900f089034100c0c524030045405040703039004074005003000d81e540c90340b541307049178803003034075559441511b400181c07a000c00950040c00c0c2d06200c0706010511000002400907440d8503002c40d203459841c0c001c1c80343e940000d131200952100302001100c6240d02c0e1a000910301a01c1038510380e0600300e4020015054402c0c0f500a003000c1da0002c00380c503000070307498015a80d10394010b40b411032030b02c0d030180c481d15150001406410400c2e00c03421080a440c0d222140344000500300304065407100e50302d038902581c8a040640b4184941d074144800c40c40c2e9468045003000045408071030401f14020a4441600917100c014003128a11f02213010f2403814202d0044a140a01e1050b00904a50b2074010001352256403000e001791304018228059004000e40000d46074151340c02e6003010b030784031500c0e80b801d0b0140b542c41d078000a148000c400050710702042c400b031242c2d054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 468968642 1250 468967392 468967409
    0x6050a030f1202060c0a0c060e03190f0f08011202120316030207060509090a0b011b0f050d03090f110d062f2d070803040c09050a1103010905180d09 65
    0x2646400b440499072407405070307101d00a1030020420380741d0041c0074024000c0c10901c40c80c0013086603080b0303605d45401c58005941c900c1c1c602410600141400e5072160b0700d40d01c041083e040c100150a01e11000900c0030b00140254021401c04042da03a0a564803000d1a603081c20601d01203c4c3d031801e044580d00080020242c0480161203144000711707005016006132010064050b00a480943e030f42024040a46400003506041c0a08041100220001c43c210003807210300845c4601e20704000380c0307065454604031200040801d80741114800000e003e00b403051a200750004044014924103074001a248a1920002040c1034509070310320710505c0004540c2e00b088085608195800080042c26500c00d20440c1c071480810f046a24100054043c0e001c000b036429045202120b0400076140d8803062a603106460940f50158905802c000c822400e000307142d0302024403041409420300400d00c0101500041c09010744003502c03480020000380d18980903001803a04078080b215115140c002c0a021044280521600b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 468969892 1250 468968642 468968663
    0x151c1209170106050919060305030f040806010e010f0e0c0906120103120804050607030905100e160815060f010c050d080603010c0305060f09060d0501020a080a0e0a050c04050a06050a030f 82
    0x1008038061045000b25070010381034040d5580d1b058130880200744030801c2c22100c2d65580e44044081401000640401a2850600c660311420035400c00c0c0b070700390141c2c07001c504440d41200610507407080010410442e035010a0f68081c989840720150b41e40d00548086035040708002c1080070401c0800e9035058120390160001c011240c03209201190130315000c0301d0241141d8040c0e0081003a1510917808041030b41d026005072806038880c8420031040d2614035000d0001c50740014002d04040150104c144001c0c00d2074001041d0b003200200070700101c83c80040c082440b88100740d02d188096402824402106e035030110a40340c04000742140900641400e4031801e000b0b6103880200b40071a8040e10a9a00134030005003852190348054041141018005003610b80100c21001d80c0d000055007400902140107a907202c1c4c03025443d08e280d188007150001c04440700c45a0001281c80080352021802c0b5946020507107003c11142d88a401c100e024205540c4055001550200008240140c28091041c01842a10700d440c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 468971142 1250 468969892 468969929
    0x62304050a0c05010528050705030304081201060203132702070c15170a020c01020c1e06060d08030a05180d020105010e060612072109120f020303151c1209 68
    0x55076406001d031b01103070350780010900a240440340c0240c640140950b01c1c0c0189025210b0380e40a06603002558100d44002000ca010401c1d411070003151405848130344025800c091a5441580b080307c054407410a11111424102030f410501040745a103a40980d0310955981007181b07021001221141300707105011158418100f1880d10508410600c03c1c941d00305070300c2035110082c40074000c3d4080c8400030525275003080721068a420621807580500c1c03001130580788000707610b0011800c1640c0205200e12407019641518002040c40c420f507a040340503440000340c156101460503101c8600e218218141e441181c462800c2240c2c1500f01c24162003061901b810142c49001c203011542c0200c022840c102103800c80083e11151040c0b200384441d400005900311207012040119080342c80e4085c2c20b03901c101891804004694000c0300e4040340803901d100031440d502c1e00c50b07501c09180310b0b0b82c50070900ca2451408601401c02025484e06115030300510f00a01c2920a810050306c034031008d2040c01a0403c0724199075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 468972392 1250 468971142 468971147
    0xc12030204060e06162306070305061305041704081e0c030703120c06060608010608060102070302031915020d09030906020f0a060e15042a12062304050a0c0501 70
    0x480854007181c5411a100c0800d81c1006045e4000003500c0c00b191079400003d0021031040406c0c40c3da078011400d40183c49119950381141003960040031700d000e16060505104003501d4036450111089404100040c1503101c901d0240303041340707056842e40c1003081d022602284040c0c000c1200e107000158141e14000c06a460394a40d511240c8120890340c3c076400c10a000c01c0802c6680e42d00410b10055858010001e501c640e44c0c03001220401d42140c0300151002d40144501900061540e41242003400102261469640000d40c3c420308c4000c1406c036a0320701030000f02000300c0c42c856100d445405413030031f6442d4011007107444000c10203500150002a0345003c00150b260010512900f642d03c03100241c03880039407684544d00544030543c400502441207012650168086c0070390103015600c81d11000384544200b1004070000c4070440400c1b181011104030420001c0c0c20303100c04403591a801100895040302c0c00003040c0d02004e1400e07407000151030400400080160102c1c04560091040c490b007442c054540004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 468973642 1250 468972392 468972397
    0x20a0f0c050703030e0d080a020115050d0b06010f031d0c0a0e0103050628021201050405012304110705070e060102061005010206150f0a031a09030a0c06180209070c120302 75
    0x9000780d00b10301c1003800070030321075114074240020150003000303042c3e540c0d40d0700c0145600810060b00141d40d02c00c80c01c8001c2c078812240b000144021102880008240d0722203a080320030140c04036041c46142030050080c1402600718008c20410802c00c1d14811449080d0301fa10b03492a440304902c02d00d0031400120701d206008a41030305803a00040282410390750752282284507a80407158003844c1d2000c04508101d00c12038001006003241e4005603000300d504d02001c0c001038030030603001201c0c0880c02480e05d85031130b910500300008040d000c41b40031520403840c008642c01c038031501340064010f005120380414404400b802d0107014020a07822100c8a03503444c1e90300c0700301ca4294041c0ba40140c004402050241d10221868180c5006c010a03172800302280f040010480b0245074411104d40c0c441100d200e0f00390201e6140c19501191120145150900f13419000301f440f500c02e100180655a6000c0400d03240030317070790303007001000e5409040d1840c2070030804800b600c1c4082202040b03442840364102e10203228031030b009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 468974892 1250 468973642 468973667
    0x2030a0801090c02070b071b0b0f090d0809040c2102030103030c0321020a26060a05120120121b090d0311010f140916030b0705120a020a0f 61
    0x4031501503909100e0020080d000710320340b450443c4544903000c680c2e400c0c15801043c0181c858a1402c00900300039601c1d40780030400340d000c0f11141d0707400d02c060682401118110390010f40c04035203a0a05100320314110600340610000703203400031710700f483c40254240c0145403038411055804000e0f404001e851000c400342c0c1f200b40001000102508642e000003400f4904030110500f0000c04210404814140d1404a80040700d2136000511200b940002410b0113850510401300882da4501903480c0c2400841c07981d2940d4440d040c0100c41510707908151080a5016041040b40070403103051200d692000d01307100303030070501d0ae501c505d0f0129008208203c141d4001c031140500c20203043c504081a00d0100a40f00b005498190305201150012010760031082c070500c2032480b5041000034044803644402c1a80a200412840340c03948641780786000c101054100000312540b00d83c000885580b14001100c0601500117410454080f2906002c0500f4283d00503040c007130070568502980e40e10021084031381008051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 468976142 1250 468974892 468974897
    0x602120928062703081008160e040f0f03180806130201080c0717070c06050f040b090a0506160b1b1603090510030207150b030c0108040615090b1002030a 67
    0x64003a40040c0d85600010042c4440300004114542521202010b0b5203180300f04074002102802048a005101344404001d0a10f0200038050520b491040483e000d42602981032070003c0e040020b42004030fa41a03c045203a0b01000440f1484000d01d0042c0c10b4210211403040010000c0b42e02007000d20f8000f441c20f218003c0c500b20000038070700319001035607180000f41901070350386410424080440c054001c910101608100ea065450038903007040340700701c4482c0d0008000c0040800001c2c80c031485000684098603095000a99500303403110028026141035405140c0004010404096000c25254100250350141d200d42c076a5a4400240e02c01d02074030002900d134034100c00d00c1900500c107281a40a41c50500c80c0c10200a805d440c0c01c000b40302e01140840c3d54000a800080b86420405520041140e0060000b002d0003001c05a5001a0715a4042c108141c10020900c0024041c00905d400240040b094025560520758466490401828249045e0380c00782c00c11031400250540b00100311a503000066 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 468977392 1250 468976142 468976213
    0x6270316020604050406080703050115031a090a0c0e06100e032104080703050d17040b0105010f0e270c0906030103080708040e0f0a0e06160f090306021209 68
    0xc5898010040400240d070444000e200105098603030b480f0b810003810480e802003140070f145160407400e480c6040d140105500f030440301000010103ca00f00002c0040d0341f043c0d1084c55a41c00700c1a45040d214110150448000030000288041c4280c00f039400b80c0000c1d1190303842400e180d00191402c8000404207509175111151303581c00d20410741c24603181c1540090b800e600d0700b9500e20b1003903e8076085400986050700312880e07244540d600000c03100014164400c840556203000d4469090300c2005210305810f0104500200d10014810001ca4881c40f80c020140d40014811960624000781c4d540100b4101074004c1c800700d003807074080a041e40c0394450700501c010b180d0380c01c603a190b80396600725003011a02c0d524140004210040c10740465441502680f40201c241c4c5486070034001078a405001031003282d000b0405110b00d4003100300c080d401281c103908124034034a4041204030303000b4202d507101030700140c40811610b1004601c9000702d07000d140d04000301c40e0041072940c854030030103070703035680200c01220350 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 468978642 1250 468977392 468977407
    0x1504050f070f0504020901030f060621060f140d02031501051002010b0603040f0c0f18060b0c0a0b070e0306011d1f0501030c05070f05011401120b180a02060c062703 72
    0x20b41c0082c1b03d20305061601140c4444180741d8a0191000c9030024004640701025000650f100300d07018a5032803290200034046903160800c211000401c0d8041c021100d030500b9886843c81d00c801481c0d400b490303400340c216000e22030801c1d81411700900a00a0b24882c070601d46622102c40e10502803062041c400403d22440c5807120f0303030340d40160180218100c0380c0c201c211348002130449004100310010306240c0d144d0160074402d4000d400440b011a0480301e4041c6090040034030040380040d0706510564040e6050b14142c41d0742030152058500e4032841c1c1d501d40b050400200e81a4004032010341d550f000401140543d464828072f1100f20450185050041803100b10308002d03641c400d8000c42541c3d0364a040c0249029015254900c04003580c142c1502c060391130b680104080f01c519034645004201d00030340012414401e5540b00c00c4130744081c2410142051b04070000042503018000d00001a60051a40395180c009203007a5071a003104035454585840c15030300f8140402c18040d01d01403151514006903103031005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 468979892 1250 468978642 468978649
    0x10060207140a0f06120c030203012d05150c0d08090d2102030112020a05030106060c11031e2103191e0606180b040302030a1e02031504050f070f05 64
    0x1800466808420302c0340009040348403207100c001401e00e641c1c2d0900c0581c294000d81d019108101c0110302050b10400041000040301c40003d15502c820320f0102c0c94401d172142019420341c1403030f0000c41d44550300c035030001030a40700c00c4010420f26806205544c500e00c02c4400941e182503040b14000c6041d00079052107543c0510030401301c05c0540300181d0490080800c0200030040382c009800c13840d080180c1e04268020762414482403401003408500070301c5890300300344d4001c00d600740f0818011f09403481d000709244160b03018800c0d02922006001c0d94100d2540203068940d0307800459252a14091148902e0b9050742c540c2011032344142c400813050f0000c0c0300c019020400038900480040c0d400c1c1c03400f1821941c1ca010a00542700103110300d075950280c15540203620a034001c52540244408103082208000689000c900c003207020350004c111881440203031041100e01c00f403d076002545405080d9410084104480c00b01e402240581c0854415110240046a40d2403160003440040418403a04028514 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 468981142 1250 468979892 468979919
    0xf0b0703051218070f1e0609091e05071e03020a0c0b060d1202070f060e18130c0b1305040b010c12020a0f050c041107120e042306030610060207 63
    0x1680c0c4661a501042503805080c000389401c40c2c1052135a44204000e070780180f011000c6e000015030000c100403413a0501c0580a5465485500c41c2e0b17175124510724502c0090018000840c0c0e000c1d041c14441762038200c4005180f0900c1c0300494804008079807140580d14800c0c829100c8001d41526140c40900301c03a01c840c1c1601c3d00041402e0ba000f40303505c024000040000014500090082d0000d00d02c860814800ca21400303c2a0000010000c05406201255903200d502d00020842d401c4ca4503115150440c20b0a448541c90ba00a0030f20160104001028200f11008044104904600c1300071309031a0010881034651010f10a4001000d1709254404102d0200c2c4281c05d80b01280102ca4050625a4404482e00d040d900140da441d00040006c0d00c0c941070178000c9510780070140b5a202c0c5020f500790b460000000006101f0010006800c0501c190b0f910b8907813100301c0c83ea4060001282400314104842585041107441034000c0c020300c00880e141c039104440c101c1c2504c0160b00070b07180e0f060912031480c1802 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 468982392 1250 468981142 468981151
    0x303030506061b0d0e010c02030309040f11040b220e041502090d05070f05030a02060f16080403121205010807060309020315130c05010f0807030903120c03060f0b07030512 75
    0x8410401e00c000a44600740f02c0e1042c50051001d049209014440940100441080d4505000c80c0d521076500694021044074070500b01145d00080c0141040c00f602e0040501d49000c1e010360744002800700308002c0c20b002a060700450050304500c610186102940d03030703010030b00c2000200d5280f4004500051446001007560103500c52005082003806400101c40a400c40416900c6404c9004140450444091420080c000640080c1180003840e070201c0c2044c0304030700e51010005804282400c868913030000021034190846031091b00c42c0c1d2607080902c48a9441040e40c0003107115821074003088040340c0240d604071440039000c3d0242c01d00c0c0c0030098020b00007600080741d040c041e602c082c0400813070381c100d542d00a003003001d80d61001c5007039844c01c8140818560041414002e03c0103d0008840e4021f042c264070881c0c51401145419091506840200700220004980c42c01c0c242e512042c2c503410341c000e0085400c00c50b41905001e544030b081c20803500c02c413003024001910400000200192207a03809420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 468983642 1250 468982392 468982399
    0x30309020f100e0a0e040506041b03170309061003110d06060b03150114090306160c05120a030f180303020a11030f0d0506040c2307060e1608070b040303030506 70
    0x10704008000508000300701c400c240e0104858102071402810700d4840c040144c0310010342d141180c281343e120b5580d24103004000600304204120344e40d071141e9400d444800259401500c2078000c000250034000c65803c212400c0000303106000c00290808104415141102d4100080d100105010b40030f108400345e00070400e841040c1c813a0400141110003d008500c07078800060040c42070011100018169071000b0501303100ba20041c000140d65036400328403150091400701c0c4c004030f0f03801c080b903054814004080c0701400c14000d09540a43d40b841010003041c261201d558204480c2c116034803120110b0755800c210100e100e0200a440c0c000900039401400b603880182410303c05031940c070004901d554425030b000103d880c404959480000c103103006444d0000e00850f4240040305501c0070081028800c01440382210700a031007912101aa000200d43c4503607003260040c000f520720742901301c0d80c1c0d44241d58480c004410090001440e00c1000c1a40b4041d54800c0c40130f039250a1450300e08801400c6d02800c0d0369032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 468984892 1250 468983642 468983659
    0x1101020909011403010e07060e0907090306020c0106030506070c0c140d020a180f1a22020d150501050408070e0601030f1a190614070c050a06080f0703150303030902 72
    0xd580c9020780039000308540e020a1030440c4400040c1400d484102031540c4481d0f0140c1c00921000e500b0900e0b0945140b002c2d244001d480da90000704903246c03e07480d8005080325200081032984001c0c190850400e0301c0c0038504852107a04c840324102e0b9000d02c48080900714051100007404919046040440c00b00401400e4030702c00d1000d83c0010b0303007001e5640d100c5001c980e0f0500340c0442c400494021074105500d052810000305030304240c400000900c1d054407034400c0d8040100104040709500c1103034442041d1100842d1103401c4910010024015070f503150000031800107001842e0361089045406a4110b000030b002c1280c0344c070500c0c582a03100541014103268030740680350112a000d102d0129141040500c0f500607295240074041c208600802807015002c6e0303413100f48605c903001280e04460030008030044e5502d48081c10000c10440e12a0440c0398032203855140007030f005a00031411405810080c44a40f2541c80380041a01101c5200080f1480b000b41e0407403c10101703000340c1c40228840e0003c1c00024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 468986142 1250 468984892 468984907
    0x4030b0c090a21110d210e0301050118090609080f040501110c03030909220809011d03030f0d0603150c0f02240613050a05011703040b040b1e04090212090604020f01110102 75
    0x6c001001103030040344810701c0f43d000d94000c1e52010b080d50400c0c40030780080000394107204401c0c808034841000c3e05c180c42c2e1a00410410095240d1210007000e80140701d0399220ba02c480c03044062688144140c03400a9550021413040d6200480d4107000e82100034010f40c0b400031742d001407265a2100604841c403a60202050442c1840c4152140c0c88592203181c289135900e006100140642141c2482c0c0481c5085080c00000030340c1300001181d25104e41848441d8503600c200d003407980940300c29000184200300d01021545074401d560010320404a254441c2d458440204404980d01e400c040307010b216041d0000c24920501e00c00300d4640e604040d014000201c0000c00a991000b0b640050348c95444041e56240100000e0714002d0301e004c00d400605016514141c94042038004a001d540518404c0c4400004d80043c480b0b520500e080e01c8014045040c0d0706d460b03940321a00e00035084904092543c00c40240082c040800104010784607d43c02400081c0c040c2c221401100e0341500741c500003946642c02c21508 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 468987392 1250 468986142 468986153
    0x9080708060f130f0f0305030103060614011d030705060f041d04052a0616150908030a0c0c21090f0315050a020c0a080712020303010e0a0209040204030b0c090a21110d 73
    0x1520341c5c0d00a071160340ea00e514500c0d058048980941c401121481c541c21811038580c0e03c06a040707070301349810304614581911314000a0074002540e014650082d000a1821316142c0c0c1031000d031080300d0208038030b400e03076000c001d8500490b0401298002c02c0ba03007228510302c201a6281080a07000000b60f203000700e01500c80c4010403090b030300c807031544c49000888203014401c00140d400d55910800d1560307010300090140b0b90360f003462800054012080b0782d0325903c41c002d415216101054286801c039440e05098400109692168410100030780001560000702240d001100401c40049942c00050007903ca0b00c10003e80b4020301002d0800d51110750200841000414100080fa102500820b80b080c0e59480d540760194070342141042505c00d640042c00100038003548140c4441e03202c0440e0130003594440d041d17000500240b042d030700000c241d40800c17402d0140c41d490060107000d810206a882c601d883c1d440300c0f54020307004140122010050210005400002c0c17080790001090400501506808041030b07440c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 468988642 1250 468987392 468987413
    0x7060e030d020d05040b010b090f040b030c041407031a150a20010209031e0c0d03170c071e0b0a0b040b040e01020901082401260709080708060f130f 65
    0x4450f4580d214400e100c203000d85003e107680104039001c00185480010740c0402c0e01c13000d1041c510342c4181d50ba00c1c4450b60a40301400052102d65008008101d2500d01c8510b50141d1b26003a181e14000901c1c4c12070000703d0309101d18510400010041151119400c0d4160707102c8181c1c003142d2240704100741c001c6c4444080d0705c5040025400064034001680b5442400103041c0340039103401758000010342204d250081c44201240321000d6080580b4040e01b056007d040035505000c800c50f11040042811040006400b003d01c041d00e000b40c82800700040745014000c82c44040c0e034008034050950b480a2003c10316400659004d0009048003810200d2070920000010301201e085c5804c40840e0b07500050002c40c04d42e40b0402079580003000030b07080024a01da02c51080d0b00300034042c001c07a040c00038807500c0d02501420b00da0300001c0240d41584150980c80c0444008280100b9031180000b03030303c268800813441950201e403c2d44140d450401c241c3d0184e0703c200c0c92941900c1117000698508604400f42c9010a002d5442c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 468989892 1250 468988642 468988657
    0x11060d0905010b18040c03021c0506070f0e01030207051b0d060e100b0306010b03190204090e07030b0717040f0c0f090911040b01020a060506040b0d0c031209060507060e030d02 77
    0x1450420190600c00c1c89802c40300308180c084004ca04120000d2440110341050700d406a038040b02c181c0000040c01841c44c6540b00107070440c407880040121311544407520052a4545580c0c5000e02c4802d20019010f90160701e000903ca0340200d4501c131001501101952400d04009081c0800185c641d150002145e60603030340c0c66001d070413054180452520740e000c0c80b90035880a40c01004690300d4102c003400d59001c0642145142080b107030801003201c0298040da00940424441046507140035142c203955050640300c2203540d4001d210014104a004060140030501c06450182c115a0b950b43d45849001d2083e00450750001c4130040801d111b140044403c01515011400007008101400c100b5080c00302c13445401c3c8038070300b091040c404690b400314000d940c3c141d004002151945411000070080e000001140781c20410000c40b2100740a410808101201d0146100080b8000601003ca880d00400d010300004210100204800903009910070100010f04105a030304100085c2003078400ea0b0300204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 468991142 1250 468989892 468989903
    0x120304090f02090a051507060c030605090c030f0a0204050109030b0406021b06180123090a0b0a020901030f050408090d0c080a03051c0501050f0402070c0b07120f02030702030a11060d09 81
    0x80c0580b91802c01040741c03006400100ea01e001182941e11b80104644901000101440e44840b41c0e80c0010307000e0b41188002e000300900d54025494a607110030003642003241c1c201d40102941002c101d81103986c1c400c0758203984041e9502c201c1d4500716120f03415000030190003186c0340da07401c20140301002203c0350142680f000c0c000140c40c241c03c010b50300c014004c4060542958903458400d100780300d04914042d10383d1000e2941140041a544c14020700e0030101c840340090031404a076000c0055031901980244007001c001d1f01e0030001111070898000403583e048070020044c20080144c0c3e8600e04d8048002003031103109001002159031100d8240e0b04102c00d5070300440110f8000301309800d1000c00c04943c01e52001c81e0460420030381d8500030000f40340c1e02c05028801c0c0104c0d400500101071082c00c460746805099a0484165222100e203000040d616580c00f150740003811414001e40240d00c08800c5130b600a80040c024a400040754440300101020402915881038041000503120300060040059050195 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 468992392 1250 468991142 468991147
    0xb09011b0b1b0a020c130e06040503030a1505210307170307081e0402067c050315041202030903070e13150c0912050c120304090f02 58
    0x5100d550040300b40070850030b80741501403048030301d82640019040171700201220021100c0403803243c142d0090401302d4150300e0500400d801c1105104001004602440e19501c0820203203440b0860341c42402003078013a0990103a0321103120001e201c0a1042d688108100d44e0980346000303100d84e5000d085c009541d5250310145004000c10820542000c1125480003d00f254100c20303050058003d2680c90006100030300c0303500040303411042d0000590300c2d84104c8951125452010942c0f95085540b00450000f4101080007034039801c0c586105d0081403510099096902c040c040d201c0503001c1d240d214140c118103006440c80400141c00c0d501049501d03003040603940745100d1400e10741404066500300e8a141001e5600400c0f001c0040d482c006030580c1100c12000e00b9417100c0c3c0320014080e900c0301c200000900305c0b6140d4408005284042c1d0f004144003029520794401c200c0d80c804068012a810200290258000c1c5c070384850103082c1100700780140c0c00950f00352460a40c03181c2a0004866100a50f843d0143d0301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468993642 1250 468992392 468992401
    0x80712050105071b03081009020d0b120c031e010908031807050a0807030b04050312090304080106060206190209012010050606040f1703090604150f180b09011b0b 71
    0x28071525403c0940c071318040051302020155844268400c000060400041d03000082030711211a2041d009000c0c820b9055544100c43e01080c0f0103440305911807803241802c0003001c03c0c010780014042120180c050064903480482c01a00d07154200d01d11030b26802552900f405600003021040214441d240100d00358518124040c540f07480c105060304200d0184045100c1440f10020003c0c0c001e04a0740d02240c0d46509580d285403490442c01820440410450354209021b081e103070210240089d01d030004000c006040d51070b81c0c00c80c3c1d117074400c4d00d042035105046c480c0601500610b400030000c0103410705180caa4a036043e4030f0b0300011038007608c914455400007003004050007400d010b00e80d080941201d0140c20079043c0b07080c0d2643d5250030f10a90819180701050040503c1090041c0c4220801c01070060303031900d50b2000030b400e50440c80381c0395000040748440f00c8502c1c54011154070203001c103030040000b001c50809810400552046040c0b80c1408044c402c24014004140d1050182ca40300d02c8900256080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 468994892 1250 468993642 468993653
    0x40b040e0103200f0f031603050d08090d0e041d100509070605070b060103021b032116020a11150c030c120f07200d050c01090915120309080712 63
    0x10034007400488800a1412903280e40c2c0380c03100304a0100441d103424122030170740002403408014a8101c00c0c8100703001000400e2040202d44520140e00720340354405c840d038449000e01d403580c00e051300050210344010b060010a0905038442c1d1825141e8415800e03100c0c0540c200c0500d020306001c1e10311215501d0782d0800c080c10400b40b18002c003d101e07030f0400c5802c03c20503648443d079100c0c004021504166002c20044000380910303501c060b1000552003a0303a9120800090780c40740740c42c07122140d003074018100d000c035948030301c007105102400f0340e90707805414211302d65643d9180034000110040d90040389980150540001d142c000e21044a03d00025503584005805650400410703140c4140d010100b4041c0550446450084542c11a030186552030814000171000d000303180640b50b031341d401c101c001020741700700803001800b4400b80c03030300b602d502412603076600f100f030203941c01d03000c08503e035103100a02009040701b0b854030a2249407090429994107510341080e0b5103050202c0d80814082401130382100148403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 468996142 1250 468994892 468994913
    0x9030510090201030f18020f0406150804030810181a0a080c0405010503070303090902030c210a050105030718110c0109051006050d12050a0e040614010806040c020c01080c040b040e0103 81
    0x45041e001d10110215825050103195150706c01b0f401074440801403100c1d0341e107a0744950b02410440c010070820b4181e1700e9005080100c1120100c0109030b10001240308400074003504030440c0c5071039106410590075002e404025141c0400c1e1030034120003c112070300c0e42d569440c7c0380b803002e0016a0018520104d0102c02c00091329010303030090b0b010f50030000c418008a42e01444800a480000c100036030380b81c499081c040341c0da00c134140340341100f00354102544016401e1040c1640c0034001403a014841a600c843c20503880b030249109114000c0c00c4004810b140040719000900e87c1c40f03c01580340d0030020601070150a54681070700c111800e030040b45044040064034481c19024003025105200d10048039a902c000c0b8100144602c1c0070b21802246c5201e210340f01c4c84941030070010140091005540c0c440d000c002104840c006207000c203a60fa00099454101485842070180d8503900401218200ca001903e01039405440c07411000020440890a8580440200000d002da2694004291b1460401040342c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 468997392 1250 468996142 468996161
    0x60c061415100507020423091218030c030708030310060c020609010302090d140d030b011409040b060412030503150d0b01090b01110a05010b12071a0304030903051009020103 76
    0x44100401d00540061541c0107904001c8250341e030507420488484155114007845100a50060801481c155001d85851031290030b0001034a02d12000e840341c6103469161284031010071358603002880038540d940300e803003100b000c0740c0380241c1902c100e8540380d0042070400040b600494001d40c8000f0074002c94050314100240200840e2038031414194a5900040700b91084101e001d0400d900440c003191969600d216885d8a13030b50000000c4d800c50030201110b503c0b814070400d40030100c0d141620820095000d0903e103109444d00d14a5075140c1381121040000a107005564181c000d04180400700384411034802a5002038080c0d02c03081e8880c0341c408200c0e00b1500c0c80001c554018000c02d003a850024a45109950544a4250740802c480f80c0640c012a0000170720b20241100e4410080444d00f80030040d48000c00ca400143c41a02980c2802d40610741d8513082881070b4200c0410703446c2c440300200c158401860300148a8503120700120307034945a07245810511010090580e949a5480e4215a018880c01098 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 468998642 1250 468997392 468997421
    0x9060d050406020a081303050d02031905070e100e01081609080d181a12190606030219090503030304030e01030227011707020309010c0c052d04111c060f060c06 70
    0x1b0200b16a0001c1640c040d1a50024480b500030012607480f032518625100702400c00b44c070800041c98040c0c001005c011400e01554000d40728035109a26151140c01c2e005040101a194000b081d10341505200c40c102e030844400342003107095040416440d00910040c2548040c955541d207407412105640300c00702c0115800040c018400d400e40350302004002041d1814000ca0725004c41141d51603804021400007000d43c40101589002c070042002038069000d0300740c1c1e0381c4d60344149081e11140c103000d48400d1454090a98564002c1c0300040000b441090101241c00c010300d005420030008004024101c8031200c629401d503230910080103882d50b844910340c10b00c5d0382600030388880747c200100040c2d2070b40304541d0034604100700c070009003050001b2030640340018400075000c41c180c04014000d000038001d80700007113010000d042c11544801d103003e01555200031480125030b0315190070a180304240c4075210359030584150311340a00040361002d8116410040c4516182c00313900015901c0d14900710752090020310b24 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 468999892 1250 468998642 468998671
    0x1906051513020c01240e0f070c0206030406060f030803061002062e0f0303020303010f080c091915060521100b0304020d1401150b0a0e040209060d050406020a08 70
    0xc1981c404441000c000c01c420030059540c0c601d43c01032809400309414251440422046001c43c1a401c4501d010890f920403001026030380f00c034241e0700c10400b4141c407a800041d00415694016103032090080d034019104890005409568008290550000764410398010001000304001420003400c2e034200800c2c98806003031145002e28410f1040c40101d450b03541d19120100c443c031003150300c540810004d44081c0c01034102c40c0d07681e450000d5580e8424068041e050001081c000351800000460701e406000040a03d1881d6860006892030030056007600c208645e01d845640c00019405080d400c0a030040f60355460b030b1004403c468501c85c4422503610500110100300300042c0000e4428200160303452058810380d2500da03030000860344141d00350044c1c0b041c00003610301c040059056000001800c074079040d98804559848042d216400340d5680c0c48007294841626181c80c0c9019401084003074030040100d070900074a6201c02c4201e8404460466180d6030010f1001d0100360030070030540c0d00a182e20710074031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 469001142 1250 468999892 468999931
    0x1c05070e13050403140307090503010207152a0f050405100210050606090904110102010e030d0501030308010b030c0a0309050708030c0a0606090c170601020109170703120209060403021c05190605 85
    0x30b00000750140f090a100c40041b000c58004c511401584000b4000103000795201c08141c1042c0008801d80e000d41800c480c50440b00b071000b40050405405a0903c564001d440c4015000e400d5a50303844102e00c200420108000100300c2e950350840343c61500089070300404a40b41983d610070f04a50002d01100d11030302081c80020311640d514441680c2c07043c0d0008207001081c00c0900141c0c0904000c0005084a02011803402140c130010b030301c1141283e00079612046c15907611800c4000303510050340c030b0400c00310017000f844905d980a50014104648100c040718180e50351059150304603009001082080d4005419a500b440807a0103000040c0c504840100110413504034060012a40d4245010040b10f01e5030020f4280c1e0300030f50200c00d600750444014422203c130b10107618020b9000c0402107010400c0300a074180c1c0702000344242c407107204029142c0b0b45018296020007003040d0303d85400e400503214610303602c40001c40a1100c108040044031452440340214070700442942c00041c4082951844c19003040d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 469002392 1250 469001142 469001147
    0x5070c050303031014060409110c1b0a06110c090a020c250302010f051201030c031a071b0615060903050d08090312090313060f1d060901051c05070e13050403 69
    0x5504840b0460080c00801904401185590080c2d9007c5901c944c9003c054105025509c002080a50044401e5864900c00741001200e8a1124240301c0d030072011458043c45124059132680a0b00c901c20750880b00422200710000c0c1002070100c0306820090b8010078442c500b60820400f03803210030050ba02d10641d1325100b105220650426200180c10410001d14035031a80380544111180480c9010090320315603102e044c00e80c5820160710003190042c031001c10002c1c01030103004403180103035a240e480360101541001003041c003002c2c2c0c500a0b42d0345991030b102140e481460101420041c41aa181c8038044c51450030040c0c1883c42107050398050001d2030080015580c0040704844158031075030120070310f0f41c984800c05031450065600307810a510001e0404504141c02040c40d444826031950342d819403401c036011040c0c4150622501e00d40100042c009104158000d10250140c25801c4100c0e01600d000210b50702c05a510a0302d100b004107500711940c60060401c4e0210303c0c8200d490300e82c10300c400d04255900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 469003642 1250 469002392 469002421
    0x20d05070506040803060604030c06090e0c190807200a1703091f0b0301091b0b07020a0e180706080105011404150c080f0d0b0915060d0e011b05070c05030303 69
    0x28510180080042e00c103541f00c1c1e003940d01858021008004254462601500d1168140506003407941c0a200281d22580c04000301c440c100031405824892982c0140705481c0001701a009000b07003c40340c000d45100c00d9403003404120201c000341c0240060703020740c20118031416460059050342c0c141001084198400000e1214894824111150a520010000c0c400600c12944041d500d94249036030340382803020040e903100540c0c003841d4007440c0665490007030040512442800a401a16000381044070b00034640042e6401200c084800e81d12061280386c0030306011341ca40050380444c040c040140031550f0b1011301550111002c0354020326107402c011111070840000303500c900800008460003000c01c02c40038180d40c1040441006281c544d00030b541450081c001213130510b0301924018000440301942c00303c0483d0100c0020f0b01c0d207460400f07600c4e554030141003c0d120083e820340d01c0319041808602080e4040b1b1158980c0d136034980e269059441c069000303071500d0b40f01c58800c0e403050060284590349120f2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 469004892 1250 469003642 469003651
    0x70b0c160b030c390f060606041202060d0f1404140d08190608031801030e01020405090c03040501141501080a0905030a050a200706020d0804240902040f0c020d05070506 74
    0xc10072948040000e900948500309000201d05035032100c21000138503800543d6400765080381003600d4940d0784040a0250b140520f00c0b511422035141c3e501d080c05418030700e006000041809502050107980d42554105840b07160f2030b091407008040003088140f0001801c18582088504040e01001c107841034000c06660010f040343c00102c60115100315025040e5000e48010b1800f9001c1e0ba0b100d00c01c1c09104414003d6075424140880d007000713440031000d40184202c8095440091540010b600c3c2c2c3c42d5161403d4100030310032139182d9078a0110072000780d80706502500c220500200b02d001a55806e000511000010303000c00c40c450704001c0302e20009a400f0003070b02d241030814681180c071400340020032107541c586141d040c000c08400500d02d80c40003038007103900c105940e03c036021179420b200403440c12208140211000351245250030461502ca1074049003542500c0350f0340401045640c0684c0000303080354880c2d044200e4280da6442d4480006406024a05010780c4605100d42001a19141c450701ca180050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 469006142 1250 469004892 469004917
    0x2103010308031801090c090e0d030635060103050a03121a01120b210d2309010309080d090209090a1703070918090506130503070f020102070b0c160b030c 67
    0x10503d035015209501085080781c01480303001c00385545400310001024050f100e140280603e00c0103984003800b07805500221404404800002c40116145a09007c107031401c44034200b45480411541c01010840d59010794040c80161081000038a40900702d07a040c501c1800405041503203000c000510328420000610702800d0107100d40961100b5040200402ea03403065000010302e0000d00c0500d9010101020a1408421078000c03290340c2c0c4041c0c032202c180602060610054401a040c251030350805008000f40c107060200d50102c05564100090f00720201d0480010b40c2c6620000c02e620702258102d070007510402c00340c94042401e40741c0030369805a44100300404400040440c442a1141c00e48800410810681d2040c0803940c08150015054290040d51280f2070300000c01d0048541c0c0c0c1004507480d900c03200651a0540381e507500c8110701000f04041c2e0640c0034411000640e016101e00402801d90050041e1070850920141c015044d03c50b60007003480d1180500800c0b080710b1040e403c4504a84450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 469007392 1250 469006142 469006171
    0x606010c050a031404090920030703021e03030f03090d03060509070207030f080f0301080a030801090b06040513060503010f060306050c091507080c0109060f0e0604030906030c1b05210301030803 85
    0xc04e203043d5030721855100e010384514081d81c040031b1009000d03a40f130b91076030002c1010751481c0c0c142c0b0030140e8404913804065803000d501d980100a0250a5104c00700403c0d000e03043c1d90801e86404a44410b54008450049007074114954480840e0b81c18410000904022601c10f0507e06107580001e40e80c94040c040144013109410045080c04100400d40d180d0349100c41c0d600d0395a6840380c28507074841d00720303043c21000700d010080042101c040c0307070054118810001e0440c07806c0925110401091141055081205941d1941c0c0820070751003c2c0a10070100080d120045a820324501d44041100c9000300303003201e40a024041d1611994481c100031350145600c030f86282e215070042c100718405101d42c414941d2190700e0310040601300b0545400c0442001004907003046402c04009003a80c40d62811200207000134507200c0c040c000180268840460f2104600e040002c0a4612106911072245a40c09031801d0b405902003924420711a807491070340d5900902114103651542e40c482c4860300001d031034042000d525 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 469008642 1250 469007392 469007417
    0x151e0e0c07080c0a0503120f0c0f0d0b0d21081909020a09090605010f0509151917060109061710051b12180115122103020c0606010c050a03 61
    0x41000d96803c80c00301015542480041e1034042d0f41c90744059642c3d00621000000100c1c50685c500d004da118141034009130349801c0e044558464994000780140c1d02c030300c7d41e80703600d09138607101e0241000202d40704002d40b66001c002e05011140c1840c03940703016006c200031034080000c10007640042d1b404150002d0400314041c1c8503840000c03802c01030b0390800080f0038a0185804203101c4d09402c0343e41244da50002c0d41c00415200c5090008100003150350b080a1604628514807500f030600c9003c03080500c120780c0f2403400e52980c4100c00c02c07100d17014940805520010041c82500131034401c11000b05288075100c200101c6500e0030075100c3c0341c008620b001007a90f8800149509482c202c02c99070720709516180c95542d1403240000c0c400080c050f0b540300200444403140c905100014411040480b10b4841071f83c61041c5801025020a00b8980040b00c0c04403500c00500d0b600c40000307a01c260018031ba6100561030302c0c1d01c104458a40380e002001c80307040000400040b4007282e8085002c100c3c2c03035058a004100840c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 469009892 1250 469008642 469008653
    0x9010903030e0706091a0c060f0411090412181d0402091e180718020c1c051803100c08070f09030b01060e030f030a03021314101b0501151e0e0c07 64
    0x24842c0c0d025008d020f00e20400501040f00c41ca10342c03080e4401d4440e03608140031301050040c2d94408640092502c05032403424070000d4000c201c0200c2c05d28210030059080c0351103c440e00740b000012078100322500c07402d82c20b00c0b04624003500d0107540b1602c200c285100700034501d00d49824074100503040410208070000f80c0400c0403401c1c071074030000d0850000302d0720f01040c0782c50300c1300002d40c0b10380c1e8803421703070302070120070402050030715101c2591904580d4449040100c2c102130031414806010070035a0602c18100c000005000d540100c0a064205484543e92031a000c078001e0b04610603450300c0010840ba0140071f00004140c62161415140c6610b02a220441040c000c40e1800001e10b103000c50390300c0045002c1d014030342e241e0018030100c441040140d071045e0362000141c030700200e1032041d2a404a200c0100c10000d900c200c014001c140790742181c00000d43c42c1e41d11414212250500100381d00803445609100d85800c240c140c0040c0e59550308049200c3d881c0c9148a480018090300e102100703403001078043c040c0304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 469011142 1250 469009892 469009897
    0xa0507111005121f06030c030b030a08040806070c120f020f0f0304060e220c0c0c0e040201030e03030f01140f150405031606020c01050f040e09010903030e0706091a 72
    0x84014024101c40000d140000d4080e42048908503129015540000c9a03c2c0d02074244c1c02440301e00c00500c80c001c07401d201003500035000c1c0040311003c16584840c000c48503a2300b0081250103d010361304480e81c80342028100d600300807000740f0610038001840005800141c40e030b50344502100c61481d02c4000e0000c4801c00320304060f00041c0030501b9102c0e400d240c2120303420110080003190515110198052545018010118034032a1a10a44220705182c05030001e915040015000c076945040007803003813280d0381c7c80f404d40d02d59001030300015205400c00c021941c051203052401003030000110700350701e08102e119101203014010b22094000104182c1c209031100c103101d103020320340100000400c44400314281c5950304940b1400307129200355003404121100240c1c2440036501075034007030000f240603080192820f9002500e0211130ce0387c10000081d000161122641c045c000d8000086000c90f21030030005c003a1005541c00e84030a0b0058901049000e4118004404441d698588500b207510500c80034201d50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 469012392 1250 469011142 469011173
    0x4021903050a03211814070e10050a0e0606071101020f0109140106170322030f0503030a060e01080705040f090609030801060906081902160c080c0901090c050a0507 72
    0x148205001c120070141c100f0200011820072458070800c10610744030100a84a4030116403480540221240c00442c1c00560141b0200101200711824940d0b00e0929022942d0121245410300194000511561030300094085c014280300740700011a00340400010118815408001d040c03400021202c42140d000340500a42443c410008014440260a020181c3c904008103034146520b05100070421280754400011a412900011802c281386c0f550503090703428518100a1000314607140002c00508042d120b401d445105002447e140e05000e624182034420035045031400000110040c0500c00780000d4507800c80d02e0031240400d150b10301c1e030280002007844200c0603008074140000d410905820110b4a4103c40007540c2d00d1102c1c959429003103a802c035040d1242221324080c40c0203034105c10041c0d0050401c01c820402c551100301510b69a03800c0160786035000d40b005070401010400385207080d0501c80d0043c51005014041241c864074010103e1107150280b6051140c00700306030041c020040c15500c00c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 469013642 1250 469012392 469012403
    0x90c0201060806010603021809090606010518090a020d0510140f01030204090608030a080f0403051218070314120702030d141b0703021f02120c012c150f04021903 71
    0x8130350b100c9100602035488195201642d040d0390110ba246818080005031040d0340070800f80545449440044615600a4460703185a07051265030301401d0391008145402445841c000582e40d407510002241541c178020424402100c40d0541084443c0000300d086034070400407186950350340310040040e0000c0c0202d401002c80b00307160960124962000100801e50070364191100c502c191b8070042c209800980c100c0700200011310510003030384804820107e080c0c0101500c160044480d82d280e080e6032419405a20644d10041740c24000302005109002e03e002c8a603030070f040245000159000301c2c0c3e0310b14a03500e840f000c0061034050035588048907010380c0e00d4040c40480d00c601c400007800c445079503070903180420b070300c81c00c03045c0ca030f600c080f0182c0b0000c94400d28181d0041d000340e00201c0f01c1407001e0341115002c0d810780e540754920b2081d11030001c4041e154061031407103855020404180360514010000000244403811001809030345240700d403410f6840341d030440e44020070b0089200301d61081c03015070703100030302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 469014892 1250 469013642 469013653
    0x11205071407081e2803060b28022b031b08091504020d020103110d090c08070e010608010e0405010603020a03060b0111060601050a0c1a04030801060807020303010b04090c02010608 79
    0x2c10800f079000304101c44440a103001081402c0b0b2407580b180c82041c205030320071002e000707020f440c80c07001030241520b14841e0b040021f40c003540c5071a42006903103c641c0001ca038445c9101445e10300d071a0544282256040c6100402c2200ca0038048920b58115521905e805c00010141d0140392922a421aa014040000300d0608034001d159018101800603203007151380380500211007000260000c41c09205940040920000e00ca1540041d8010604c45031448810001045104d800700c03010301031aa8082d02c11174240319100d181601850904505070490020300c000c00004000940d4410b80c2d05064805c106042091621a494640e00400f0701e944000e42101403090000144816503000c03c1440c0400e803a0f0389000200c1c0c0c905103468070b100320f448a001c20000e11214071f01510403041180b03c680310700c1c0c0c2200400700b41c04100c40030741d50407902100007031261401403000c203138088400f0b900a600c6000841c1554180062408280941d00641c04440da4420410203114802d42002000741400421b41d903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 469016142 1250 469014892 469014907
    0x510050d0633080402150306010c1b0305060a0e06180313061e0e032d010204090b030d02070f27111e041421010204060e011d0112050714 60
    0x540740b01c1040c8141c0b01c040741002202e24a1030040740007910a66000740055844c0744030085000b0f6642000c0e05950401122880e5040015824150311105841d1140c0540c115495441d00903d0120028540c45004d410309602e0355101c0300004100d80c01032030f0309411502e940700300e004052441c0121840107510040b0f03a407000034103039000f845a0a83e03115410040c00310031290a001e03140e2543c2040c0c0a80c06038800300680d50480301040c9420011021110405400ca202d1502242a41c006402c4801029555803400c0c0d0149010851694515a1030000e0000c1c203141c103260420342441c910841d00c1c1a44090800380100300b100d4003072136450184100c1007000c41810078810030a41c010300103500900104c44003081000c4900b0099a040760050380361b81018221042c14051200700a4440703c00b80002c40001820941b8207002a0019107055550840d05000c80c40004228802c0c981c5200e41c0e41a08400000702a644415000c08145c46050302017a143c0314003204403072a90a2450b0355121450128a04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 469017392 1250 469016142 469016189
    0x221030c060c190f0c0b090c040f050105010801050909060705030601050f07030e191a1b0706030f0f09110108180109030c1a010503030a1101020706060b0c070801060510050d06 77
    0x200700d1080c84441d286100900c5140903204d0050000c0d51802007544042d58100082c400c010b46c40e4420403001c19608a05250800302e000d4420b901102040a911003005101e2940d100f1001801400110313110b2800c0c0c01c2074038030b99890385000b0f46408200040000000d0b040d13405001140d00c140091708402c0e079180c4450400030149401401d07084e100342d29640008980d00172101481060301c00c201d4034181c9945010302045802e07480b8402113a02da403180c44459a01990a01001c0014080d03920003140c0300d4600200042100d2410507003060480c58200906c0201c0c4036024110be6204c82800c000107592207a405070111076074891010304c607540c02c04910b10101035019410001c0b9070701c40c40e11401603111002000c80f80304004d001d05500f583c414080100e00c14400e14266061a52100c001454042207850309400d03100b040c0c01071105000001001c0070416820450600102a400001c210080c10f020000710710700000070000042160104403101c0b52031856001200070401c103c9403440d14280f15584 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 469018642 1250 469017392 469017397
    0x5090108060910231e0108060709050409210e04060b12220b0c1e070213050606161506060e090109050108060c0703030b0d111c0221030c060c 62
    0x400e040c0030fa2203102c410004580600d8201d0308007422446418030000401e50702c00000105401c0b1040030456850406219940c24075010380fa42c0b602800c01c5190451024142054607030055005c3da142503e00c502041e4900d0001c2d0014540c0720b10003140100c004c0080340d02c0e488801c41c81e44d1003840c003200080d000020034014201e032948045190682d90b60001203900c1031002d440c85441098141d1901c80014800c1c040782540080c605201e40c1c10b118103440b035980404003c0c001e03003540705400a00342c0d09500d070200107141401e03003020080c04603142c12400700d1600d0044038040e03003411000c06010b004210304e41800c059000c43d0050100256135a42030010000008021030303a000d12010380c0081900c40a030301070107051f01c034008020103060720761540b010b0070b503404ec2c1415020596189001c0b0010383d5407000d0009540d00504000d030f00049500200200c101201c10360f0214a151241c1010044c1c40d43d2903843e100220620507a007104210703203002e5085209148801843e4002d034001c119400244a01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 469019892 1250 469018642 469018651
    0x20d030c05040f0b090d0f050706110a0c090c030603060203040f2a140f03060906010602160e040809150d1401090c051218030c07180c050d050705040509010806 70
    0x4050003600380c098019100c5200300e000e41041d040b40000103101100c800c500410303c038040134104c4845040140c9584015104009044903d5004100200200d0340e2080d6003902c000704020182200114560b50342e49045600c2c40b846408170b4552a04242e0180a03502071402942c1044c415560392520b807a00004081e0022011100f01400081c0b20420f2600c5980c4580c0c800081d002801c021405c01001e1170313104490100403940003043c840709100c1c6440500106000780140d0000741400d5042110103030030700a40141443c001c06102404002d00140f41e81d42a1300036800c195440c0e41c5074420400f01d40714803048518404e10140000303413002800400e6020080b40b40740c1402110060b40c8074500300e02903076446031079040090014004032490240350849070b5007000050203501208020f0f03d8032103040d074008185060468012510400101c2c85002c0c0203426400e1441c1e040203416071500d0050807500070080700c864000e554400040c01c29004004071009050000c0c54500340f5a541c442c85641d65100300d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 469021142 1250 469019892 469019897
    0x60609061b0d0201021306080402060708040b0706050f101e090c2c0a050402090d050d0f0e030c061e0d0213080c01021614030c19030b16120b031606020d 67
    0x4110802c82d62043c030039070f1035000c0c9040180399070a281c1002103629440c0a48140c1e8040d0b800c005600000e10250300510041034542c200c070b501c803202414013800f120001818030b64074505600070407503000710104441040c0c44500100100310b07462161694620b105a40003059038130302c2c00003165040d42e00504848601d07a42903c0d0342d2081240380c0715200c400c0c1d80b00481e00c1c1e0441040c20b414091403610340c010f014010f0000d0441c983c152500c2d26210b1402c402000b9a42c003065144000d8103809901c40040000c51030294001c008200b00d400124010740b1074a400660794400b2020b0360182d503400b982c1120a40301600c0801d640340c04d0511888514200c49205403800e40c8942c0400724819400419190681d944040c9940306403403824903841240f508142e090ba0f418020200c040b030099a03203d01641d0704a1000aa20214509501d4141174254000d0a0000e800442c0c51511280c030740e00c840070706a516140100450346042501c0401c2ca8401d044000340440301803440d011401c0c0390300207590a4420221b1707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 469022392 1250 469021142 469021153
    0x70f060b0a09060b0307050d0902040528020309030a0e06220609061718030904050c070b0705070803070f0908030c100b010c0f120504050a0b090333060609061b 70
    0x44503400103c641d584260803d14030144005003400340940d01408903c0115000846c07040c095600080440e441110000c0003488003980c10f9000400c070741c582941018840b1421417071414500c80d0240d50f4040c089200042101d400094001f07501c8000540c0c49200240c03402c0343d01e11f80407058840c035980da68050300c40040c404850024050740300361900061140c601c0741c1181c0e01d4860401c211001c154180a040c042e00c8104050709032601e135846214170641c0d04d0b608184d100c61103843c124541c3e850280290b0200f2200740300000206004c1c1c000c49400540d24140080d020940d2181520007107910350240825020205040b01e800f00041080075082c040e0036020811a000e0600548506d410f5480103800102c20003000350000c0c490201410100e0007904110703090941c0e40002030b848054a82260000d0000402d01150368103080094074201d0340e40b510352244c4041c02242e12108248800d9820003c43c94160215010b80c9403e0101c6424080103000c50f41e4649c074458611741d4141030b039000701d08a40301d00f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 469023642 1250 469022392 469022399
    0x30f0105011a030628260c061905090a1502030a0207170a151b020a0b060d0308060d140f070f080309030d180b040e0a0513051c05070f060b0a 62
    0x4a400716841110700400c0c117009101203a01038007111405d00500190204140c801141c20200515542c2c0241d0200000c1c49419515052132414494420310190044009001c54606840c2220185049000f6854116120700c90313031001680e9500f2580c4115101480000490442d66020000388580007a64003200d9038180d8941c41c501c3c0c1e0f644151902d440b035401071903200000407961007200d6514801244042600c400c07107500156905c107544102c0703006da845040e0040403c15086401503001030211005190321901d07480c0900000401003156108420005408041000c10710040c0c003800659821140f10081203c942aa107103581e0140603080c5030703d204005100080001200c2020b5800703806040289240c8400b030714880c10841c0f0030042c002401c01d0209224145502070801000d0200001400c0c0c10000d110004a50001e002408400d0b403079414680450000a5100a6545003040555041e0160b25085813a0700488400420550500900c2c60500141da000b0140340c20044170740441c0ca9a8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 469024892 1250 469023642 469023689
    0x50f090907052802030d022101080705010f080c070215070b0c031b03040206090105030414060924090a02090924074512150e030c151302030f010501 65
    0x5000003400140e01c20007501050801d0b54010b410241c50300040c42c07610040e4841e23000400c004c02d8019000c182d11890081201e0b40e4081e8a00713404030050700b07101e50a0b060030320301d8107940c4c46102c070041d0181401000f4101c200c05035032b042341e0000e41c1003d400b04a605144000f0b00d2141e02c140c1d44030b02c103010480310b2a0300244a0720104d078007481c1d008044a00e02850f00d00151981c1c0c0006200340c030b000c90070b4a01d0f04240c61007440514441c81c0880c001c2c008641241e9052a46408072410b4007a0205080d02001b50200b4009503201c00280c04603403c0301c0594030011414903010740d00c0c8600c222404c15040130700c0408400c0e65100d00070721710394569000b80d41c1100807003501c50400c0005a020700109503031038a22141100002d150030b00d00f5070381c400d420b00e07141c0305140c40c0c903411210110f406070b54100e0340d241540b04038481c5013100321107003000d189440c42000b0072541d10340c070b072002070600340c04094089207809403181d4141c0700b455400b9064074002c06030313000301c0c034000e007002d1140c0c4d03916945417880e0f08601c88 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 469026142 1250 469024892 469024957
    0x60a060203040b180a0b03131511030a050a150308120702060708041502120408070b06010207050d0615030c060207080601270507140d09150516050f09090705 69
    0x42200c6043d908018182901e0a500084100b0898005078200360100301c400000780218401c04200510307030884a1540340081000895404541c09a0b00d04040d0200c0254100100c1e41c10083d1140089059210a0b0103034004004244001c0b0b2552440c5900004014004c0040c1c5440182d60a030000140c0d500e04080c1d1b182e90f4104c07140e9000503208030004001900025008034040d100b00300041c00e140340060910b503a00800e5806940ea0a80403815008210b00054059030086080c030181684914044c0828003402c0040d100820031516940c10440a1041000710801140c00100022020383c1e03420b000b03900e0300f400d070080d03141c940115000441c0140c0200780700f9150104041c1140c030f5a0401c4a0524020880a00800f0400110304107155205000c080500703d0656100b000043c1c50105180c200119a0101c1141404604110400819403000030f61084080703041d0818540d680e40c0b010300c2042c548991308400c2e600140034010301209517480301c06044000307445107602e11208105400c440058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 469027392 1250 469026142 469026149
    0x3010e1903050a1e03020c0c0307050906040e12160c060e010519050714030306120c0f15120103050606040b040e0718060801050906060102010510150513031208060a06020304 76
    0x2100c0d10410240080e2054000f4841e0b100d42d4a030403840307100c0c0301800308a1001c908041c040040e40109030000ca0b060240304012540c032040b03005080c0341d85040d0110340d05240040c500c03482596104a4260f40602c144403030501c00d030002900302da41d480e0070030300c40c48918501182522407801002010801a006012070241c4c004140c68030307818480f0425039a01801d081000801c10007009004e07180005802d41c8a42024080e0300001e162246042024481d9000c03000056000a9101c0150407803551070f850703410007190350140c6284d03c00401c8071080f07038002d200704100600040c54120001081c08030105400f40180021117060241c031030300000304001e0341c0840c00c0d01d2074035030850700e0300304644203184050100035003468201150b402e03a1107031110b0842d1400c558405682c3c0000c0e04106140d0303030a11a840e44205030511071500242010100484201502d1500061000001741e4640b0031010840d42001543d01c0000c100c514030040e503004118078403c0d103642d0300401c040711011413564004401d84095 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 469028642 1250 469027392 469027423
    0xb0316030803070302041701060911040b16050a02030a0609020103061d0f07020709020711090a0e071a0f04080c0a08031e0d0209030706080717070801140102070906120203010e 77
    0x9050954640c00c11507803000e0820320906500b040002144407801c45a994803058503800013070003030700c5c001d8004180c5500e00c0c0c10300b10010b420482440070000d14415034940c00c0002c0d100803080002860301c1c501e068500d0070301a600d84038000007881002460741003800f4161003030b0303000c0c0a20b80da80c103150080035200003054030451a8074000510341c2c11035440007950111485c41200c4220340c2c0c52040e88100d920065066400c0d10100d209107541d400e0880d8040d811000e088010041070380c19200c401d840d84006e00503e002485800038483d544044401607401d03000302464400c0c0d641e0b070b69208240c1d40b88400c84885008415070440002c4400001c03080e0b0700118100c41d00204d002500204244550703000d54400842c02c0d1382441103800750307141045484090400b6484000160402c2540580500d0150150b08510a0503904014009501c65141411034200c24012480c10f031000d001030b810b040054009895035840c14400050700d44082c1c2e045e41c60f0600a80080000c1c0100f40881900c0765030144c0703441c06 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 469029892 1250 469028642 469028683
    0x6010e010c06090206040b070c170307020d0305070b0f010302180c0a031e0204080607020609010e0a3f0e060c0c060a05040f06050315030303240d0203011e0b03 70
    0x119401140e050700064491000007695101e0b90b80051181e42103608010341d0104040381d9041001205100400501400710000880c0d005132004e40c0d0307492085140c000d014521103076520302003601030703401d6a56565100c0207015052403c0c00f4404a114000d01c0140d111b0203900c3c422841480f45119039900881410022500d0301003c2c6000340c007d8003110604200d160b88024a80d460407103141302a102810000700942018284084028a00700c00a0b082070701c0c50b4541800072101c41c60000d036044c1e03c0b0354007008010712244104100e000103410040090161110b942e800002e040c0503080c13046103284140c941081c184a0f903030500c02c0c1401404e0303049410340c1c00400c110001d450a080a8100c2c0c090503e4020f1030241c99074044050805079602c02c8001c608040113002d0100c0781d400305806512010f600450031807034528444000e524141c1040400300c1880008084d980d11654141109950041c000340100c5012842080031507a04411241c020703031806070340004504e408100105412003a2f400441c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 469031142 1250 469029892 469029917
    0x515040b01020c060c0106050f030d080f180d0201050402011b0b010e040204021b0f0c100e01030e03130b1c060f090c0207120f0b0a05060102071406090303070804090606080601 77
    0x40200034084420703040d07100f248111805642c0b440001e1210500910010800910344020300c02e10340b074001020361007500300c4429440555031111075140d015201c0d451810054544403004079041d14160080010380c050495810070864054000c40c0c080d44c802e81c0c55841c8111840c1c1c00041141044100420003036441004100d50020503100b503400c00c0c00103000620b4044042d9111015040c0d85482d0482604548030001410400303201c11ba0650788255180c0403175050fa940014202d0040c507203001d050550700c9622500c02503041064903a060075008a50320041e45030580c4c1103032a003001c00900078040d900f0f28440c01c940719a0245408462544613132890090401d0071100107000c801e580710f400c621541900090100c1d85004e00003c55004600702e21721000c00342080740340340c1d038010510f0500e0b508080a011041e40d0008100003280c2084c8107000300c42c003100000038607520440202d2581440302240b25020311103a03800070412990b400204100e04e40e034903001690900720032580035000c140c0200d202c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 469032392 1250 469031142 469031149
    0x20c07051c030804021c0b0103060b0609060306010809120a0509090604020c060f0a090c17010b10081602030706020d060f06030e0d0e0f0901060e0a06090305070b0c0f030309100f0515 80
    0xf03a400520080c08241010058125018608031140d0103407001c200390b40040052010a110b82d10303403400c040c0c41e60781c60b0000010229400d0b110240c840d90400c01e610f4002200d4030303014480f40406070246c0d10f181e6034410100100a102d5084021007a20401d041408500035180900c201c4245100301400380c9a590740d550b00f40c0e28101d40086c00c02100503110848400001e00302010140546881460710500e00c0d107190600e400c55000d06509401460b1a1840164013500058910390105a0500308050b820000004a065026000c0001c2480e4000714200561102d16005141034a00d036200030307185144e842404500391448007090b0f41c09a0408000403c1c0903204040350b40042101800c0c68455812043c04101c9001e424ac1c00900004c5c1040c6407500986420320721072000700740515083d041d0714115141c03640c9546561003801c400c1c038400a88554419014082c29030090000010b6a40b24039200091b01c2c0c9414192030b00f1154185022240d18036181c0520032031b80142c80190f4620780074200082070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 469033642 1250 469032392 469032407
    0x203031f1503240303084f060216020306060904031715060a0e13060e22140606150c0307030e13060906050f010203090105070f02180703020c07051c03 66
    0x441090030f90481200070030000712440114401e40c3c0d10001858000d019030b1341d0186212040403258203415500322000649864080c107912000a442c030000b6248400d440500c0d080d03e0300500007400443e103100707051842d03010b80c29000d0007030702950303056a00c4400b04244114211001400b0858401d00009242d55000707400da80950b468415510008001e8005401c03038108200d071100041c41608104a80d04026400760464200d4000600440741070000d002c4440394010310049201d00e4801e1800070030304c450300c4c4402000d0b0b00074a113880241c1c0000000ea88030502140c4040c00b500d03680805402008040c811a0744d0112000065410607a20f55002c82d0860485111103a00040c0f10048070030f8030849104040c014400e91400148513403402d4203100441190501107419504240110112660848201c9610b20351003800750301c6070303101440012084c200c01001e5042e40340809041021258040e0b0040c01114107038022918603956400802c420b032051071501106886001c0e00c404002409000c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 469034892 1250 469033642 469033661
    0x8040b041106070206030108031e0a0c170d09050706021603030917150c0a030f020307051204060603060207120e03010b150c010f0207050123060d0f0812070203031f1503 74
    0x9220f00d40211070300040c005400a81203c1031940002446414014540d90000b0b12002488031003401e2030041c80d8003078030f034115500e409044030003040d02500300c04010328211000000d4850041261030014100140e40d41540d00130b00026110f02c003c40b40804d011074074000c00b1a075042c0c0c2c0c2d40025600740644807000c00703c0714400c88018803801400c200515460b01b819403140941110082c0c07201001c10005040c0c0307440495201581d841001071240d0940d0000480d144118030321116520360702c441c50090001d00c2941c0c03028111610100320744040242d80c1c5211010340c01e00303a0302c00358220710560806080b603101d801c0040d0303c000d6014010b00301c1e80011010303104a0038103a00018a5010b0030198038141d9111400440d11a5911080c1c5d411408141d56042031000003e0f8504002d80b0b000c0010410007040114050180c09610b10f0580800c95000110349100c04074022481880c01c4c0001c000e541ea030800e4076084032201212200c40c405444200382d0100300c848059603c141400c29001c240d0003400722a8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 469036142 1250 469034892 469034899
    0x608190609021816140a08060112140a050c0c07090e0a050a1515060c030516051f11120406020a020c06070807050105130201050d0b0402130b04050a0608040b0411 71
    0x703000c100940d41e0381c2c503000b08004001440300e9a40c07501070254004421140400410b11040ba000c2c10102c154200a6440302e0706142070281d19a191480180c030f00056203203c0e10b0310740f030a28100d1190902c46100e014029845002c2c18016905c401308188100c2c02000144071803580030031000c000004030344d0001d00380340d041e46054400ca884152122070a0540c054016180341500c81000f0402d03190303d2140eaa1034941c01c14002d0180c40c10840010503880881c14040d08214001c61110440b800b00d485d00990942c0c444210b61130000b2840b2400c00c0f005040004040c13051509170342c89003040509080f18404511951030039115a640d940c0c220003900010b100504500c105044c00200c0e89400c030091001e05d0203461105d40f508400c1c54594250b940c000c0c032044000480000b02401031340c000080e2041c24440d54004126009030501090080c021040b9254142c43c08010001c0d202c9802c0c1d00070001c0e42c50903903221407101d44506040d5031070035081d1801000042d00e03800150220b4030000c800c10300c2c2d0000a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 469037392 1250 469036142 469036151
    0x519081f020d0f05091c02060403180b120619120308040c0302150316020106060512190515030c06090f0d03020f0313061d030d030e0c03150402011206081906 69
    0x101503402c01c8441210511081581e25001e20021100412a01c05130082000848110034a041c1d4000d480e80b10143c001014401641c44851106c41641910400750410112082d20bc0e1420018907961a00694406000d00c403807511840d51100035180341015560f6044018500002a54080390000d1005000f0344401d1007841022006030740da040c2d0002d8060140d498540c490070b0403008000480761880c05803095a26101c0c08201103500401510741b204c034039400210407a950410b0f10103c1600307022880e004ea602e00001c02c81460035000e450502c545050b800c642052a040c41801001d203c0c450805501c003e81092400b420300d802c000000d40d40b44244141c40800d2020104540365030000e04070810741c4c8500e400103010042d0710a00906841c48500c1a1030f86032210b0700c0100e83c4806211903002c0401d6101d4a210001840802566104141c040d00f19010201e0b50000c1d03000e60f0340191001c9000901000004074203903458090401990340880150101c005011000a60a0b03501c1c4400c55246844 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 469038642 1250 469037392 469037407
    0x9050d140c06010902070c1d0a0902040b0a2601180f150903030603020f01020129120a0f0506060d11011209021903030f020d020c280b040519081f02 65
    0x42c081d440c0200540c0d440580c4030816450726400c4c180e029000010500d8201446001e0074403135068043d040300400301c00054014040c000304d0040c0c0384c41406903401031a60070002582c60051100448840464003040002c48054900103090315020135201c0d14800107003c100300424028540190850f200769920f03035150240c20345c07103000c1d80c05120040d00072a5940604000f5810f144010380400803091008202e20003241071180d007120b0016204100992901c40d0050281d1140d000055500722104201c80c2091014034190444000384102104c4038040c0d44086801810004080880329500420803004a1041c0c8011520361956040c00d40d6815210444240035840b000300d82460490385030210741c0c03110300b5410007401250300c503a00b0f00215885074ac0d68004099020400b240c46a42c00c0b2a42030410900e4418126521440c601000c90200030110026803950704100802c1243e80998a40e00600f80c1243c589208811510818400da00300411687c8148900303143c03910340c010045801401c0c03059 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 469039892 1250 469038642 469038667
    0x1106180f0613060f020906160606050a092403050d110709020a030c0201200f0f0702040219030b060306061b070f120201020c04050c0406080c0c030a090e090109050d14 73
    0x281602c2082c44031902d0004041804443e02540086043d0100250301d091680000f08016124804001c0c070035501c0240850708004070b5400400083c20000c180603501c9031103880301c000800c0804182c4c0c442e40c00c03950f40651105a0804080100c0f07070460701070980d034070300450b05445004004051041d5806203100115802c0c1c1e10307101402200e203044e40c000a0744445110301a00b1600c8400005011950404103118948550401c942884282c01c510b00d4440000c2040e1400d140201c04000754091300100d00b52016101c0240c0c480d1405c4a207907418010080028240107080c4030980742c180d04980c0c2049030044200c0c00000c0380706040c0750f420488211560300ca201c401503281c00c0d042801242c249115084c03e641e8100b121941e400c5c0c00700c90400040c14005d9420f040342c400c1d442a141480081000201002642c40580d440a00c8203400e90313a8503482d41d8001000281c10f8011005451030000c00300b01610014417444000781c3d03200c0b004040a8002000940343c0740c0c24a03598840800e030400c0504001c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 469041142 1250 469039892 469039903
    0xf0909050403082a091908010f0b03070f080d2709051605040f0608090a062c19020f06090a03050105060f01050a050306240313060c1106180f 62
    0x90081d40c5101c100c1c2048811900012031000c400310101d2107424014800841c4d8808444640708201c5480042c076004103054011008194401c1495520345085050f819103e0307000b0400b007401c11400c0d6100380d61580c034000781c07ca44501034000c190b4024402502d07490700440b00104d00507900e48415404500440040b0440b40c0103401c00d280e01d83d02e5a0500c404d03100c030004400080400c5081441c200703400c2505070b4544003403d00c904070402c050800818800c4030700380800c80b03546800c0f4001340081c510f0010703c0d591502c01e83d00d402e1074480c504140c001c820300d008566480c6066045145c080110b18580811a99080507640194170820420100601380e0304c04c255003004500c50000450b841c0392000401144200c1e180364141030003410032001940d0303507018084a1740910700b101d15602d40002c903840800d143c8403510020004003070020611456400a02c1c51800c0503202e00000d00030048072600440d00e2050b070030605843da50003e40454081000a000c841904200204840d04d402d60f03108010700c0c0c80c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 469042392 1250 469041142 469041151
    0x1806070c052101050105040b1507061104090207020109061b060e100f06030b090309010f080a180303051605040b1b0f1606080606040b030c0c010b060408160909020f010f090905 77
    0x2c01d072600005919601c2800703124010901260b007003140341c40000105040d0810201003500313003040000c1e860101304599204d9800ca40c0e1130428592902e84543c9060000e41c0000c106902050100d40002500351241740d074a22603081200000440b0400355030303440043c080b140b01d14402070003251510f00c04050280b081c0d040001e5540310200e001455400d10420580380508800c0d902d030402c120040007640c2080905580303c1d0035141007140350780c0348030500000340000460402541c840150300f0040c1076054214078080d140100c05549050310b8881d0540300c1d44101e104000341110140084046035072494128181242c418068411000355100c4040c10034040c2c2c2010a280c0c031520030140001a4001c403940d511032000c0c0c803110b00d02810854610aa40401000030b0000e8000207070800003c0401e4001140c0031402134a1070f916242c942c20101e0312500000200321402400c000001020f503854014082c1042e00a030081c0d2810380003c0044809800d42000c65092004d8a407000a400044e44200c1d80304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 469043642 1250 469042392 469042429
    0x1a0a090e0c040c120f180b1503030f040e0601020c150f120a1e05060102330a021905070f0201081305030310030201081521070e0a0609060b1806070c05 66
    0x60070702c0440303802c081728403144840081c03610703251480c1340c000c034a2512603500c2c9401c84041016940c941c03030b80d407a00028541015406010100d642d9940c1d502c0b40c801340064038060148503200340d940300d004980d100132a030810350b4442c00781d0951000d280d009200402254540c0e04440785400801c040c02514804240c0710070f04295982d6000402c0380c0da0000c2845120345020b2814805420110b0000350b0741e540880c0d0b60503014005544000340543c0301405524141141c500d01c403e140340c40002240250000c0d01380f100c0d0f4a01880e80351850710300c610115030303805a0205120303180b21030907001100d2100e401899141100c0d0780310400404600f081014500c160683c1107500c0210b07085200043c034803000601a9412101c83c444442819507500d1010a8209620b03014034003401c0b4a42d44d42480d04909901151040a000c0107005076410035420600c1a9810381030140002c5a40d807105500900c541200c46c0003040e03035003030060400c0c6000c1c0b0045c04506e00500007034101030b4981c8009000100302443e1800c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 469044892 1250 469043642 469043657
    0x5130b0607081902030703231c05150d2114040807090c09260c06070606081204061409010201060506030a14011e0b09040f0c080a1a0a090e0c040c 64
    0x1c41031241d040f00c150510992001c5c2d410800385a8003d40320341011007001840d1400313140307050300034001c210684119110f108600c101000042c0e03108002860140c440c20000512508010650f00f80412500da190741c0c01210501c44100c441e10b004ca59400c1c00741001304105c9a4003058624200d045c3c083d001404402002d003121920706031108003100c00c5418050705010b000207003001410a950b2864400240f034480401d0046d500320200d41c01d044151109561003c0089001c1052001d240e00c69803d991a8004460402e1300c90501b0b41030f41d0041e031183c440061501c00024003c1c070f41d220701a16415106000108044d43c032440007680d2070b0402c0345d0300783c0d040e60b480a140d2060b0b030034100c199005013601e030003961040020fa00503103200d1b02617015a001010002802407210303110790b44100000d48940c4000c00805440383c070010f040080542e003400b40e29003044110602c0420200740044441e90091503c0001850080c416000c0d0004071008185801801c8601205131518001c1ca81700d1106552001e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 469046142 1250 469044892 469044907
    0xa051801080706031505010c050c0a0902070203061807060c081e0d150509160c021003090b0f150d020d06060e0a0c0201141807090c0203180102010c080105130b060708 73
    0xd00d060070b950302c00700415040c200404481c4003402210302c00d4070801c0c0b0f440c01800d202400c00310718085000400a812041c51440010252000d6014000c550320071400d86100d51110500400c400f09000421480e90304508010002e580c003d010590b1041e00c1811014103010030960401c480201c0f1040203d1240c00000381500b044010f48202c48d100c1e01c404022120881c20030000c00c0d41200002c281c281c6082c20712100745121802003100c2d0b13002d5940104003171070065031110018060560050308a5a00202030041601d811042d5110b0780701e0802020140c1007491841c0812225510410080e80c00c41d10602202011800c41e01400001d40f11b1000e014ad19401c14000510850b040b100c8841c00f1a45041d4030b01191090446103070350014070000001c0380d00150402d810741828255031100c00114502446500b0071500800030f01203440c6005181c104076013032100160300341d0350b03040f81c40c0d40010100340060000f0710741080d0306102c04188803000140e405100d00402d1466200c0e44040d0346441c400324091 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 469047392 1250 469046142 469046159
    0x501081b031b0a0302041703070b0c030705090411120c0309122116081305061501090f06030c090b070807021003061d01081b150715091103060604061505090a051801 72
    0x190f47c50302c490f000317518003402c5841d00310415402822007580c0030000000b00d03034030511690a4a03a00c8200038001c000b019445e20f05507107980d000003000090300580c00300040011100c0d1060324030070a80c0c1006040060b207200320000c07295010002c050040c070400040b45007940d0603d41000d01c103c001c0d0400e00050404818080d03ca020028407044050144444e0b200c00214040340b01034120070700b030020307580c1c890301c02c0d0040c9c0c0c80140701d421051184101341000510300d603254015120000458951032102d0744c0f603044000852180c2e807809005040d08100040041c1009000c1102d1400c8510b4009101da132102c070040244c41003004c44146038922640144422a0240680d041c1401e00701038003d54844a200800c1c5140308296032800b020ba400306900d030500000030109242101c210360200209055481d0220b403002c0a6694a80a88201c000040311400e040c403502d400e480700201c014883e04540c0104490551000c0e5049070000340000000425485642c101c1c104c4d00809100e0350407070360600044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 469048642 1250 469047392 469047419
    0x30726010e03030601020a030804081b030d060605120f0a06241e020a03230d05150904020913020a0305060c09030f060f040230010b0103060501081b031b0a030204 71
    0xd19100c2e810400030320500303a80010303600218561605100301c0c540e94038203003900d440c01170040f02c804420b40c464400442d00c1d0080024000c01608150812000e44c40d02000c658502a002200c0c0c40d03142954007255a0400c80400c1da54031298503840440c1140d1940188800c0120f007010801014050280000310540c0190070300210b04400c00c058480420390340d90095075201406405428031111070740d07000c0301c0880c1442c03036050020b070700b00510368482440c0c1c0004010002180c0042007404d034020b142219143c409683c0703004940040150a06071180781e60001202060001281c2c02440c0e80000800240140b002c503106491200d1010b0701c1d05401001d2604001d0503048400c00368000c403042110146080c0400354025405840b854050402d444070b00300c0181d400312407041f10034080e08007495144015002081c1d1242c080c4d0b024001185e80300019504aa4141c8505401809a01c2c07052441d80c590300140da4816152206040152191500c0c20741c1503001d102d05600190300003800f482150107003580d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 469049892 1250 469048642 469048661
    0x13e030c0d180b0c0a03030e15130b0a020a080a0c03090209010312180f0905070302280201060f0e13020316031104050c0301031a15120a110103050112030e03072601 72
    0x50783ea00c1c140410204a0f01e4100701c40004042c10f598180f4a00c800d00208400d2800702c6507440c410b94141800ca158205107410144c045811003001c200087e107411048c004c1c0e4490b042540c660400d00c2c1c49402104015028100c2040201030b03070781220501581c1c030084c28034000c50150b1140a40000c502000030004031030540d03400c0d0b640d00002c070104169501e0016140407035071000b4001850f600c030743d04e007180a0f1150340512004c040d0611100015460207141e1602c0360500d54000b001181d035543c1c0b25a10841841c0300c1c603184200342070b00107040d954114a880d05500d20040561b50208440322007814403039096001640c04070300c7ca4403801e03503030308061158a4002c28644411400c5d50314603621100c56400f800301104003030074002d0200301c161b111406d8128008034000e11840d0f00e000d0b0712031069643d500c880402e99213903841c0f01e02000e465000344100c80c10381b61242c0c18407141912a480030b44070603065208103074040c031441100088200071041800d80000e40982c202d1000d025441d401400d403001c514 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 469051142 1250 469049892 469049909
    0x10092301180f0201050d020f0307020f010515061b030406111009080d020c070e130b10030803061207090501061d030105010b0409091509050309013e030c0d18 69
    0x102510001d05281a054005592001041807603101910040b10780d4001d070160811403500119800b2020b0281c01c0285214243c2c80d421503400c503d40b4542282680e83c10385513012000c403030000842d080d080c8a0024185010301c6144420b060040340c0100e4615401a84420b0001344540404d0028a80902007c01d00e80440d950502142440d074a034a400344c8079003002040704603400541c816103180c051000400402c1d50f144405c14920784400624607080c50814119440d240c5240020b100c1c200f004d40300c000742d980000038203041d66105806e0025402030380c1c0541415101e1204000344241d01e60250b01d0103807203d640d078210307480100c10502160048101c4954841d9061500601510f61000e0a0700c048030410306020520080c80d0030942c0f2425100c00c82c040c403880c1483d4002083c00000401090b2900c0207030390f002840c29401d04100e0009080003000e0440a80b85003aa1a1886903103001c6100a9880802e1713924000f0818045032401128038548004186641005480d00c48800c401000400824 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 469052392 1250 469051142 469051151
    0xc090f0b2e1706220509030a0e0a0b040905090a0f0f02130c0804150603060203151c0b06060d1d060f0718090c0e15030108061501051602010210092301 66
    0x920b10200707940000302180d00501c020403685858881021401d001c41c0d11454080203e810595543c94681c1d0001c00c10300c01048525584220f01c1c01c0c50b01c0c0c501f0403102c1240c9030078182802d108910014000c0580083d036107100307181155000c90100c440c0b0328011031051040b29184600752041c0b090080f20080e2141d81d003890411000c0d115034020088a41c00b07584410f07100b180344c0d0381d0009a002442d058101a100900c08000c0204031241c41101c880305180c100c0e62088191403018004060304010701c0000d107800d8008007c50890300300480640036020700400301240c010500c90513401541210141011550322007400d0042506d01008420b401880034039201124201001050b000f02c05d851244500c0180e68804140300e00c0d00c602045034640d0380082540d140c014695829100c650028003c0c80711902504000c41c6843c107036165114540001130312140c0c1001a030f4913900c0351102d0582001e074158042c0076840a4441214842c0800072807041c805801c0031002a4000300e813141c0c00c5540300b200d5a261 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 469053642 1250 469052392 469052417
    0x708010e0712020c250506040b040e040204020415020c210a0206073009050907140c0c0303030702030d0b0604081e0c06190e0901030c090f0b2e 63
    0x899203881d400100c80c02d00002c1404250014402885040900140750081c28a260143d81c90703035440e001e1480d80d201c0441102921503040003254850703441a021308500403c0100510a11180403a0b401400144014142307903844922540030344507003100d00016005011617103518a4a0f42c60f0019210701c55441c00c803441d101c41000c9940e21142d0308041d11460010421508002d004456a0013410b22040c03140c07a0140013240c206c031170040f484202e90200d002d8940110740c42c03c0c2440d001d0300c0340c1c0c02640e0b6003031680b2412078007100c5640705101b031220300c1c01841b841140d2074804100441c050421503000750340c1d51040002900448980c20047d80c840c40080008015104001074603c1c407031240841840c0d407401030b580040d407510311041180c41d08400b01040e00d680300550021000702208158440802e4440c00b402003000c5a98240001020040070301c40500c425207582d409000d0b2401401c00c0060001004c600040b4a00350707801901c0c040d0007a0452004c4107a044000110854490307051920202a9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 469054892 1250 469053642 469053659
    0x12010b0901180e070b09011d030a020f060c060c13050609030d050a021c08180c10050c0718090c080d050403110604030803071112181e090705090405070801 68
    0xc040c8940d064007101c044440e030307682c6030550024050a500004880310255282c4003950340d03801400707034140410710115450007000c4440c4d00b00d60115100501500e04525164200410745c400d40082a4004c9030500004109001c1080b42e140290703840150617403240341c40086c1c4066030041c0e411103402504d090140740a952000546d01300c580640c0e081070703911080c0b0202d0032803030210a40b24101030400700b920400d07030598014025038000d42d001c41544000c206d90030501c3c1e070368401c0710070881c1d0003c0c1083c0307003071040c00d1140003c0c0c0700c013800f90400d0700c400c241e450001054901001500303000903507481038200704012100b008100200f60060203007020080394400a41306000740c0c030002e41551059505d000c06a42c032a001c8601541c2e100c59a039449040c001c40003020800041300d0a0014031400395000c2d0a0311015090300d4417140190130b40c40010343d001041c1310300805642c0481c510459407540907007841d0385210105101c1c0304a580d641d603d0b42c055204000940d480545001c00340003990006000340d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 469056142 1250 469054892 469054909
    0xb0906042a0b2503031b09030b040201111009031710030b0a09020301110708030a0e0f0706030b03030705030708071523090f06010f0815090309010f1115010512010b 72
    0x4012000b000d0312003500c0c42001c0024800540d5018009080341c415404054042d8404541504414035020300c2004414094a001100c1e002c00f81244680c0d000240c0150320448681c400c8024110940e81080303c4600e480098440003007003240850b960500d01d481003010341c40d002d42d010344603000000f0090b00d5034960052000000c5c02203081142c4480c0340205540f000d40011210310340200e225035450b00141814140c070380050350410500c81c00e101c05402c252100080c82541d0301d0300d440140003030519040c419401010300003e2140c02d030006012000c0841ca081c00503001d4140140c0c0c074070356203112525105841b02c84154112820507e032204502e4101c61940c807500b0900514841e00c180340c0c0b00c052034517181c4010f84201c02814404c450021840e005034440c0c5008442d1190215990503c56651950441004851901e21a8002e0054076035035031207511102610040303428100724080341030b801d807802c0c800107042551090040f24010400c9040a1501003100e400c208020010b1031549030002c0c6002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 469057392 1250 469056142 469056149
    0x8012007140708121c06211a0109090308070f0504140105090a033c030e0d080a080708180a03030b04060503031201170607080c030a090b0906042a 64
    0x103a074258040d15640c2003003050102904000d000c0b25a401c4c424080112554000a0b80280ca030801c00c4c1c00185005440c019001a03075040c1c4182d05045c402c030283e4200d550503841042d078101005800408481c101c4029aa0290071800f40200f0a03041c9800c0240080c01c020308903004100100200009881d8010b084d14240c1d5214050f00a541510b0001200c40e4002c0c1102c4c1da0b4040d0342c0d0003002042240d4882010340040d1141e00c652600d1400c04460600045001c401403802e4405662040009202e0185d0300b03e04200240400c0c1c0d2440d0a4440012079040400341001051012041c00600e9400030240b60307004060400006000221544031074803031401e08002018103440701c1c01002e06e41c3d01c50704454050480034085985030040c1c505441e100600030720a841c06020a00ca100320420002724015124103900c0c0c030b03082c440e601d581e20b529140c0e50004002c40c40442d900c000e520005403900403124018030040c001071580d07003032509052000306162400d0354000e05a0341140e948142141c03083ca000c9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 469058642 1250 469057392 469057403
    0x91c2118090515060d06210305030f101205030909011202131e0e0303040c060809030f0319020304030c02030f07231302070b0a0b04090816050c03070f08012007 70
    0x2070307445502006160103d0348000302c1d03111001240c40409010356620010813140c0c00303810001c4584641c8a110504004c01e5400b0b00043e00400000d0000070031b0490064004046480745140551f03503010300b009440c1c0100c2c0884503038000144a000c2c3e171800030200e44c05010041c070403440000b00e6a00003401c4641c5256070700062501d43c0d00303c60041c1c440c1c08022145500c2c1078014091420800710f00f5460358000c460440c5c010503071f030402180c070f54422030b031943c171640c04070380218030703200102a80d0034a43d00024600c54600140b4811000c0c42445400918000c0d8425116544600c0c0b5503c1014108030b6078046903102c8c0d070700425007001454100b05e000c01015203002c44082001c080c2e00c001c20100000d0108012090b400051904100070800d500b0511036103198100704030b0482c00004000c20380c5c0401d80041d25a200c10301c1150700071040c4032013000c01980305004a41d00981d281c00460b0034002554002d903a01d1602e40010480e60b0b90130300035031510400501130a04044c440d03480d200e01ca4040c42801070038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 469059892 1250 469058642 469058651
    0x11041401140913021c1202031b03030601090509150a0308180d2003070e2701020f0711190602011a040207121103040f090506100c030f05091c211809 65
    0x20704410505c0d10440d10f13810185280d80300c5c1e1881c80c0a940c99010116084180c9101c4030341c0f00c2c0402021041c3e90103250165540d54881c1e10b84410801c00100184c806548080400c1d000f80d86941e44016180081d4440c0c211507403100c10a407103610f101001c9054603801400c5a005003070018100302c880103d4014040180140038007200c02292a240e020f801000320901c0f4071042c00310703012000010070344051407810010b1105240d44101802c0c0d0080d0072900c0c545d00424407810001a102e40b034a9081550b0203080b076050404107440c40c86525107542d0020b40580d54901c10406c0c02c44480a2008d81c800069406601d40307012a614108525030443d160010001b000444c0084824240101e5000b40189507890303400546841540c0001c2c20151100d92144014000c07072203035a4081c5086041c825019151611080415030080e01c0c1540300c820401c0c2d100c5d032a00f020880b0310058104450f030310380c000c0140d0100d07505070a240f400f4078006401c62509006550b0716100c00005070108074420303620218801316 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 469061142 1250 469059892 469059919
    0x40204022b09060f36081b060601020312010312050702042414060d022a0715080108031602030c13060906080309030604030e0f1804020a06090501020307020402071104140114091302 79
    0x800c03017040d850018070740b00c000110031059424000840c1e0f280340c001000da80355030702d55000582e0742c4d103c1c0c02c141e130114a941100420101340b071503c4035a40c00c05582406072400c041a40010f04665011141c01040008890003240c1505000c010001400c840e0030102000724005001441501880c05d20510341500014220075401c11480c40301c1c542c4c0c2c0b400250304a2114111a8181c561845000c6c054520008400c040c103458810780c80141204c0044001d14070300300c3c4448410084465520082e44c0510074440c2311313101500c03004402405000c05600003d01541445550425140d441c3d110102546c4140304503419550b000c59480d0b0480d034075042480c41c42e05100041001081004115948043c1c1c0b045502404148180043d101d40d1084403031341c0600b500c1d03c034160307419181030080c1801644140142401410075070f0060500d20b014405407400d4180040005055529101c1860034460301c0f10010032540c1842c0240081043c022500100189000360200c40c041c2c21000b4064070500b48c40342e964 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 469062392 1250 469061142 469061231
    0x10207061b06060306060305030c0607050a0801060c020a03050610181a060d06030203120d050f01030b060d030c080301090603030f08040b0703110c070806220803040204022b09060f 79
    0x645e803080c81030102541d02c2c01c1c120303102d0300301c00d000401a0040d02c0000d0f08162145048401e42411501e4003542c590801c042141d1500424030100d800050710341001c0003050003041030314441d20b0010b41e40c0101e20700302410100e00006c8506c0025006003400b010381d9044a01d0484501120700a491143c2c031003806640a81c0a400c02c0e500c0690140102004611942c0c1548010507004280c04424400c135101c401d1044001070007440060201035500c1d02041071840c180611002c41802032074035001148035500e5a409584c002e80c08042c0c800c0d03843c03c04200b0190000c09910300400d542c10102a680780503110b03200746a000800c034a04042ea9502d175201440c90072070694201090040031550907545401820f541e5041c25a81c142c035040c42d0000110700c0c20307000ca106c2c10419901c16202415500e40c0d50034030019401c03d0341c59060301001d8614440303000781903400003107009541900102d4005000e00b03141e82211035140351003100a0078804000900011911800f03202611040710600c08603034100790 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 469063642 1250 469062392 469062401
    0xf0705220501030c020c1302030601120f0204090506060c100b01020a15050405250b030c160f1b1a0a0e030f030d052202150f13091107350d0e0c010207061b06 69
    0x880d8899803500c43c030034070040d006d53b000d0303c12b484111100304040c3d101d50b000c0051500412183c4402a031101024925880c15a0031254040c281070045400380001a5213803000c40b2a81811b1078801a500c80421040c0308040001300c01c82c0c005c50100000c4100c68000d15005401240581c81c04050000b000c241c45202070000c962410614024030002c001c0d80d0b18000c901800040d10907201843c4002940c01e410341ca00c0800d800b1034094441c41d90603115820307400b445a401c5119030f5070a000101200342c1a949050101781c09a100c084081c5903074902c83c0c0d4101d011540b000e00703000810200c91414a4844400300d001840d8180c0480d14041d6440806079040e00314890a455503c032110301007122910381541220803400da82e6529800d00c0f5155415031020414000c8000103410700030110702d151a00c4510b882041d5021085020020382d144200c10018200e62000303180105456540e454111450b8080c001160715040c03d10240850343c3c5010b20040080a5a4090103254403100e0070314010410250700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 469064748 1106 469063642 469063667
    0x50403020415033503312f060909040209040c090501060e0f100909020c0f0609010c080a0903080f0705220501030c020c1302030601 58
    0x20400a00310701c082c000d0514540003004404500c08482002c04142d54040c84160046403d4502104240609070000c1d070b450300744240407131003c06840c0c604030b541710404013010b00d000740c8496400a01e841c0c007008140001d440c40c84810151044400c4448403164154180e080700c21b00c0500c00b60b482110300003640040f400c0d0000d0018a0400ba100343c1150060088211040d1103400490445000ba004000462030110040d2040c0c60300345030020070761400343c41c11b045807140207034003401051003401a440c005070042600030311002d04011850340c1024002c02c403600c509200d19100d0080112901c00300004036410005490f9020a0043c840c405500d0360720a0960303034407402210316a86000c0c020008000d42048030603201c09184d807480c2c11000c01541d0300c240b01480c00d000034044403039102c0c005056400ca001a030080ea07440200500104141807800769503940c900c2e0049624155024 = true := by decide +kernel

theorem cover : BRFrame.Cov 468884892 469064748 := by
  have h0 := BRFrame.cov_init 468884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 468884892 ≤ n) (h2 : n < 469064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
