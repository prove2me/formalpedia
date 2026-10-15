-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5453
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:54:48.43762+00:00
-- url     : https://prove2.me/submissions/5aaa3ba2-4247-4473-b335-1da12c94ae68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 980575539 ≤ n < 980755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 980576789 1250 980575539 980575573
    0x20030426060a0b0316030b1306090b18060c041505031315020307030c2c0604080d050703110c0102150c090d1103010e03070c0e0a02160f0209071718 65
    0x110601034030341d0000b8100031603c101410001c0030504a1108070202c6818000f203000b0100311504001d03003020161281c2c0c62454100d002c0c3c00243c40103013820f40f490080080303100e4a0240400303441d100001307130303019959102e042d006940113500801c0c2401c0d080c103414202160250000310b13007202040ca616454001c0c00d5075011005030020280012580d0080144406250180600400c3c10329500344401c0d5006080001c1c0600350344c100d4035083d00c0d1164494006141c44070422034001d040c020082d15a040ea0482c03024003d0b5110000880010354031014040015801142c00c44030004140c1c05800d084029100604001e00050524006d401c02040f0314003695580c00c0d91004024407440340180101245410182120400d15050003550000c20025000521400f075200584110805100098a4912078071000b4055514505280700780490510184402d41861041e850b01c2240c8009060b503549004880080d400d56003030402110744d0000c150303032000d20100c01e2070241c02103089034136061204800d61 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 980578039 1250 980576789 980576791
    0x110a02060a03290108180c06070c0f08071406040e0f18011401080f16030f150609020c010b030706120504050c0a0e0414030708090d0611040906062003042606 69
    0xd83c16a04010129415580201805900014030103824003c1c940050754941c4840ca1b07040e03010710501000580c80b042168080c402c001400407032049400454503400020b50341c0340c15020b0000109521442998549048000c81d804e4410702d040d494020345481a000c1481800589007080c43c0142c83c148250b03502007442030520800f60700d51503268551400c0308450504e120003c11944980003401c003144080110110750044a0780f0582401c52002203042074145021241025041107084c178400090217001600540000d944400003040b4134825039042540c0c54115101e04408140640d040040040d21035200d25071040c0504252000741200400090440401c0c1d0040d0303041010100034001480501026002003e88010082d8a4241c0f140c58242d03150065071007503132040302c090004008200168001142c101e50b1038000c10380722600c1d260510044c12090145800003003554040c0103405905070040d00c81b0b460060040c620303043c148020240000c3c0030444410001c0e0a09944d4030800400b0400c079 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 980579289 1250 980578039 980578091
    0x1106070504030b0a0603171e0d050405101b14071217070f02030922060602010c1101090f11061207031a1f030c031514030706110a02060a03 61
    0x441da440b400d5250258100d6005002d00119500e00081800081c1002903d0f0038076180d0a00c1b4141c9680011500c48010907100b981c080800c08007040080c01200d10390000f5004a21580644819036100780840040790400b0710400381b100851801e1030255405281901450a842d4030454a420542c0d1129820610341389103c01c0014001c40398401c9000e100841c0070b80140c3d0754a481181500d5204000395a8058202e906200c0d00d070b901d0010070100150722544420350134841e0140041c0d0703034418010f4001c20303069001c100816100b031070b481051030341032054200341a4441e0044003000c0c119142d440008242502203074000030104541e51400403400c4074144901c15a5601051040581030102c1e01c00b080081030720300541c80c5d6421a42c598180c01154050100940382c00210b843c1188000c401401c014000056541d40040380031401a40c2c55444030308140d0154101c41805640c1e400884075481c00042e10685504034a07030b4a001481c1c03400060091071190302e0080f0313078400b1404104100401c1c18002d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 980580539 1250 980579289 980579297
    0x80a201621141e0f09100816090f15020c1305220206270a060302040e070801080d0f120608011d0c030c01030e03070c0f0f0b040311040c110607 63
    0x10307600740c0310382c414400100c106203610501d0a01001d91100070700800c2c00c01a5558000d400b0980c002003280010517221405801060013400c1416402c01400f05607068600c00c640c01440d000001d000742c02814030008503400e481d0049001d610300000700c00b92a8070040c4500440c012010700d600266500110141081c030704490002e0181444e0320603210003009010b200c1000d1b001070f4400070140e5100307000c1c0d4041d0100c80200404220b41042d4070610f902022076074507031040f04202d01082e4207034107601500c2500c0c212103840340c1980b6600b505880450007442690f181c0e60001e4001d50792281304540c0d00300140c0c035a0500459918811460758103503040b5400c40f60b22a075440c001602c070700040c886100100c81d10343c0080c0451b000c03001302007903c5102e01481c01c2d0526483d207080504041080080720542e42c0c00040549403640c5031540e400e04071b0701d00d104a20b0510f51481000c6204e41c0401e08035012a5070100882600303994400900000d0043c2000310b10900178079440030400d412040c0304040c4100102d5030713 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 980581789 1250 980580539 980580593
    0x30417190210020a3c0230070816080c0d031505031c120501060302301b09090408031008070506042d3213020702061c090201080a2016 59
    0x182c3c143e00000c1c004001214444a10008200b80d004011034400f59040209c00350b6a0020002c9155800c20813600142400000a00c2444880740445c1d4035008030340c0c60b0f4003800b100510400b4981008200d00406078940c01040350810900c10f003954042c0615558241008161450030301103088440903440140841d8000940322481c20040c2c8103606d0700c81d004600c104c45110311030700c00d010321720006003003001021107440c91500c0561600e0554004c110001c1076030b41d481c60305241c070b83ca494109451009a45d11001008218558049411401c1d9900584058282031034180c0729030407050392001900c1940c0142207606a014503514503d4090010480c41d910707242d03a54400504036040100c203034030504141150314030580d96203504640603100310b1007016803180e0300e070700015002e071003010060342041c88180340c40c04849d00c81d90822000d090013620703860303983d41d112000c0d074065504880c4095012941034049040c0082c101016048404003030030b80c290010200e03503c3d5002100c0308204423860480641e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 980583039 1250 980581789 980581813
    0xd0521090a061b110109030506040c0e0f070c080d0e030a030e0606040606270b0c060108010c11061311060c1b040b010212030417190210020a3c02 64
    0x4184907004105a10300f07039450303541224800c0c8840f80d5000d0010f00b80d0102642e00001c40c0e100710000320103950400c0c02d480160825140c100103a4440b41300e5280b11100c49000a0174040c8008030580c401c10003910360341c0c8103010603940d000d2b965201140f001c0301d076070744d0b0050088400b00c1000038120300083d5440000c2c8409403600c041b890480010309540c42a81004020312005a012092141c03c0310905401c5544016004a810070495142c01800d8810004104802c211a00140c0355040f030340e4090003008440b180090450f5010700050402e0700c2e0b81e0140012031a001c01404241d98451f014545400c5080c011600151096110034550200ba9010b690b481e0754010901e44180540700c005c940c20042040700d40700107900e4540610882401c200088005428054103040801d1500040c4001c1660340c200c0ac07154600c64903021200000500c620080c80c14121014170840c0c18001690301c0700304100031800c502c56449000c003083d801400082c450300d012950654050007591003c2c0360040e200c802010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 980584289 1250 980583039 980583049
    0x606030b130605220b04060e1c0e01051809090c030d1205092409010e030a0503070318021c03020118050a0210032007020d020a08010204050f0f06090d052109 69
    0x1c2c018085080511600d00d2400068169a004c0035070700030030b285120f54650401500800d0380900c1403140d4003948400030a080c80d4980320405010352901c0d083e130f048401c1d01c0115078a000e021a0b42c044000d4103822410945808548581e1200c51802160f894220b00c00c0031a04000c80c80000700007191680c0d004050383c00043c0034481d8001510380c0104101c001000164450141d00e00290f440c0c80800b00c00b0507640c40d429000306904181501c2100d581300301941000f415540f08565440c0041d01d00003c56420300003940d040c00b003468004201843c01e4400174074040b00180000411410740d980c94007000360503901d0311340000d403582c00f4030f000c0c0c02800030a005103c400c0b0322007841b21040515244070700b000d010040000f440d0601e07001400b80d0b19001d1910104d41c0491082001030360110240307100180c0300f40150002c0c800d48030244c514915000785101031000c00b6160003a1154060018040fa92103820000c20240c0f04a0082d4100c64802501281044000c409441c450400c2000002d80440c6c2c2d040c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 980585539 1250 980584289 980584291
    0x10609060510030b03190302120a050304060606080403140f040e0c0a030b030f061609181d0c01020c150712120507050403020d0320030d0b3a0606030b130605 69
    0x981e06042c0051000c11340080c0c0c03070380442201d5050301040c13820322809040c401c001c400400780c915440340703580350780486001c0e03c541c10480c1d00321403030f0b0304121021442c01d1144605a008540c15104e12442403c0c3e0400c084641d084034054088022041c040050040b502c458524014080c104003e940e8258a0360010b060300d4074200c1c2c5c103000350320141d1010480840000c24550103244c4040301124040243d0046a00c00002d41c4809510020f418990000d0b511030f070b000716007144580c103000410490060f60551035040c400a000d000d6004800803108900700030b404c003559625440c40f00d9161451540e10626450321140c02880000c0e0348100c00c0e00c0e0080c40e48032302600036800d41005400c2610316070004076441c035540d05c010200404144000d90580c4210038100b20030344034400342ca0316440c401815030010300141240c248104142840c11032511079802d103c4052100542c07525414010304076594039441241d0b0421107810340e5614000000c501c03000c0805025502040c1c0c0045010082c3c100386054a80c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 980586789 1250 980585539 980585569
    0x209060a050d0b0901021611190f03080c101d16050a0b0c01090506091617060705180d0602031e0f070e01180e0603060108012702040b030106090605 65
    0x1866940a105903980c07035900560581d448568000c01d030341c451504c5030181c015003c0303654003561005d150f90200328035090100003143c000d844440f600e203003000d0365040200f15071184085410f0581000c0c000b00b0307040f200034220a42650708507808100000345802c00ca07200c0c1d804a141036003154100604900c800c0c007182821800c40d01960f418039040400180c1c44101341d22503008020000160203c00c460203401c00200d02b9000400d8445a1401c40042c2c0d40350006203124012031002080e0200e031104d11070f541070b030170f074140395000340615561030070280c81540c04540c0134040ca0090104003807043c4c3d11a0110450148a40c1000d42c4070300f8110707a00110304108500d80012000d5207010442c1c05800c0070103481d40608680303001000080c154006a924140c0200c84a0f04565510004548111750b180c0e46800707108160200c03038060f0390301d074202401c84851380084807141052000300da421010720250041028001000043c6500ea4480000d00311a026404114000d4903000f00700814982034180040400b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 980588039 1250 980586789 980586799
    0x60215010608100e0604290a1a160807060203040809040b010c1203050c0903072607030c150311160510060e0406020313080a11071a03062803060207020906 68
    0x1040046a2000244181c003d820071031503e13000049803680c9036040315034a80550403219402c402a181007030744070040c2c00380c518000c2c0d82e40540000c80c5070303140b44040141005500e803142041c2c00040104c1c4056170b10901943c00003018404540424050b1004600481c0300300b266035516208042403000390b038085181a410f0251401c1004085070100001c8040080185400a1165214920a0120301a00e40c00319050f104545010074903031000c1d8500402d90114901c1c4d8010a1006070100b9039541c07507400014070810840d5802c00a07086c0d0414840412003660a01042c00c41502d030b08200036400c480c4901c0804050301014509002041c09150510f8640b11020300049060420302d182d90f000c0507000610081e40040060801000101c202c00c0f0f0903404403481d60b580c0080d00b0300800305000c1a11410407030088600c006103c0c040b403003104452034007040c0380e2411503852004005820040c4150b201d0031110803045550807481060140010754403400c401a01c910107401032240c51040245801c0c082c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 980589289 1250 980588039 980588041
    0x111100b03060f0402060316110a03021006090902030d121b0206040311030f120c0d140103060f09030f0e19151d01210e0d030e0c030a021c0212030301060215010608 72
    0x980c0b01c01b01206c1d840340d54180e88180100000800320354100812824410038061240342e1010075a010500c03503031580d083d040900c22641c032072054104507088100e000750303d0750046102100750703805142d4003614450744001c001100d401c00c62007040c0e07600c5181088401130b000041000101900000151902c41000004505040d0380d1011384407540b040d044103548801681002507070491900c8101c5400003c4400288045800c0409136044003200780000c8512a0a00b00304100c4000a4421042280e0301580d9101c48003503000c0056902c008020328603500103000c6100c001511001003040070043c0300356a520a90903140c1a0020b0a09580c40724282c1d02140b0010f404240c1c0e079000e940228280445d4820011814100c0903000040c0f85c2c0c201040c9035400394003032515105030540e0026001c1c0d1b0314101581d019146c0d08080507164600398000a500c40d00089071315080000b407580340c2104030310181c03020008400b245c2095255130400d91000b4011b9100302d241510311040010090b004040504000c045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 980590539 1250 980589289 980589293
    0xb2b060e220309170f10050f070c05030403080706021b0f12271f020105061e0102070e0604330e010308030a020a030b040905070509072a020111100b03060f04 69
    0x64441c1ca0703ca50812001c0c441c030440076000e024000c0805049040f4203c0e00f40b4040c0c40c2400000c3c100031180081020001c500288030140035841e4ac011155109000d0f6107000c7c01c540c0c1e0100250004202590103d07824050071841c45e40c00442901c0802c59240103111750010b2017201c500d440702d0700842901c02c950601910300c06445014038412100e0300e80c0c0d078500e6045600c40104c0c286201c0c81500303815441403446244038894042d0f002a0003042d09070389a44208a0400d0320b035001c10982254580141d01040b410000310040f5266150040c0004001150f1059050114034072060b030400915840540400e0304281201d00100d003c0040c010311091484c1985103440328504c500005000003002c80e000550031a940d8403035840007940c0040104100140756050802642c0c401d52406a0750066401c1e001040406004400d0404c050321103101d110301d44950316984600e400c1c3d9842c0124140100e02c0c10700c03403d00c3c0c018404054440c0b21480002503980e1408201441c01001501d000184c201c00401c1c040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 980591789 1250 980590539 980590547
    0x7240c0c11040b0f0303030a0606090b0408060a0504050705062214060f1303060513140c061b010609060e09150f1314030406050c160b2b060e2203 64
    0xc0007200880340052a1038826010850400038000100d5160000004000402496a001c80299022640e50780ca509449401c0c0314460300c107500814001c0e600c00c0c400144407010903000550f101e4822010790344030903a25000f051141e042000c05000c1880500848d04e4031a54030030301200103200c543d10f041095100c04c404180c05106e00c2e940758201703500000e04500104041801c0f84000d40c0d0280d0100542e2400140549011002c18011200790b0414000d10817a12000600c44500000092046203404074640040e440b261601980e03401c117548034140050402c3d054440c02005040d04d00304040b4501d404600c3c1410090a02e0a07a411004c1190601ca040e85404101d80d07840720103084c11005600301410b208030302025048104d80207120000f404941598840040c041800c0c01d0b20440e4072400c5058244404900140141d800e560307024002c071080720102c0c020b544210107514403500807a61070300f44201c3c02e07034545800040098103d43d0034003050042054409004140600d181144082a40c3d0014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 980593039 1250 980591789 980591813
    0xa06060f170c220e0a030e10030e12090409060c021f0c21090b15040614090c0a0908070801020a0905010c03080c090a0519080f070303080f0a0207240c0c 67
    0x914940c1900489010400f140d802250304120150440d0f4074414940b034003c202c524042900e5008540c0d0300c21480005001e8084c2e41c1c0302801c480041c2040704c2e04108044d00ba508400300c0d43d503101f901d40d010b0307101064552040c035404c045640c3c0508800c0d1144180c40150402e51003a0038241c0e0700d00035031660007135440030522036103000144500c0841903c980d03c107805480711940c00b03000390940200b0300c040b0060b070180b021801c4400307803030511015030f464030420080c400f4000c03150b030042540c000040000c02c0d01030007014040d46604140009a40312045946007032060780128090381c8d40000d404a14640103441d0800400003441e0407201c2d1210baa400070030646001c0d140d41c40c40a00402c02143d180d48a440702409010301400d041c81c000c58411a00d603120b0814801d0304914041d10753301c5c0351203d901007015001d50340c064943d64070036125040c418501c148000e000351038440e801c3c460b543c00280d009100502d8545107000b8410525103410840c0e04a885850000040c054800b032000c2c002074031700d0b90103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 980594289 1250 980593039 980593069
    0x10080303011d0a06170a0c09060815041e0c060210020316140f13031e02150a02070f061e020c0d02060c03040b070813050f0a03060e0a06060f170c 64
    0xe1a083e8842407450000350085070001201d041c03400d64442c0c40d0260001d6150511806032541400c1141c1c2c49410008462942c000d07900d0a0700030344400d03203180001000c170f6904180b2030001a1030f64040d0b210040414100c0d140c0440300c400f02032404015240c3d040003100044800c00301d04607d1818554007080b110b000c00d000c101c06000310705180409404400c2c0940c2e525600182c1070903035030b801c0180e94650b241003e0001312122121104000a402d05006e98010710542c040c10800c502003040300140c41c2034218103080c40c1148640c1c0804918400d0f40030b00e030130041030b02c0c2e22040c404c100328842288000780500d10a00840d1f20014242c2006e035102c840151803e134043da01107a45401c0080d205082d8420360300880204c0c94000342880c10498070400600c00f461030804410100e070345030010080030706180c0b0b218130b038400d01846090022582c140d0209100c4091641110809a4556a10f01c10307a00d240d07201d158452102c1400308840a50302d11003e40b1210a030000d000f500c541c29002841c10f030b28082d15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 980595539 1250 980594289 980594339
    0x604060609030b1806090c03070803040308030f0c070c060c0203010506010f08070f030b09011203020f06040321090501090c140d0c1e0906030b07030b180105090717040b1008030301 79
    0xf00d8204d2071140920444940b402059a09515040509603a2070120b080c005004e0f10800d480019003076400310648041e03a512501d01ea24503214440f08543c1700030003500c1e0b036003021420048080041d1451740484020302890701c80c0500400c45004150031136a0080140781030100f01b0301d040211a074801c00c40d40d400034240c1022144aa102e040490013080e42c040f00f1500907803620004a400036100303881e10101c51003a421a07002c40c907150442603c0b1482500c1c010042003590a1441aa0540c1c0d4000c00d0554880c200c00500003041d81c8840b03082d51102a13003035500c07810341c500c02d00c91019440260000d0000070340300c01c042c204d0b0a543c3c205d000245031207054a050000c101c002d04400480407448000d2212a07410300a9940300e00300041402c5080d12030704082841e1842070412410302d09c070381d48011821182d0001050b0301e00024805440001089042081301c2100c14025400403009050f000e1406408500c40a1a00000959525031290003140d032940c02880104585000400039400c00c1004003c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 980596789 1250 980595539 980595541
    0xc14030a0b130209010308190f08062214040c06030b0f0f01090e0103152a0f030b06070b04051b030303150f060408010f050c190c08070b0c120604060609030b 69
    0x164a18041c03210b80080d4005001000001070102c4100036001190b1501102c1450440d800c0056440505c6c000b82e030000b18030b4110000300d08c0e20300f100d208501d90300040e01116201654070044011207801203801082c0c80000307024003003400740c50b03081c400103000b280c242040b46c10781403070004148101c08960a4410780021174038000d16442100090018041103e80a4003540c40745821000f15101d80e60600c00c051512000058058014000300c04500c02880c030580704002042040713860301441ea03030120070f1544500b244140741d1114401803100f5401669594110704103407034800d007000d08c00b00445100d001c40c01011051a600401120740040c80240480d00e1503c4180c081561070014503a0300e40e00c424003040014107010123401c032071007100d00050100180e541c2c220b81c5122a0051101010100b04111400301d86135000b429401e89240c05191000d041125030b81c0d503944801c0040307410b80c194050109a4002700c02410324101e41048084600b40101070400030b0040c212146844003030240e10140c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 980598039 1250 980596789 980596801
    0xc0108060f040f140403111c0503040221120c010e06010f0b0a0e031c0807090614092b0b01061b080307050c070906050f030109170c15010e01030c14030a0b 68
    0x5807241c02c210f1407140110030744d40340030700780075094400c2410001d20500526282c143d00f00340c50f2512002035000b0b40ca03101d00f95101c80c0c0074803a5a05460b1241000071801c0864900005420000001d0011601d8a007540d203540743e102c0c03242901c3c4000c1390f280b15640030100601811643c4c1c4e140c00281ca040c2d00806486a00040381200c40d0601c184485805014240c112031000c54600c0003642d0125241c4ca40c0c0245468003a0304442d44609446500b00043c401d1900b80c0b02c500e1a500108411000200340c0c8007021108000bc00420110801040c5040300d5a40100c3c100f01c051070350300e0b0041415040040d00c40f8188510803508082d5090020403182d0004001400c560182080e60745041100e0201d6903ca40c40e044444000c2800f030081d18814404984203003078900c1d050140125159005c241500075895110000f103194100420074250303809038040e6205c40300300e001031fa54004c00140211551651450914100c00003064202a244202d058111000c9450004144010300d500c980340c0c0d46c0a03940c0c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 980599289 1250 980598039 980598041
    0x6010e0408071b0e0f09060f0a180b0c0304030f09080d0e1c14100c02070e15060325030e0a020d140d081e10060c020619030c020c0108060f040f 63
    0x6a124035580f000f0000d8080b0b075007002c40760101e10612940d00c29803102d803210301c2219a1120201c0e0701e070b8841c0003080c0016440c1e082540050143c00d10600302401c500c1c20075501d108403100111110310070240084100001e0550041c6030710201d00281c00c066000b5802c1110032503d41d901d07200d0910a201e880201400b1035125880c12804e442285601030b0400c103114030300744100c031310407100c416650b220312000c00e0104102882614101001a00207000d12032903e90140c00d02d900c014010301c0011980511881c3d02d4a602d00154821262014203020349024113415034482d80302c0c00b944204041c40c2c1070310403180980008194003065011182012207017013514045055072844c10b0881c03101c1c050203a420000c03a4100c00098094854112501d886030040c24004200700700032076080b40e0741d0641b034004201e01d90143e00e24070802c900182246252a0032402d182c082854a880304d08002075417000e01600c2154140103404205034240ba00007400d050880c005038044964540452140d41c0e40d1801031320319421 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 980600539 1250 980599289 980599313
    0x3070e041208040503040e04060f0c0f05120a2307091a0417070314010e12090a12080702041505010e01020a030203031602010207140d081006021009030201021b07090e06010e040807 79
    0x101d94a204414523080c0362250250511081c070f00c42181c03e108001c800c60780601a0344400f8102035030340c01d0078031400402c14007030514045c158a0100340d5680000c05075880a400c194503014a015103040f09003400c4c10001c1c49010740303a10443c030180d2000e803803842c2071010004850888101d07580f82c0701804000c6021a04000780e03980010805005420034100151041d0004850000700c0c4c029103a03640021149040540710300510301d603121145610500940c0c1402910885141c003c91600381410030036804241191181440c1c1240c010040b5410400c0c0d6912400c00e8120036028030251000d074040f5075019642e408050000c01c4904050702645402600c00d5040d1214980c2000b4a040301c00e92400a5a40720031410307a0080c00514101c000034981007402d911042101e500c2c0d4002d00c44500b5920128004240f07210b4210f046540800541c20308000103007240550504d124003410190380340c19105021510007910721402c5400a00040004071408020244e00070f03040481d481da201d040c2d240c581c0b06006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 980601789 1250 980600539 980600549
    0xe0c041a070f03200619060f08071203140408030d0b1e0f010c060603080909060d0308010b160b07030e011a0a12060618021c0219201b03070e04120804050304 69
    0x124802c100002e045140c0717403024071b15011032010082192103103541004082c0fa80640103103039200305400c2209826989414100368005d15204d564507840c1c150700001036005520820203544045000c1c0c0c07101f001486002c403010700c2281c103001021458a0b81110600d0031640c4907216607441c00307110b046030340910007010701c056000b0010010652070741360004183d000368960300c0c090031080000905604003601c840c0040d98043c1c9a040a6038a041a00c1e4801c1e0f021481641004a43e03820382800940c0340307185280110380588011441030031b01300c09a03084494284940d4111201020744500a8403001404029200c120195812810f25801c0c000b0160061703503c01614111800312103489009603902822101010003404030140705d5400504050303010340100d2000503001d4040321214a030113200c500c0c5413103903050304d41e40054002030501c07401c14400b40035106807184010400d102c0b601e41030099602625211030100920305003501c03402d900d8060041240c2c1480346c40310104050040030025034000b05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 980603039 1250 980601789 980601793
    0xe01200c120319090803031b040b0a03090b0a050105060a030b030307020d05150c041409060a050307080a0317090d0c0303090f030c1505070e010e01090e0c041a070f0320 74
    0x880700c400ca16a65803203480007a1008103500a4502040d204010090849102c0c500071815a2182102e02c491b045113a4000c1d0308a110030000010500c0c0103502074440d43c60309441c00142d200e1642440200c4402c02003072000c0c201d2a010041c880369a55009a8031441d540d403900080c0c40d00c40d8000b00b17145106588010703500000440c0a90103304e00002c01c0c110304480c1c2c00703c080303058079104452207a501941c0209201c50003e40795030103603410720a450b00d501c058000c04811341c0740e0f681c90119050540c9900031a480703401c031480300002e25800034600701100c22030074180c00030b07442c3c515001920b50352412210f200b040385039040381c41498420781194610030b8000c03400042d4940c05140280202d50601c60441d41c08003504001111000d0030f00c1040e10442998894580128020300112165282102100d051100039540865001c00d2030702000d00c03d859400415540c1d50810401001000c04006898020301080080400050b0804a82560240c1c103040c2009980c00140388100310081865006c4224 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 980604289 1250 980603039 980603059
    0xb03030d0f27120e0315040302010209030c010c020303030604020f0d06091b0e0d1e1a040614100302060f070206030702060a0c090f0e0901060503030a09050a05010e01200c 75
    0x144015809001e1000303000310400b80c0103003090354041d00311800352006440744080c85414821240685007504600307000034255a07001c10480545040103c00360350a400503903000c107202c5103d007020000c0b556441001d080022141c85103500081d40c0c1c0c4801098079001d59000b00c1c95000b5082c0100540b814203e03007110a124050719a003d610040c509040502c008585101c40d80740e00078004c10180c40c210b90090440240034002d602c0e002442c00020780c00b078045041000e0755802041815062003544260010381e47c80303d0421b81424015170b5080400c0d000000c03060407c0c4880c165600781080100c8ea03050311380d1511014000745c2a821800b414401a400400010400000603804070304584607000c4001d0800280c20345030303030443e0790080c58017a800e4001c00282c130038002c0c00c5a400f4a2944104c01c0c03000801c0355a200c0c2d01003411500030b00368981c00700b80010014425460840081005480286041410080c1307250000b0308100600c03103108001c0000c0c0240001c41039091000448803407002d80380f4852 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 980605539 1250 980604289 980604311
    0x7053007061a060d020307020106050604080d0309031404030606030515240607060e010c03060803040f03031d03070b030406050906160507110418060513050303060108090a0b0109020304030f210b03030d 88
    0x46d6008403001001540f074144081850704c0c162003900e0654000d50001e000e007042905094009250241c419001d2050600685280100003401007000e54801e502c0440c1003481c61401c1454030094600700c81450404004000c5021202c204ca0138000007000f07200e040710002407000c41c030203104500c2c000d080c0a0403d4241e99490505400c03860144806680c01c02c00a6954034450741c480c081c0d80110a07032104001401c0011904c542c1c04040703072002000601840c8814140000c0c0740101e00e9101031b8501c6000b0040009010152203803641c40000031014254928107240c1c900081c0039003042902c1070080c0443c2e080d092121500050b0200380c40940104240d0140760003d1503a40e281220441d00182080c2c0000d6601d504a100c0104075a4044002c50960711031100540e62200001c001c4903241c03107209030000104035404a800c4c02800076940069a81c205410000c0c1507070110301d03405051200318020f0144118913003000c04242513581400089007808500028198410300c072414808900b40310004803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 980606789 1250 980605539 980605541
    0xd02030708010509060a080d120204050303180112020405030c10050d0c1211070b0721021c0606030b030706110705040905073f020a0b07053007061a060d 67
    0x810303248100e03512002a03545c1e10800c2040401c600440328990082d800912090340104401c4110b00340445000d82015100e1000c01d00d99000040c4150003265088485062940c01001030820b065580d5400c1d85002e0400c40400c1d9110507a40d1418000c1040c0001112400c0c898019141c0075042144180034800c40da10000708010311a0545900081c948150058001411800c071440317203a00c581210b2080d950803c1c155074090314070084031100400e800468822a80c1ca10003400103400781c0c41e41d070007a1566121120120740702900040c090510300301c03038204541d5002804200f01c8045242000801002c4c3c4c80c01401c0c20f4103944800d80044c20300b41b42c0c00801c03101055881c146d43d21419802c0c540500d8882c80040400102c1c0b88456280d440454000c080c60003440003100d40d4006860707101d4440e03480300078407403652010344181e0b901e42200192011800d4040c48540c006940040752801d019403500c800e400b6445500001040c980da614104125496031142c1c6409141d002086140c6410045000300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 980608039 1250 980606789 980606791
    0x50f150705070f060c051209040e030f04183b0712060c03050c0d0e0a0c2903010515091f0206180604151a060d0902030f0604080a0f050d02030708 64
    0x60003c0b4030000003007003e912826103041010b4002c001400200360b004414a4645c0c08032003c55001602c0310020307140c0074000c00c000d1102041841c181c40d5030785d290000c500300380095003c41920903420502000c440f038103640e501381e0182d0403c60307ca591204009400091003154281c40740054000d82c18000303441303840001071403443c44c080c11060010303921800c0c08034200d8204884801c0001c500f0b1000310380801d03544d0303c0030106c118148112610f003040345c1c803580080303000307648111404002d02c22031601c450490107110003129000304e5030300e0841d41440000381401c00c0c2c1102e100f880c4000824208150303175480302400400500d0351144464020b240030b00079110070040b14240c1900e240c01550300d0110500217616489550001d003d82003100e2001c0e00c1201501110221140b80c0c058100366405580c3c1fa075004006d001c600c0c81f0000344031901ea2041c5800c1002d94680c1013481e40183d0b0400000c9600d0104942c250500c0e4a01080a848000350940d42030003500019502c440c4080100000d4a8000b0245 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 980609289 1250 980608039 980608049
    0x60f10090501020f0a0f0807051612140a031b050c0a0b21040b060d1410020a020708031e0304080d0905010506040513051b06091203072604050f15070507 67
    0x940d1420851901095031005c1c4010014081c2c0250340f0b0000c0803a002c2d00250080724401c60a569048000340003100303056015401c104080303982c054407039003000841e00c68805100840005400c0c1c0d852036460103085184ca000c1845d900403201210a0200541400070340841c1c8802000400b549807100d41030021070300047d0200100b02100401c9001c10311886090701c4c07003944d10203517440c1c29541c0d0340c084c0040036100120866201030000c0380c20440c81d4042c80900b440000cbc0c0d0300b0058840c240d0540c000e140104a40c81410140c10030040d0084c58001801c18030800540b070078000340d8130b45039440c180c1d00c01d220710040901d10300e00d0600c0308402c000064104500801084409115035102d481c3da44441c04074404005245601080a005c00781d524000794000e00700c002003c3c10b00340522070700070981760840e0b220400c2d203d420014100c030800124030011031108010320f122510b2401c20245232040b034411f03401071501c19428110240700380d0781c814100034551268803440c90784407030300c61421980c0c0b440c0714068 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 980610539 1250 980609289 980609293
    0x1090b0f03060c040b0d02091008040c3206071e1110051b2103041b030309120f1a070e041806090c0807080304060201150e07030203060f1009050102 65
    0x546800340ca800030b4524082c0c00c0210609140c940303400000030680c0d00100c410001c00703400348a021065034581d216421a04181e84800328946801c0c40d2074140c40c17607260080d40c1c8808507800f034503016100151280c0c0d200c143d040d01c0c010041851100080080c056090001c1002d0484102d8160b08040e0000580d94248900c59200307050241400300710101c081c2c411a080010000d00008501c1c03020242140d200b01124020303a07015001400380712101a118459142446d000001800208406801e000c801d20000400145103d0b05640d4000e28000c4944564040c4203c01d90405007800074075010503e440780d01c60f920040d680005901110041d00843e040c0c000300d01c1200300b4481038101390140d10082d0031f01c030303030b60910031004d640e100802005a00c03829500414144808905054200101009001b1007001141c8441c5001c034002d003034444441c108030614141d0302d410000c02c400e44480540052807800c002da200d5880e1400301d1007080d0340400b01c40d40011021003407082c8a030000ca540702620030070782c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 980611789 1250 980610539 980610559
    0x20316080f1b090a050a0b06180a050307050619050c060114030d03110f0703050d150f061128061407020d2c0d14150a0c02070911090901090b 62
    0x201619805400c826500d0700008070000040c0c13004041d500444d8015104140060660301d9000840c1081d0003c116080805542818440031450b241106100400c0100d00400c1800c1c10f22020031464040c42c0940b01080349283c3c2004040d0307000e48151000d9032500422111650781d1540701f0740d000c1e1400081c450082c018803180102040c405c4c0210701d00001800013071413030511701d0b4015240c194400102541081814450480e03298400e004513070300b5160140b40740802c141462076002242c0d00c141e0151041c84814500000021008107245101d00c503484801d07070860070521400514400140302c000c1203a86029880106c99030508400d601074646942221081d20b080300f410381c0d1a840b88121017214040c1540a06605013011041c01d4040c0d401900585401c0a1940c40e06040300c51246410060740111400030308103031004118984c0540d48500c24030960b8810b550107074407440140a900e9005488541c00c0708059004411a00e0340310000c2c100712442d42e07665191900520302d10780100d1054010300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 980613039 1250 980611789 980611813
    0x1a030c04081213090e120a030b090415060b0c0c0603040c0b0d09170405060d050714040305010c1d011d010216090203090c061c020a03230f07030c0e0d020316080f 71
    0x1110f007041c441d05c240020454106108507501c3c0725049454418100b41e15108111002c0d107950920a006520809014018070030b200000015a046500185c100781d005210742504504009000318102000303860840e0b40792124204100403500c81e800003000300500140e80009a02c1ca507104504603802440802c40c208064203c101340b600c40c070721070340750701803014003030355070808525800290000f032241410a06148900d0341c03c402501700342e00c10744140e5526480300c007019802c80c9580040400001c11401c5d00582580042d00b45c00b0614400080c9070040703502c520342e5074020404484e124114840e42400190b540c194040650b0003120214554001e03094600c4450514070107403020002c440e400101e889102003c030b00001d400a42040d0b04051705c0b038101d01c921241c14981344600c0c0903144203460031441d09840381c5182d84c038007500c040c08051500704210940d80d1310500010303103240e0495011440c050b15000091810464a0601c007000b1010f40002030595000038101d070360b2032600800c0c1d07200304081e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 980614289 1250 980613039 980613041
    0xd02010b09070c0602130e010305100b06030c040b3a0b120607270b0403121d10020a080d06080d020109052e0c080604060f1a030c0408121309 62
    0xd84242c8007080040f0f03409000101d10390054045110344e1006100e096660b021044072801d4280c0c015600d5400c100a641d01c0c02c00d01c0d008910915a06036034851650070098401305030f5104611500210304004920710780030141c125a48504415a288145410440d00800384e22000c08003102c010320300d241286400e10f070b0802158500e4000c142501070f0500d1780e1802720070f4420740c84800e03000c240c40f04014003005111405421443c080c0c0a1800350a071100d0562070300c1c10104c84549800c80500c5512520002155803100600a40b00e40036510031000401e8402c040e45030414a140007005c00030701107074422003450b49911000860b040c04003200c0c400300c5216020390880b4501400603125800a101104129424806c040d40d601002001d205180d1440c0c01e4407011103084840e03210015450f0800e10a035440c15002d000e002e050b4032800c40300090700d008940c10300d1508403a4007030b40036200440014400e20703030582030b90000c0c16030200345c1d040d880d4000901051607028500501e0007244811001c07039000f580b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 980615539 1250 980614289 980614291
    0x5010f050a182301091a060705121e370f14190201060602060615030f180601030552090c02011d0109081c0603140d02010b09 55
    0x70a0302d042003111044000909001c0c0c0000c0d000c0c00300a070600f0201c8003203010081c020942c9000002c0c1094600c1303403c0c1c42ea0000c0f0780ca09840345c1030038800c10002c42c20100c0c21a4000c000690016986c80841400c040c0e4082c540341a84810800428012403451075404441510b41c19110400c2c1d070400c0c030302c1c0b140d02c0703001c04c3c0b2204400044054015a408900501c0c25480d00e0b1840d080c11030805240d031030300b444440301e4100f03d100103035100c01c410480030340c04008aa81241089440c8005400c402200c5156800300030040281c1407000c0d0085081221205284103204600e41c0648040b5030316424107603590001e030b1503009003106040707900080085180001c4c510000c0740c000c010103040c248504981c410060310043d002c03100d18001e800515504980b08181c0d14881a4002203410226100c80c000e00c500106800b0002307904210460b000076540c0d034100e41800c1c214010350250740d0a6800003100410030b80d04000e004031800700c8140070007040060704071001c0515500a2050490300000c1c054046d030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 980616789 1250 980615539 980615549
    0x2120301031205120a02090907050f180616050604150b06091e040c260c0f0a020c1008010e161409040902030604121205010609060c150c0305010f050a 66
    0x150910060001503410481c00c2c0034802d0b03e1410f079080c40f2540702400810007081d65a0200e041d40014080b034076040c01e101301130748190581007242c2840c0c081c801259651051098401c503442444046141554500c01a40c2c06403a214401e8070480c00715240c030658640e000d0f00c00b5640c1d05d0042502000310f440b903008810150f400504500d040804040a10129207020120301000700b2515405058640b1a8407841c81140d045564200c2ca15002c00c881401c0c0000346030000f2a41141d005c10806814426001c441903a06034900342e9544a4580a04a04000c20460299806003501030301e0070b43c060f80429200e06845aa107030b44519500c0b0813003411420361800e060103000c18000c11041d400740c00d1840c09000b04d01c2029001103822401075002a040440407130b01100e540381da0307003d80c504140c1d006a240100e020500d03000c10255050240240400145200e010100001c6901040408c0301d4500c010781c00a000030401c0c0a150100c0700d0180186c0424010805c6e003144403000040d180c03800c0c19550003160 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 980618039 1250 980616789 980616823
    0xb090105090618041a01091a120c040e0103150c0c050c0402220b0c01180f08130905190c03020a050301120809030d0f020c0a030201023a12060602 64
    0x45004140920b0f90040c3c10402d941501c0400b60304041e8607640a08504184000c0f40c03640c1001a00c0009006030f44203030407130303414901c00c42c2d0740140061103002190036881c800c0c604a612640c031000116030500c02c940010140c410030b0310000040000d040100b00c0702c10142c10080c400c10f502c90008031030803101090050940c0d441480d15496600780f0b40e0040180d128489203c1000e15110100c061100c0a180c0c494110070380c7c000707007010302c0710003e100b48010a240150f62840280c2d6680303030b40d4540442480054035481d000030740341302800c1c7c6440016004260900c002d12007854150b03400c401c842c0504000949150034425101c034403a01c00d1003143c4540240e9203615003164240b200006015100000848041e07004000d855400c0c0c3d4100041c1003c43d417075a50714179001c070703034204001e0810111403082402854140c07400c0c00182e8003c070b050352064030309100d6400142490b00c400600302000800ca481115150000c40800c41d9000c42428411503107490180b00490b030300c01d0204e80d51010360054858807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 980619289 1250 980618039 980618047
    0x1050f1008060a092d051303050306010203070f030e013b0414040b01170a0f03030203090a0b1302010816050403020d0611040b03090114040b070c0302191b0b090105 72
    0x11500510086800210141402403c19262104076007119451600581048400103480340900c10350118101c4459107000d0500082c240008507405122030f000300113081c484080000b89859108101743d0b0310841c1c0101651990fa005030401600d00401694842e001604196008010b020090300b414080c0c03076095500c4451124101b8610381c1041d5114150340c5c8a500d9440384540d09513000042c0740964041d01050015514007c600c1c2944059108004440e42250304128080360b00c48a000d08101c0d098100569290348040e10f042c1007081d803181c02008400e245c03040c0030f0320a4002e850000d0061003a02c8500e5141c0341c2030502c04001004084940000700d08000500040c01c141e201940b569104400c04203103104040001d101d00e4100c0c0e0040a60424040108100074500340a900441c2e00c40241070300b024141b9442d028089007000b00b0b03400601100119190070507200700603021441142011203841400c25103420b00c018100c0c03988180885911820114100070880c044894680d0143c48052030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 980620539 1250 980619289 980619319
    0xf0e0906220201020304171608150604020703030b0d050d1416120203070b072105040c091d190c0608010f15030209090403020a03030c2328030504020901050f 69
    0x80d20a4407408a045000030700000030700044a03400480300e55040b5020308407000200026a620030345613849141568064686580401d0441d0013094003d50103841c050b99907141030a059002d00a8541600c0d00003058800c424203100002c00c46910203051550f5010000e500140003a25a015005003481d650080413a10400900c0101851412a03000d0041d40d0503c0c0b881d442e40b001c1c02e50100c48001c04610401e8503800142c6d00c0c0c24129220014000b4100080d08040d15420300803003080c001c101c0340030703a20401c2640c46008849800028004a01180c9681020303190b00723244000310f40340841d5116810365004c203c16002e007140718180c9008044203100c1518080314043e44103207200800c01407641c204000c2419840310444184124001d40040007070030407034603005007140d45582000040006408070b0020007040e0300c0c45e140040e09600e40c3d00e91101c0c501a105941d044040800301d222001d000000010160543c00480c4914022120703401160f99550038040f504041074556a0301444030601042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 980621789 1250 980620539 980620591
    0xb060c06160c0b0f07200c0f0102010b04090302010b0f040204060819020712050a0f2f0304120b010e16080601030c18121e0f03051806040f0e0906 64
    0x10001d2991030060320b501100e40380c0c2d901c000410382e5402e1400c5640000c00c41c4a075000b04007584540c084004040084107250401c0340c0752010500a0b0b4030407450300f45012140ea100750000c070300705100108100b04909283c50f010f8001c24601089070b0246000302c5403c0c150b0b240078801e990848005844031314042d9554012455601031040000041c00c3d424080704020079840d110401c808030150300c1d62541d0700103c4a01500d07501130503000004008080500c40300140c40850054200303481c0d600e41005080f81250490708600031600300e0302d01c0c0c0d012a5a060f050080302580c4a04035100c1c2c0781400c029850b0600c082d0284109111004082141400030880c0d80d4826403080c100c0c0c0d015454008040585c81c1d12400500f0030a07030100b4018a043c20002c2c2c10f000d001807082c04034403000d1600b6070301454159104465121071910242c1030240c00b10702c45c5245074504003803c1c10080c2c000c11700c2e0758030340c0c5603241c64200300342d103005808180e4003420010341c01e40360005055000c1d0203c8141000350b24800b181c068 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 980623039 1250 980621789 980621821
    0x251e060c121202070804050108340504150e1903170325080618190905210d11090a05040b0607060f020307110d17071e0e040b060c06 58
    0x40800103600b440103450000c9202518005210b0a001c2e0340c0d40e45400c00041860f14060111084400c01091038a01d2048651601014a0400011b05d44844040e00191a140030b5540310000540000b0180f041e107960022059480001c00c85a80c0a6003a40000603141144140002009c801440d07070540540400c3c00080c503840307401000070805410300e403500c000558a0110b01100410803a106004140c40c0542040f80450403d03c100c880038901400d0001134070f50000b03411001140c0c0c402c0750400748076080c400840010344004105111540c800f0003596642e01441807a50640d10301084507032102e14550840e1600d0400030611803845040200300f00041542901c0035910040c10048040029864040e100d00c076050245c0058132407a00e81409403003042681e030205201e030403031040300c1c01d034a401c4501100180015200040c0c0b59407011001d4a259815200400d01d600300c405000507415440141070540c1c00b0141d80c2800b60340015018440c0b2400741d001c900b6030030b030440c000103140e28504075042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 980624289 1250 980623039 980623073
    0xb1b0301080132271009060608011517010e0a080901140f0a1101021603050403050f011404140c1f0e01030506030a152a03061a04030311251e060c 64
    0x3009000100c0708683d458881c80c5d82d01c10a8090b21292000180501c910401008210920003809a0840701003e0010b40d90540150306414121849040034406c09520946c3ca41140c201150742001c01810000c0c103940082c0c00c081c2c00181d200142c0d0103d11400010f4840c1d1482c0904154240005114191a00040da07800c04ea0a9035080c4404150011030202c440000c07802600c1daa9560707815424200c2c1094848078040200b681030a1035244070321016402241e119810803501d91801364160101c500300081200c2840d40081290385004e4400d2600c5000301c00c046980d160303201600e07203580043d410348604607449541a0401044100814050004100030141c585800aa901408024070303020030041540302c8100c00801c0541c8091517090321480016101c61484099010507203640d1449610490100408020f2880295030a20608002e14001040b000003a1619801d004004c8440c115181c4111a8620343c011800e007120700002c2514015140d2540c3c0380d4244211360b48034075000c1020742e4a1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 980625539 1250 980624289 980624341
    0x3010603020d0f061506121103060f0114070803010e0a0e060702061303110f01021b0c0a15050c0f06220507090c0909020a08040201090b0c0a0b1b0301080132 69
    0xd42410156000c5e120058502c0ba110341d03000c02a442d4000c2e040f1460749034080003403034082092062a03030341d40d0301c00c02c0c000401340303401011429010040c0c105401181002008040701100110704c08007904015445054072003c00c1102004103030542d0768421041c0d89400143e0046404141c407801c0d03501c540d810007402800c002c0380140e110400d441c5030201c061980344099601080000380310201d03103c00741d011280d284c01003610070200000600854400d1040f884e04404011410602030b02560035505070346208030646241d105901001c03521a10215018000369031182204080d81c0390100b420901650404000d0136500d00704240c5000a085082000f01401129070b00010b0f504000e000918a621555581e04414140780c800504503006d6900039440c8190280a42c00300c040000440000c6c41c1d4000b03045412544032116941c400c501254074140c03030080004004109008150441c02d01f46061035014640412176550400c2410820901e51103403d40e041c0201c1c5000d44603040340e070300c50910098 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 980626789 1250 980625539 980625551
    0x51302060d0e060f04020a0602071401120902040c08010509060303041a030603010e030c010e0607050a0210050705130b0306120f03040e1e0702061f05300303131103010603020d0f06 79
    0x150614003141110710f04e516056040c200400c60511038408402084203000038a541400c120f80c0c07003065404050701d2410003081580d901c5003005580c0105600a4020b0030801c202032000034000d10042090080c54003903c403c0002c10300c0d509000007141e00711603010360300c00e5000443c4859821150f00c060705c45a419901c1c0d030880c8448441c140010103130400c0c0030000044030300380b0a144508040008111006101080c0003283c00543c0201d0400e180c0c0342412400a4560346400c0181ea00740142038135280c40310003a600204014810300e00030350180200315030040c0160050003c040d511214684c0f90300b91900280810081d0b0300341c03030b0811600101c1215a000c08a0342c030155144001074101c40120046c1d002c1c10600005074032012903400d1a000542c0c920f14441d00f0400400d1362003421031044251200e281e0303e0034005030800502081b0700c481c2c2c1ca080e03966030305201d44400c1c0d0700000c200c029035424003064041d0407249414411a01100da0150100d4540c29683d00c807901c1d0070341c5141d815206540c40f40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 980628039 1250 980626789 980626811
    0x5030604021e0304030e01030c050307120f0509031c02090627040906020304060c020c0328050307030906091e09050606130e0108151920070f0213051302060d 69
    0x1960b03108000100e1030840c0d203030710301828000c100c401860346a070706141c13900210100b00341e0b10100b100c3c0d0120f024100407002c4a26141d011005140505820040138a41000e0100e0150088020030360841512038000310b401d484803028049200b80080e0036408030003081a441c3c80c181c2038100701c0302d04040085031000580780b000404c082c0c1d010140200d444660000c10070013000241d20415440c4c08207031000f400c002d4240d00109680301c2d290554103820341506a00316981801003240d0f0b240d126400410baa40701c001034500a441c40d09240583d00c00715044e9107001c03481000b66542d06102041007210700302c50340e28140482008250260500390402401c0000078900264452100010660340482c1c60541d890407030840e080440c0300f0b20329800c0301c01d02d1042c402c0d8103030700002c50422401c604d03d00198914221203c2c10fa4940c2c80b4881c1070704030f02e0105008061061000c80c802c245802076801d44840c0d0402c003440021101704640b07071b09152600e0640704015003030180150035621203007031000400d800c2d01d03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 980629289 1250 980628039 980628067
    0x810200703030501030213050712050603070b040f080114100b07020a170601060801120503070b060a1205160621051008100f0b010f08010b07150e03030a0b0609010f0503060402 77
    0x280064002c030f41c4a40c010411404e04c86403240100c08400400c000605220b800140030383c0c400f0222180941d2200702107101c5a90910081b070060046031001a516542c401c0700c1c0601c01c03954480e41c00c80303518001940c6d050546494a60703218040800e5402400c900340218034100790810f14080c1d03000412040f000c210b40b050100c600f40c0b41c40d0400024509517143c02001059080142c011600300200c01d00c0a0300010750000c1650342a6a1203004006690344030004605000c850798000a545c007074100301d078028806c2c085084041540ca4070300409569480751801d81d054580d040c03602281c0b042d14141c094070304840d640915040341c60b4400c3d203036510390b039108514640152214140381240d40c0301c8601884104030710585443c2c80b420b00740b501001203800c001500b0380300144207840861000140c4074041109412003070120745a0301c00204962404010043e5880d0811244088114642410074000b442c01e035040e510071800595940352240c180000445603508080e1516400c10303028800480020f140d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 980630539 1250 980629289 980629297
    0xa031202010f2a02030412060203041a0c070302070503160e130611180a121221050601170108030301091104090614130b0a050906030a1703010602070906081020 70
    0x43c0c0c01e00b00c0350100350b9030b2062a00d1900307a800d01c01e41d482040100083c00c0784c101c0849809400910040c0c0b00d03075841c1044005000d030080c04481540d400e03410008035140c00e101501800c0e000e80c1c2100d5880c4e40380d03014990341d2598000e8059407490944402c0095801400d0b0f110783c402103032a501901e0305401e54440c0b080d03c90300d80380079509150105081c407a0000c0a040001c07216001c49042d415a80391800a540940e514007010b07020b2018002c80403c01030051096510700462000810202e020111300b010040c50103640c11030029410306552400d4007809000766058507410805140341d0703480d290000006142e12508650090b009200c0040c0303d041301d01c604402412104030400420044108225500d60403510f44104140303010058039590b12498841c40590b04161080c010540f510000a4900030081d00700034440494100e4a0512541e00070282d03040760b540340c00312491543c5410500050b9401801070540c20f900034901c070041c01e03150340c102c80b000704270000a2101003002c84044002c9a40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 980631789 1250 980630539 980630561
    0x2723030408010e0601050f04320a06141f09032102070f150c080403140706180305120f070b070507030237020303040503101a0f0a031202010f 62
    0x202003000c2128200030b004a020080241c0c000c0e0000c2e60400340012080c0c09000001c600581c6d96042050f1401a8207551040b043c601c8000e44c4140c1144000c0c00450b41412206046074605103072001030b843c070100d4501e68403c440240713003010001d0b01d107480d15400f0b1094801e00c0c017000711011000022502c2030f0107104c62050020319415928100040c082c1c6851402d6000510301c0c500c940027003007540e98500ca4110649014581001d9036904c0d8100303c18503006940000c4d00510350500c903160b181000240f144122511038035107070040b01229545202400c15484090044e0300444a0303200e102900c3c030b0040c2142c0082c0c00ca0142042c01c00d4032a00c3d4494000c40c1c00802041c00010110240b50b010800001c1c4c0811129070a030341d952aa411103462012240c400344056821020f1050455605206550181c40094102c03a000a060307441140903018a900c01c1c0c00d0360044030760301c0c25141803c0107440429000940840826491903940c02c0304400180c44900443d51b0390344034016401c119001c0e01804803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 980633039 1250 980631789 980631793
    0x406110421051606140f210603060a110702060d230906010b0f0409020c3408030f0f0310050a060e040e16050609040902100804152723 59
    0x2014a080d0b4607242108a92000c882d811400c00c1020680c020b8540045c12281d9011030380b50901d82045c0c00c006d01074208000c0380c0b143e0a21003110303001e080d544030310b1159800303c0c00c0b00c102c0e44912030110103e804446241e0b0b00710104120700e00c054100440101900000c4100020f0842c0c180c8108490140e0005a80040e01400e00e040c450703081c800708111400b406a8282ca42e00e0100100079148441c480e6102c0c501080e80c004c40d00c0034101c10140844017180c41c0ea142c0381000400c04244d041d215283c410403d000280c00103401207180c060010940b03103203030764041000e032030b0602800c00700d210b9400060600a014110350f401054603165a03140e400208520b880c5c800b4840d1404d010031042d200d544106100a40c420049803a81070392801c0144225503090315156a07900140c80858040c022101020f90088264400401d005500c150110711a5000b00e402349465030302d02c268242a607803505c080c2c90901c0322100d0100309080110100754081c9104495824100300b001c3c1c60701e0f00c0001c206482a03203903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 980634289 1250 980633039 980633099
    0xa050c16080d1706030601060804021801140102010f060b0d05060a270c051e030c0d05010b0c0f03040b03040b06210f19050a290c0403170702010804061104 68
    0x81e04103c0511042c0c111000450301890a540440c0c0e540710144544010020608007241c1076459900e480619981e4555a01d82d1030b42e1940410000010702d45a11030044d031800200519800c0c02e840ba16003078506585990345040c040c5801e04010707203005442c840c0c0c4040c41b1100001d0441c800200700002a51000c80c01c0720407a11403002900320b490011a1106002041120102608000c0c3c03024000500d070060791500d913200d050b500041c50060208126402e0710340780010800340303c81c03405000f9024501080329443d00c205031015440780141d00c42c0308101c00301400414005902120342a9008001400f2000c2d03204400031803410241c000c60f0140b9150b007092235803682c03650b41448008a14035101c1c99000ea01d916550f2050303a2001250400780c01513007010105031140c0c41010302c20b218070101c0e0325642d460b4103003c040210680c3c070900c800c807140300406400c0d1301580014400e540034250143c40340140d641e5a13803540c502400e507004140c0342c0f00358200004915042c46c5200058840910400824070b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 980635539 1250 980634289 980634313
    0x615041b0e04060e06090f09010b03030703080117011b03020307210207020909010605010c02010509041d10050106020607201f020d06090603081914030412230a050c1608 74
    0x121040f540003e92101c01c10010895182c88085040e5081400d82100505982c0c4844401c0c3c01400034000144d07040c000091508141a8014a0141a52520300c1c60000d8909202d10f0300d82240c0503c0303d110000c038008000314680a00035809140e2140c018109468580c2c86020013100501071403404254255000c2108030540c10820754075030b40320711914000c02a290070040042c1903a905608000c4c10440300140c2e980c00c9441e96013000040ca103c110401c0280d8443c0201161100045a07030407408600d17010002031320f14800a100c1c1c0c000c80d050384415512100b80350340703100300200c10590740e0002e00c1040c81c2c48502d250b100346090b112400300b103c016226914202c401003074036469800100301c2c504215085c0040346810046078240342c500d40b8030b8408004d02036400d86840f541000c07103040c80000401017200303000c504588070421210b16580c1010420300c0d6a0140c1a421001046148594041c08022038030350151008242602504040320612180d0720000b00022441e904403820540001000001d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 980636789 1250 980635539 980635541
    0x161e033603200d1707020d020409033b09090a0c080c01020d09180b18010602010f05220204020307090b130f080604080f07020d05010513030e01090501020615041b0e04 73
    0x601204111064900c00c0c00c9030300c078034a04c44105103403029044000200401103541e1507800156641e4083c00c10302c803180c55400c1c042c00380007154010344002c520300c42994920041138030000d0300c002c41034644030001d481031405000003800c0003046603100340b16107501e01d0040f440d2031806900404d07802c0010000911104002802c3c9904c09588406001c24840d05020304140c0c60101c0a6803454148001850180c000001e09038180481d50103c084001034000b042e040d9040d0820086d4104a0300c3c00d201c10344920008035130004400a011070b00f244541500b900600e03068000315081005880c0110340c00c0d07122505007060307900c4108404c16045280c0d02c2000300e0503640001600802c034072009048a4602034840024a201c5c28600c00402640029500b04640d1340017941642184c1010013004980703040030b002c039a454190041500454a132050a101940c07040b031108081c0c0307206901500854542001c0307030300b00340c2e84000b2059009496000c980c0030348411400078404098a0381e159540c50000c802408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 980638039 1250 980636789 980636843
    0x2091c030e04140c0901020a080a090302090f0402010f211518060f0911040f090213050a05010f110a0f0c060801050d020604030305031b161e033603 65
    0x90181c2e0501007490700700184595002d501009070902c04e56039a00d603000413400c01c4181c0788000c0c010344020599810859000040d03030282d0307100343e4060f4007039200c034210810304003022280280010500328074040010b10645201150b4411090503c1010200d481040c1c143d90641c80345c1e1400c00d801c200100000c110610403541560a4100100b28650601d0390f02c01c240c2c0d10070300419840a40780e4904080d40c200c4c420455004001741803a205245454201c0b80000c0d5000150300c0281202002001c5040e2074500381241c1110fa05860780c455000740e00c01d007a03a0059180384c1428490080344c2130700c00860031984207441e00d18814094541c00c282031042c050325400c01a00000d008103500d0100500503187c0078115026290141060ba07180e642d00c0e451540c800c81000c614994040c2c1c00700300e11240020b114102e14106120b0352001503800340c448a100344003580c0400c0a000a4504100c00100b0f6060342030340c100303040718107925000300d448007583e41648034070030ba00464180c00e82414410b82d01c01584000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 980639289 1250 980638039 980638067
    0x3030d140609010f27060e0618010e19020405040606050318010603080901080408090310150602010504080d1e021323100807050c0f010527030a0c030302091c03 70
    0x42e00c000c0d418505400000d01084c0501012010701201d40d044403039840910010304207210605011558075002c0003440300600b034842074025040710310300f1000180040043c9050380d00384d0b1100c14050307454148440750380142c45407040c40c49608000c0402e03581c0b1a40950006000141c580c150389007808514501400800c110000c2940d16000c1c0c03d10024003400112481d6020900e88800d064640f824121303081c0c4a14110b80d641031081d410b0500c20351071690400048200c0a0000080440d612801a420b841085030010311801003007015107001c203032651084048000811420b1100c100207540d01e82264041d561001a60b00b00c1501004080d01003c0c2c14140000e8441011080c0c04081c004947d10031031340c615a0040c003040c100015001d910440035150b403000400103d49180e595000002d000346001d441ca24800d2890301c0c040c1184440100800c42020300d0f20009520f41003180341c0c101d80c08503804a044003095020407a8400076681c5098282056105991060401c11a4070300078001c0d1103c1c00ba1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 980640539 1250 980639289 980639299
    0xa0606170303091002090a080f0705030f0c09180a0b04080c060106031e0506041506030e0c030109050307060b0d020918071401020307020f061905030f0109020403021c0303090203030d1406 82
    0x1048030982c80131030b59003041007001a0140c0c46034013000004144002d6a00182e150784a03802c0b42c08941c070000036004044034019800e407643c031290504580d449001c009805a08059404080f48801903000c045007107a074244002e82d40d2401d1256207044d0b40d0741d01a901a1100e0070049000c0090306000d1002c0c900604180c03c0401c0244104000c20780e000c08030b44000c0340d0300c0d40c3d1b60740000d4250325140c0001007a419100f01414100d502e50001400a10002404031003030301c14000c4e0000c540c10148038400c2041d400c840118200602c1303540700c8000e8200395039496081702e680e00c18a001602c034003a000d07004000001c902045104405061841d12416900c1034242200d040050b01d5543d0300070080f161501c0c1c0645070071034a040210040b0711103101d100541001300d030b000510441e02503840f10145000756100303403086c40c5507680c410002c020303806240030280d030001c241c02c0000b8141c5242000307100603510904001ca0070a42c1c1da00004d0854001401300b0415070307242c1800c90004d1003e2050540d0010040310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 980641789 1250 980640539 980640541
    0x10c0c11062502031c05070308090f06131e141902012a0b1f0e040203030d020a180603020301050415031101050913050403020d09090c08061c050a0606170303 69
    0x2c0701c80701c050050010141d05030114040700c0540d03c05100a142c2c810620601c0f03400b8010342400113145501040094000904e0f070004511600c41c0446c0c0c00c100800210028907803500c41c000803100d543d00840c0f04454540c900b03d01c40d0011840c1c1440004914014020455a01c6080341c1c02d0303007003034021b1070406420345a01403040300517038001101c00305103800070010200640c0043c18100d4a41d100d200e001c1d02c104800f100704416128000b00c044006049000b40d160055039504019001180a0301d00942c560001d1148025003007041c0d0142c181e2004c68038010000003138002c0c1d94515486903400900029800100500090070b06003c3c0503000000c08840c44452851511109040c49070600e00504000c070000340341e90f541d40c1e070303169098803040030750002c101078180fa10780a503844402c10040300c0807620943c000142c41a0700e03c40c0c4400c1041c1501c4801240e5500c3c800c000000c030540401c0c5626440e00240070001c21002c000c6000320701d102d550000389441c145285100c50b011000d8a426050380108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 980643039 1250 980641789 980641807
    0x5090313060e100e04230621151e0906090d180b180a0f0302090a0903050d2c0102031005030309010f03020a090b1615020a0903140a05010c0c1106 64
    0x80f1080c41e828498a81800c003140745000041c05003003459402280c10740081119600c0001c2060141e004003402c96240c40304040040e075401e030700ca20f940032400c2d4a810103d02c0207501082c41c0d0f0450780c408158449403603010800114aa000482640c503a1002d40c031000070854082c80801c00e01842d19258148403c4400300c01e40180010000ba019107840d603031010410250720360030000140719115004004031b142c00d403101300004034070070180b1080c3e2150712a880451800222440f40306400b03174143e035480b03141c070704054a400013030101c0c0c00c942844060884001d07420070710410340d181300c1d004440001503503e06203c0c0f601c90b4141d21036002580700303400400203600346a80104081e00c40816604000d0781f64280c4040c03c1d205407415610040a00c4800100054000c402c0f850004409200d030070402400210540490101c1c0184d658074404103140900030300105054203102c10499200074200c4d50490310390395a86007502c580d0822034010510b0369140608200e283c15108417545410783d17942d03007441c0c019 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 980644289 1250 980643039 980643049
    0xc071505092a0112270512070b0c0a1124100b03071805041e0c090b040603180c15170403020d03020304060b031501051302030903180604030605090313060e 68
    0xc0c40c0d0f041c04100080c2c0000038000d03070024014035915040b0314850324242d100c248100c1240c444115900d01803004011101c246190595807400c0e0800302c03290742541d40360040c003819806040c403078042c4101c290031480881020403201d04d01144503a55071a1480d400001c04800c6070020b27003451005d50100006004e0304031040e054039408a030380d1605482c40190114011051461604801c0e0054242034140341035032100144200607460100080204da0003021040360b020b195401500340c1c8a40400042191601c01d8120b1740e0a00d45c05800409012210f0350346420810040d4050000c40103d20040c400c0039401011900c0b090002d822403001340e03d440c0e64000d4482c182c0c40c0d114403e05a001c004a020302029511140701d85102504035a15020a040c00c5c15031060248102489032040350311205030b401083c0281e9004003102c5005500b84861a40c1c1e032503a0a60290080382c210704c042c803000021078154098180143e0740341019507642c920825039a842c600c42501300c40306010300000125155120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 980645539 1250 980644289 980644363
    0x1b2303030d090c08161a07111002031c140916030303051005030a03030e010b0616060b061926130f0303150e06030d0f090e0c07150509 59
    0x29101c0006100ca07031625200c420b609040c1c0120310b96200e0705400011880420044505940580440d5508401c070700340322500d2807003005002011842005014034440c108020302c0c001d11141801030383d09020001e91460000000d0224049085803201c0001040020f080710082d001104180501134422001001070301c0c40c0d070315200c01010195904001400707081c1d103030904005485e008080e20aa0a51400c0082c007810095604001d99468262035030f200740b80c8901140e0744006605281c500c0841e40b48c941100400c0900b401da60000020404154040504503082c079214565840d0712916004100810100c400d10210031056000000140240c030540494007110450340155039403011622460224042e00c00041c54580100c00002d011a12f20030900c078442c41414160f0440b100200f403418200d41c462889891070b0045174600009100140310940d040d41c1c40207000c0076645c41c0000036a108114070039090424004190707500c091003040c07581803100d890004450704031001e00074181d8003d00000c081d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 980646789 1250 980645539 980645557
    0x6021c060504051e010e1510030b0901060f021f0608031b0115030c050904060b0616050c06120601082d0103030e090603120a0221031006030c051b0a1b230303 69
    0x5d005000600c0300d031f000e16050401c0d04000d000d074021200d41d14000743c0075000b90000140f003420540c00116005203e5051264005021380c000d0110080011a40302c01d69819042ca0810135100e91021480f400302700001c03c03041c42418001c1d2211034a03440d901d8211242018100e08003101103200f00041881c40104106842d0b00312100c0c1d045840c3c41ca0603078000d10301c1c00d501a40281000c60410042c4c5203504040c05264080c0c03003a40c28403001360040250394454901c540e800109094040746c40365208001051380003a6140c5060011440595240e42d500e280c06444648040c054005004059002210750a0481c00341c442452500b01000081d480700070075014410b40300d5000c120381071018400c000690784d2684040414815040e07103001801164802c0350702c110080b80070240010721034400d00c0303062001c250329030341c031810134004181021030408200040c0c0c90030f00c01c0c44100380106040303182c2400d503a095405803800c410302c1c1c1045040d2070885c100171030145200e0b00002801503180842240c91040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 980648039 1250 980646789 980646809
    0x30907060e0a030803090a060906060518191815020a030e01020c07051021020a0807050403052814250302330a05090901050a03020f0d06021c060504051e01 68
    0xa03403107003059890080c2d001d1010300810708094070501840074ad54080c41c15180c082e21400c45560329120305034480c1e407080d100007090740c0d4440c02903218046e007680a00c030140c00042440701e1010345600c80c40b011039541f00804520701c0c0d002980074000740c0c1600c035407901021031000030b60406007102d004544404240c0b28503805011441202011188600b001c00c0c006000c94152000d00e88a281d050340080d006000b405020442000101c0e82c12401002618100c9a01200501201e550408140950803443d1320100c10b22010100600004400349039070300c105e040c500c00a14481030b020343e020300004c031648010624a100c2c04014001750b01d506c0c007404441d241d040c2c0100c141b4080050003001011a02c01c40c00a890804241041c0c41a4894001c1c0b542600c22903503240d00d40d803100100706120605100013540242189038011150400181d200f03402c5011780130040c1080440d40742c1e10301400107000e056412642c0d424060080f403030240b203000d0301306415501ea04a09503205407543c240305018000c00b0a04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 980649289 1250 980648039 980648041
    0x3010905070c0b07120e010212040615050913020f100f0e09010f0b090303040e010602030417030f0d0f1527020a0905120304080a0b0f090f031b01180305030907060e0a030803 76
    0x41c5c4c290703801c424034820201c00215620940f9262400306008240c0301180c099040201c01907202480e12603400540d0002042c07110180c4807074004c84001c0b110118100d812000b10250484184d8075082c00001c001955151700040d000740c400d0003407000030000310613485021500014000986002011002c1e1120005c80c40c2d980d809030800a032440c016544120b00c400161000410590f038084064012542514518115244183c0200b03880380124030a4801d0802e01380f2200e6107204d12600200031b4408403131000074070394000c84202c1c0ca03100b0071604041e65079644418091050140c40f249018181c9581004509010311008014030891484c4915071040240084c651488141441150010f2540204648801c11130f484c0c2401d000c0f00888100560031041c0d000030364040b07008126034040350f400801540c903001e0410f0747e091a800b2503040c002c0a945d80d41c06110482c1c804400c610100501070f0300c803c0e4603850841000342c6400001d81002040081c100003404054440303a960300166a80820141e4407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 980650539 1250 980649289 980649317
    0x11107150c0503030405071509030506060d0f0b0106081f050901030f021207090b010905030309012f010504060509070f03050d140f22051005120601030603051203010905070c0b07 78
    0x44500019070182482c04000107000070840009121004c50b480c082c0c03401034642d100031040e2100001c0348006041034000c0d4001420601d07080c00c248201c00d102e4002d888140c51580c4074081c1d412400d07044107001c0360060050000402e9580400c5815080c1c45103403804c41c0d410320000c144041d4040c840185000714004260b0115682d0b007004680f280041c40c01c440c6969611041c60000e40700002410b030100341d146c84041070500300841128580d090684811201c000702c80d4000c042c0460281001c42d80120b5503c03000c2801600b80985400765008620102e0182030010446003010416844400c0385c440c8120100002900823920802c0360030a820034049500c00b00d55000c0003072103400d8400325a0300c2c000502140200c00501c8444130032454034000f1841503217401c14040c580c1c08062011021400c00d00140140f500084c010550100040c5000702c0c1403a41e1f80d41c0d1038900038207019034280d1071801200600c040300d454400d040c5d12010903d04403010507001d403a007001d20030002d400c0c03000b0400040d08941c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 980651789 1250 980650539 980650547
    0xf010b090609151c15060807080f040204020c010c0c1e030c0308040305070c08100e03032703090307240c0803040b0a1d01060306110c0c060a02070f030605090c01110715 74
    0x103201da1003105808202c8042901c1d00005024200d8060342c003420101011446d82e00c600381c2907229051036200c0104503182e040d60881103880c000c02c100da00540800044107002c100380225402c071038007074a5083c1c0702c045900d030810314032001c0d00304004034145904145c80400da018114600c000d8045c1822025900d450030101c03124400c8072701c0601003075050000000c1d10800002c08219503104020100180c03110120215201e100a41d4002c000700c82d0b00712680011411b084a4140b0070000608507032600100302d0110b400c21003aa40301d01803c108900903a00d14401c01c980c0c40701c0030645842c14030091240356540343d505000c0540701919110300403000840259090740301011b140d40104540300c0d85005050058017030a901d000031234980303080000c005c03200745081b4160b40d80003001001404240022070b043c000c0075004009240114421444001034150901c04114051070090702c02084d0751410b069a00e14000001c0100c13030410400c0603440b0000b5001107100c41c01e60b1950f200400f0b922a01c400300712 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 980653039 1250 980651789 980651797
    0xf0a091b1d01082113270b040507091e080106080d0f030e060403031805060c19021605060c030f071a06180c03100305151b030f0a0f110a080f010b09060915 68
    0x21802a868041135031b04140369045c01040080291010b01591403c40e0601060311810f40b80540070584a020500c4004850045000031b20030070189002901d90700c10065003507a856502c100f1440e0003421105403680e82c40240801e40c500c80342028004110b100406654580c130060028040554614103c2e0aa030074015614021a400008407840c1d424840614000390744030444015001902d55100c0784020300110301c9240c4000e030200760b440282d1a20f801c0c0107240d8090188800140800c04c154640c1085003800b03802c007180500d202c20f001a90341d21307140000308005031165100700c4005400c0510001070300040f503480801d2910050301c0b5140c1c3c002e0b01c10030b80780a0304010642d000e158041107040e03044800091290300000756a0010313031408900034000c0d110039500c02110300d6080c0006400e41d6069048001071141c510b03000290400c04103514061604100e01c803000283c00b0f41c0c1032140005403e0541c5000d017499040c401d1030044444001542c508c20701d0b10603402401c0d00c15000390100035a038292 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 980654289 1250 980653039 980653049
    0x8010b0f04080d17060d080706051f1403010f0e06040f051f0f14060607080a09030c18140c040306050a0b0409050d030c02060f0a091b1d01082113 64
    0xb50a400f450880103002d10450448004443e000d10000480d14508918000410f60b00058014640307081070303c0e40350140000a00701c50140d407080040002407940514018014181c0c4104034500490b07402c00c0500f900d11402001540300d0074044601444c2e04041841900141d04c035080c1c8041d50040c0c58028200380080700081d2020210342041360071070307002d81c00950181d400000200540052101055112503003a180c00350090000d210b48000a054400100904110b0382045d0780d0f00360b034a0351188030303150068001011210700d0140c0c0140c84805c60090440840c10075521f03c4051400f0013004219000b54070000c1c000e81e44400114890190036400b40303801000242003402810307035a00f0b15940d1503a60251050003e07180c99603404a540c400b09a1601070607507503c01340350f10740b02c514001d4091720410303078155036980500500d10f880f940088001c6000341900410501c0d2584203040904400c1d5059204000a0b0481e07072240c10880d01000803900c0c102044071034980c480c0c013145041000310405d41c100e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 980655539 1250 980654289 980654293
    0xf1f1206090b01030b0d0f02010503040519080a2c01030c031d0706020601151d1f081512070b030c1308030405090604020c0a02060c010b0402030a0c0e01050a08010b0f0408 75
    0x4a0300c280182c0050010490a8a081c800c41140a042c004600d0321124007903d0000d84400020041d0b115000840e0080e011340c01721002820503920000d038500c2c03a04005c840d950300014172150f0150300070140712414004014403150240b90420412080007008624504040e0b950b07035000106e600a900240718441e5807143c0024070218240c2c81c0d603840341c85005000252283c07100004403020340e00261081804070b83d5820b104000c102680703c4040c00110307400c0b50301100005240500c0d185115090410070b215549114090824000380f80054420802d62402000c2036070303105540f985c0c006050401c0710380c40c01015071341365101e4003150814003418035004400350101500240307580c0c0002c003a009842003180e001e16540c480100f000128410f080c0d01900c1a000b2030515000743c80c1c513801420310220712000103e850241c49002900700d80c01214441401c40d61a0861005241c0c800381108d041d400c00e00f480c0c3e29144507200d02405646c0d0500c96801c440d4000520001108801c0c07064400070864182 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 980656789 1250 980655539 980655551
    0xe040c090801060b072312090402040503160f0803250201021f0213060903030e040c02032a010609090f060504030207031401021803070522020919030b060f1f12 70
    0xe0801580d070b0020f0030507201900001007180e1b42c81043c00c00c0b44140002e14008141c2c8000340d2103c01016000200d086034400d80c00d0000040c16201031002c4a0250881c0104040042c1004840e161281840d0072402007a072003405041c000000ba0183d101d1400b014981800d03406201d440100c2c64082e80800b060741c01004840924910503654000d4202c40124441d0604c450362610000c80303103000c03548400740000307030808480078860401d903100041d45251481600e24286e1202813046c8241c11503a6065040010a40188100d26003031141e4800f40021202c1444920515191144100d001010141010355241e0204041600801080004580c450320360107200a02c542c1580c000d4004040460000402a5444007149008586a402e465005120031241151505d0082d00b1000e1010721000881d4200700003140750780c8404030701c0002030030303186c007078a8060540c6821083d5030070182940d40102d52417450140c103607941c46404c00d07424803881600c91810f0300340c1e201244c4291800704080302183ca000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 980658039 1250 980656789 980656799
    0x1c0e1e1f02012306220e0331150c0f0b1f050a090f0b0604031b0b070c0510180608090705031f051b0c070302130506010e040c09080106 59
    0x2084000a03004107400800151058003801031100141d412100c01c0d29108200252480ca030036082d040000640720786915690580070411412590a080d5246c5242c0c00421180c000b0607245811008203010755071844040d00d58907801c030184581c64000d40840540304014444400d1007059203c2800e13801a0032003440070300f9814421605032065880340c7c80c1941100d140031010040c400d00404a0b00701a0214043d0392a01c04840f00030402c3c0c2400343d804540798030305040345a4401c4081d00245000b10300032407800e40d120071681e000303401d031340c0c006040c007002448400f001c1391851100c00102c60f000d40380140c1200d0102000c56a000074502c03840e501902040d030108803194003064072441884e41030115880c2640700e008141d5155030a442c924a40072150b208408030048642000343c0044002c01820fa80704c8800e69181c0d15608444551a401d6201d100c3c10030030b5243c07100c00c1c41095004444108050304000c4002000441d00d2071800c6d000c0d6480320840d292192040d6181c2000344005002008111f46030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 980659289 1250 980658039 980658079
    0x6070f08121e0603060f4b070f0e0d020402160f03030c022b0e06030103111e01120c1103040806040210171b0d1b021c0e1e 54
    0xb540741c000c044400c080051100c0c180000c541d4011148980d1320005031f0380d0305881c0a986040f0341145600000c088103002c00300940c0107603d418503605140a04018402c04082240d8454001d19000410022264144c54141c01020340044442e050728400741010103070000c10068410251032120007498080401c3c1400401c580c0c80c2070b154429074052002902101080340d0b50548140c01e4140048042011000724100201c0541301c0440e50030820b80d407003110f40005020341c000741d20940d00f1020782e40c50381241d454101d04d0400d5480039421843c85d1005074a000a00f900c421501c4115034a40e5a000c00f0080c6009020203250988204101c076913072501c1e0641ca5440d24400c0ea0224001c0c0005d980f0f986413540030f62050703480106040d51034940e42d560503040020404603800d0300101c84000304120040d00d01c2502070b42c00e2402d04040740ca10701e01c038066402440c0071701c00d010305540d4401524078800b05551007602079084c148101c4a0341d80c52411107003044580443c008500b03501c00c2d01c1c0312180d614a01c0d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 980660539 1250 980659289 980659321
    0x6060e0126030a050f0c01060b03040b160c030503150d0204110915030105061615060f0626060f031c0c0308090106030c03230106060e040c0e06070f0812 67
    0x6008640311401c10395501c11641c0c1c0c050b03c001007002c65010321424a007258920041c0c805640113170000300c2d1907941c039401c01110364429102901c403410341004010503083c90600f40d25882044e03103020078150002c0d4500800c42e00007e008150040b49403180224150b4408400ea0303d01c9400400400024603011001c810a034803108445001d001c0b095201ca02340d16019055030b040359000f5003040e280a041c0c3da9405628840e00c803040310030a0280c2204a4000142d20030b4002626055900b003504504056005e0b015070002450311043e0780c0410721440c1d20402c2034101035048401508c071041c0d041380310300010b410103000580f9601400354140e010403001d81c3c0220809691070298480c00220b41380c54902a003a01c0c40d6010252011070301040800000c1d011269900d404074022074030b52281c0002040c46802d40700c0c168003007000520b00407628581440c0c07501c100e402c4d45003242410480c880b10400421540d019405011b041c01c9404d00107036042c000160100d9404646903e8180f5040c0307451201a400150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 980661789 1250 980660539 980660579
    0x90f0702011404050a060203061302031611032d0c030c060709120f0b060f040903090e150901210c08060a1118210a0311010b010309081606060e01 64
    0x820032109008199440e02e000b809540c0040182900b903040b1b803503020107544041d0080b500a401c00d64401520081c074800785018000c00c0d144280702d0700d090440101a01c0e80d9054801e46a041049401d40440c1c4441310000030309842d00306e04000395400c019160f200e0180780c0780300403240400100d034580700d00003084c203038411800b640b10b4903005902c5000d032860115844600074080302410705c1030030110700c01c0018a64010301c000c10321805a40c01c9070110301520b15a0400b00d000c10461681880411f00da4094a40d0015486140c5150708143c8030020f00c1f400818461504041e1460300b181d10006d40c4960882103403a005440540c815075100d1700165144400c8404990390b9203440c13048a01030b5012000c4843d62010055190900b45044041242c2c1d42002941007061a15142c0d10809540040c840303010414002e80720800d641d01440760280c2541e8401c9001810145004007850000b0034040c180c8450381d49071103100f90602603030700d4020b000300401d4020410201c60702c000081c040e00a80350041450f9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 980663039 1250 980661789 980661791
    0x18052a04080d1b08180d0302010e01050106260c090306040f0b13110127123807030e06010f03061a010e0d05030418020714060c0702041a090f070201 65
    0x3072000c4907400c100110f068405000c901154012606000280010740000e041841c92a003040000a42c4c03403101d5081200540d4582c01841041242032003418014103103420700314040c455204d00403461030010082c1d07100c96200d00003c5626a51002c0030f440401031701408841c0141045e050011100300c9948040701c18040c103200180001c00400d000000780c0342d000d00007180b020b5039030005503518002400040c3ca11814038250b1003188496400b4007000b015011140c6000c40e100341408a5103010380c0400da4240c00600d10214040da00c01c006044140c00c042c09107110b41d031140310342140a07044070310249400d4880c4000225a0b00c01540c0584100c07846030500b04035414202c000782c50b4440d40c207d0f0590110f5111001d0701c4150a012003070340704407407155098925060702c0303021900c04418030b181d00e2060540e0104441c4104030301c040c1c0310305d8070003505030040030b051500c0e10404d219841030000c0207001daa211000100d002c6607004804420341c6005040081301d02d05294111803003141114040015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 980664289 1250 980663039 980663053
    0x30906070f0e100512162c010305130f0506060f040c0e011412010801061403161404020c0303251412070e190e0a020418052a0408 57
    0x180e00030035001d5146141900c840a80098050030042400041c611180a1180400008511101c8084218440c00c504c40c00e040b00350100c4107008003c050310465a1500710380502603a806079840c4504400260401d18010032955610401c1e808140d00c0d00d54001e045000c03c91440e4100400404c4c003034450402590200303070b1105140100019900c20183c40707404104492002003a65200d0000914103500600c8510310b041c1c0d001a0115004000346e1104105035540d40080c00001c51150b00d101c45884210300804240d8040f010300f8a1501c5540325400e8110f908e800001116182c0f5015a40d0a00032101600e45902c1c1c140001c07a5001c4c0c200ca190207500608100104081e4042c00300003000240045450b81800300f1a043e515078000044c0950301440180582d0384001c0c2c3e501d88005801d220410140c015540c40d085000c0d6091a02800c6009801d0061200f0301c007046003d151905000f8030250042201d4540100806101d50038074461104104910305800360401e10030001c100302c0303446100711407107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 980665539 1250 980664289 980664301
    0xc030903010f05010b0714240f060103050108061f090207110405010f18050c1b03070b01082802010e060406111e0a0201120b0a061e0c0809010c0609021203030906 71
    0x3c40d5070034080c285400710180104030200d4540c0c008404601c80b44400c90b0702095060348460b0340c0050040700b690450b03c40e5410020800307240c0e45403640007502800e00b841a541441403140d1100402840744030141e00d50303904040d0008440142c400200510f1004540d5641d15081400e4610903c09086000341c1c100800098bc9884000d61001219100c1e044040cac0c04603203241410182201401d0100709810a00110036043d507030100b0b40303a25181c20301c0195560398951801004041b0140c0c4082c0d103603000b1880108001200004100080c081c40141c58412003591005031103c41c54400038540041c0e01140c04101c6a070031010304070340d101d54001103c10300401620480591115090b11b8030303807500107070307000401035001d1841215000e84c514800304005020802041d4008002c0d401000014800d582c0480e000348412390500c8a10103d2502003900f40c0180c84002c404d20403221a18104020b40c20220240502503120896443c1e008000c109000c0d0b002c5400342d0303641c006640c6950366000350404202 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 980666789 1250 980665539 980665541
    0x204140d0803070c02040603140102070221071701090b0106090501110109050703061503080d0c1b050c060a02030d060b0c070f12060506010c02030d171003080d0513080c030903010f 79
    0xa03900400301c1e441d40d40d403543d04072085280e021040303070415107a20000c00069084d2254000e552460000182c03201c9490041240c00c203d105400c3c511a1000b50004e81c0c0401c0110b412000c0c3e888411140304040006a030b41c9005150b1500080c202c0700403c0e0002c221198030103450030417900c1c2640ca80340c1041405c00041d08131803a4950003061540708540810028080390404501070f4041d4050081c03242ea291541d0f200c0d940174011086219a445903c03030441a00403089141401f4425280c40f04200310b0f85d0351a035500b0501e04200d00ca10390129840320810720810480d80040c0900340280700859507070000d41d030f09420407100c11825006140000c154920304008030000c98400007140c6802c0074640d200d5100400c0098501030401c1989500800075840030080700300c02240e01d0703403a03526417044403201c04c41310034015001104060300600c041000c02c0c91813080d0f5460b001d480900040e1511809000e000158404c02d00030071700030003c41e40b24180c00011002d00a52a01a0700074064103006880c018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 980668039 1250 980666789 980666809
    0x206070314060f0a0e040f2d061104050a0605041a0f0d0903030f050f150307080a030302160b160305060a051f020111040b0c0c18060910051003020414 66
    0x1010744036000000702a0f10348220010b820700310190450712110340317440000ca0340c400111070980d52002280a10010440004003400e58501801c003147c82080a00611007400540d440300034020701c0d00d8204e0318070902c200400301c1d4002c040080220700201d90382d50300905103401c60321a101030032944141c0004244082c80803112090600161646441070790b810150040c103003c20103908155440c2c500826641d080d118550042480304054038062909080d08a442c1001006090094001020402040c000044c5022000f80c2c1418017503190300340c190a002c4841d182050280580030303801c1c2400301890300780c4944201358683c1c0c1d405200b40d070385000601c01041c030360780b04541e008012000e030400c01c40745c2090615803641d4580700114000030403011900381a0010781012400000c00130b072484428004001811000c50203071640302e60340c84043c80c0c0764040f04000340302a0140e540c40000030742542c9c02002500c043c0c180140304860350545640010001e402a0090a06a004440e620401464409411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 980669289 1250 980668039 980668061
    0x150c031a03030304111c080f0c0d020706080123031209090f0c1b010f090809030f0a0c09110d0c0306061713060b01020a060905030c0c060f031501110f0105060102060703 74
    0x5d08071080d2900d0074403000b00c8006100b1100030b151885a034002407160f0000300003481520070116118000f50404074200307800701240c4015980014000c100311608030400c01d04480e10201c0d00c0085c80440f00340c1c0304900c6120b940c4a40c0c1402072001c0d2804262200780a02841d020540d0400200c1d0f0743c400a60310b00e10700035960040a203c0901c88030710741180700b084051460300c05000220390840d01d114840c0603290354502c2150500340108040015041c10800305119050110007050700703080545803624015068050b03418000d881c0c1c540d0a1290b080081250341200a6600030000d412481d840240102501c1c040c010001d6202107650b0450000c207241036000d442d2000a00e54111007566590b0005c0115408007810f40c014810031101040b041c1c402c0c0b0010758001c17005181c0d5002c07140035141c2003c085402061003030605000b040390844d044020b9030342c4070711454040201c08030000010380e41075028003002095882032140301c1c8d41c0940b040d0406070103980c00380c08a404ce61101e040540c150303401e007121 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 980670539 1250 980669289 980669303
    0x1a0f0c151003051b010c140703060e03181203120705070c171b0301060b040306060906050103020a0207090b13092001140d050c0c071707080c011b150c031a03030304 72
    0x4000c209410481c080520300c4e10506040c0d04400071961500b4a59008104046458210040400a220150003020021003542d0b000c0c5180441a1090809815003481d516020341965500d0030a8100100100c600c508011074101d94245441130006010341d00c0708004407070010801c00c0001703070503101d0b0f82c0c10036892480340050800c501e4010360107246541e004079040e500d9074842c0741c00204215050018005980900350200b403185c10641e805041d2541680070320b04151040105a103050341c041030920544806141c00724000d50203000181110040b036400025291070110300804005510400703520b801c04203503c210107108030070019515000c008190301c028190400400e03140c0380b01540f00b241d0145440003018181070180061a20301125500481550030000c0c4900303490300d0041041200410a840007440030607000c0300000d000d010ae103501101d802c0c80c541900e074200300755000c89450400103d0000c20052820400c02409803400902503e10b0044403000022203060100c00c8a1146402001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 980671789 1250 980670539 980670553
    0x605010e04020c0c0933061b1501090c0f02060601080a1d0d09050a120203101d010e071503050c030601050a171e0105030303040b011a0f0c15100305 65
    0x400d00c80a58448920002d544c01201c604001503078407071220a000320124011805142c071030341000441d104841d4051420050b02c40c82d80d03400c0c2c0e583c400444039180c28010107152080d94040f00c152034040c44481d49100c0c4503000e80045010240e03030b880705851151980d101c1c66000e46030b200c140e071030f0b070425180580090040c070005080a02c00ea00216600100305507407102059034041c805050100c0c210107003002900440c2d0401c140d140c5809014040d12044c04c900d2101e000c03a40c000f0741c1d40d0481111901c0515202e0043c000c007030442c405040c111650b000000d100701100003a03201e071075614900902402c03a601130011105288240702d1540304109100b119171440e11900015503158000d0b481a03010010003da09010031021209458000e84001060310b025551070141c20001440503000140240c0c011310810010664445038281102e03000040d000c00c0c846c0b03010501681e84a03015013170711300c07580c00180a0399001b000119003151100301c09001c20a9180e441180c05c03a5a0035100c00b03052988854 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 980673039 1250 980671789 980671817
    0xb03060a03030f021603140f030f0d1a030d020d020708030a0e0f190b070512120406051b071407050d2120011d1606140c070e1603060501 60
    0x11070755103034140d420700407643c3c4800741a0550401550036001141c4211f5413100308169400104a521094040a0080e500f4000401d401c07101d6400b5402d00509810b07280c80d0081e0140d10303440108042400054190b50075605250006541c440101011000500c034000000a03082c3c80401681c122205950380e1580b980c10580420460390154000c2e10b0f807044900580b07022441c03580024030000c01c000c00d01d454423145103040450a088480d80b030f40c005d000c02040b5100c50740c050200c90590081d40100f00040903181c00d04404452100700c040c0c2082c80c0300003e465401e002012000e0101c0f00c41d43c90880d4070744d54a44c1d0500c140d24094500c010801c80e485008820303581085805242102e4061400d6560b0a0303240182240451000442c40347c6650340e00701d032036a00c400d4205c1480441c507082008000080b400450914012114032401c2d08100d1202580c0040e842c0000c1111200702a6400310b80c89035440d0482c01882903030983d4880514129048003031f031580d00070300400080b01d0303058541804203070400b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 980674289 1250 980673039 980673047
    0x15050c09120106091803090b040b03060415080313140a08030301061101180c1517070e12060f1603110d020309010f060f0f0506130b07031205040f06060b03060a0303 72
    0x50045070701c00e54a807003001c6a07910b620711851111801e0b0140c0703008401d00d541400342140e8050b4119868400703040005000b013004510490790490401e84000a48640f034003040d000c0840d854021550a0000243c5042d071801c0e406040f00030b44004411640c3c021040c60204820820349203c0d4507402e40003800100400b600809116a00c0101c4400102c0c0c62280105603084c0030401c24012034014011050900022206804000003407009090003244034804c2100b8042c040e00080684c0200094000803500b40d0700c1c1c0c407001c108440c080008941c2142011051064450804c68112101110350f800c4d80700d58070701c24001d86641003088805140742c01605414800a588000d014114a40d203a1001c05000c0c1c4143c03241d04000d00c1c442540a40507410003404c030f5251134841e401140703c3c02c020b00c000c241c8040c410300410202c40050072407503625821460150307400c2800c40c60501e00186001c0c10442441448188a912030748680400c111039512031400011501003a542107400c03080d0107109100207806 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 980675539 1250 980674289 980674309
    0x50f1c021b0c030a0b2814010b07170313020a03050f010e031303020108040f050d020606040b010e090c03100512010501140406031a0a061e0513020c150c0d051315050c09 74
    0x42840c0d01d04440c9590311000c041c03080c4204da01418250b0f212002c1e0b401564001f02d080c09444000c004902d40000c9440d2941c00001070004681107220000214000940740460604030340d5016200382609917990400d03603111048144608000d5081140e448028600071007214ac603000014600038042f42540c0045070613803001402100c07041940c200d0100403442c100480715000c0047d60081411349460400d110507503110300d40c810b0610000c0040c03a01c40381c0c0c0b003946a41c1c0c000c3c40c1803403c58495484520030454529160701190300401481e044c1c960040064204030706030740ca840c10003800e4200301c905220488429100141c201c8400c07004592075a10300c42c1081d5004180201c000c80d03240d0710b84100071408076040f60f040c900d1102c0e101c0200540c0c20b18444600105904940450810480c0300040791a0602c0280e40c1d20204441000036415515407800d5447d580b03500c050420451424258841c500b000000c0c095030300010240380552545008d0140d248504509542c0605085020080c0800070074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 980676789 1250 980675539 980675551
    0x50a0909020f0d050c010e24181c1b05060d021b070801060f0504020c150702150403050d0b03060105101b020d0b01050a060302040509010501050f1c021b0c030a0b 71
    0x20b9a0300c2e0b41c0034590307201842c00c0c10080c09140940030045540300054010000da140b0740e402000c0f00e00420000d040035104419581c00c1d00414142d499980710440703a4907242107402694042600ca4036800b810001039003010005115081c0044038030f40000c151402c801480c41082e5101108010b445107a100b9a000351260915034442c641c5200410700c212810811507402080407a95030b640200b202d8507420a185000b002c090307808518182100200d40d07200c0c1050008200b40c680b80a0200702d00710310070841041c0f100301d80e14050700c560400d8600104603038007201c0300222441c00d0040f050050314000c10414126640100004e001a05006003902e4000c41e16080c0a40700c1c100c0300c038248c050388401e5041c00d000c5114864202c00366042c80b007006982210380e00b002041500c1440280119100e8580c594191503090034260f8544481070f2040c0340500c144400e900021025a00e054104a01a00507001d850424040c035051052003111607940c0780c002040140e03165000d07005ca0800710303a1004180d50860 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 980678039 1250 980676789 980676799
    0x20f0303070609060f0b01031107021002070b03161d0108010303140f1303021503220f1506060e040c120f020c0a111f080a0e2505030115050a090902 65
    0x1d580c940301c00c070480d055004151071a07911420115005442ca03c00c0c4c2d0b030058000d0071b0821250354804c107509028015118000d019a8258402c145828001c00588000700300b2282d01c0d81d560b260111200f00e8207400c20b4041c402003a0f800c00f02820355003e030409102c9440d41a5600c4000340c1ca5510122905201e01000c3d0200d0072003040300f503000b0710740c0e1001409982c00000780d0b0698207155105201e0f035102052409241d01c0300620600110054540e01840c81c0c0c40c1d15015118881d02d64102642c021120910040120a0200741080940c5280e08510129071194840e161034144400c00e200548240b40110f0000807041e08400b45000c1b241c0e4000e1528040218005041100d0001c0d014544640e04d05d09641c01d10003600451824901070b00090b201440d0000d4071456048529005002c0c7e4030040c00400d0169200d44a10780c241d401003104059960400503e103440e0440b03259040350008450044900035400c0c0b502e040f1003100b100000314111100a4902c181c5c0510b0001c28000074103603c50300320f03484 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 980679289 1250 980678039 980678047
    0x60c2103150602030304020a060c020604030b191a09070807021002130308030405100e011b08040201030b1c06050912040b1b01020a090503100c02030319061703030709060516020f0303 80
    0xd40c05441c0400040c00d11500150303034900f0a40104402c20b000c03a80020100030340888020300584841050741c01f2241d10041d14492911801e15190048424440701c034001440c0c00200703a040c161f54151100702910a03511001982c80d01c0c0011501103404507540b00260f84035907490280080ca660003000d120302c134148030fa81708503143c3d6101d002640c010355040e1042c3d4801c01013114504014841c0c80d01d4614484020814100301c51089041d40051880788020b000220b00000d0030f5901a0b0003010b032864005104011600403940c460256405020050300d07190b15120004100140c0000c000e8900321800715a241403501d405010765040d0f0240880201201c90030042c403c6119090000d4003400015031070b5441c1c4103007081c0a25261441c3c0c003070341c01c883c03034140060312400d150040210b130303001400707943c009003402c107486401006006982e006075458505058441d00c00b0f080440594000d811507903070140f01a9039410101c03000d000b00780e0a4100d0702440421500145494a8240380000018041e2810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 980680539 1250 980679289 980679311
    0x50301140d0c0b0a120603150902010302091503240a2c070806040b04151a040b0729040803070503040c08060709090e0d0503010302040e01021204030306060801060c2103 74
    0x8007031181e012100c0f01c01c001c40e0b51007581e5040f0040b501051414041002000d04e1926200b43c9041c1c107040e404511aa50038911007035912a4049075441c51024211301541d4072070320000c01540d0310440703107a5400c010590b031140581d08011020f40d801c8000428088103242000000d00502d40c0885000c143e58588620503401042c5282039648204007546070004903107820024042910080441c8a2080d0301d0a0340c1660b03d403801008000903144d010310303144560340c0110303001c0307a40703110f40d40101740c3d580d00202e5a8810000354180041501400e0301801c1d6001c0404d2181b01342660050f00c1c0103000540500000d50424420400f1350340c01030180d24107480303003940d882d560750510a05071111030001e0000c903c03d102e12011030140030b6600903903070018658a02c22000040c901d01042c00001e101d1070319100306190500c000d40580701d100701603110030205400d092074050001d0040d4480c12021450040001800c035000f2201c1c880b0345034118042030304000c501c00c4100700400384000e00c0c00c10302d9554100204 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 980681789 1250 980680539 980680553
    0x140a180b1206040c06080f0f06120106030b0a0b330d140a06082d0a0605070c05010e071802031e090114090d050a050f120a05040201110607050301140d 66
    0x20764070800360140c00c1034281402e007422204901e8120b84180711540c014050f0494141c0b0034954007900410340c8944a80701c080c001010800c406551504d2582010004000e11403c2c01b08240202c40407901041850915000c0c800a010500410707189644e0701d41629500c0008280030011060038501d429241a4100806c2421204409840366001131220304001c1d04150a109041c041d10f5190010720351860b40c87c0d05003001030701c1d800c20030342d55542d00c900f8008110002c1002c070503c82c1d808141484180742c40f003801402594030300400e54496081c03180d11320401070b000c28014243d0354946452046a1624011000a940050028048241201b0780c644070500102c0901e40182c0310000082980321500d01d240c4010500a044000a900480b2044075689e4222080f62010502c40c20090744501809030890105d0041e1848103000700b440750100664000c09600481c03240e40300f600c0d080c0954440c803c0084d03650008548103c0420401c10052000f0200e07407211030760004000b0101c20240c070440d903901c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 980683039 1250 980681789 980681809
    0x1a060706140106090602010f2c01060b030106021f060803090f1804200108060d0b09101b0f05030f04020f030c030f01020c0d020d020304140a0503190c140a180b 70
    0x500022003075103090102c17550a0207140c9000e203010005000001c40c205d80c40c00c5064503072200241144c0754200c5c1d20b0204a00707400003001441e000003850b4682d03a503144069110b10180d1110301c4940e011203010460080f031849104141c13095807000b14107205110060025441d03011002550120790200000b405081d49100b91340724501c5103403074841c08180300000d5001c0110030606a41030003640003c1120b20348550400c1c0c402150412040c030302d035440e885000d506160704441e82d5080b050400a036669502070a4040000c1440c0a0b0707511402e00841090460702e9000079118203c01751000d4010502620305444280c60310b20004040c0d4503031100800000389415020f80710148030743d401003600a00e40318140f00002203c41d450000d1301c251101c6000c002d440f40300714002c50300540030141030864039072544240da070080d200c040c08032401c5185000c107242c40f501d401030084074000da05a1010031038114800c200407000300003400c0b015010b402c291168840c010b0b980440e00505903100e54180b4680d503010040307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 980684289 1250 980683039 980683049
    0x7030302040332150c030406091208040b221101020f16050a05030d1418060706021e040f061101180b190c0905040903020c0a08030903010506041a0607061401 69
    0x40510b8100900c0c030381c4040c00100403055558001000b49007130040e405030f82a9001c5003800407103641e0740c0c8a26000b4024006c840000c2c095507072070350140b9034542c0c0200c80710340940e0185c81f00038210703501c940030800e8840124805283c0301d000303400760704000b075240c0666000030001401500c0c3c041c8841440d003842c00b54034141c00510b22091210400003030030805108005080700b60042c003081684450080c280912004d40d441844000060a414040c0c100c0205070306850000c020581e60340c22810000c010b900990251084d04401c1c0100b940030354010f004903821110b01c41d600016591822805072283c00141c1600c21840d52100f0138541c0a041c110302607123120b4815221200b031800d092102040b4446180340d8600218074002521a0545d0403803030800446004441c081280d5555190403418402000306031504614000c501050303007600132024250b0004190001c10160341c4007020072040e20032802408464285128610801d81401002001014080c010201d0340201400400180c03040036400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 980685539 1250 980684289 980684333
    0x908074821060608070302010813080d02070311010c020a1e08040905040606030b100f1a09040f0f0b06040b03011e08030f0a09140307150c051c090b1c02070303020403 73
    0x4001c1004000d10403680600111802402c0040c03e5500192800d807000c0c0c0344d400b80003290800c24041042102c210354000807502c6007952118018900606800e440c0800c1010950078071a4481d8140d100180780504541c20106100400036075158a600c04902c403402a036400c1e00410020820354104d01402d80603d200d0000003c1440c91420541924880501116800b1500b07982c204000c0d81c4103000d11003a01d40e4400150009800215041e80c5881200041500b20342003440d003131842e014a40c0950014a072269043c405c480411040103090300c13683c000d0f00180c160a0006021401c241d0000c00300c0940219082d000743e07030f1902080c5203590003a034030000302c02200107485c560a070380c4074000000030f090a0b11038404180303a0b03500007a00c0e0710700e5010310070a110841d1000c0010900c0345041c0c6845680060540309424002c41141c001c0050040040020030b0220100140d002500c6007140c6440f060501c043d06100159441c03280031b54001c80c0c0c1030702003580a12012001c6807a03c1090032503100c11a074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 980686789 1250 980685539 980685599
    0xc0903031e0307020f03030705030712140a06080706020109150b180a06081b100e1c0609051507050d0b060f040b0a120c020a1b080109080748 62
    0x40007490059185c280c600c2c075070010b100f8002c81c0341d003010549800c41c1e40d60034202045020800c07004024010300f07141910303102c122000d1242c4a030a5a1060080c0c6842005448030191541816802d1390062000181013800c0315000d0905403c0310f901031507100400030b2404000c102500003204c010501900e80c00c43e003070ba03a401d04000319a0708100e00000b0850f00e0418481c48146032340041c41c0000d0301010303001845145442512995030f03100008545400d0031008a01d810078500b000c1000f0700240c0360071900341c401c03000340030110845078070703101e20907102ca6072003910b0031145c065100041d2203810315054100c54144440ca5440d0390318400381003d401c40000c0291160031800c4010f1000f84d039000d914214620b803010854006901103000309819820440294522810045602c8810207992081045500c1c00c400307102040308000c000d1030b1950040010801000300032001408203040b0681007070189001c10400015485c1e80a1400d26001801d980030f4000b80c1d0b81d21281019030b40e651201d022800e480d00b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 980688039 1250 980686789 980686801
    0x1b030702030715020c0f01051207031d0a05070902030f060618060304080702090708160f180e06012601030b0a18060501210816020a090f05010906050909060c0903031e03 74
    0x8425003884c403041b02e41d14814901480007a00178070071200e4640c00d4528480c0000c0d00c190080d0807101c00505809130200c00001e210755100e8440c41655011102e90150500005d000e61b82c50080e640650300009044a4a49030081006000da208180c182c2700701c0b16820144900e030340c44001461190b80181202c0d0b644961620402c0316075140107080b4014030035500140034400301d0114440301c43c0c0b00b49051210403000c042400b40c5000300000f05e08074012340d00d4500403806010b180181401000c003a00c03514454611060011000507283d407080322482190001040410000084c480d00700038036440001c0d5500c114407810803804003806003941d0f00380d20707800108039914003900fa10310441f180288101810546555024113813160050162170001464a0b09056640b81000e110043c448464104081440c1041c4040645401d100c1d0f1080310303243c80c0c4000f4540c180348078481d124038560300181080e90365030500700d00c007500701c0582181c140c4810b0055003262110900014a51010307a400c0507101d140c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 980689289 1250 980688039 980688043
    0x82d0106030b1005062715030a1a010507030f03020a0e09040c08060105060f180a0f08060a0b041404230f0601030b07020102250501020d05151203040b1b03070203071502 74
    0x21390000b1301440c01002100d41904202c851280441c19840314000b0880042d80020001072404550900c044000024042d081c0103c2d48039218420182210f103800441d410010340e40c5000b1514040c0110310200d000c521a544281c1c01410208998281410000104004180b0300b400484046501d22000c001c284296081000341500610044601c540303130610084880749a4051011021104400c1140da412150b6881c1d8001010700303520f1041120301660f5901e0300380e54010644130a10036619264002c4a00e0070203005402c000c250b0100848503035180c42c0d0f1025000303030301c50320441000c45240107000c1030b90006001a82c2c2c0c09844030020f0400c0e504508000501d050080e003d08150382c81040000e001d84058005a2080610f401d03440008910605001d4003a208480c10f182c5500e1901d01005102001c0305454444c5040071380300c803154903034001e0b072440c0c1d01c0c40749014190142100b80074140c80e098001c0305441a026a00f01600d00345071850340031904d441144d8200ea2000e024a501c0c600c43d003641 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 980690539 1250 980689289 980689321
    0x190e030c04180605131b1409010b0f0c0c04020c010606081014090705190305070f110601092c0c1905060403030804060e0d090915082d0106030b 63
    0x200e6003004058010030541c0803590050702d0007842d21351a540002c1d00e82c403004010080c01e5801112204908503207590039070342d4440ea4040c000418111550401c41402c003804050b0580303008400d003038034200d0300792080900c0d504003010005640c810085200f550707841e14000703001e200d50344100228055040c103402521044004011142c180000c01e01008040401c5c918840c1001068528541903100c5450841d80c500c21039464411450305008518540d99055008a108420543d100d140222600304111105140710b868a0945d5200000620045000740c1c8040e945a528030040d00b00380200c80300014000b03c0c1d40480130890b4214403000043ca0901c60301800e201101d55034003041e2107040c03d0000311309008070702014080008840014080001e698000007100191400726110f501c100c0100030f20001450040841403401c1c410000b110340f001c0c2c07071a6000c2e56444005010119000400791800c8031108465486c486048042020b80f0413080c8145000b440c0200700685940c54415154183c0c051 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 980691789 1250 980690539 980690563
    0x161703030402060403061e15060e04020901020d08150d061406010c05250b03040605060102010e0c030c13110a05030718120b0c0f0408010915150b03040305190e03 71
    0x2080042000681e24034048606690384800c00003203140a52142482c07081540d203044480f640340400e00843e00059241c4201146ea4a90301c8164116035030081c44203a0113a6061036015900c07041d96540305a00400311140d00a0b481c0f403a005420240500282a2071b4921070b09032092a034624040a8055841c11829449442824800340050465440d65501c00350058011410300e48151009007282684010350014405105800c0e140c1c181800d01600402050b039501c7e01541c82e103124020300ba50041410411a0801409007441600d120b0920048001e8980c00481c140d6880905a5845580c500945030780145070380c61076200c0ca840280a003d402281150074404001c400040217103c44040c4003201c4030b0750200172004c0300d489001c801d480034040c00c0b603411400100070030049000c0d14154490640c19005000030070301d0304c0501c3c031000c049401404210131400e4854000f0301084500c54000c40e00a44a881c101e80792a0764590780355856070805150b040000c412412081c101e280c01c2203e000a10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 980693039 1250 980691789 980691793
    0x91810081501060e0307030215090405010e090a020f12060405070303020c09040b070518150a120c170c04030b040b0720060a0c050c011103181b011209051617 69
    0x424800c07540c4006600c140300780020010350003240c441d1924180441c034010761b4007410304403038004403000f00240d980200c49102e0195242c0b100002309082524001d50054503034001810a100988e000d0000c0203074289801c41c0c020ba54a032040700c03600d004100a61141d8011400782108a0131850000d050441d40c0c6007261040491105120225980c40029900f120300c509040d582c0c0d07224201c4224410b00c001c4142d582c030158411b2001c0524a6100c01490f08541e070341e59580d904d91032591410704542500c1888400140d0308003400c2c401d01118480030b500a000c003004030782455642d90300c080c290042210300b1503242c1c0b8443c1c1400003107600003115000d4154401c884803000a00ba490065403060020228444503442d606812592406041295180c5424000070302c01642100442000d50703100b940e1505a4401c0044100c10803100412104500145800503064034481c1c8001103c002041c210300c1c0485503076800704500020300c10050314801856241c0030f9001d02d46803001d042105003000e4030391042e039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 980694289 1250 980693039 980693053
    0x27080a022706120f070938090403050d06182a05091809010203041b0311091012200103060602070506250302010b10050703170c09181008 60
    0xa90540069900080c1511a0b00ca6804201c8100349030004000d404c5800c0d009207100401d1100e4240c205080500c600d070500c08401c82c2c00100302070009803040071070380b1003010000e68503000d1900e03a8030305400502034035200c0d040c58845e84050045a0b06640000d000c04c0d0341405040503400940541003000010240303030959103c480c07103200d000707811560041003004000501441a603503810f0000000c402400aa44154945940c446000b0340c0242c40550309450450395446082c100040c0c1c180c1901d900209550b950b50400c0700f4800742420103071194a42150340c03035002c1504c41d0511031501a0350300989041c1140c45055807c0740e80b090391411028109810300800340304032500081c2c020120341054402c160360b100e8092a84030003034501c080100b14040045a91424903905400215100e502291080480d42080700281c609202e54100100800c001c1c40540700e20541222001d41d22800700a01d00b8039120602c0001054802c1032090b03110a00d200d10180852030b04d00e0074140c0d014203503820003007201d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 980695539 1250 980694289 980694349
    0x6050a0305010b0f180102011805070512031e0c0a0f0f0308010509011a0f1909080d030506010c03050903100c05120606070f2013022104030e0127080a02 67
    0x414441c0709002a5024140b04072940d17580d100750300c00050b00c508003000f0a0050118036095454410a200d0140f00700c07407140340702504c8100441115216420040d00d8441184010940c00c602e03000b04043c07982e00d0003041c0c0340401003008080841c0b01d581c0b10318180d882c2d03800b03030b481e02030001d03101a04840e005401d10001485968501c0e103001f02611001c1182e0f6440f400c403450490b126201340080c501503100425030703c041d160303048108036041d15128002d4560008000c2c00071421120100c4840340003170ba2008014001c80e000c1c0008048000c40030341990850100d41c1d02010540d030002d44840c000502c002906200c0c000400c102ca074028100721031a42ca040c185440b80c1404031142d28020303204c607081300e50300308410002c02c02348200d111020b0030280303510083c190030f40000c0d001210202200c501043c0700d81800b0755141011803080340d042c1c030350103405204440115508020b2000600d4139011200f81c0b0001c480c901d68005006004401c0100b040030150310600546401c030502c1d44070103851241d10881 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 980696789 1250 980695539 980695567
    0x705060a0525121d240f09070b0306010c05070806071d030703060510030b0c0a121b080907080118020301060f03080904232a0c0604260406050a0305010b 67
    0x240f40e03140c42c00045500030301c42d640b42e4040e816002501e14644103840c0c1d06440a00c10410010424452801400b070f259030700301221400007801c49500300e41e0380050308140700328008100550341001c010701d402654a00c00e0fa079040d107042c5060700410041c1e03000108000e9410703404000003a00440303407001464881c0c0f0040101e641da44150100030603030b60720380f0009604000301d080b023a4003d40d0465810b01703070750501040c244441da0081840700000342000d641500543c3c030902035214444501c8003420700c0c544269104680754180504280000d0080c1c2130005400c034070074010f803103011500a1054140346201c1c410142115040d070300003000d00810080400100f000102a80c083c144190307800709113a43d032440d1020000c4032170101e4100700400c60060185900014540b2500911250201c142c142845030700c50320702d4050042032521717a070301031070000d000070300840710000d1424000144004007076200601400c080e08250800000280b02040c401c0c4025818047c0d1801003a800340c07501d15011090007920 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 980698039 1250 980696789 980696807
    0x20d05040303150b070c1401020c0315060a0f050f041d011505040c08010e04140a0b041a07020304080a060f0b1f080a1a040b0a0308040b090f1005071202030705060a0525 74
    0x400309442c2c4c91f02e0300030690080c440c085580c10020140d4801e2141207030013589161068070b031a4014130490801140426420039064140c40000303000074042d10401003004060b280c0c6500c09281da500d880d00501c0030321000d0165125000b1440303e50800641080103210440b02a00e031198200300b403c000401ca1419007007209a00541c2202c40d81c5561a0000c2c6540d01e80180c08200520400225040209010501e0b1000318040e00d90901100c0c544c03500e490490b520300841c024000f51750030a8071010001641940200d00d14180c000700800c890040b580005d24180308070000781e0203884200e4402c02c1c0658484000c9911489e040d004002c4507080341c10248003021011046400380365100da205650b592800c490384c005603030006040b41d945881d8030485a4a41000961a015800c048041d1340f05141400781442c05013500d035500c50a01c001e0340c807603941c0d0481c0c1007107030070079400204071220101d2402c5c402c0510540c21030401242d517007405a884c1d41c2070f00c0e17800d5112241050811105071210380c080114 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 980699289 1250 980698039 980698049
    0xb0604090602030a241208220f03050c010c08030a09020f04110c06070219020d05031b0c030106050307120803181911060c100b0a05041514061603030906020d05040303150b070c 77
    0xc2c1e151421003080e0fa444160328222081014007201c0005420302c9c1181d514029207105609a07034250303c142c0011760340c0503254800141316100610004103d010154002400e5500040494000c031711400082803c03a002c034859042000000900045000d00400415030800c045100404010100c103600414118240b88024030481003103801109100080041e03d80040c011440d0300704850001c11030030b03552a045280c890084d400c00c2c500213641d1030041010401c0300c07480d10180f50050010b50f03c2c00400d82c401445100924a040e018090400301045400b01800c4403040034030420300281413010f1b081a03610f265500c40c00381003003507848211010a000c101c1600b58080440c840035107a0008507410303002c0d0852500a4a001400c05221179000c4801c4102d81c10403101d0b0490b201d4005c180110f42c0320300502222861592410800082d110f07501c04405940180760050600d07d40c0d10011080d558141e030140c00117512001d6500d0001e400601c03400081c21036020075440e00324140c1e107400e11003c0314465 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 980700539 1250 980699289 980699303
    0x8010e090d080606120f091b010c0215070803040605330d030201061701090c060e011b0804090906020306010f0807090501110f030f040f120308040b0604090602030a2412 74
    0x10400c152101c009980255540c10805185480c046e940303141c0001c2c0494801065120710f9102c0896001108500602000180e4480507413028507000e12107204141420542c09050811012010542c1c41e03015501980c07103050046003505040f0111419080035800011201c02d40e03101c2c1620f80c20070320380f10051064040e10030011180300c2c0e007000d0b40100300c15800305086e5414041c01c031154081c190300c60030380c02e03110390341c9160029181c0d42c04443c403c40102c0c5160110310b10084c00c4030001c00c1c0301c1d0603000240c42041c65528064450381010b05407040400708403001c41e004818081c0b15a0000706070030508525250043e01807034400300007010148144242c0341440020790510030380300c1c814007031007a9270303001c03082165620800d880704031071194418812400058104c11010030800040b542c00c0038516095901c1c2c0e08a5140e588030340b140110040c003026405a61410011300203070707980c0044d500c0340240b003100103a111198102006d100c0b44032002039841035030f105030500c58524515050080c080d00608 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 980701789 1250 980700539 980700541
    0xb130b040e0f1612050705060d02131d060f0901260a080301061e170705070606060905010e010306080a2d05010c0e0d120f050f0304050c0108010e090d08 67
    0x2000c90010a82a10914694080c05141848400d4000f921100c9640f8030084010800e9452044428805605000070525006040100704929000000c0c200d40c46940900629121584000401d901200c0d409100700d0605840312100c00c803480d8143d2070388040c050f184401000c40d1040025160841402141c40351001c500c4c0c5c04000c0184400581c0a199400d41120481d160b01c2c101080c4542091048100280d42d00c602035a0100c402d4007500204091902d805250780c0d5141d810400b8000c008041e203007005000d0100d000414940d000b02c00c010b0146446420175141803400050056280c0c80505044c07504005040045e40030000f0b0042003e50008403c1040c80341540c0c04100c01c0130400929100213002049030310a10806502804000b04240c8a80c40d0000e110000d0200300b00c1510360141000740c980b040341800340d019141004850506242051404c0415040040b2035002070740c0071b41c3c540e80104000041540c2007416a030240c0a110701c021060328080c403026a40d400340001000c10008410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 980703039 1250 980701789 980701811
    0x60402040f0905030f030f010518060105160213060303030b0102070303020a0b040c170319112e06031a09010b130b0f060403030c0b070e0f060306030304081518010b13 73
    0xd440500c0465002e01940d40d80d100295207100380d50400da1f0560001c8071301074000203407454030044251041c00781890300d106590708c007401511240c01a0110641307110002504000607500e4051201c0041c2100c0d1000810f42e085080c004c088440f404000e5040d507002d1801800400d4000828020140c0c1c8500a410326641d54a010103c500c00c503848403034900c03440f090441e50f40304048050f102ca2240128a005050404601190701210035040d20903d5040350f0f145041042c008103060104140b08592403954800c0020040c0072582654815540c2c0b0192031144c45d00840420030700d541001100c4024800e40c4081c90008002650403c0d150500c4c60303a40104490320f440f80c07040c42107040c03801484251a16230380d06014005001d10b4108440300c0803600700240031035000700501160f503e4050b0a8014441600c03050195650014180550601c0184070018414034108010440c25401d042008030f24100114840503c0b040d0180c1c02505034181404450a9110b0200c04d00188010440104503602c5031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 980704289 1250 980703039 980703041
    0x20d0c020714010522081219030902060315030109021e180610110718140a200d09210f0903080904051e010603020307090b040509010603020f0c071d0a020903060402040f 74
    0x20390310110307140c0144104400c81f000b480015115002c0281e64454050680c02422012282520402580000d0034030100e24859410781602c0c886c0e0f070000c0e0001810641d00e400041ca8012446e003044000204c0041110181c181300000030f2002501b10a05041800c203a0b00003101e00501150801c00c00113560081b00c032500c8100080c030300030540900701d415860818003060024100c10b09400108180300404607003448130b03610400041007290303140e48034042911920b880303c43c0c0c0b2509011139690780f140790101c0890303861103690b51050180260b8450742c02e8005009400120079040d4482030200840c1c003000071031713100c070200e552410040302c0004955440c4100807068640010300f00003c001007d00204a40d81c05900840c018003c580303075032484c41c0c1c0d41c8001c20707170610942c010281c0085010b4010081c03a4003d0300544505c81c1c040d41600e082c2405a03003001d140800300c1d44414400741e0307900764000c8a10100003015400044462096280071009000700340da51402520081c0100e03521183c6002036017903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 980705539 1250 980704289 980704357
    0x1e04020117010f03030905061309050606041e09050c03040317041a0a0614030d1409150a02070303180303080403110f1504020f0613030b06060706020d0c0207140105 72
    0x60711418256503142c15405003030010034041200840e5485c00e002c105490310405880c110040c046030111001c2c1400003001c00341c840500950703000081030001041410b100480c007080c1e5404003000b121820311b001101c0c010b17228007402d41c000440c0b0410522021a601902181054084070520402034403203140c0b15400c9040f0010101e641242d80f418444d1a80840e0403a004940454059107444a203032410191180305420864000c20540880c0e114515000360141840801c010800300450860280c0403405602090481006802030f0720103008140e04501b604603460301200c0c0d5403250364103540c1e0141464801500c0038090010864038422040c07420445843c48405050940e80303ca030701000c0440045006072822880361386070034446081c81c1810700c2680c65283c02c000b00e1030801891926600e6800402404a40e084001001020b011885a000801211004160028805060500c02810b0840b80c0c2c0100303140c1210581c4008040e0fa200c01500c2410642807213200c8480c01241c411014070b0302c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 980706789 1250 980705539 980705567
    0x2404050603070804020108070f1d03010e0115210f060f0905031603080f0f190204050910170f1f0213060509011403010803030408070201210b1302031e040201 69
    0x4000010071004550040c400fa00462003038031800000e440300c0c8020740e04101800c107500001901c04901802d0290a14500710041d08040c00010344044030307401103400d40344c003d042899003200c2c00d00200030345c0f510303800d4203012001c0c42010358504071074540e80c40005080110003d010f8036242c8680340750003079240c1d0101400540c09011aa6134074201c5c81c0d01014004909421ba01244207000082c401c0003060811170700c90380c00305403854207a40e01e01d0703030f042d500500c0d040c8a00314040c1e080c800810180c0b240d0007203d00a8110f0740039030043d1460003003900c1520344500c1070a2025041000d513211810300c002210710050500c1c000980c4400190080d0301c000340502034002d01403402c1c2410000304241c014004150103030f002c3c2ea0b0000d60a070b40a000e00c0d00c030b10080c0714500305030303008000050200d20080301074000284140341504080034426500b49960076101c482c12849944c404840700305141050748910000f05c102d0341507055140500705d11512041c1c8001c00c050503d03002002804680c0704610151600c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 980708039 1250 980706789 980706799
    0x6020c01300f06080312040303110d290f0f0f060c0307080c011404030e010c03050c16050a0609140d060612050d0f031a0d03140409150e06240405 64
    0x28421030340c0c41c4007804141d4101d10165151980200c0c0c0c069010084030840c6100f2202c007006901d4070394045009000f120140c12018005000384e241c2000b650081901e403608400c18400c504c45025450718041d80c81003006445035035045440645600c400f10120800441250022134060700003020038624032484900341d180e40000102d810400094402030003614001000030440740c9000600100345030002e03a0b0240c0400c940c080d50014940c810910010102e110b40303815800d00e0341e1031014620f0403071000c8142542d04034140c01170003682040780c03113040141854540881c1c51031811120170940c21110150b14042c182c00f04036401030006079080702000b030040920000c5907031030030b040094482c600b0728000c0300001e00441203071040c1c9109002d4440d405001001c00752082c40c2440c00c22090036030041c022800e01100000f80c202106401c0080e00043c0407140b40454900481d019451018850f90054500ea0001806221058a4218420702c185240c00c4254140d62411400345202e805640d03c0181e01c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 980709289 1250 980708039 980708117
    0xa0c030b060c060a051503072706060f120203010f090b060c03030c0d1a0913051510081c0801050d060608010903090905090105191a030709020304140706020c01 70
    0x100b24000340c0c2520602c0510410061612140b10901d4001034568007240c4c1030784900401c1c48640c90589111004400401c80c42c274203001e00030100d106403034550344102c000c901c1a107a205e40c40e0350003440007106881d5614046246604113402514141d41d6402084000d075961414a86d00c0d44841040701e440c1c00040048039100c1c43c100d48030400035403050320920301c2c03113080207600541ca51840c41038140c0e00000904c2d14440d81d48101072082325071b070250002c0d1483d00c03c100110800c0c03201051074a00800ca4040c000c18280d0400c0a4180381030001300e0750700c3c52031400c040b842403903541c00390410781920400c842c540e002e45003600f003140c0501103540140d4015468800034800f01600191800116050403800313000c2550781102d80781c02c991080310b10402c2d0b00035101c0400346000720796028410f0f60985120f011000034103480401d01e000915000321590660000601c000c0c094040310310325666a041d00184407881c00d10f04002c4d295425a0119070500034a4820303200c407501703941036009119004860221036 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 980710539 1250 980709289 980709307
    0x130504060b0a140307061d0405010303021e030309061b0c12031b03040c03060e030d06090e012403030f030b04020d091119050d080403082805030105090a0c030b06 71
    0x20306030246900d00c030300c82c403100000e0b1114018682c099030100040103407541c20700d001c609807940c02440001e80001441004030035159075891240601840c002c7d401420503040e4000c0400d84a0703200d115280351a402401042000c010005a00d0744c00a501443e8055442009514042e02c0c0140d01014540c0d0041000700340540d03d006010310711a50084140b04026190010846582e1105490180c2481600300c000e0000c1161a08290307541e20a80c0100c9103011300d066212400c40d14160480724500e0344955481004400074000c00000c88004c071901548070924041505003010f5a210060a10480d04036503050b4500981c40548402c030041c10541d43c80f48540c050400401120000b103c3d420038114404101c5e007406004441c00004102400c26002d00b000104000c00380d002c0c900b1101c0d55420170001c00016040c41c050f04484d0404217203416001e0040b42040e4000480c42c82c910308000042c80100099500c0407441074000041c0480003e04d00a02c44003100640703021144243c10080009080032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 980711789 1250 980710539 980710541
    0x1110a060b0108060904110103201c0b0f06030a050a02192727060515070b01060e100e0102122a011a090702010612060c0305071403011413050406 64
    0x40c9140302640c83c07036240d03980c1e00108491600c003038074054600881a01001403d5002c1d0340121104800c0c0050280e20003201c05140c00d040d0300182d8a2900320020368640c3e440d886c540e00501c1d2030b40404580911035603605e600030038400e02005000c200d890381c40384042000e00d451541150800003166841c441d000341c01420241c108804051559400746002d180c00000c56180b040b22420b448213031255140304800a040d420b40c061030811040d00c8150b82c1c090005250780e510401028500c1c0d0304100319240d2046003044280004143c0c07055050000c260454101c3d9580d1142d0704440700e010f402c28050303507858000101c0c50300c0d01e0092400714100002995811200d29041140c01c0480c40d00207220038444419040ca007650103c01d900c0b007400703540c40c0441c0a980341030f44855038000902c1c8000170340550b64003e80b03d4009092041951540d41e0780034003900d1180e050103415803010403410b009200e201034071100f003210300c4144034100a01840100703400d01c1d96a0308803c002403545c00c4000b40418101420028 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 980713039 1250 980711789 980711801
    0x50403050408060a050609070e150d09031101050c0a031a04060b090a17151806040606061e08010b0306040902130203093003100503010c0c12031401031101110a06 71
    0x400c540c482c4030002984004d403809801e10849003c0d1a054007601c030800e080d00c49200400700b465000540d55008001038074280e01030800e41300301e480046680040da04005e41581d00343d80324a00564144020001d000c130262080b520031319141c3c0340005441040820f04281c00221101d003a50285c18504005140000500508641c0d001200d024001a46d6090814401d04000c100c4c1802e640101418501545031540525440944040d644070b0035211016003d080c071000b180d088480740d940350400e0042c5a4841d00c01d4400f121011038503002c480c60b40b603004d00400070503c030740c5031803aa00000003032040c1c880d0f130040641a5406005501c01c0c030340c401041c5000c2e400440f203554080c4105d1300200c1032002d811821104100300f084240004003081b21080340e0b1030740020496a07880d000c884000a20b514244201620070410784d4401401d003460349402c0b0000141d100200d01090306003100420114508004241100d610012a01c00c0c855003c0040e9030301980b035281c4110a00641d24070809200344c0d038000d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 980714289 1250 980713039 980713049
    0x33133609021e09040807020d0f030807091d180f07030c03020f010801061b020f09090105041511040524032a07030c0209040309090c090807090608120703120504030504 73
    0x52080145030b0342d078101c00d40c103101e4141648410008040b40204411000814030706002403c803403400040b944485200d00e0500c4800c500041944080100144e0700c4201d00b0041d000c0c281d034000c2d0014528204405d8500d01400360001c08644681285002400704a1100c00307209040545048640d0390404d0340e5044507510040c1e0080d001c41c0c008036485e42c8910b0449040e00d10070745980c80c41c0b001001581e00301e00e0310343c0b204982000e480b140210160341e400103000c1c41101e42d03600208661030645040186440700070981200103040400b190201c084c03c0043d20166402500c0783c5120701d00c40c1c0c261114860281690500f40130300001403021030342014103042d4406081150947c4214440060290244108040903000440b52031444c001440e008034074640090007803900303140c10f0381c850307035207204903038814050b1400319030407100c00c00802c5018004a030083c000f14104011091800c0c18442c1c950203d5002984103880c002490010103001d080644025081240200841c1c589407402900d154018010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 980715539 1250 980714289 980714299
    0xf091915080705040501030308180a150c230306040e1207032003070c090e0a05060c093d1202040905040c0509270c3313360902 56
    0x880c05013464043c890407254513540307201c51540d640f102d03c600c2d0104102c041d81903016078802c0d007000c683d40015180d85000542c000041d05160394002408040664a03d1030306291045082e455403440001a680d00c418103450101e0b4186070141c40c1030800740104203554100001258010a1582c4600843c08150328101041c0b00c0254001f51240d80e401403520040c4480006c1701c0a1004c10390079000302c800780892208450810000386c0e595400c09034126000904160041029a510319110021a0f40441e40101b003454245601c04c02c98000b003203000c81d60042e900b10083d00d801191240485d0720500d40c0a21085449545074070212010305000d40301520a20510031002c142c40c5041c21038140500560401503501e8140868003481012081c070090315036009082c0034040030f4036402c07000003040055908500e030728207140000d40c5e6040c003100d41c03604510380c0a2140c0c81e103103900c0702c11030410b5491480c06101c04015180c510341c03550301c03c5101401d8500c0c0340d2090a64241c66500a45841842203603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 980716789 1250 980715539 980715553
    0x40504051923071d040c110c04020901052d030106020105010e01061d0405040305160809120c03211b1b030c0a03021513030b0106120603020f09191508 66
    0x841c045461008000e51a150259034041400c43d405004103052501140c401098003405110004044800700a600300104401c84203c0b080c3e000c060007200b019101c00c550440c240144c06000074441e002e4105000700c1320030455400261108900d03001e84504e620301c69038a40e03940c0c41e548000c0c041c00003842041c5c0410079003000418801d0182094511000303e10380c2130006015010f08200c040c10b0007510590a0000c20081c035413440140f9010914042c0c0100709065499200d807052210b114500789082c11190407143e02e00040703640104400a2010300c1c0300043d40504a44110020948505294400c1e03c00d0401680100b101e0046000740740031200c0c0308009181c011100034035031500c81240b09a43d20105451083c00103141204403d40c3c1c44d02e81d48081c9003810701c0c014604113219419001540c1c40b01240c0c004000e802d9104404280d1801d941c1001c2c0403042c0b540e8045807054514808c100d102c0c40a03040002d42c5d920b000c1d101007081218800045c820384008619980c071070880d034040c4421a010300702c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 980718039 1250 980716789 980716811
    0x20a1e020705100513091805102d0b03030d0e1b130c050d0e0312010f0311040c020102072a060c0b0621100c030b12060114060405040519 60
    0xc5032001c2201d0010700a9070034205000800c5030543e2024143c0c1c041c08030080c03804110280700e441100300741c5104d075421100b0002d0394105589007000e41030394181014184040040340c500700c80c0340d0808002d0582408241800e41ca0141009000b08070051501480702040c6240c40003419085800b00c0403c1c501580c0c44814080201146c000941c40c41c103401c004501455000f01c08a43d0009406900910380b55040424400c0e0000176501c4650324048158008502c0100240c082c500e1180100242044d0820039440e503541c914a0610000c2054422965081c01d044224000c0d0126403110794002c2c0e0012251014400b007000c0c0f62444040e428440c0a066004251140900b100e0001650071144000c03443d84c41000700040e4003160750b003041514100350380d07054480c0402c204010b00c1100c20507002c104240180d200400711b440781402d19209046106103038592103c0403a6260540b08940300c0c513100c690034400810951b21480d2300198010b4903000c1000400c11541040a580c000445030a10504041c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 980719289 1250 980718039 980718043
    0xf380a09020d030f03060f08060702070e150105090f13090302010c0c02030a0f021f08090115030f020906040e070909050c01030b0a06080604140f0910020f0a21020a1e02 74
    0x208030003500039000c0c400082c0400d004009a180c00a42854013140264883c00100390309640e5521041096012105000707070300d5014002c0c9806000d5030034010100d46022040076000003665500281403182c0090807810b0b540301c3d4009808511130140400c0948000030f08014020710701c24905030019440c00307640e803c4140c82541c0d4200b519400400821056660b9220103441e1550b02e0003ca0340540d802d0026400c1500303088840e09000e081d900c48070124502101441c0c00e48440480c00c0d400f0f50800700c1e0900c0021420100500c05c560140d40e040f84680c0c0d404040350003003040c05c0c0c106400b84a81280014a40784036081000e01610550035250003e402134010f40c1070b158244c5419a00c4400c246042c800c06114840725640000020400700380350605048000c424041900c43c2c0c1c00088801041000c1040100703c500c80a0254000462038400010361001c000e005588400e4200100070780b4025155030210900000c00003c408119a198024000038214080e0f40b80140c0710310b44242483d20507d400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 980720539 1250 980719289 980719301
    0x42703050c15281a150702040509061e131101020f030c0d03230106050d0b1c0b090a1106070206070c0b0901140304230f0a0524130f380a 60
    0x408010800d40c550b00001c21940402500f985e5050410602101000da42d450040300c1c0100103400141c00e40c1d040c046000380400d12910350f4a104002080c0610400882c0078109c07219442d0480003d142d0700520200403824003c030170300401d00611010824201250010a04074070f4080d080c1c81c2004928010942c900040c40a0f154403142d03034540100400000d4001d00c020040c040c481400007030902040000030b50540021000c1c0c200c0446d00c10324000030008840800c1d03810a000a00422541c4d1095548000d50358503c00c103280600f5010500f0403c64840105490400c1c0d400000c1c4003885468040140550b0004084540014a590104a40c0f801d186040300d00803500300190710229011491118201981402540d00e0b500c52310b548030703905500c1031040b0b0014500c12405000c220750008004180074080303c0d40c0d912070210042c2880313102850341041c6100241e104509092000e681d0900c2c1104540540c1c0c40f01c040607201c0c98264080b601e103100c10103800420110600c0988840d1a00030844107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 980721789 1250 980720539 980720561
    0x10e01140a051011150a0c030c0810170a06060b0904051008100203060a09091101030b0109142e08011802030c180a0b070f02042703050c1528 62
    0x5240200f184a41d100d043d0245250b40340d20121a00d8070306580e080940c1c110125040c100c01ca40d41c501c004d00040e41801082414402490b06450504151070071003c04035203841001d0250000f402c086151850910510a5140d000002088155a07a489800d50707544017007038151095160000080d2550184d460031810b48081100902e43c51007801521f00c0254405000ea07540702c1407020300040e000c281d40c0038800d0428401c507441d2038902001000901600d1344038032542c0c14841406010710048841074804c4002c0c100c129049400c1039000400580b20110303180b001506070205072200b0070002c0d04083c4241c100c0304406c07154403003400703040d4403c0100d000c159071154550300108100340d9039a540040d071b02c200706070040440d51081c1c0c0e242440100c0c4c0e1302190045035103020b2190040b080d46010320910210380d40080d1080000f0805609a40a4108001c0020107014004c2620300f403041040002c5040c80c69420b0241040e402c0035049035581494071440d004017000c0070303030000010740c00034010307000070711 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 980723039 1250 980721789 980721799
    0x313140d031e02012009031e0d0f121b0206014b1e0803030c1b0c091512010b0a0317070609030806040e0f0d03020a0315030320060c03061c0209010e01140a05 69
    0x810400c811242b402c1003401c58400c0180d05040104801c250740f1841511544044411000314040c000c041d003808016444003151640007888105003029a91500352051410b13041c094140c501a40c0e03803034290000e0640003001800b5003001150303d2421094400140e03c862202e00310150b501c1d5070440c1e503440102c6035a075003000184020f4804581054003101c0d59082d08040e5500e0a1000f00490200c1804407002d17050300c0a116018521810b100c54503540e1001440b00030302c026081c180100310503280da03100051280303107248091305100c104002510105a40000284900c0446080040c9080825a80e542c0b140340f52000d0355113490400a003503c521008040070309481d5224020540c025080a012107042c141c41d0324005801c00788040c2c860b00514482d840d142c1040e0301e510b40e90701d00d50030b140466200d030760b011100b80112201040162503200c4d4040b10400c0403008810342c540300d410342031040250080040b60002c10308460694a59044e940201640c42c200c141c800d040000c0402d962007078a03080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 980724289 1250 980723039 980723053
    0x1082203030e030d050906070908030c0706080c160303090204320a141008120f041404060302130b1c031205180313140d031e02012009031e 61
    0x303010750442045802114160390038440c00084140c140d60b0100ca80100e47c0c1c1200040120080d0020041009401c819004500b00061a20002e0b51000035010300403d005082000804468a0701c0c00c03100c0b01c0b803002e00e050f9002c645038600030f800351a940204a01c00c5007080b109010514202606060310900c80e08449040d800d84840c10142c554094a44041143c50700d0060b0741020000c04406e015401d20018840603d00d412941410200680c2600c040d410041280b0381010300e90405950031f40703502684036844069210f0000300204501d42c0004c1d049010540c0940311101d1030b0703005440e4104284e500d004000094850a80c104a813444000d0115103071061401c15618203501082e0b0025400208000000507210000e10f1500122281c02e10f0801850090002c00c0a501000c0054901540c0c860341203410303a9005040031820520744170304082000060150180f0035008010442100d4400e9040c0031480c000341001603000402d418001c0c401c115202c6c5032015403000114103c54200054044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 980725539 1250 980724289 980724293
    0x60c0d0e0d050c15091b060f040609030b0a06030803010b090d020a0e1b0a02120306030a1707030306060e151305100507020f0d0210110708070f0e1302010509060a230306010822 77
    0x200710706c040d1599406c0388081c42601a500344160041000d402582c541161071442c2d40b50039101900020082e03145541406020000100a501501d05660704464515110060480032808030084c064020b58092850180010000e400c18440c1d40509220000e83d8001c3d120860720300041d1080394811001640801d21001c00c0751899405107811070303401400d0300c0c0004541d440c2c054258403034845a2031007030070000b607003020540c16100c0c0000074080703800e21900c41100700001a0049009a2424070030340da00280c070b107961030381c1010050068000181207505200c0303140c2000f040c980102504a018420201080240d887c100500404030756004140071212800300c00d044030b158000200e0000c040c0b082d0304c0042031071442880404003504415a10807015458003200c1c10522001070814422103244030380d1000541d0380301085032152602502c0a039030751152170f00110343d00301c2c0b150061601c02898155a607007107209500110300440342683c5001c2180c03030340b03e502507224401c014840c0091008510f1040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 980726789 1250 980725539 980725573
    0x1206150c02130504060c20070b07020310051906081204050f03030f0406020607080f04050c06220306091a19090f06050414010c0f02060c0d0e0d050c1509 67
    0x5222407015212840003501454680141c2e1016502110b2460304c0d5402180c69603800201110310b8640340000c1c20b1181a450520b41d1200d07001d0140b1211144009403c90035504c080084038420f080f007500070009898090f40707034134803400d00d1085040c44c24204500060140720010b0342c08105030040800514081c5044100f09030070400425013034050200b44140c1510201100c094001403140d40c024000e40d02d00040000c02c07090700105800441c0c4103040c10300c000b0403c0003803580031002d802c0d02e8441e0346000d481071102c00780a128841c800d090303400c0c840200c00c002040c2c121201c980d20458160141103414480e400c0030301012210b08034462955000c0c0c24501c030b119006100b20303a020b0242810440055200c030420b5400031a41916809104150200c80b41c400348103131849565103203850040c0c518181d90003511444068509260190003264043c20800c456101c02001c030810300c03c0307031218902c0c0140649a9002900e48442e1405503503036215550f24034200c8940304004e020081c00c626070103030003101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 980728039 1250 980726789 980726807
    0x102070803090d030e12010b010801090216020409060e07060c05070b030105030d0c0804050907031407020c0d06091a190605010504050d060c021f06050306180a020925080601120615 79
    0x740422510ba08801c03195206d200c94900b10250040002ca0b80c900e00750005814200181d002c070400303600c104050143e0207407120f540054241e0440c0c000c5107096081c2801c00251108409200c003500031242e001414903081407002c3c00641c4100300783c2e0995a035406a11402e40400d12406406400140b51082102c0c4101145800b2520902c0410b080c00d4541010850060007207540d00c0119540e00240701ca0b103002078100701e038000b40e94030080410451000108a1240c1ca0035402009191102124401c1190180040200c40d003030030303901d01081c98400d02145c40c08210707880019441d803030690042502d500c10012501950805451000303072902c136586090040a141c8a500b00314081c00d4142c10781c5003a090207003404c51618003004502d5034100000c1504282010b40600d40d540445424141c4c1c0000c0820800c02c600d40489200710503580e400480340c101c0340e01c00307405040c48404440c8020000d4000e07080600495003070f80c400030640e4007580403004131482ca0207450310301c021802240c103000c0d1041c4100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 980729289 1250 980728039 980728043
    0x70810140115051e0a020f060402151b0a0303021207081e041e060c09080c0904120221120f2802070212060919122016060206060102070803090d 63
    0x1031032422a803804840c003815100f11490454400005a504121b90f0401c005500110850042c0c4000d0401e43d0004040c103501e96200c1121342c5000c102d0140034080001c00c3c002c1210316000ba10400c44a51400400075405040a800d03602d86603004603002e903201c2d2031585d1041e83c800610703891080120360200350700f010080088540300481d80c020f03210b165004030000d5640344501300105450340e0b4003c000d05503942d50b401c041d8096104d1001020b9560f03601d5030781c5400a810140f0800d518400907400ca0030078814085c0800c000d03080b0440c21642d0006103004000307160072804882d005880d8401403550702101682c0c1404044ca100c00f22003510803080051480382108a0001898080d01d6400f284015120b008142a180c120908024001c0414490800c600101e1903000b80301c50351310f507200c2541429280841c0100404e04c0e02c842110481001482d00906150b4115841e00c1074840c0076088a01c00c9000b0b05005002c0c100100e20a0350000a0781000da4000a01070743c01d00300710005201c5050010142 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 980730539 1250 980729289 980729297
    0x30a050f0706091a0f1b0711030304120308041a0603060f0a1503030818070506040b0a0309140604020102012a111c02151f0b0d060b0c070810140115 65
    0x10400014110301000300c50500c061212030542e140907035080325048001800600240c508503841c5005400703100c01c03995501d48c480034640360110500c01007803441c0100d0b04500400444201014140358011064a100358421158000c1e50b4003010450107003c4000d594041e05076102071b000c07800241080c031809501010b60304002410490080c59000c48240c2c543c4281d01040d200300a01c04180010f13440c07005550f40c0000107000c1245050042605880380c2d10a00b001c0c41c5000c1000402c0903c2a0410441250460f11311280042c004955503210304090340c2c120702641c1307841c41032242c9050107001490128081480303244500b0201c101900c01030110751b001c0b2540e004400300c1480d544c5548025140c0191251300500800d100b01d4061562036401501296241c0c8160740d1640c1c1142202c00b000702500d004008440e02d40155a02c041c0141400740c1006100031008540200d62510011b84442103e0a010454000600c000c681303004483c0550781c0c460a031441000140500388030441c54070000d40700c6140c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 980731789 1250 980730539 980730551
    0xc1e120c050109230c0a120b2a181005031b071a1b070f14210d1a090601261608010503340f0f0512030a050f0706 50
    0x184d2002c0307441c03c0d0035100100800a1001d0b03035240d2001c208010703110601b604c9440540b130404095403a0b0400915004241090020000e0020f0990409041c070340442d500510400c4000d12441d0100c5410086062406180420441d4200c0c54529481d2201140c903458043ca948c4034403a6180036420b0064802100020404c9214002081907186040c3c1300d01035170806009041c414140c44614000b002003140501051003440302240b004020814a41ea1080c0b2952141a480c03502e6805d201503140c201c14802da04a0040b044003801c0401003d00040b0424108050168481024a00c40e0043d00c20b54205254000041665002e1420400a640b02d488001401c07003503100c440301004822070307080103203140d40c2c1c800500c00c9412500c0d0ba030140c04224040c100040e41006440051502d44400310810f8190882d07600104803c001c000000d043c100f508100716540302e0f10207001e0383c02d503486098040c018035003504144007804415100e03035000c90b0350f609190084901d505200758104000642e11907654403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 980733039 1250 980731789 980731793
    0x5010314060a2c0117011d0319090b071a31020102011401080705040b040903050a180503340803070b04060f0501090e1006080c06030a1b0c1e120c050109 67
    0x40700c2c00d8020407091501c0c003042c81001e0480790941d5403d00c1201c91f0449901e0440d8800c40b00401954074803074801504542080b201c40d01100c030108154402c0c2c03c1010000760520620a08500c0322a07005403031415a1b043d500d611601503090702210205890300f144620b6100900a00c40c0002c020150051001190b0417030309c40c0341248086400e91102e24603078001c040400803810305000d8515501c0080324104102820b60b24060624407401009004101300c0600c0c80e54040d0100b500c0102804c806411513524100d052490007003003402c50610100601c1008040d150601c0044241040d07541c0710001d5070030480280c0e1014243c1d070011f001119002c0d11840e81c1140b489091040d42d0081070700030300101c0e0034411124481e092000314811031001c1030420f0001e0241100005070044001001e07104980e4958031110440d00500d0090700c10300d140c0400d0740c0c3c1c1049035030b8481c15220382580030343e40e2120710100c10611440c0e4000700d01001480c020b440c0001c210402d0291281c010407502840007c43c055660b6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 980734289 1250 980733039 980733119
    0x2001060b03180f011416021f0f1404021f050d0c0507020f012c030a021c0201021c0e010e06070c0e01090f0519020901020a060c0905010314060a 63
    0x220b8040e002c14403401c41401001c28200000300b0f0b01000344008014032280303083d10805d00308008003030703240841035520385002951007089080c6200001e24003060814000c00c6160010f01103150100502e642013294032400ca9200000d228000c560040024010803080d000c0e03c4c5441113115024000c1c031000741b095900c0400076014240042c1013541da00c503904c81301441003080d50140c00748900d040221608a4401c01240c0348009a1031601261010400c0e40700140040c2c980385495000a4208140924034003250080c40c036403c41882c400d800741d803155030800c0b00303010b9080b01e02442040007071034103030807000c041d40100600646150060000c61401c020780e21201026070940d40001d01d901d464400400100e641407240d050782d420880c0c002d10150a181140d8485582c40a0110401641c0019071001583c002c114011143c0d91102d400d1240280d1860301400343c0c036a070b101c0c040c0443d00707001a01c8551401224201c3c85504014038140909003450f0500400b4046425124860060032000e10030420507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 980735539 1250 980734289 980734291
    0x3130b060d1205190309020f1201021303080a0e030307030f081e0f15040908031501030207021003050a05060906281d100f0305060112020a03061a03011b2001060b03 72
    0x190f44a040d43c1380f0f010701344140421845100760003010318040040c1c1c01656224403c40ca500011211610100100c8100302d009200e448003003600e003142040c00100304100c1030058803410100740c50765100700c207211f03060548a202d195001800111421222000d641c002e1491a410a08695039048000740c600d10300c8003a084240c440e124200040420081d114410f0150b00d080c0320802d0354184002c42c801e54801d281c50001400c001030700d141d50344c074005841c0d11a070305481c12a03400420004041a06100140040800ba504070018908050000d1101c2c02d02e441300c14010040500800b2021010811000d0011403041c1c0b4900d82c03604009000904e46420528041e03601088004407121742008ca00401e0207120300d50104203040070904003040071403800b043c190304481c0000144860001184001110403209030030050140b45071041d1062502199640158ac1d14801e80082002c14400f1790b201141e0303015910744d08001100030500704291042d585c2100480c2040030f0001c545d179600c1e4034224030141c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 980736789 1250 980735539 980735573
    0x121e040e0403052226030d09151107080d0c030e01020d0e060a06030308010e10030519110a0b04090b120703110a0e1003020105180310020c0c040203130b060d 69
    0x400c030752141e5065900c0038850513003007482c3c03001060b141440c80742c4880500303081d910b20340c003074a00c071901c0c507640600494280e5200080104400d071114901209025000070b40565110310f030400c0c8040042c1d1000498400b680c004400070b0400c03180802150107046a924401d00701030310780c07104085c0c04400f4009481034242000022852400d91a0718a140c040300600030344070303907040c094100046a04401c90768199010100080242c0d07803403403d41a001e0f006c40d40000c0030752007000300c100e0805540c1e409054a144c400c030845640b21402104201c07040907280940307401208100001c01480301c0c2e55000140c02d4001030700c1030321003181c40101207040281c998010744140c1280300e10f42626203011182c100190400340d95890f81400c1c54024002040110700000f410b11038002001141c40c070508280384150b5000804480d007443c3c100d0b0450010350029484c0050340c0c03081a150b000c0c50f14240c020350f031151200104062802210b6180c000010001502c1c2603006038800419101060030141e444011032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 980738039 1250 980736789 980736797
    0x102160804170309091303050f04060306051003020a0828141f0807032613061d01020a0611072001080a06141e0307060909050603121e040e0403 63
    0x3460b001c451039108181038405001070700b040140050315500d94100642214160151408044051030141c50b90b1284003c00c1c041c1c2c0740d0108000495591540118095130f60a0319164111103144406900f0381c050080c58202040404000568031899003040030503290305000c9039040c0c4001d490174402184c003c00c88801c14214003008000308a602403900e004c80c44a01c3c202901150700d003242e00c07900c940942c04024211240e50195041c404c1a0015079000092426022660746400c40c9419104180c6480b030380b40070030745140080d81d800b6100000c001001d0b1060300074095020a6a0350b281c018400710241c401c0c01b0f41c0a00c0030001180c0d40f2100c1e907800d410980c0402d01c2c00705071100090300b2000c0042141c04183d08000c403d02944a4910488003100401d84091801d000d120309850200700c40715071156054419401c000584c141d205661104494040b00100025100c400526486400600d050743c03403d04100701c0b82420700300c100b84c1080c0d0140341c11a21420552a20402180d04c9000d5030150005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 980739289 1250 980738039 980738047
    0x20c04020412021504080a0602031308040611210d0905030d020a020601091b0c03030c0215100617090c1507050304060504090c080402030c0112090f0605010e07022a0301021608 77
    0x103003030130001002c0c0c546102c20b0381410140741c14181a9228007640d8001d1020342c020002c1100d070a150340e1401021607110b650300d900c41d521580010081034168410381d0a5109100c0c09000034200b0801d14290240c001c40705c076240007000101103028200301d0104881038030080101c0345088540f40301501c00c080701039000d00701c81d500d0801440c0c10b442c0b4180741e451440d40c0d02c104103030245820200720052107030705040105502d001c0c0e00041e410722014030410b840c010b0300381e41080001cac1038010340817003502d0301d9855100c404503c1041c0c101c0342c000202d8000000e94841c2212034010302d03000e11a40c003d05642440149001c0c46a0f40740703425600030f41c1c88140450008241440300c1441030068060402d400e140005240c545900040e540b0070360940554148a40d11046800c20040d13034100042c4540c108810800783c101e0b900e07140d0020403013441150100c3ca400c00226001c28070200d104035035054078061001001030394000e0324000c0710101c81116810b40d4200411035030781c03400218240b245401041b0144d11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 980740539 1250 980739289 980739293
    0x13020a0e0112020c0318010c0605090607020d0305040b0f041b0e04060b121513050105160207122a08061509062d0f0d052107021e01020c04020412 64
    0x405102c203500400c0900512083c0d80031000042600c1101084210254401c500240180d9000c0d03c900d8016042c1c03030400d0100402520700050680c0240d0307041d42185d40c00742141004600b02c640554000708103035003500c0411556954580e000b50011701804c0c00660810540501240c1002d040c1d0001c00144010003c00080c04424801e84603882c0d000e1319030030400c0444c44105915048200300c01400c200402011070580c4104281c0f20003c0d540c0710008001a0520381e000440284005da0310000600c100c403070103d55100740403041f82d0f00b640c2c00403140f40300200d048160004008040940a2030408203800020b001101704589401081d1a10181c5034a481c0401400380310b120051019019541c010b04998980b000e18013099001600c1400220300c05017000d00240024103154411a0701c40c00c445042c40c140170021a11541d21500c03a8041400000e550706142c070540642000a984908070b040ca00941402840e00145003040c1481075400c60082500001d0480e0801c0e040443c0521206c110101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 980741789 1250 980740539 980740547
    0xc030c01150b0f03130c170703020a0b0c280c1806060e0618030c030106030c0e01060c2a081c0311090d0807030516120e090403050904090213020a0e01 66
    0x40d001250b00c0c585000aa5140c00d0320354031002d02281348a00904070a00c003440070018410025004502c41200344220041c429079444003640030591082071036800010769141f0070000c4481c901c5960015080302c0da41c801011009121a11a60b10140c1a1160341000260815600c901424005841c100c0e01c1440280703e20440d440784d000340c004d0010b07000d48901540e881c45d0035034200c040da0302d1a4141c60645000031a003400868407a043e0198203201c0e001c010040600402030954010f400107a040c3c2c0e0740e5107000c84680d115148050130541205611010003003158104600f0741742a018002d05250391350980078649039418400600041000c08021141c0350300d27000d200d9844940042003424807100e2742c002185510340c0c020040c840c1e900002d000d4100350261040e03d01803003084010203040d9015003804800320b22901d04101c0001c080b421013910034035108151030701039600755a0b440d05010488023800020498400f00340d17441143c490511003c014180000c00400204d45d5030a03d0a400e10340000d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 980743039 1250 980741789 980741831
    0x111317060405071401030905100504120c1104090623061206040b13170f1c020315040c050904021801030c0c05121608120405071e0e0601050c030c01 65
    0x120060308010240700114800207001c50a803161124190052451040140c0041c001001f0003030030745c01041c0c20076072805030a40c0200d120704c1c090226581e0403e00e0400c200c1d030501150000902307003264100d07540010b09040c1d000070b03000d42c450300700014034440c0e503001c10000c0100240e8880901c0303000f02c100300041c1001d1500c4503a91000d10000c0940d03081580d07901c414490700074080010301035640410014410103c070002e03821813182040f182c0d10030400e1a840b060ba170105c1a030000c40c01403030394880841c20042c42180e204543e04918031004d440d00108210181c90028241004c02400780500d2407159550310040c410b60030f149908000a0195100142c2a10984c4a44c00c3c02d1051402c00c80010038004501c4140c03030054401c0d4995a1440340d82e003803907102d40180000d05201401310380464044400254540140e00403c22a045103650380303000ca10407a505c2e0030b03a802240280314108400801c100d04980c0102d0141013aa0601c0c0c0a4401760b45180c21081c51540503039101d41e0741d0600031078408a80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 980744289 1250 980743039 980743079
    0x50a03030e0102070803010e0901060314030c061b09010c0804150503040b06031f05270d0207051e0402030910020c030a0801060329120615041d1f1113 66
    0x95041134030648409501c0e00051281c0100566000c001491001c403c0d031148001d96406040803a0303580011f44480d54039004507500c440c007032047c1c1011405410469a0303000f411000a142e05141c07940340b100445075141d14403012620303960140000300d90040c03c840b000c8001c525595507161a0f11305424846040100503001a000c0c2d007246440d441d202d29450071440c018003000001050584914234007014801c815070041d80307041500b0109901100c404942101c40f0340b129801c590a035501c1c2c000300150710b0451b181da03084801d4040d40085842c10070784c016561011034038059881100318001c00005980c40496010500d80002803401c0d00a5001301c0c80c64050b082901e01003140184514080d014210190310b51000b0161000001d422a03450368183d40c040c5900d5000e55405003003406c0d11540060038003603450700c02e40c2041e0006502d5012000c0b66501b80550600405038074402c8241c0c1491541c40d03146070409a500c41088131a1110b030301c0001c02c030310402c40c0c20100030701c0e1038103055101546501c054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 980745539 1250 980744289 980744291
    0x304030e011b15060b0d020a030f050601021917070312050f010503100c1e050408070b0322062a02010b060c07060f02030c15060f0409150c18150f231c0207050a03030e01 74
    0x9101c6103034ec0c00251044034104200c4801a034400d0360514802c1d1443c6814241c283e9980010000c0c101035009541d4004804035800600c0180c072480c201e100681001d00035079415604c05400c03a00100c04903082600100081e0628001a42044890300c200450448813000400e0001908206090003080900024401d541c00030f415070a02481d81500e0815503160080c5003410f00c502d240601200364401c407290080c04c01c5601c1c54500120400200080d11407075480994030700340405090f41031840c220343c2510311400240c61410b05145044e40d64180c00002c2108604c4103010440b4044410010555101d41c40ba14200c0c1d5894003004124041500803956401282400c4030940001c854400c0f541c0c003108100d50104662066000844d00f88800014802114114034000a030500100700f590881920541c0c8280301441c030400152009000c4c3c40301e0b10300d034042001841a448a500000d410150032580143d0a00c401510300340c4140d8000104c152600d8005605480800d90144a102a07085003900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 980746789 1250 980745539 980745541
    0x130e010833040f02061603090504060f12140a02031905070504060321051c050402120c2b0f03020d02010605100f0507060b150304030e011b15060b0d020a030f05 70
    0x800700e001c01010704018101120402260f045507542400e98aa10003007122114460009083c01000860b4a118142c002c500c0c01e0b0b00403920a400701050400d548045005001c030b900260341c2c40b000d0382000700d540d070741c24000c1081504c0165010700a20b0514140c407c1968400701080c1403460030700000d40e2085103d00e16001c0d04000003030218100d03103212042040c545200601018060300d6a101e03010860075120f2400d56900160b0b5107aa0200d4043c80c020307226400c905008604140c0d80f5590310041a0340b029001d0b400c0d43e0040c3c10140e42d00400c4c00c0003115845401c180d60340e010242e05000c0d0003100942c000c507000701c043c65424440d04008000889107042d44085158000d88006030f85c0d071404c01080320020307074036062100c03c0c0c00090714143c0207400b89107816508441080241c000703403411400564181c00390f079100c1d80300d40e035016243d010060f00031100c030a4550719034440310600c0a49041d11070300c0b8540000c001e1081006072404600146016076a119244401421159a207804a46040c0307000c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 980748039 1250 980746789 980746873
    0x1c050f01020c03034014010c1107090501030b1b0903100606020c0102070b0d1a191a0304120c020f0d0308102304052a121515130e0108 59
    0x4040e1760342152000b803085900300c90500c504090866494842c140d0308010381d962640760f0140c0b0440f5034000c034100b9211101d072201e001c4c03c113680082c030000c0c010b000d0000214209145890110f40c280102c164568600f482d058081303030a1584202400180f55a204c5003009000d4050081881d02c44003480541119410119402c219000f14040a0301c030310f90f55400761400e900c4411490114840042540305000c0d006040d07140100030900800100340c254818a032400c1846200b074a0040da440002904801017419048441e04030340b4800742d0303209014403582d040b1520380300c501c0405240240c0c0d85081601d800c0f0880540c5411a51210466002d070310303010044a414a01103400c044021980840c8a4030b0322500b40c250083c80020042c01d10003a918214055425100100b03030b0a110314010319202ea60348861400703481d4881c24520341211034200010320200a00e401003807109a00003011884a4448507c1603811600b60003541141d40850340311009105600c03800003607107048010141e8080000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 980749289 1250 980748039 980748121
    0x93105070e01200703151a100903030e0109090f0b010206010515070b07361403100c031d011e0209030a03080604091502070c0609051c050f01020c0303 66
    0x4800c0b1502c035510a030a000082001348000402540c2106514600340c503807015600017800055002c0030805506d9088402c6820107032441c103085007181c0ca8528045107180c40c1621281032108446041116940c00820020814807601c881c603002c5074000545101078100180c50302e001a0005445448030b241d0004030028018202c40b44950b000400b00703000e442d804020750300c002034500c5403048407604800c03640440d6100d0300c07400b0346462020100c1a819580f030301484440500c0c404c1090b015040f03250108880d0b0303100d8010b10038442c0c43c1e182c0001c2907252015859400104440705107442d0f51200048840d0704c0d4103040b00510007034031280c01c6181515802c0002e0356580e048000400b80300303da900007900da9941d540001c2405800c207402181d9880c201001c90000d5214900071140c6031400d520114841d0300c503d80c240117035900982511108030180d628084008400740d0102e8151180000c1c1c0c400c00e8a0038009050310380c514000131347e140d04180031208504426a00c039110320f241d203013500d40750000300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 980750539 1250 980749289 980749307
    0x5070b01052d0f030303130606050108010f0e1003050706170c0c0d0c1a010617070807020601140604050301241508060d1e03050d060905060d0206093105070e01 70
    0x2101c0048a091940c40000c182c1100003c0305507507040c0408020400500b042d0050305200310321a03001006800d40358001911801c800307015000c5450005003090183c0d601101e0040c0d0029401a04104656502e5880ca0303c0c01d125030b000040004c41c4094012003056520801d2504210284030441c02e1440d4040003940d500007404400003000300c05500345050058a181089580d0041c022241156841d00e4010303240c050070307000e0b8200701d031038240000700701611850301603004e10055805007081364a080b040c01d80502040340c5582c2d22007420480041d0395a42489000b804000e4008207190316030112900900d20341041d0302002c00740007200042c1882030740c4542403650104048072850340d0b2101c1c82c1031100000fa880e24070141104d403040e040070145038001c80035203e0b840111400344a801d85136807017042910000d032249500701c4100c0340038500619000000d0584280e001d8080e4460215910b00c40c0e1022941c9502019940c461a42d407498006450064550010150810b601e8802c0700d90002003034110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 980751789 1250 980750539 980750599
    0x30e01022106060f030a060608060d03090303030b030f03190305010f031a1b16022b02100203120106090302150711131e02030a0b030a050d081b03010605070b0105 71
    0x750280000b02d40c0c0d41c580080d01c80d18990b0080264a074139108802000409950003424046020400001e90a1074008402c0803060b51503640d2a06051941e60160007a10004000a030315001d10016000c07080310070000380c1000114600c0c402d940c81000d400103800c462041c0c002464038001e800c0c0600c0410244220f90302c02c40d0b100315104105542d4004800070540e016403080c0300d11400001c01540840c0c0f0b4040301a44a80200c807481d0b01200a146540407003017040c400692104c0030503801d04098038084d2040e0019020034010360740f42100ca0414046807407c05d81001c008181c00c0e04080c010750400700c3c03410784170500c00004036240000340d480354550034007489001d5100b2820f201409120302299002030142c604c6081841342810b03007151040c000b9403c01c449030a801c0b0f241c0b5004048034600024400c08668000000d000540d50044007100d201c20000e014012a0003140581580300c07120780000d5000304155a01d40c2c0d15000c0614254100860682c0600d10640c001c0c40340340e140b40f00340b40914501c85 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 980753039 1250 980751789 980751847
    0x90609060f070302160b06330c0a141b090709050d0c050909010c0e0414040209100e0424060b1b0a0803040b01080715021209010e090412030e0102 64
    0x1076030b0090100c019200700803200703c0c1c0813505485001003040703102d80580940c0c004c407141d042c60b03100000408402a00d06850b580100d00d4141c1750342c803205102c001068461421015165a942d0588038080e40e5403021499204030342c0520701003a00c0c04101c424050a10303108454088450038800c0d4001c00c0d2101c1401010311031201e2503240010810a00c4070f04004280150140150349004403001d8000c000c07041c200004205201c4035020343d8a01032240401e00c9100501215003620b5607000c2c04040803004102d1803803c0300014022501760002c5242038401d520400c1d071a00c0c280d045441803a02c020307800c0b540c5200d00d41040c81c1400290305400030396810351580c01000000c41101000c1620300240c83c0b401402e6810000144000c3c0082221078134189c401400481d071040b5507608407160702c6e528070300136800160041901003075a40d402c00014000990145000304290b441040000c0c0c07510400d84084030a641c840c40099000ca03014040c1002c165540e10085040240c0000c0760440071a01c0a80d0068174 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 980754289 1250 980753039 980753041
    0x1706010e071407021c0c14030d0e03070b07031704150c08150909100509030d140f0402010e04090204020c0c0a140109030b0403181203021506011b0309080f1005090609060f 75
    0x146150132407140d203082d08070840301306c102d40d601140e80d202103480e50620301078040d1140d0004844e010b081602113005010700101202c61070200030801c5034110b03100880412542c281080023607280f00403160300a41c014849070200d203045d00c5841c1c0803209e03001d0301c000c00d00c80030404029061644000e40a40342c0703c103603001c10407551041d4106040000c10030700048890300c0c002c00d104041d000003000e44008012003408215506c1d4811001214030400c84810510300d81309800200154428421445100e4000c0c0c4082104042980003406903089001c0d11100740c2d10200c1800e2540c5481d07114003004010030000030846283c8003000030481881030001400c0c203810303032010030201485135207005011120361102d2498241c940c10303041c0d01d000c80c8050980040c4940600079200004000030f1a000f0f140585580e0055001c030040c000d6511a201d400760144080080000741c08103050091801001040d000b819841e40c58030090012981d005d4011410f81c0e004004118014400043c8039801c1904081c10940c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 980755395 1106 980754289 980754319
    0x13080d030603051905030f070503070c0e01080c1c02030d050406020f01021204230709060801050a0e0303130c0f03030c0b06120d0c0501061706010e07140702 69
    0x1044d00042e0410702100f42103100c1041080c803035819282441c9600c04c501485030440e100c15a8680c00001e541c100300501030003043c0c003030b00751036030901001d5041020b200c0e0f13102c02d1440840d000700030b195040e640c15101402d0200100d0340c0101141d040c1c241d0701070b000b440c035003003481100003500c03541c00c1080380203034180203588460b0200b001e079810980c2e46807603242c0d40d801040b1018040304904810425104028044503014081c1d0501c0411001e00d00540103084410090104e03000d0740c0340c0b03084085032810200480303810010710624071860740e02a05020041c180707a91301407aa59400f50b42d00208040d00701b681c0c2400303030f40142801802562400c080c809030740c1c0700a196031042c0d00314148840186004d81e181e082d0640c0200000105240c880c4004000c0000c0480f40341c89a50040c40100031140b120707800d86034407101c980b40154841210321002081409504070081c4550041680e83e46 = true := by decide +kernel

theorem cover : BRFrame.Cov 980575539 980755395 := by
  have h0 := BRFrame.cov_init 980575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 980575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 980575539 ≤ n) (h2 : n < 980755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
