-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2220
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:02:07.740953+00:00
-- url     : https://prove2.me/submissions/ccd24467-06e1-485c-82d4-a24ec85ddd77

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 399100719 ≤ n < 399280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 399101969 1250 399100719 399100729
    0x5091507030b040204090f0f050c130515070c170c010207271b090e0c1306082e0303120506010207091a090705030105100f08060622090c0908060408040302 68
    0x8903000b103a100350f0800002810310003901ca0202c245032a803002003003d100d080035080032500000c001044042003003100028a03581e644111081e100d04442c4110300c1c080c080c8543c60705025040c4010109042c900000c01c080b01740900e4141528141c0046a244200080049850300d601e88205803000440b00100515070b00e400003050705003050780000151707078040d907610064a0170948016001160710366006000c40023112001c0759100e000d4810041c9031128400b01001740e09040e1080f64108010440403849a1400b60b542541200180010a0404072800c021312000ca9841c4811008101480c20030800e85400d8028a84944c00507000780000c01d15202d0300101a2503284148000c0c0c6070410030040465545074400750048505a0f81c8944a41c101424458600c035512100010301442c204a10407859100344203903030040060324496100c2c2d1504828084042403c080001e2000350013002044c8a265a409510740849603618081c002e59a0b0f014152a00401c3d500031341084810031061000d401d04d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 399103219 1250 399101969 399101981
    0x10090c0f0c1e030504050f010507020a03020409031101090c060e030115030b0603151f050117041113090b240a15050408031605011109010c150e03071103010509150703 73
    0x1d00494040510301407000e500010702c6141140420404903003403015060841400b000c50304203081191901c0d14540000c0c1c03c0303404522000b44601e450b0402c1800300740c41000003441c8800041d009000c580003518041119140600410700010380d440080c60091405010340194494a03440d80d0f44883c1c01d6861304420b000c401440150184100c0c2c90b0b42c40460b00c1e0600710742c031460000754003035034000c03207002d07805007140031680f01904111190b8030b000d0010380210b660540050f4445102207202c0004000305020708482252503480c0c030324110f01d0340c0601030062400c91103080001100c001d4128014002c590314984101d0360b43c1c1144094106001e011035511301c10410360741d0b81c1001c506040d521001d080c46c541c40b44001001c0b841c41c5042003402c10009004d60454615207059641c200502c00f40006c001207035409014080c088403201074401c1c03444c01c1d44000610072880080d260341e00810b0400043e80034069829602a603c0c1030006000e1100100e4440c41d80c80f20301704140c1181d290031034124044c0c14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 399104469 1250 399103219 399103223
    0x150b0706050a11070309050a06020307380901050406050109050c0d020d151203030c02030415030c0e04020a052107080f07020106120c0618051c170d020310090c0f0c 72
    0x955151083c00b003070189800f51068034440d50f80c0c21103107420503050240b884029031103a400d642c42407121000003500f9000c0c4000504010070403000080d05404904408540000d1003200e40035954203200800354107403c51880749014000a104c01d907a509103a100315070003260b1402c41030f00d0910424005100c01c1d0012701031104e104801003882200500f00c003001120780d600104824440200c00d1080503058013961a055900b8000341d410a8a800c0030b40d90001c0b0701144017001c140d0b942d12080a40c0780145804054504050021134032a004900c0241c032136448600c1341c24a20224841c04600e071919012018824251035a0307a05082e2220780d090701020304040c140406654840c40040746444030003102c005054010071074194954900640034003480b40c40440e015060080ca007090103d500e44c240c00d042e2a0031845844030f1070303186505007240401410211003407011800540c1c0d14100303c094010314010140410034040b15a52444a4422a81c107031074640049640303c1b0303032030042d94064040084454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 399105719 1250 399104469 399104471
    0x6030703020919020705061303080a0903171f0807060909021305150c0a0f031d0109050112021b01020a110d08010306050a06180507020610180b01090515040801150b0706050a 76
    0x5009549403410000200c480c8c240c03a04c00d441c004018150b0010702030340c1020102400308400e890685000b0302055046800ca05148400000302e010084544800700113100c0904041d45400c0e118444580c45840c9407003183c0001d65801d4000ca910000c03407003205e00200a0b0710f81d940d1200c1c42d11052001f060001d0200a0700c0c42d80a200210f1030760814010881d043e4461040725904081c00d19002d040c040d010689940c0c01c1e00d441c035091940340d030800c00d560242d400900b40a104805c1800410001c1d10600404151914510703140480d100015005090040c1440e2560b10488802201041d614542090043d00080d00c403001040421101d9101a4000340f008001080081d261008a40400074400207010055655000c1003105035041c030245810182e40c0c5a02240b180c540348041c0e02d0040300d4a503241005556803100350040c1e014840f0036008000140c50802880d4540b0394014654110b0f220309c60640d404c0841041580800400200640301c0c5c282c511410140d05031104402854003d220354041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 399106969 1250 399105719 399105727
    0x60609140f0a060305010f090e100b1c0f0b091219090306060b09040b040b150d0e0a0b070e03030702010c0f02010c0206041701110316080c040905040b0f0603070302091902 75
    0xc2d0325020300441c060005900c0200d550b500d0310b4048061511940e0160000518002009180d101c0201d0040d50280f10130ba40422a4040c6400041c0410200300110008000214440e004c01505041c4038009601400403407086950b00d4580580f0340c4041d48001d075580f17030100b0900c00800c04503c0b003002c01500c00d2038100c03409600c07607540c102128a2070700507003604000490303110840e00e4580900d0f0b0201c5810360703050220a0003040410131254000c812840305840108136a03800c200145e000e181031120340f100303d4080341150b040c004510300080c1d4228000501402416900d41000800c8400d01030341a581d803090f11a0ad502c03004020780c40c4071022810001d00701e80d41c201503650100600080c1002105440e9030390090b0091500b1181c14009540c2c50000070702c10070407011840401044004030608000c0210707130340e400e003581480c411038010004852800b004d001c18801400d88140c4500480c03200c1d80503030707104d8000300f60f27a0740c6840c0300c000d5010a030003000907080c02c1e100c02d0343c0760f40c00c9040e4805814 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 399108219 1250 399106969 399106999
    0xa080f0d0204090b1f021b0f0a031a07090e0f180d0f1821031202030406020301060306050f03061f030f080d140415020a0c0f05070e01080106060914 65
    0x9a0b8016800202c10f143c9813401c4004d945003010b458018004a0509051040840d040c003070744544482c10701e92413240c16501c003c003c580365429004251100280300d44505c0d6141e19001c580881c0321601e510003181c3da4000103618a020305900c0041e101c80700e03006030321aa02e6045083d01b03a84003c0000d889c41c40664140041c0c1903042150412003101a100d15601c0190031710010450300b0b034192600558410240100b140d81ea055108c0800d4544c5191078440710300d5241003d81d0b0036034400c10480b5103131b48000100b1090181a90203141a2602558180401a601d20821003510074420f661396241d040f54000c9407000080741400303003035180c510314000074040d0b8070f4507036110942d10398406590541c00000c0310808080c81b0310480100c00012681d000c042d040c6a1900e01b00b030540400e20450070ba45c00140c880f21a400f648284500c55400f031b101c4111b0b110b540c50b001e41c0f034441511a2a0300b00e80d91100102d400b50307040c01031006842c041d6582414440c17030718800d0718001e514000041e8105260b0800808 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 399109469 1250 399108219 399108221
    0x141803010513030206150901090f0b0604031a061f0822050a0c06050403080a05031f150e01031b081302040c0207080c0409330609090201080f01080a080f0d 68
    0x1109800081c0188a0039102c2e0601900380301000301641d14001c086015000f0070b03990840c1e40c50545000403000a249075104030b8020091243c501d005070f000310003090010800c9045110041c140340b181616610507103444003400112161044071140c1c0a0b804c100d54045e061044a12540c000880e21140d540c60040a0046240e2014640181e42c0e07900596980014880301902490040410380b5026103003500c1d5441b00e0b90a405031640c48001c20400002050300d500d8070040d000022101da9070b02d0081b00d030f034407204011002408000c61001c101b1410011049600911540503100c9950720081f6900e21415030458581000a1000c0b20010400c1d43c25405a1584d1065003071710001d03a0002d1032020309000c0050300e0701008008691280b030405d04003500081c82d015140b4104642c0003070a10183d06080c604010001002803048500c91600600080b84422030300030f164128000e03216005561100c001004800e2024010103c41c0d9100c4918100011032090081239058840103885080115081c1040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 399110719 1250 399109469 399109471
    0x37021e0f0d0b0f0d0f0309050405010603020705150402061c020412112b12030917040612020f0403030c0201140301080c090915070503090f011803030b03030304031418030105 76
    0x249038000c01040e555200200c40c8900c940c403890403902c0d122406050800a044030301181002803400c0c1c100c0c018803080500071080c0001900000b40140722968468100134001e4100c00400d54080c0728000d00c41c04501000d030740081c01640c02504961034080020206180894221141000d180c1c0c00c10001800c82d40054540d095039200b001d110122011070420000c0a80260b00d844007213813900c4c0340000400d40017100301040c05030301c49400c28100ca00741900740d00428a148010b800442207c2c2c5d103400c880d0ba00780003081514207507290140d6021030310428030120b002e1440c00003100c420411080c408240902a5011305500c149001c4c83d0218107156a001c03d074000703900168045d4040d450b1701d001d91808181007036000c1010001048034031002c200e6048103c07000741087d000d2000c00408035003200014404002007810b420300900003680c1e107070038070151050041801d9000901d00b004a00c0903141c040220f83c0100d0b0035039211030481085c5811040f1560101107280c0c81c50b0b69220803d526502d0a000ea5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 399111969 1250 399110719 399110737
    0x6211b0616060518070803180a18050a05070c020d0b0405160807080d0e0d03080411030d0e030c0a05010507110402122502030903152d37021e 62
    0x3052a00300b00c0790280c9043c4e10042d60080300e8104070018000741000105840e1503041c424425201400800049220680c09400a00041180360b034445519206a0031041c05443d46050801031556000c00848450a00a100031b40c000d00d000000c80200d41c00d007400d60341090003030050b15010710311650910950b42c40e03a400703400c1a8011034010041c098061020400c0100c281c10301018003c00240080c0c40030001800040c1800045004078042c0310b0401351010214901504481e0f29442140f405000c400280361050f1103407280c2c3d0440d510f141041410360302141c030183c5629040150f80e5949120300d4070802b50f403a410230f60a101d0035820f000020300d424018104a01544282e840c8403e500e038007481c07800c03c00010355100f0010740000d900d000076050381451030040388280766200c0504141d18410310b261030b940c0021540d0311b100f407000301c0780c0400d034000d2001c0c0541c200301e0f603140c8080d081e040519503201040702070440c40c03c02d50507a2a40090030340c045a81c820361549105501d00a13500c0e048003643d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 399113219 1250 399111969 399111971
    0x62c13152402190c1203140c100509210d11070f02090604060f0501050901020307120201060609150e040207020f15030117150105010e06130e06211b061606 68
    0x4600c0945805100040c8002c440f45049440e00b000343c0c41344a5003050611840300c030070500170320580605201d40324850340781060244a0b0b640d40800520b40780d65150803034100513a01d05c0c00001c00d000540003c1d030b100380c0140304601c00c030f4803c00c107501d41801a000084503044c01034036408800a241c0f500340007441c00d68418000c0c02c191540c0b0b4010701c42c00050013002a40600e1900d6400d00c0082542e072100e104032802442c00030303914a45400100c6c11400b40e8103000b05042c1084504044080d01904546d042c0e50340c030b41d680c07541d0a82d42c03101d80310300d40d4030113010310041a0b060041c40c20350305203900100445030024010f2602c040805004c40c594450008600103038031000f20041c00310000380c000c2c10300e12114210088c00d43d211400581d07000b5401c10f210b4181441401c0c1c054145540391503064132003005004900400780c40d600e10f0301104c42a0100e811038490408c14080c100840000d00c3c6060b507800b00344004010135039846440c1d414100040c290150321a0301407041d41c0000c03802d04a40700246206e07600c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 399114469 1250 399113219 399113279
    0x190f0f0308011404020304030c170912010b010e030d090603180b07030c1101090b15010e030303040b0403020d170f04020301060801060602010f0b01030b1005070804030c062c1315 78
    0x40304800683d0555028030440c010811b02c00401e07400204041c0c01c54003c49443c1400e8090104480c0c00e100e101000c5800800c6114404441b40c8190b11508025200382c0741d401c0300c1c0c2143c0c1c0405071200201c4201a022501c5604140101d510031f9114401909000b01410b480003001d4968034120f0000f1520600044c0c1c0342c180180c10f1980c0090107a0040ca0710310000d100142c0e0640d0f4103c28132100030215544203490785402001680300e0702c54081900e8019050702c0e0b8a043c10b061200803c2030846080c0c001d840f803803001820051084200c2c804410b81020000d5513900c40000b461044100988140c0e4959211680846e8103c401e200302c00050003a40c0001912402c00070300b91080c2c400710311546051510f0b0080c000c03002d480741041c29401c0c9440349080c6583c1c404601e00400940242d800140480d1081c01c0007198840d00100d040018a6980d50b00c030070014041c0425200a200c0202803d4002d90550b04a81c210360309034100040c1008900c401c8040740f42c44d02442e03041a0590707a1103c520070b01c001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 399115719 1250 399114469 399114479
    0x20906040512011a06130e06130c09081605090408070302010b060d0e060109110405010f050f0327012a090306090b180f07181b03200408190f0f030801 66
    0x403105440d075040c1175a0340e40c185040d18030000909020307445860340b0020310800003603140c3c0d074176525000c4682112600300f203071000c54031000b0402c0c0e50324016034406c0d124158126a10001503082e5a0440d44002e1000059036142d07540c26415402c0031004805640d22805051f00c01c1e5200006400483c0100f0341c00103c0c901c030001300350710384a41030744652030b501e2a0500c0144110308120880e0299002801e18013030045c06414100e0f00340c41070300c54a02e60050b01006000c4004005511280c4d02d12154840060520b07481014508840704401500e40580400500001000151900320101c05440c10542800c55480d02c4901c252680e2440441d08070222904000300c072006002d4003940d1007000710003450300a80340705940740d03030701c0446c000c9080c003100c00803070404542d00303a400c11403c541c200714082101c50340e100805005041e007002e610024a5081920f01441014076060310110b442800092240c2c208c0b4005410160241d00004d45181c1c0b1151911400310341da5400d81e9500718400e5494024540c900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 399116969 1250 399115719 399115751
    0x6030c051c0f0f090b06010c14030d0209010305010b0c070e1b040e01030219061d04021c0605030c0d0c0e040501090c0806191a210a0309050310020304020a0902090604051201 76
    0x3001e418006070f10384040040841c9081c1102944006d0030309120300403d2250502c010f290254a0003420144000941c41034801c1058000c0d046c0707580c00b80c07001d0100fa40c882c1210b2000c0d020b00840444151f12613513080210b80080b03020160011000d6610340b9a032440c00c41443c2240d849034212415801c80e0f03000410450419040001c0003c01c0088c60080c110b00b040002400840d0381129a0107003108040e80048642e11941200e001c4a05603c0403d1412801c0856074043c1c040f030710505220f80583c1d02c080003103051841480b450186d100002450071802c042c240042c40a02800981d4259601c1100d1000103500d0800c850161403400c00a000c039141030540c8440880d1260301140741c1c0350628004048840d0032b0007126103c00f10450b0447d010080040d0421641107002c8003210191003808040002c1c941c02803086001e4601c00d500750780015000d0320050f810392000740c1e0000d41001c0480e004019404540c0c1c090061154014211880c081c1d540700002c642c0300102094130a01e0350749003294400d048074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 399118219 1250 399116969 399116981
    0x62206050d03050c120f1606020d05091c0908101a0603010e151f0323070c0308010911030103030c0305040305030307080906060f06090d0c050307080102040f0608090706030c051c0f 79
    0x2038640d00c28981b01841480c01c0d0796008410007400c9030303051038502c0003c009003074040e1080c0d1410000100494034008114035aa184000034541740d0050340c008140640740f0402150301550f4611008140c80700344804184010808640503c07010020030002503425581e0030015030007400e417a08840c1140c10300345c07404218031304240b925a00c102442d5444180310910150503e0030442d81d410001080c0060116140d80d21a04650600d90180030404106040b45c100f080b0000480c00f0b036948080c1c0e6030326103100c03400f165802c4510b00004c0700c2c28001080003d00c5002071310810f51091501d50b00381590f944d1542e2445e0820ba42c82c2d004943c0312400c10046170000c01500794084000c68103040110401e034041403541c4101c1d00380e6030242070103004100c00c0c440d402c0c02040080402070f085404040e0b81b220228000e4003d40a0030384c140100c1c0800085581c0304410444c042d80010b00580141441e01ca4150000c02d400301a54050107418420501c1d500c0003107a10600301da0081d04d02003410361311403992400300e41e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 399119469 1250 399118219 399118243
    0xe10091a090a060309060902120319030b09010302060309120a02072d0320060f1810140d0b04052514043005010906050c03062206050d03050c 62
    0x6024001002540c2e0b481d4605021540542000214003a00e810018042e251300400650080394054020401e80d00c00002082d070200307a000300741020760150104a09480782c250740c030303a804400b500050025141180085400c41754000c2211005441100c0d20307000358000010001c0542c0000700f0400204000f4020a80c2d040541840c090b1000300d2100d1084800081c3d0001400c211240700464902075408010302406040050181d500c500381901c40034901e034407062802003850313403003c095140c504040202c00450344032500d83c2d078205400454550442e800c50741220540c80d40311200684152aa441614000c0c012081b0030003400c420b250f80350310045140e03140a0108040d40074801154104075054600361000d061000111103a040340310703250150101242042815401c1c203880801205600058025114420500060f84d071400500c01c2400b08036903a6400144207803030140070115040f00480c5140030000d0000d102c5840750b01040c0b01e44508082140841da00155a0052801c01c118012881d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 399120719 1250 399119469 399119519
    0x20d0c0515031e15120a02040b040504030c030302180a0e06030f030c120f0f040e16050403020d0b06010c0b010f14040501060c0803071b0b07110d050414010e1009 71
    0x2081c10b003044032504140720004804214800c0100e152192144c00c10b60507010010a1000c4540f4103800c5a61144580e5204920851270449103095a04090144030b2041e9051b44640904001c240c4040d0041e6002c061003c0c4011b0600e038040039160341e824181e80150844440c0d100040ca40407040c54a402c400d100010903543c414404003046071000038a941003a621509900e4440d021251495010700500304144a02800450081504a201c07802544200ca00ca000d45100d010080030650f9203206038000a5088180600d044010403101c8007115045441850503881411590b101d02881070001c0c1c002e003103c1450818100080203c040c4095011542150100300325490008094a980084800209509404000650003a02031180c030b04020300300600801100c1c1c85407412024607041260a100803800700350401c12850400148100a000980c413510301d07003424503000d8592000704440c0c441c1005041000245103464400403585800c986407240c90100d401c1c00c9405c042040010b4090440c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 399121969 1250 399120719 399120721
    0x41e030507021314060607020a030b010b090a0f05030601060302031e01031b0e060904030c08040803070812010801020702310e07090e120a030f020f070b0105010f0c022b020d0c051503 80
    0x103a4516039000c0c0c00105c1211299902c0c5e0f800c2c80421120862070f840900031030f14800001903040f200340c00901c100300d4101c40140b41c513521041d103103019075203d028050700340c0c1c847c2c4c1c0140a0180294005e40e00f082c40159a103510419452228035041401d801c03c40f44a9004590851141c03945a6410007a001400b1108540d140501c00b040928100800287c108002003450909000c40030044501801c1c08400b40d80e520302c011b06011405900082c010705401c400703d000064944018030030796a1280d4000c22544d880d0640e203500c0c00f030f1340c0c0301d08000311032200203011a00306c610018482d0b16420042100070707120301443e0a100c001180e1301084003240343d401c01440715020300c6940c4112480341980317040c0000c08008070040e10700280120074000c0c4120900080d45014040e21440f071030b0407243c0c266200036540841c880100c2c0da41c1074860b0000e411051001041503d007903240f180b00c003c1007a0140c0d2046070382c0550000340d140344050340c0540399480349490511140c01d100742040081e04601d8400d03855 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 399123219 1250 399121969 399121991
    0x6090f080c04020a050408060405030703021014060409150f0b0307080102071505130807030503090715021e031608040807050904030e040e120301060509030f0d09030b041e0305070213 80
    0x110398550724010b108990000d40b02d0b0040740070303034156000b426805003100e5540c50185041d65607980f0900080d000b601c58540d60000c014000d0281c00903a940d0b150110742d0548644040c00080c06002d8800c59000c040d44561003041d000030301c141c2000071803048000c90300d501004145424801550001d183e1a40100304400100e038840c01e003400e03040041c4600141c540d0b01c8801170100c08000110041510700002260000e250b844000b4501500a440c25204983d9940c000380da40120041c5d840e0025030854580400350850340c903030041c4035401d1072058a01d0a2001c00c2c62054070008104100c414000104080c00320703003410008100a408292a10106800e244d14064008480c040685201c0e54880c40840640581448114580e40c0542000b540303950716820080e1403034024001c01806441142c140442200b00041c500010601a4468402c03960440c0c0b42c1119084c4018011b0324085440704a500c500042180e60380e58840c06a610140c80312528410400c0d03403400c0240b403510490402d13000301c132 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 399124469 1250 399123219 399123223
    0x1030b061302090a15020c0a0806071206050a08070305070b031009050702012301080d091208030619030309060305062e030b0904050d02120414011b1b06090f08 70
    0x242080c400c81e00320811401d280c07a490068441d4400d00c0f50081540304000904104a080301c011034000c5401303403413404141505000201d11184140202a4002e80208644900481c00b0203121103100c800400c40705d0302d40002c06c1745080c3c50760044119034050002002440018040f14001d096440d1801d451420185040d0300000142e010300c007411541d45001ca40500d0007544804a14035189891805803080c2001440620009120304207144c094498201c40551040516000b907503080b0340f0080c000080c50300c0d040d905030401070407190060701e80030710340701d0800c10800c0c00c0300154466610002542e0800c0f200074283c4602030440341c007a8074034501c040c08440c41c56840a2030203c402c040c0c1010340c804c50304128060710442c1c0f990740e04001000c0034041805400308403902e011403076030200c41d0403420480000d8021302c918455000703904240026012b4561144500004030401103401004019868503010f0101440c90300f01c90000d03a502004212180e00280d25500034526007440c01d14076480c01614075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 399125719 1250 399124469 399124471
    0x40c17070509010c050615030c0409031e03140a020a1803080a0309170403050318090403020303280e011506030605030c0409170f070308092b020703050118110901030b 73
    0x402400030100b0200d00a134420300c2d00503203003a0030800302c8013141071030340802c003004080c0c244d298043c0c0100c6030018054202401600320540d403690316100e861440803030b08240e01c0032600d03000c0101500c03802e00541703015010510a00a00848400603515040020f016040b41c81e8030100c4190150000000c101140c140b8040d5100c0c2d210301e04001c190307150310b0310f0181003055461101203240c54000c5008402d21000002034040407049074140f10400700c0100c20000082421640200103a10401c0001c0d100c01c07840d001011001041f09000b540101004103600984240010000031030b9900c0d0000700064440b03250103c000d02e800e040400442c1e040c000460380300c0b04502c4d00540200d80b25020b40042140d0401003034625103000c0a400d80700c0302e1002007518140c2c0b05060660000d4502000700d00d0500d4007140141d144a041522402500ca948403034680b440c400b145064254015140700002159003030061703128609810386628006d4401e03203401c6604000503045207016a0740c4500600c002902460b10b2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 399126969 1250 399125719 399125731
    0x607081005013c09050111011a150409050a05040b070c02060a0e031212060901090608030d0b01020102130f05010f02062406070f030810141503070504030c0311040c17 73
    0x2c9032400e11072034251103402c2840f40b94584200c410701070038803040c1e03403200c3d200c000d84d002603071640b9070120b507001d000307003070f109940c8845044e01a48400280f140c0b5200800c1d90040500d0b42075182895500d058642c125681222503861543d141e904001c10015042d07070007075001005080264006605030003081860107464840e00a01542c000510011b41d001c002c00340d0f490b9845900c4030b031395021890742080c40c1ca400f0b41c2e1803030095000d1000031403280c0f02030040b0000c3d141060300860a0000c61a040c0c3d0203011042c0c801415558204110300d8180310000045018220241c01c0400780c9180c034000410100c4400c000c603046400c00d1017440302d40300010750300d105074a030369a00b050b19580200c800550300348903d9200a101700c0c805081d0038201500036006030700c503039049901483d501e0756031426001055074181c84990722240c0c2d080300d01e04858000000c2c40d040030451600600b0580c4079582e10071040050341042d0740702d40b1110000c0d1498039141c040c00d90742074050300e04440d074164140c0d12413030104006065 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 399128219 1250 399126969 399127007
    0x301090f090b271905070b16030e010e040509010e060601020321180d0809060c16061e02040e011404020412030f02120f0918130b13080408060708100501 67
    0x181d140d4940411411805901d0070805480940e0043c130035840e00103038102c000302c881d0b0040c0d41d00044c8110080e4143c0f00d0400050000701c1c001086540c0840b0400c2d1403003c081e0600085080f400001d807254401c09101e106100c000203810008480010324100c00101014115403081009900ca007500d04202c50b251901021207840649409088416078260425078601611900010144142d0302c45101802800d0780c00646005484114846400d44588500461001c404040300c0001404940c00141192080c00c01e2130000c0000c04501c000380da219034040b5512800700d40041c0b000c0a007440b5070015914089904626140c5000205c204801080c10050306100d00ba01d4100d002d00e00a204045a0706108245036503519085004c21105030022080316014002c04640b0b80400b5489001d0207000d180c0412200140796142c2c0c0d01c4200b2444028007001002c9001c81c0d9041c00148101e01800c0604050741c054130940c6054203004005800c0203100c1480301c5000d0308104007e9801a4958440d0b1040440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 399129469 1250 399128219 399128251
    0xc0c09010b0724020c07150503060105070308060307050a120203061003020d0210050c0a03080106120519021e070507051c0f0b0406020c12221a090312040603020301090f090b 76
    0x4100340702d8503e5060301ca032a0714000184644e01210100d03004085e140708040f0410680c545c0c0c13904076581d00040b21414040b0f032080180310007281c002d031920b9901200040c12111115124804292810711a50040e84c200c441900fa02c1d045240900c68a6400b0400c1d903441065180f664000a0920030540e0b0080d0052008030441903030030340f252040f210403503d0b41c8200c61119406107030081c19034074244500c070009045641100c07992202400780b103000f41350b4481842038191109103180004c0d0301590410400c1e014030002089400e030384001030300050b03000d14007900c04c081c982030900860110b0380c0880d1000c0701000c001d010004a000c640c541100e07800c0f15010031141e0f04c0c1d1a00700003c0c4130742d50040d8014400c0c1d8006a401620200c000d0002c3c1020188000321410103119100340464a802041220b0140d40c030740401d48000c82c0054500c3d040300400312002d0714090001013106500c680c00110000780c001005112070141030041c488112050403081202400d82c1c1c44003003d0030b902401d48406c480002d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 399130719 1250 399129469 399129503
    0x30304020307030624120c050316090c180803130b0717090a050315010824040206090402040f0909050115120b10080102040e240907080a061206020c0c09010b07 70
    0x11103541001c0000c52030440d02c41b0784401200a9403002102d180300c9066010440c1e00b40852071817284124100205841414070021301c0c00307001212164020001c515000d601235000b044aa4801480100095541c0c0c00c46174052103610710058100d00b400b4142000020002070012108140100d000070303030551207600e501d0004400440a91000c3d505110f0131203d180060300740042076048400010807a00e8203031032800301d030440e500c0784510002c40b8100000001d026080080040c07401c520700800052134580c0382c4402e07082503040d5070000c0103002d584410102c00c100c400d1080a070689100d0f44800803d91420207582081548140c00500320300285000c40c0300f02104103050300c003500d0202c00039519240c41e0414407030cc054007180c00c0364801c0c140030070305d0107545041520041400f5015000780a203a44900d0700b41c5945c04054565004c00d80d44000000d51940600f15515005114001c0540c0e914000c46200e890480f180ca00c03a032140858000402145096604035541c007640000081640c07140d413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 399131969 1250 399130719 399130751
    0x309031b0d0c090c02060a0e15040807021807080606180f0a0e0a29030d050313020907260c090d08070b15150405061b2416020303040203070306 63
    0x7051004004100e00140890030b11216000070b025505180d0840701c00759203540c41c0000307036410f03103017012103541081035140c0d41461070407581548240110002850071030554081100e6280444551400f40c1c030205c00e0155090b40521020303005036044940600348001d6450b000c88140c1c010310410311400d420503090486d038517032150b14002000c6a4100011a1a0040c0c0c42c0e005082d61001c03814000110030f40144018000300c4000d5061800a1b0040c940c0362418030095030300e9880904070661300d2900c08034400041e6604044648291295580d0700148082241d240010403101c408a4940804950030041c9a000c0342041e40d0310480221081c80c08101141041a480e00c21072001900c100d2129003003286e40900f000e0010b00b0b0441c262200765070583e1204109800d4042d0340607056112500700076149690704018441400d90700100c0c141c500040001c400c15482c41c0c0d49000780c010304070100c02080449518a0349620158503030380003440c510300c1d250707000a45801c0c06010040042d40c1c1c7c0ca008440d10829 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 399133219 1250 399131969 399131989
    0x20d050106080705040c050f0909131b09180f0b180f01090219080303010b0304080c0d02010507030c03060b1b0111032809030c020d11180f07020309031b 67
    0x16008204507501c8144040d151109030180600441c2001e40e1074414034800e008a8900c20203450105041201803000c00c240c0401c0034140e1800e1707010140c1c40101080c000080307074022401c3e4207540c9030502c0c50052290180c82001940051200f401d03020b50010891000350080c000f584058a161940e456004903500c0f808071004008d4a4811000c0c04800900150b0120001c9030088034807250642522a21800f0a2130a004102d515003080c401080a00101d4000d507410602c034241150030200300211092401221403401d00050b034541080c0035044e42c061182186e88811490207202d1981001700791001ca128444200344161460054807841c100c0a5001c1849014020101540c0313060000914042010985480c841405045032124507880184103101800c0c4c3c0c1901c1e01b495283d415020098400d00b2154243c54002904410404541d1600c00c41d0700e4807204454408464113007100605d02850700184003800f558010041c00d07087c1d41d0700046801881c1e01c02070381410710f201d0001c0070403c041c03c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 399134469 1250 399133219 399133223
    0x91b080c13060314060607260f031f09050c090d14010c020a05060c18010c0c0f0f1404060b1c1b08090105070c0221011e06080706020604030e0904020d 66
    0x2000c01070100c1c1e0103505030054840840c03862000400c907191389080203004c2c840e5150040841d0003d103080742e29a01e62020300b5246048034041903040044490980307800f5842150049208841c0742280c07000f84103d03a002c00b02401d4441d000700010326116105401030301c24821030901c030f003200d0043c0104215640c840401a185594000e108080c1d100380301a50361144010200d8460150030001000d1070100001c0c0c4020f2040241c0b00c0014003810300064460f92640442520540207030080828102408405400246020000c00d101c0614106400e130b1022031035a01c081c407541c1403060800903880042c0545103599074000c8196100c212009204005001c2d287ea088819109490400c0440c1d8002d88100c3c49215080028407180d99a604222194074494030002d42c421906100d641e980001c1c50403038445071090074000101003404200c0040c6901150840110b22500c0381801d1060303040178084800141402e000503c07070b5080175640038141075a40610180201c414400107025540c1d50300b10940156 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 399135719 1250 399134469 399134497
    0xd020a031218060906050f09030702090705070501020c0f06013204050612120702040f05040c03060510090603080705070f0e01030f030c021807091409040b060a05030d0513091b080c 79
    0x160305e15000700580b500720f407031003040e000390340006914070320103c00c541c030b4594000c100c441c06668280f42512103800007030341034410f0b6500340b0209101c83c00c10414181140354443c001c00c3d0940c50075071140ca40d83c0070b041c03403600900c02003241712118222410761440d48001c00c49010450380d40e0300b0007054401c2010081c401075480b40c4d8401602c06907044000746611802518103210307080102c0030203010b440c01920001c00c07415550b002080414801c0d0701050300300c10f00075803d919056440d4000b0050f9000ca42040d40c1d000800503034201040380400c40680200030184001c2045c51801c00540394466051001404200d039440522040611541c000c2c440141e00800311014105191100d888942086030f49001007039809501160b541c00070380094994150042ca451025995a0760343e80e001c0c0ca01500a17031b04403000003000f0a503550203001801e41464256101030b240d601e032660007040c2c0409a403000c070031039241a20404101040340480b44050700e09081c035412940721110540264451100021405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 399136969 1250 399135719 399135731
    0x7080304030c15050408070215090a060216060e09160c06050f1f0b0f0c070e1e1f0e1e2409060f0907020304030210110d020a03121806 59
    0x250300001c000e24401d000d10101c43c102070140181d641103840c291000303080c0c81801e101800052404260075941c1289100b00a82000144004143c1514080c5c0000b03008d44c10400700c502c1c0f9100d4120070781c0c008107118070b00051500410004242c4800d00034160020003140c5a07044108940500d40718440f90358801d07010841460f020000110402c0700b5580040c1032401c031b0507903414003a000c0b02c1600c150f89a06483c985042c03850780c0c40c10415401603071046081d00800a0000c0d080b14031046841c461901c1441003070462100d540c01c0c18160200410744030320b40040f4010400441200200401a100c8107004004280c84440c040c6920004e11007006007188519400c00c210780e402041081514040d2901a2140300202402c0040c0d80f6000c462490b00f020301856810814a0303c2d0300059008034403070040d00d1034945c503500030a045001ca43c2c40d100204410041103503080b00104450860903910344090850480309550040100d8044100080b026882d400c2d0401c024080b5211601c03547e6200f6020080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 399138219 1250 399136969 399136973
    0x6030a020a0b13080d030c030c08060f06130b03010603020a08011e03020d0515042d1509030903050a050109020901050d030f03050601050c0a060b1008040c030204330f05040e03040e060607080304 85
    0x2407c451300384240003a0a00260008041c09813003003d004920052641d80404a4030082c00b805401c102d01481c0308000142001035403140e0768000350301801040ea4003580c1d5604001d005464140b040e07002d11042400d4480f8921096209404001603e5040703e1402c1d1a036a0703400c01c0c900d4401c443d086001c206038160244001c0201c1034900d4104207840300701d508000c000450400d0007280c000d0001800c0c0103503081c1d0740300c200340480e40944415807103030419074851510381d2911440c02d120b40000700c406a5541643c2001d510700300980b9401810100c6000300340410030303500109a500000c0c008428503481d0303c00708825038080d2051303c1d0020391107001ca9003d14501c0c20a0400381072281d40517070168200301c2e080e200c807902c41c14a40344280e401075034400ca002d1955007404001c203404002c0c006030100c0b0030361006914607003007207018a00b4040f200c0d003500c06050004841d840c0966902941c806c1d480d083c4210009580401a02c04a0b056030b551124a5a50440414243c0c40b45e444000c02c844000020482 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 399139469 1250 399138219 399138221
    0x309080d080a0c02030a02061501030e100501050906060708090d0201201005070309021809010f14090d050309070501140403050604080c0d02010221040f080414040506030a020a0b13080d03 82
    0x40302c2c0506000c1071095111814050362030f84a6a40c1c0c0f0f400581164001032803041040400410421040c500081c0130100c9220302c80c00c018030704110005158552004004900c2e00b807148a070003030012215640f61181c0ea0751018a24440ca5040c1805170403811205401e6a00030500e0026050607241c05034492102c00c100c082e120700ca9070300200700c0306203010003040c03449109200d48040240c0c050710340c0f000320368507280d450302010004001400940d00c8004070803048a4502694030782e4138030302503400e4580c20624103160130084035140c4101044410300c00c21243e0100040c0c981e089507001e080ca01b031440c40480000c0e41c81d00c21500081c146206800c14031040007208402000c810f400e80c030540e07010400c0c0fa1000c038284e20032140000841c120b9031340d850000c000391050340c0c0c0d00309100b101d046203040c10396901c1c034175180c1041d8020491002800030103115030815010710340d80483e0480c00781151038a96800198001310324081d904101001050300b400c1440307a401e13220054450403049071042d60143c64010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 399140719 1250 399139469 399139471
    0xb04030212010914340e1009020a0504080c01020607080a09030219050f0706091a0d020c16090f0509280b0405330a0b1816091a0301120309080d08 64
    0x30418402848404424100c0c0c0035902c41c1811400e6014100c1501d00701c002c406c6003901604c660089400d0f41400a004180c07840180206030050325403c1c3c03228a030405607400c2503181d0b00315038190b40040742008841503004489962008110078005003400382814100d141041c0000c0d21074407065400810401e2003000510240d803128401c017180c0105031036000031104c4400da4402c0440c504010b100d855030020204000c1c04180218680050a05041317000d118a001c805002084121913031507000e000c05070a6008814528036100030620090820150311070307454103010b519444412402c207104400e40c03d1150a454180c0e045017003040f01c0d003810b00b0040c0e00c440003001e103110100301d0710702e06000d910f0220700c5480b80d0025200c4004455910b860803200940001007441c1d500c02404030302c8081d00d1503560022030050840780c00e011420b80729100041c00030708180e005040802c04a03455005040008011641952541c901c6550211710a01d011b8401c01d58540100c68140100c6507483e070282c1d1303c020a6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 399141969 1250 399140719 399140743
    0x60a020a1119020307080f060f0a1416090527040507180209100806010c200301150f0506070f15020403120509030111160308041b150e01090b04030212010914 69
    0xd100328546e1840c9150703440d001540c1150340d40d0001400a1541c03a44000c500764008601c100c0842c00980032000c4a500c05002c803840724052281034041c8030550740c0620040064002590403c1c4000ca00706800b081810703401400004100441002900300302041c000700c401071840f14081340c008908d000502000e5044000c1c1c55000d40040c02a01d408544507140c014081c040c1030311860b05a07516501d0741e4000e0134000b40e058182c062022510303101d50300c1c24410104051708101405103168202410b07291010855441940f1a460500464000c28215130306030f018685d01000d094021030100c14448007900490b030000d40058018407112001c81d400c50001c2c61031650031002005071800000010305940580380c54505000b0034030141000203805011100c0c0c20500070369900444076030b8290452030480386030300540501c00d00030303001d1420550800a400c422202c24201024440e041800005003809a444068450300b601980c603204da2000794408401982c21010011641000001c09079644912000c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 399143219 1250 399141969 399141973
    0x1050c1801090605092e05070c0503030703050f1303291e15150a23030403051e1603081803040b03060f0a210308010803030603060a020a11190203 64
    0x9808400e610496511080d68066140c03142020500d20900903c1c004c03c8105150382200c0220400c0f2a140e4081c10160806c00da949842c2e668403203180211380400b941e4801030182d4010300c410341c0000d400c40305590100d1405800325444103050780340701002c808141d10140001020001d04507500c070034040c1050110400300d0042c0465200c4144044a0b0045040000321400b04140071030b800c125180f1800c21110f10007000c02c90046035240a00c0b4080d4044001c010200e6110b5645100320740181e01c0207c1d080102e07420481c214549901c0292851007404454055003009200118080326640c060310400505281c03010007001d03562a01510646081d41c589880c14403411500a4400b40081103400340c92105440b103085032a000184404054002c4000354061034401340458003454144000c10700c100240c200202e845518100a801c0e1041a0032030b08158204004000c66618000b52143d0030101e4103c00503500e12505030203d411006a0400034040e011340701e0a000c1440742c3c41103000b85a8001c4003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 399144469 1250 399143219 399143257
    0x1706041109060d03080603030f030a0606030e162c0f10090605030705060a030216060b0906090402030a11010210020c010203010f06110601060c0507240906020706092601050c 76
    0x80000e250390860b00940e000d005496080c000074407484400b074000f900030781100d05103d214514032a4903081250201c404039590101003014076854060081007801940241811a46c10000c2500703c01e61030040400703145d400c1c0d80f0000b04a5040c44544440f20340c0079000c410a0030b08042c2c1403406030301a18000005085c40f400895a40310500c103c00817075400600500700c00b032802e414802e064202c0d9403d2420b0503824419107800b01808a01c0400707040c483c0c0c400280905a120030070a140b500504414001c45a2008000050700c0000d41030000c140c05c0100340040404160040f890b041094200d03081e0326001040552034a041500518141d51248a16090346c0b03459110442d0f88540d132402d01c00c8240c0c0240010400d650168802001c4940030b4020340f1540c50300c032040c0c0c1406096840b4100b18114000e00903200e015805000d1401410ba10710181c4030091901e00c1c01002e021385d902841ea040717203107a0058070801072540000c11040b000140280001e2414554150594024041080920130000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 399145719 1250 399144469 399144503
    0x20102100908090118230d120f17060d0204050a0b041d07080307030905090901060506040605070605060d11101107031101110d0906140c1f0b0103060308030c03070207170604 76
    0x206044203652201b041d984502e080f00100514000e40341019607007210000700d107040812000900c00e0003400c1d2645420021420350200105008405004010350070022000e00c115a640c9100c034030748040c0c04440c040b403182c582d4088440140032b09604a40e22502d003ea110499000300e0404100e5003019800380c405450ba10010a61079201c1c041000300004c01204051180340342125031582c0024840b400021499261008078410f035000e5004600401c2c0301164a504000300c40c050268480403d0740d54585040071580e030b20700521800c4128501c102103c5440792130a030b10580d2400c0a103a111000c0b100d0307403940c900b0040754000e02c41c004e9600140c800250f002d24000002100c00342c01030f09540d1515214500314045035010111080c40040c1c800070480ca984043d8104800d0300740707081c1000248840104d82219008403070400300740505040c248042000441c0703680040d02e500c03610755140d00755203070303034182080342818504d030022000c01c0001c448440404a000580d9442503200d000344142d504034030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 399146969 1250 399145719 399145757
    0x17091b0d021311070503070602030114010c050c04020d0902031209040b01051e090105070b0a27020f190f090522110d0c080a051f090b0a090201021009080901 69
    0x3080082d400598001c9840352116031036020001c055550078000e810100159500c2d03055500c141c0041e9803168002c801480b5181500081c020000f1007401e100500d008655103070764130749e0351034843c0901c03455000c120203d5481c40c40d081110701da9402002e46260f61000c00e890f0f07011741c10002e00b0b503000c0d900e40354600d1041d5004000300c0e00311600034050445220021001d02d100c43e4007200c4150704008060129000007040540742c280180740c60123001c203c2c44289502c401802c0c2c4442c90303988480b1558081030015840361304420260000550340241d03101e1251582e13201c0341086034054404600030120024101c0c6107580b005000b140081003001d00265101c840081c005c0f808840a002d0f003581e0f0a04040518058242c00c0405114000c0151403542e107140d000d0074030400584c10f5070300360080702d08041c1d500c1d04212080b10304600c041d0308220070b900d02d40301c100c40e140009100000b0656200540825a03000b040b1007500d2446120003030080014a1926140ea03800186c0c4481c080340619480c0c0c030340c01c1c8030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 399148219 1250 399146969 399146989
    0x10e0606042115060303020c0315070f11030f030405150a1509020d090501060b04030506091504020d0c0905130516212a0e07030608070b0a17091b 64
    0x50780c880c042d404449103040d06880c98400d03800701c40c140c0400101510494180c01824000c40c003e401500c0c0402c05030f014541002c402d80d00c0d801c0c0d445440b004001d0072603004804400e60110714900318440000e41c500c058a58402c0044010000034044108403c21100052007411001d146040c4d140b04d880d0101000b056818100b040100c048010500303001e0001c003940a494040150440410b0844454680a003100c400c0d40040110a00004040c018080308002480d0800c00c0d01000b00210000c00a0f060782910018100a00c280c0b4001c1c4108103001c40c0740340540262400b00700030440d9003041c50120a0805075003204440e00d002d04a851450403100341640e100700c61141000450107a00d80458415070034000c0011501c0d0303020304400c01c1d003120b80e800c400742d44160340040440c5481d0508205411515008110600b05410004140080d28005c41c0c0c0000301c0300c0c4124156140c41c2d5400d402d56490f400310f03c041800e40c101504000b0f00d0100003640c11800c510400111000d4a5075800f44400002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 399149469 1250 399148219 399148229
    0x10204050904020603130b0709050f091012080c03130302151305011101090b04060203150306040f02040203071e090303090f030230060c120f16030c0201060f0e010e060604 75
    0x240c4400260144c1050b0004613480340640342c03011820603155940342d400c00000e131100000540302000c1030055051100e403a04030a070701164035030f91515080020100c4607402c0c0c01180841e018105020303042000301412303512001c001909032134a03000c0c062454003040035103100503803086280200c04514104601c084034803440b12050411481428000155003149011885031519943c0b10550700100f480c941d2800d000741e10901000d81e90b401c0005228003200ca071011940c4c404d420031010b12000402700c4a03030400c1c0790b034151030140e22030391000810740b803912a15110b40d50240340f4903d04080c07a648009544162840303520b03800541c94544510700744120b824007000707400100094400141280300d4002e2840907a6100000803030001458510781800002d40e03018800c1000030034044840d15000b5001540300c640c0d0b01060141d0302c0d0600006443c044403901c18010306682d0414214194405c0d001034000d04681c05942d021150368070101c0e82d45210901c0f502c0c014106c0c03207001c5521403520318104c4086038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 399150719 1250 399149469 399149479
    0x109021f14042102120a0602030609060f0109030b10051005030601020106080304081906270c05090606390d2d1b0c090203190b0102060a0c0908060906160201020405 72
    0x20308a000300035000c40c0d483e44142d9100504007480302c8954810000305228034810700015860303062201c14018030140203807506100301c1000109940701e0368001c03001030481e034101c040b00030240c0b51844051800250b0750000350700840081ca42004607a04203000794041d160a9000300840341d030b68160b558890040d40122a25030b0000c0d58072900c002800010040c50078050900001d108001e902c0302c017100d800500c40e411400303000703100030020720404040b81002403600b03a555000d1442e00c0c60000d44c4900c6104240c44131031884102c3c101188406c0c003100030042c4a0800440402600188003a5030784502d2500040001c00690740c5070140c94245801690100152841c040300510802d0140c40102d19100b05100f540d403104840000304100f405680d00801c00c80d080180d507400e10307075000300e00f8880200700d0034001418440c9100441c3d0f8006402c2d54010072040001500c0e910000b0201d800005582c4a600a0f104000a1000501010030400c0c018050700d143c6500c842000c42c4203a003070b401280700daa40c2c05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 399151969 1250 399150719 399150749
    0x1140307050a1a0d06080601170609060a05090a02150309012901030222030c0302100203310e040b010e0106080c03070503070c06020a020703110d050a140109021f1404 73
    0x200d440301c400911564034000f0505007011140180300b140c02d19030015545500400c010080d00080c200c510100000001c00b800713051600042e0707141d03204c0001e4005148581d0310000100759820500c40e056540340d00500d58490071261902e100010b07002a901881c495280c030304111803080140c3c015464001c001842c034500345d00707500b0041d80250001d9940d6500c10566000b0703040c0307107a1800a0340028510841c40c19021900314014060303940c0d403010300f0009641c010002442c13900307070803220080f43c4203505900203058507090b0008c103035a64035a0310002d440f155007018001004510407680381070302c01d0011403500c0c60382d88802c1111030180690b00481203034000c10210340c40d20311072401590700068a09055046c0443c0c0da0703074007013242c3c0940008801038204040074002c00030664040c000d00070301103a0148500010b030301c82540b0b40512003c010003440c0285107200243c1c1c000e4002c40006a00200320420171105084040c84081e0483c680c0400100c03d981d40003134074988203080d10240d5210100070400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 399153219 1250 399151969 399151979
    0xf0c07030c0f060902150d060e090a020f121009060f02030106080c07030201110301091b020313050103020c150117060106020604080a0c0309090606020c090618220503040303030501140307050a 84
    0x103403402c40410b88203d1386036020b100158882540c1480d600100c29481595032103204004811103442d600410141041603052140950000039200c1850707804803012406001c04c2800103581a550101e0040180140619031200d1007c0e40e00400c1428004e82051000c9012408604202d10090050301e0100d042640410540802d070b00140940758868000010860a00d903088401d0350426400071f401035132108048660310483c842d41e45558092800110700b00f03c484110320900740c4a5005032070401d41d010560000450b03042107440001c0716041907150140d43c54001c080c00c86440e000d6030380002e101e200c0001411902c0044e84901c00d50700401300b281000c90010049503004c58030750082d81002002d4074042080721080c41081c00422143e0010640f4101c0c0405010400500800040c410118522060704040031a543c035a8004a01400d0000e5242c14803400280d5402400020b00588404180442016095400203040e12455030008110b00044000c2584d29402401119009800d107801005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 399154469 1250 399153219 399153233
    0x703052e0c0207360c020f010603080a050c010b1e1f050d0908070b090c010f02120406030c0c080f13090b1008070e04050f04120215070f0903021002060f0c07030c 71
    0x5600100c002442d81d03104500c82c400d032a690000d0143c421342554031841680c3c0190104800c04606900c81c0003440310a02d15101c140039401040201018007100091816690500794400003c0c4a4020030b803014104200d02207121807400101603500407039900c0c0005070314083d20780d210b220086980da60f40d80351805084810014020743d54044451020a00214000403698070b502ca200b902e0500042c220307a9040c600046c03006d070114a07004155042030703c510340600c44107001c43e0141d40090070089211441201c0444a1410908000c0c2c000d0401054807014085c055000740440d501c4100d448000c81e0300c0300c805008450b4000d40596104154100280b900c50241600d2036021041e070810000e000c01c3d5102250554401302c40f01c0c2400c0030540100010400412529680341c1c1396071004008071020160b05584102c0e0103800403040c0075864001c001c21502c12150f4030301441d4082c00841004000d207070702941c1c981058641003200e02034400090000d003d41c0040c1c03a0b81c1605030359441c0302a411616908 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 399155719 1250 399154469 399154499
    0x212070e150105070b1e101805060307031a070e10020322180f051f030f08071211010506030f070302060f04150906081311120703052e0c0207 62
    0x741c1803220a20a060200700401c901510429640940c0b02e41d2a45800c0c2d0300d42c010340010410544107132500390070302c08036804201c4c406405c40c2d4540c0c0092561900c0c80000c1ca0b2059a0b03200401c03203021510400390990b01d0150082c01b480ca90345603036030030488c41410411440d980c0c54412005034400d00841c84001d000030006084030700300041c41d801860f1a03240720006105401c90f100950303601c601c2c80c18040e00142c410143e200c00380d03640c020390021100c1c5404010103220312000e8141e040814486061100900880b1200e5034401d038032031014100400c0c003038642e1207000304610140d4a841c000500b507081c00b01d000240007000d0b0016203800c0341154200409a0051060003c00e80420b0101182900d04504010107842035901c44900e068546140144078176401451000509218849100090400d00101608120072242007401900e100c1c001440c6c0229035102404a210b250808024203120030b0004800c0d030b8401d4101c0d07154000083c2c0e04010f903109005c4010061b40242d60400802491640c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 399156969 1250 399155719 399155761
    0x506090f04060914030c25120b090304180c030c080603060c13150c050d09230d1a090706031104060503090a05100b0f0d020f010f02071706040212070e 66
    0x3c000040d4902c25074a176412003182c0101a901a104040b00701098109007254030000820003501641441c5c008400e00601c517400410b012180f501181c1410740c00e00948014000030341401c9581090002c1503400303030030401c10002c0400c3c40c0618450349684140c01c824400c0308042c0080415440c0c0c3c01c040e070002d071320921902d0b81c12a140c000c0456408584104690300c0001561000f1458601e030403c0b5060041121220091083c02d4504220802450555036505a60f00418074034a11108000c00d945c4810060b008140c1e04407180c81115196104c24054042e040b40411038112030340f510000e5007210941451500c0300142440100040b6205c0c81c003e59115182009541c8031b501c182e540c0c585450410300301940d03501d4991810180e03601f40350f01c1c140c191250032140d0f008003a00a4011582c6403101c0e0f1069070410040102d52561070b4020000c09c0c0090034105880014810b00b00c1c20651641d40607141207200307414000d00350f0a04503000a40c03d00b59482d00c40b0443d4180c551358415200850b45c403281d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 399158219 1250 399156969 399156983
    0x209071805030601090207050106050603041205030705040306021b0d030b0105071b0509090303060316230103060503070e041101260421051803071427011203030506090f040609 77
    0x200300d03502d05101c81030082034901c0b40541c03114000d103040c50a4031001d8000f68002d010520401001c1030b0061011200c2d8103031801c200e135494440e02800c540a01c95a040036156600000d00b1240c03050b06003440600d00141d50058071084503240c01e040381590080720106001030000e000740000b2580c0c0048141c40c0088070362207080b08580d0398021413003200040b07448460f035070400300c00c02c031007800d0900030a842c118011b17220b00c5e81c0a04040200c8101d111004181d400c1100c40e02420040d64040d0784800040c0a0040440c0c2c515135943c081400008411101101c45a01045400140b94064001003203281d48a41c07002070700c1c1e20104440904420000e105454504060440d43c42140e0801050113911196a9a00359a910038806514800003003944070740c043d510944041204514552011029040841e890030f4010b03903031012020485044001401d400075510000074144648024403000c0c280309440034007035940c80000f08403e4003002c0342d45603400070002001a00148141c2e01440c00248240300c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 399159469 1250 399158219 399158267
    0x60e040209040204080a030f021507090b030a0b03030c031806030f0c031f060806031c05031315150e1501020703031101180c05010909110a0f090e040c0e0f04020907 72
    0x7410f4070305401e03c0d074191f010548c040002c3c440c1740d0341030204148528180d018200c65042c0304000904525441c46415440d402c007001045480a95402500b07401e07100074200c90322400150811a01ca6101003440c40c10440d2145484000341895001d1320320034994a60501c00a0703440c4c0f040800550710080ad84010601190742c02d010b1440b510303d02001920300780c0d488003070074601001030500d016412f11070700409001032120341c164030754814200c0303500400780000c02a002580e4030b40650303603104092142c448a801d00244415000c0340c0e00d12503040391003140308503011b51102c07a01e9042420078442ca050042c1c0040000f07102081c01021500d5000071100c00004080b508901407004043c81800105d8046a19400030003c0b0740e801070300c03200540a0b1550401003003d030703084904d015114050072203017031000402e800c0754804d00541c541c3c002458039409070000c0c1d16080c90b05509040c0700380900c0d503410000901041040043c4c0600b00e10890b409050b0130002d8450740b006942120151480c0b0480c950511 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 399160719 1250 399159469 399159479
    0x207061b020315100315091a06030a1e0b01080d02010c14030a05070504030615050405100f03150e03030705090a06080720010b0d11040e0c031207050309040c050a08010b04060e040209040204 83
    0x240440c0490300c6032240005400d4101c1c81c0040c0c03c2c0121031004c0100000210a2000030754001c16098903003588880840331503800880c900b02030f11003484018007403410180c00080c020340d02140083c8a815980e000700504c04420700c1c03e445242001c200c1c12a0060280002100305420340d10803900152a03003800da04140c1c0c2c940d20101a0380c604c0601200e100070340b032030400c101d092600443d5006410216030300601400e16965050702007140c40080c042402540d1070701500303201d82d440501404210b509a96072840c08001c080e080c1c0e840803c0407030244252000c0052001d00c030300c100d9400f0303c6241d980d5081000e8007650034a4086040e5200340300b15543c0340001c0401b40d864800180201d8820840034119514210801045900080c103d40080d001040340e07080f00c0d41d01043c1c02e071901d607400e0441a00c0d0415401c003203196015450549400c141f800130400405a0071030040d018044060b510703100301c0d80e02d91034121024015486003001040d0518086101403030f0640142407001c0f000703400103050a90354 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 399161969 1250 399160719 399160733
    0x411130303030c031d010c09090b0d02060313020604030506040c0b1903150e090c040e0111030106050c1501260d0212220b0910030533030d0207061b0203151003 70
    0x18075a042031507076403440007c1d105500807501d03030000c0007030f8041000006440e1002c914400020350009106680000024800e64205102000c2187d0040d15041c0c9968403494030940e2110151420760700ca0800c02c100241c480e8041c41261825040d01301d01c0462603d0b9402c01340e0180000b440c2100c11010551008592a420601500d200e5440c1c1d400901c3c241c00722805103c2120384d403601a540c26414181d940a0000c01c00e07080303d044409920307000d80d9402400110f40c1c01e24001c0195640601c14141c00018980000c0f1072441c0885200d0000109803810721100d1640c0d40c046200e8403016821007407040ca07040440d90b001e84440000000c1c0440c43d4540d414249440c0c00080c0c1043d10b04240218032107429041070810706041c443e1030b04081187e41040d07030b5820551107628035002c940b0030741a2051380800684180c040c00004020301201d04120044001a4070741069000d8540000d00c03a003027400319500500082c400c0181c024020706a8501030454030307000098002c0800c8044600748400200103100e0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 399163219 1250 399161969 399162011
    0x807020f060f060103060f1d100801110901030c020d080c030c0c010f0c031b081302060405130506040b0a03170c1504080d050a0605010503060d060f0c0801050411130303030c03 77
    0x14182c2146003410024080720a15089032040318006903052140c038040456100515000c025075151981d1080801165002e417600058200c0d420701c203050400e4000f0001400c41c24a09032018441800d5114040b030b40c0d0329004086000040b500c1e008200106180c03001540c03c0512241150b20f89403404030410301b56a1025950b8507610750340e68030382d041282e041c0308180071020800003510245002040003000310f580a810f91307410500c1070840380304643e6200210340061001401c0b902da0085c0c2081e0010041c0340880f00b4500542c00c01c202003003240707072411070ba00a41e507000154944011843c0541170041c2c0128000401902c141c0754021b074009582c0030304a1240f4480d615150b07443c2c050b504204190392010b451184498203040044c84030740e810000782c0380d014105845900035101107080010240c050303100446074040c030f41002070b06200c0e40103221605880c03081d581406000703105909100c26100d68046031078200315959041c00068801e4000d0300c2c10140f03034030303012400841d40702c00100c3c03581d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 399164469 1250 399163219 399163231
    0x20f01060e18010e060f0c0403020d06020901030b06040b0f0705030426070915150905060a030e010b0307030503090120060106030603050124290316200703030807020f06 74
    0x12400811200800500d0318019000e0b1a400900c961a0218685a0740d0407000d40018940070004000442030801c1d0300035600116001080c102c55011141030210095010500c00c0d80040c0c2045211031441c10408100c40c216100400512324144140e40802c1c02a040034800b16190301082000040007440001c00130040d4030f800d0340440700202c040500da860032100340d2091003a20700340038030080107842001d83c10044a4908a0f044003040d12071904846841c50350f00626408200442d01003031003136059200321001c070081c0c0c00030800c94028404069a4411601c002842c51703001b0441145c03c1e51044020406000c0c0341e500480041000015080c14054240c01c0b000000f40d59800420a006090107409080c03025008030a01181c150340590518040c0c034040c00941d4009101c4110340d00c288114030402030b08000b044942c41c1c2c01c3c50b406004102e601c1052802c0010710070007035101e031b00a08144c856010480440140403591440c1d400383c0e02c0303100c02016031007540a0398a5001505106001c50340c4101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 399165719 1250 399164469 399164489
    0xd0209060f120106120e0d08060d0c060806030c090609040206071e0803240108040b1f0b0d0509160510030905150609010609030b011a1c0b0411030610080403020f0106 73
    0x50b0414800070301c0e0100700050350305c1c55810b01c0940408940e01080c078201103a59880c0c028a6541c4410200341c0034210020700510710001d001703001501c680d110420305d001c1c140807403e489044a4140c100241d240703082e1a841d40c0915100301140c010302c2e00200400b41548501150041018288000c4421a0a0a80543e4818000410000d1441c100740c2461101d0940b039030040c200002030400205141402800103141d00e04c11808600401c1d500c803811100c201049103030541d0b568940c151858590002072904244c0c50901e0081582500041400c10343c50003c5400f0700221440d00c0b04001c0720303051800b01a818590381d86d1030000451030600100d048059102e00010381790404006100700d03644141e0002c801c1043e41841400007a00d60012241140d200f0b40200321009049082c045052107120109400d2802c19141c00c44070011907001000d006004880030880840c080220940500c001c40b0401c1d80402c80c0e00300c42107842c0c01421000e82081c00381c41141c070401000c10107d400c541440d0805000f0b2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 399166969 1250 399165719 399165721
    0x3060d05030a0c06110f03042406030312050f060d110402120103033f2406020a030206010506130621020d33030b131b06081302060d0209060f12 63
    0x102c582401740c0c4491100e01e04c0d00b03500c2d0012220342d03210355001c06800244091040040d00d18140c00055007007410703240d52241000b41c10f94a103805003011412840c0000300c0c908200001340c5a04281650034030034100030f8901800c0c801181c0c2c0301d0305c80c07448100c00994000c1e424401c02a049903420ba005019500caa2560901c10180302d5402c0c400791480800e000688030ba2059005a0082c911540100203c00f06000302c0c00b0615001c040141c0d40007003010710b03100c40b01c4c0c1000042641e400120204d5042c000d80a071145a6241c10500c509403103800a101d81210001100b044514464119460722110f40d15a0780f9400041040510985e44803940c540101c83c2c90303060301000244041d4061b000700440d10101e2080654910111207820054880600505408000100c11310305140a03c046540e100b617407070402c0200340e044c1042c0c8401301e000d0000001c201500047d0740ac3c003019041e00c2616002402241081b0f903200f407000180d80800c2c900c94011100b800380b41c0c203d542c2000640540884441a121a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 399168219 1250 399166969 399166973
    0x90616090e0f0a0b0907140c1207080912060105030a03271410030515040e1e0d1b03080f2701020703020d080c07020f04090206070302010b010e010f1403060d05030a0c 73
    0x10340340c00895962054045c0418840d1054000d45500303d03c0362140d46950311524a020290708120302c1351103080790070030300254030010000108024185d1043c01c881c114604030015191765601c4409000e215019030000c107402012a0180c114241d0700305010544a03040301810351071540e02180d6a01000e0002041c412118491401c904640510700d030601d010002c5292600400000089003480180110381d2448510000d00c01441941420052081030211030524110160b5464401c4969500001e00e1007410050801c550703520b4423001a015982d40c00c054842603101d04175031001808030001c00e00c4189400062010410400c4010310070031000586408850030081d040076145485001040000c4041046014880c425200b23031076019524030043c0c82c0c076000450300070700080c20060741c08880070959108055054001c5000c0c0705003030b600d003035802038590015142d94241c00240e002282e0294040c02c646444a00616400b0790010481c62000750903440b00c1d805c4d81e0000d98141d0001b4664604281 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 399169469 1250 399168219 399168221
    0xb040f060c320d140301090905070509010e250503042a270c020d08070507020a090209041b0905120a022205010b2506110313030206060306090616090e0f0a 68
    0xd00b4a050802082503007424407031340c0c2c042c40140103003e000c540e225414424454100a12409400054045096541c441d66070640c404800c07608181c103444c0802001c203003d54214024404208181c46840c04c40d03c03180d0700d20034500341620303127011800082c0740700418480060600000030b080e0704010346ea1607902003024000300809102244140c034101340b010858a940002c0c100251a280c1c5003003031007925550022603040c440d61001943c4558030f408081340000051780100341c016001c4800b000641d4180a440e4035050140c12004080b8600c90010084c0d420014a0000221800b8040d203450302c00c50790000312041601e00c01d1510b040e455940030040f2494610541d409044040840c0f403c0103000b0801440c20310815030312a134401031070300d180002c00c0385d1030b00a081c0d00312030140c0107600c9207010400e24008a0a0542c02d400510038200460002e08011030403901403070100010384417a036503100e580140d00d4a02644d50341003007040e500000b2510700501c0030a010f2001101d481d100d904007616050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 399170719 1250 399169469 399169483
    0x100c0509010201050f071b050c030d0306090f0b131e11120c0702150a0216170c180103060c120c031508061005040b0a0b190305010b040f060c32 63
    0x1692489440003401b2145820280700c00d01d0700f07181c10700c04c02c01c0020b0340750260a209800102a415228a920f100321064140d0844000d0780e4100b442041004081caa6031416100480445900081c0340b071107100d054152030700100f40c0004001c0c444084051007400407001c40710070f40c0605401d61004602689065200404150489010103109080c810160009007031001c0800c1072a82e071003c0094ac8158950007400501d1406070048050f154060366404c0280c004180411a80000c3c02845c4821100c0e25040c1c2c141e03100c000044800c070440e03a08642d1000010324505000800b4049155451050151140102c0d203903c8507946e40407441c92200c00c600205030a1070b8021801c1500440c007001039240070b10b14480e00322002210040340c0c41085102040500c001a003000c68004000510122600702c840714a0000251031340c1c00b041543c1e03030340c030781d81d5054000c1d802448a00080c0c041c040280501c00e61071501c100d8060b080c4586d60000031707002c2400d5070a100b072100d0040782032480e262129542c18800310f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 399171969 1250 399170719 399170731
    0x6032406061409062b061e030507090203040f0222060506070203060a05070e04060b0301050a050312270907110105071b0201080915240103090b04080903100c050901020105 75
    0x2112400310060241c0c00d020320b403400e600403c03000c5210a20307801c0e0b882d405c2c405882c0301464100130320250f01c05400030780741c24001c2e03060307070b0111841e42c40400c141c048114003102d400030080c02d00c0b5400c001401d40658800b030005e880c000078600c01c03036001d0b0f0350340d07106902c2c60601d503d20b083c850b40d1036030300000581c2e01c103600c1350f841010284407000150b02c0200308a98000140b00000805070b4910506581c1100c0340740303111b0b0f08a0319184000c5016034030100258141c40c402c8400c44501c0e0360703400405a5849040d1121481c404045c030001c1d24140344036140c00b48485080c1d0150040c10800c50208030181011940b0100007856045461492002880f0305078004001b842c000e00400856100c0c1e001d400344409000b4100840e07007001482808060003136040710b0702c0445000c441801c110003c00a4034400d244800321001c07200c2d41762030b4558028880c0413001c90b4881c0c004803655649848400c02900590000342c1c040c0241c03c241d0030250030764811501c0314401515241d0311a0000340009084980003068 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 399173219 1250 399171969 399171977
    0x803030f040209060a150e03060609010303051c0f14040b071103040611030c1005161e05030c091302030a061202060d0908210f0f070c0201050c010603240606 69
    0x900000c0003902034440c1d8000d0701680d0f40590f0b602c804000c0340e0070940c135030f01c54042c0d0003c1e160840019948004901801d510031400c0740c803c0e4a8603802c0103612002848014041842040492040b6100740804019007448071000182503032000c0e21002500c41c040300c1c4202c420009000c000070000c8400304c881d0481481d140805405d0b85076098140d581c41a400b40c00140300c180003618426040400485904a500605a80701214103051010141805030350501c6204880e4070341401c024425192000104841034540020a0360b25401b030320b5030b078000b500441030790390104508003140e00d41d203032404141101c001e001039403450202411070480b81306402a125101440b1803000c09079131240c00340d813800d0048102c0007076085100d10700103989125109501c0c11501e01c8a0046c20359070200c1d18120312484401401000c2035889a04104280f04200c0b4180d010864000115000d0352150000d00354001201000040484d200e8460049100c0c41228000300a00320f0940701e0b0900c1e1050241e40020581820 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 399174469 1250 399173219 399173221
    0x108030316110c04020c24070c170c030307020d030501060309081c020909190f0501081b040f06080106030203070501050c0601061202090915030606031204030f15020406021501080303 80
    0x2074200c04200c00448460300704101c0700400b01e4168824420800d690100420840d556030070000420f864482258445154440c01010321001800050245216110a0303039500840c0c165030740da1080e0188481242208001c0030702c902584818200015801401d568004100410b10707a60001d00b940d105800440c1054100a503100019010300705403200008605844c0001d41c00c8002c034600207010b240d03505a4442d0783c000c14822020300a041c028a1400340000512a0705c2072613446c44d0998000707101d5046154425901505e84810010880080c8a402000811700e80c1e14151440e00303540840d044103e25035500c0d00e08200318902000b8090081a00303007060760804158030020f0b41c44000501c903580c24440c2d070500141a11080358106d5290503402815084282000c0740098180031b000e84055000c2c0c424040411128900050341004420b01c1540e00c40c5002e0969840304d40310301c4802811209810721056043d1280240c4c0040d0001c0c01d1150300401d030101c105482920000c0041e03001004c103801c108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 399175719 1250 399174469 399174481
    0xe150405011b0f05040608060f1c060c0e150703030902030102180a0f0e0f090a020402070809040f0603050303070e0105070c0b030f01060905030a140a050d0302031f05030c0d1403070309060801080303 87
    0x9445c04c4032100d04101d44103649801c0410210352400e02c9942d0f024000b10a0021032500c0002c190600074042c9600300040301c4e500d075058600d000102401c56200100d01d80044c1d1160060000b00b100368441d00c2d000c1400801a4007103400d90f044901070118030b041e0b0002e00c1203141054070608000f80b50300c0002456462412452150f04003019000ca00c96a81260020b0240f0f0000c2141f00300c900d034003810071541c4145030f0800c400260800b00c0403501c10340c00c000c0d41d00904022401190183c81c0c001300514a140c4410000303450012010840a0600a0500461340072401c00b60504004100030a902c0c0d5503071a00c3d0f6242100a54160040001c3c440340300303410311442d06c00040e103407085544160044030007840c1610003894280346140041407481210b0b8208070300c44e0f050300a580202110403501000252800600c40710030034500070603030150b001807800e860f00c0c50111100308019024031002103e00814200c2075080d07611021040e00402e00c45042040000c3d4480100d83c01003001101940c00c40c142a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 399176969 1250 399175719 399175727
    0x1f02030c0307030905030c0304030c26070b0a0903170a1404080c0121181103010c050d020d15060e010e0901060f180801020a0e030c0906130e150405011b0f 68
    0x1500c84420944c2c0c90b242001042000c0045a1900301c02804a80d2030302d94911301000b9500250040700250074080c1d020722040c000d00480060301c003858901800c13680341008807020240d0098a01401000f03c01d4100001041001c0590210b0110341c0802e580d81d610b0200d0050700c40d603484c07030301440f000c0002c10040003c08800b06041141c50303001d11385841410010301c11807042e01e00b5100d20100e242c1c81c00214001404085490403112031148051859841582081500721045030032403d0200f1801c100942c01c114165000b801c0d0f204d6001c900046686c3c01900200840055800ca0f401044540764025820768020401e883c2034901200d4403261581850001482d240a6070084828080500d001070640185c04624002074a80d10b0001c640746c2911920007130907031000e04542406801216101c8100307003800541103208000c040c101055409031804440000c102c5100c000025000b11440903410721341c960f4071140070700d00400002c20000c2d200c3d45d01b01c5815001e0b2450000740003035540100c92160b04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 399178219 1250 399176969 399176971
    0x41e020a1401050f0c010506030d0206100905041a0c0a11060c0706020901090302030f0d091401210f06170d020703230106150504030b101409060409141f02030c03 71
    0x11a8818030401c0e07008401a101401902e03440c0c0e03d408070200300c00c280550150b024620440b411000c0710700405003034100303a89810054a00e003031030300350701a010300100000c1e4000b41d0b0428400c0c99209440d003250b07880b101d5482c00aa400300c0b1501da00084a101c030542c080c00e07806480c22110b01500e10ae00300111441e01134030078800e00a217090713004034088040d81c0c012030840c402540c014003034460058031401c0300307070300c420204d0400000314100300004100c44030b003031552192808040e1100c0700c400c0001c860b82c00c40d860141a41241664a6900d06e200d00c0301280500002081707280c002070904262682c20a0910451680000440d4002c50082020a145951207100d0006001103401c4000030b0100c0c850145c180c85d0000502c2d13507103400d012440c5990040081044a002e0380400e8900c3d203803240c0686002c0154070071641f141100d07404043d440d260088410303030418001000010301804c5907607640d80d0758050031100c00c803580109001da00d441c0305001c2c1000c00100c1641c4214510310f0011184801800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 399179469 1250 399178219 399178229
    0x129030103021e120102090102010e03030928060c02240603280b0c031e0127060801150f05180a0504020f0d0606030c0605030103050a030f1412041e020a 67
    0xc2c00b928400340d1080e00b805082c03c0703c8003800500c400b020180c0364038041d5010321209801980b800104083c00b40b008000d890007002200b01500c03201e540d50418503030550040400d001c17507144403800d1900240691080002500054002c2e01e01510780e8112204521881c0c84d0a141c145606030812915980104504030000c1c0002c07000340e101e5080080f030002d81c11610100400301800381041c00440c1c030300740010f944110000300719110b134090004020404c10070288030f071800d40b94200b4040d42c10403038040400e050311a0b0303c03800059441d5440005500303490841203140e9854a01c43c8060145421107401c0d000501010759000080f10b034140000240444007e0001c108241ea801c0810110740d110b003244940000000c0c01d01013a00d005050542c010f0400d0312003215055290784000a13001e0242c4180d0f4101d903040800b9204d00303407107500c05540c5030040441d44000c00004016090074401288003600007088006034a429924044c40c202012049645504c03c3c00384c600c001c081d0069a070244402d00341c1d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 399180719 1250 399179469 399179479
    0x901052b05011506080415060b070f02130c050306100f020a0f08070b040305041401080f181f0614061e130306020d0e06060d020a140f09090303012903010302 69
    0xd6a035040490041c0840b5010820410019100140309030340140c215000d00d02a0480208516001a0840407100c0314841d07039031040000c1c881d50005c14040c3d8958031085001500c21125080e420800307200300c1d4118000c10001c98004010321031541001070380c050522890303090008905a0020340030790b44210791080281010013200001c804c00030200203462140d5841306245616042518000c4c2281e0000d021300c96807001c0000103d0040c0d0710074000170f07011384076840741004291500810f00510311594100940140b0988034102440b4a6182c04c5c0c503107103011100002041420440542260f07240034100d03071710448050006201100b00340009501a00592048581e50300744140c80801c0c5040b81d9001a105a201150345125088103400c0450964000d0b13080d204565180e030100b051050050384061341051880000f0710091030b031103030307145011400104030075640c80101d4002001544c040b9404c403155000070004001c07522030884900751024000c1c2145010020510303d801c0306010500c0302a00c25 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 399181969 1250 399180719 399180799
    0x4140103091e03051207020a1703010b03011a120903030a0b030705060a0305040c0e0903130b21070309140a020a051002060406110f0d0b0907142a060a0b090105 70
    0x103004804a9031758140010710038a0a143c0307240c0c041d40360740ca00142550000c140c01d00641009020100b100e040e241445190f1f030031642018403009500d0750316406240707600350400c851514101001c6130303c0d0bc5010100f008554038600400260151288512817030300991124905001d030355220301c1541c22403041890000769030350b100d00300031224044680c000c803410707503400d01031008004012004110580032101c0048019546000702d11040c814a07407904113000000c1064240140b0019840340c100d0f05925004c900c03c400b9449401700100320724140c1c18540d00101c001c0c4214202002014002c0c4030840c1c00080b5606e154102079102c1c2801000100f01c0c0c2c1c0c2d20242d424807803251209456620507400f19044c0c070380c00c4c0c1509010082560a48107841041050009091a84500c0710003509000c00b1084a00f00341041001450808040e49410803d808011481918800400030144916030100000c692860600c003030242620068100d180100042d0545000f04090340d02440d0918010060100311 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 399183219 1250 399181969 399181973
    0x31e1b0a0f26092707080a11030106020c0409050f0106061101050f010b070809240c06060a051513030614040303140709060f020a2307080c0904080d2004140103091e 72
    0x21035202e500b1507101d04d0350070b10900580560120344544242d8071008100000021103040e40c1050009208034401640000c5d00041a41400d03000f91100c1e520171401c075805c44803406191030940c1e909420410002e030401074450b100350000d002e09170704420781104190680d418140401030a120341c110103850303140d0010b90034025866a504001c2505110b41800224450655032001e40383d100c410300305880d100390f2000c90810b00d4040300c1c12044550090040c0640c200003018061140c001d1800150040c4580c140000030035480e000e49583c00f0b000005c0080c49117424507000c1c003100e400701e50303070022801c41c80c00300020544c12480c0c2c0f00681d01141030000307901a841800300c0c0384c400b03004c00c010003201540c0b400030300620101e008004078001120540c3c916649800a03280c0c1d600c204440c0d00e604c8844800400c0110b07080000803c02c5140040d00411450307407903403403458150310080104c42c211f60001001c000505480d641d51610803000d00c0c05000e6a02e40ba1034409444c1503400c200712004684c1703a19041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 399184469 1250 399183219 399183259
    0x5030a0c051005010b030619050f010c051f0b010801081504020d140a0602040503010e120d0c0203040914041505090705040b041d01060305060108031e1b0a0f2609 71
    0x4000304103100903c034641e1116151005500143c0e04103010341109030010a40c47c0c0c0b801e0300305080c0c5802030b0000218014020045440042c0740c0c40a44881c0200516400030156005044e850faa1080350081204525400014000700050307000820b190444582d600c0c003502d52460a40e0410340440711508919103909005100441d07810080034a8403868070740c2c000b00304190300075000300e82080380200b2030101e4084000d41c48194465031802001c40c06c2080480d0211640e0100e903480074a48100d0303040c15219200b0070120381103205040c407000c040318104020056030068600301030b81286c5003441a03050030580d043d900c095600840c1e10403078942c0e5140d08661200c0c0d009180742c0207183e401c0200303107009880d954020034250100b41c1c1c0300d000c0c0c0030010505403400000c80e0185100d03409456140e9200c0c41540303001d074200d15000c1d1513608410200808034041009200e10590056081c00c4514400f8500902044141c110491692182c084401103058441042c1d41c1d001c0c4c2c09444241030350220355172040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 399185719 1250 399184469 399184483
    0x1109180c0f07060e03070b040606080d0e040c09031202031909030f060b03010b0d29061c0804030204020403060f050105040b1e0d020a0f090e0c09060607030207240212030405030a0c05 80
    0x404c0324403020890406000185071214003030b5008002c1007000c980c855a006464000415810003c1100e241600707a1506180e40456071000c400d01d000385901c0d07181c1e0344e10410703407021001c1d40c00107a2002c2408414080300030550a8500110700b441c0c00307000d2642c1c1c0d07002124005600050210f030341e40c0c0c04142540e1400c1d080030b07000400043c074904180c6500d01d07111800c0003d2030717024140303800566000f0b016582ca01c45c181e40070390401400b03c140509075003140c1036002c0505004507011030081c0000001070312a40040d202551180302c000c2070020b0325a00c1c0e5021500c0c1640041d02c81c0d400e10a44400c2512410040000015a50030b50202064205c01041c0d030380c40c2d080380080d0411a54000000c4003912610450190781680f1001e02243d030f0540142e50707481c0e0402c0c1080e6408008440814442e291560040c4407040c8a40190b90550740e2798510090644080340154102d02c14281009084940c1440514070300e140d00c040d0300d425800d15440d029500c0c09044140010b020201811000b4040c00300040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 399186969 1250 399185719 399185741
    0x40c0807081e010f0f08150408030403020109060f0b0f0919020c01020702060f1207030905031204140109140f0105090c06130e040516090504030807211109180c0f0706 73
    0xd040d50b540c200c02011000303103108121860170104804101c1040110b6450050308800c5a00310160322a91629400ca6001800440c25996156440c030001413050203100409900c07240c0018410802d0b01c107000340c0e501e03207080720703441901d090081200000c04107410446a0600c48001a101d0140c3c8480302d00902c22184040d621580c0801d60000c101d024200905c4000c0b2511128003003070700c9070701081d410b403896980020844d030030600801c1c0440f08170320300d0745034440c0c0188012a00006c00700e0303e42e401c40744214000c0d00c01482e102c1c80c0106202040106041102030400200310501d0310096458403510381c10402d921450001808100000142c80200050f00c014140c030a0030b400c01d0b2420a0b40c902e03040c66006c00d02400c0800c00244052203114052041e50140c40b22981603441d150210b40101e000b12204209507400614560721a030903100303102045012045090345c802c0d03040100305001d5840c0f02d00425000743e220802030f44144444c29101400b40c0c0c2c00ea1702d0349806032850680c014060401103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 399188219 1250 399186969 399187021
    0x20d050c0c0d0b01080111030907050f0a32010e012c0603010603050a270215190314060306040c14010203040e0f0412260603070b0a020a030e040c080708 67
    0x240d043c401c144a1940c12541c1150080090300345c828aa00e04078001200e1000e01600030b004200500d040c450f0340b405034080000c1100d1340303581e180d1440c00d105102c0419030480390010048508828603020b101c1c91036200302401e05080d480c03c02c0c40000c1102a9400040008095110400d0300c1c01d2085100900c00f00303c001c00b440c0d201c1d030711280020020a0204c0c0c0c0c030f41c6414104009000c81100798688118040f20703000041c80c8594084d007c0c000500300c5000c0305d0b4110941001014540e641e40030b8032020145d078541d07010407541b0100803140449070340a05014465001841800005039550140324120303503e052062051031074420050f0f0030b5000c1c550181e07000c003500307400300990f9401c0840010701c00c030306c520791080c10b03404001030031038005218100c03000304007a07c403010030800410480050350110008085585450310760b011110030b0b401c00d4428802580c030a821401c10150420311094605205540800176420f15080007009107002912007018446080302149903a51600d400b440c0c14511009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 399189469 1250 399188219 399188239
    0xb241b071d09120423131506080109060e1b12180d02011a01031107020d06050f01080a170304030315080c030f0309090720070f0e010510020d050c0c 65
    0x192040c03001c9070448a64456006070b084180c2424000800d036410380b0b03007035040c403c08072410042041c50290000700d103a038480b100080786103030f201041c0580c01c40030b180701e20482d5405142c41005894282c4c1078000183c0380b803c01c83c0600184540c3d00c4a04d501800b0902101200114540d250038507110340e0070040f1405c1500c00810a141400d1a90b0050b01c9091000b158460490200100c1c01c0f078016039580d40503006c028103119000e610a4114040e03458031560300d40d01e4034000c0e80c0010220042100d08440c540d40300c200300b120706020900e21500610040e4081c0c0803d0095580305c80c0c3c4049030005420103030b080400440d041c90b109078890150b500021070741070f1125444600c520b54400c0000c0c01d152013842a0505125011808801da44c001200503100c41d003c0e072101042070300c0c4842e0300244240024901d045409820408110030700050403003000c01c007070301414802124441310050f08480e02441c05440c9011066500203603d90302400c8600e080c94a41da0452499418407210000b140d42c0701d90088 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 399190719 1250 399189469 399189509
    0xf020f0a0b0f030f0a09020f010e18010306050907081212070905030a0b0a110a0212090102030c060a0c0f03090803040b18030a050c071e15120f0b241b07 67
    0x140080d8000c1e1301500c402400c0d40d951459000580f11180c20084d0010000c2c095481e003540200c21451454200500d0303d202c000079040c400103c0c910076402610aa81c4902c284a5244400d00c00c0d45d003e0a5074101509800007030064160981c4910840d01c01c030950085c0000324064400da05000252100030b050f5407000d6000e04140c40710b0002035034a0102546070480c00900c0d2646601152231002c00c0740c029008540da44100c8803815003011000d14150300040042601508041c0b200c180300312000c440011307000305003a20040c46038041c0c000d00c1d81814034254428011860800a40c2d5000380d100e15140801c0d5100076240c0c03004100325250141c0d51101082c200382035600040544091090441120400355803032442d60a83c02444111083c95040003109001c1d592054a881c00c401010f07050960210001c02d9842040780d0800003a00d40aa41e0368480724054640350800e0340c4909450607a0500c400d114012511482c8201c00c241900d2a140c040000207840d020b00c041c0e0300415104a088030030004203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 399191969 1250 399190719 399190747
    0x20a030b0a050117120904020c01090309030b072c0f100c290705030711070e01050103140105010f0f1103211303120e0f060108100b0108040f020f0a0b 66
    0x2034032541600740c180b5001084240c0800c0603034a1003070103403004160b04000440008915030000004c02e800070303002c10a0072200ca00034051500c1e0075200e07590300c444a61450030300a0a144020340700c0d1081000d4195246041c4a60140c02002d2215110f01f100185601a00251204241ca4400d0380c00045403a01200c8480d0030101002c05240030320060300f103540e07a031008840a00840002d054031504160003140d0268803482c051079101c220380c284466108408030b402860540e0b20b9100d0080070550400600040d60b141c040c02c0e2524200c60303898002c6505100001c0e00b0200c960403031808014035052203012003485a15284c503404103d0742a241c0c2d501401020151103005508143c0c151f45051003c603188030684000d01c400035405507159000101c1802c000d00c00341c411060461941c2c42003420000c0c10100c00d201850003003102100502040d81a601c006040e10b01c651806810b1014010030040031400400302107a42c0e580c101c03900200b84c0300b4400010041c1410b5042200007190100b5182411045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 399193219 1250 399191969 399191971
    0x4090507050a0909260d02130617070c0210021204121a010e041e081b0c01030b061c14130b0a0506180c1605012013031707020a030b 58
    0x1501c1c19601642c5910603401034900301c90005181105030314020341c2807041e22071702a480d039000640c0c0c2c0e4074150514141000760f8000c400b00c046545130b9007004024098000d08400c03500c400030981c50002380b900034000340203118144000b034050014400751209482c420b00c0709160a01800c04503a403038035100c068070150310807080001c0710b0018250303001100321700d51070000604070355104408a04a079540d550300380380c0e080507034075a4039040c0402d589200040e01e144041c107100380016004601c0c0c22010b62920345080a20501c081c1814070f04112140c180d110a022100300301d611004801035903a0f043c0d0594010a24000c0d08003070b40895109200480c84400d00808185004aa10b00040e0b2605000c2000311035040e41d03d160b020b031955240c1c0c03454000451026a22078542602281001890582c240c0e0301a008001121182d540f40c07a0415030f55426503101c400811094501400d10300780c007a08091510f21808050084aa0000640d04010841080300c0b59070364003800c2c1d021038540d2481c0081000310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 399194469 1250 399193219 399193229
    0x3030914060f0f0c0c0616150c02030f0c070e040f03021c0503070f120c0c0b010f0806070c05070f0b030919050706050a260601020f0307020a05091504090507 69
    0x4000000000c5203004001d40705401c07110001d032450054140c1014007643d01c0b1070422106402181402104e03031303a540001d004080c1501044a00d83d0610707181c040704610032060814401c5151520b00c01031941d0020a4544003142c075400150741c0c148082c3c44519200c1d83e54403a0140c12112010001004580050130a00a1083d002c070740900c0005071182a41a102c02c3c1c40500148050002034880d42c4200c0c40e007802e0100c0c81c200451540c010400c00c0b001d4a41c451414800300d000780e500e8008001c0281740b841e004201104880b242a810400016220f45005d410714040080810802041c4441444401f004001c81d0241101340c0e6929112200350703400031541c1207800d0203969103840712a82e100140c510741c80d80c000c0c05800d489003801c44c1075889402c15101310040204071480c0e1200024405640312140d0901108014145080780009107410700c8400f21141071340051000400588400e8400b4094650031140c1445507920321020074041c3d00002c03211584117080c19959030070b100000c11020140c41d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 399195719 1250 399194469 399194489
    0xf0504020a27030215030610050f120a1b0c0f0803040203030f0a0c1103010b0d060f0f05090115050105120402040203180a030e0102160605180f030f060702071d040b0705090a030309 79
    0x185960045e04240c1c0422104590441034098051850b90f20840080403c0c0481d044401e0606c41090601c00110750308132000079155549650000f85a0700903941c07407840a445241140c3e1051a6030303900c51160006090040021a000c03012408640c0c00717000351803000105032400ea85440044030003c2041541e4502650030442d02440c8500c141410f0140100d0340b031000c2c0c5401411001685c1b03031401050311030f00080010f66910b40b84c1e003010090b4091640038002d05400450300c00e40d020300b10645580d6560140d1306020b0108900c071181002d0104042c0c0c41901141d0040c3c5070f540b4240102200303421519004e0547c019081c60808140d0420302d501c50101007a800ca80c01100c0e001208a840c00460040e4000707e00c05000720700319003501c4015220321900140550785c03e0b0032000042032070701a1124003090325421900c00c200c41c250f41001290014010281403000b050091030071004107200103000500581c0440001072030050140080328412007000d0b25454001d070b078905000301a40480d0091440340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 399196969 1250 399195719 399195739
    0xa0b070203090f0f031c120603030207050a0b0a08070f0c0209010608090610181505090c070605101505090103060f152006070f090312030f0e070f0504020a270302 71
    0xb401e22130b078464000c3c01c1c05401010380840400c80c10034100030704100c6004000100b83d010b14144c0150003088001d601c01d8000b04000b504080412458030000d41000e10007075428048446120b91000240d07801982d40e0500d41c4504009240844507014200006904182da0a000288031a032100c2e10512030a0b140d01034072101c0d00c030a007400c001000300740f0451152940f40d00480448001c01d038880720100c1e524280602d141940c0e03c020800b01001140c04582a0801241c00030038800c0c0b03401180e6028080c544801186414099040501c40c41100010204079002c43e410510344d004c0e902440103000d01070600c001040c3c0e1a886d1969020000703403100b000444081c29000b90f040d003141c20840c0b1500c91070140481c0e9984e68001c407041078016006804200d030400d0000040b401031801c0740e11a058980d404203100c11001070341010380700f05014101031607000e17400c1044950a900d00701003d440044401580da080700000031200000f007903503900c001e1044804285c598003000009402228403d403080900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 399198219 1250 399196969 399196999
    0xc0b030105010318330603050a140c01021203360d03020909010b0f0f13061b0203100509010f230c030c040306091707050105071407050c0906030a0b07020309 69
    0x14484810014410a00391010286640d07a0a0a0300707002411405e01c0c1844031102080300e0b081c1d441c0d581c000c1d20140c2201d6490401e0101d0602104104508940102072840001e07000035a60041c28049441d07015003c0041611158840c14860745e50034401c200d110301e81c0c000004000b031480f200040405c140b0425034144610340c080d0007aa0113844004104401c00ea28100420100d54091400e18112600800c07402480509000141801c006c2100c15802c80c01c0c01c11b50007400b40c913068141e00501020007009071005a400203551611014580000b0402d03441d888902d03400f424003180300c3e0710031a050078501031020030844140402c0c064100c407100c0140d00c500d02c1e1030085200540364000c900c40200810f00205071103400400b11140b04090041e040400c07816090207680003488200c480d40d440b0824402015442500246881040c05110f89000319554401d41d03a1804058054090610200041e9407540c05100f55007060b40c1040b0300a03000d15148000940701d5201c081c8213841515941c40541c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 399199469 1250 399198219 399198251
    0x9020105090d051e0f03090f0402040f090605030c0103020f07030c0c21110d02010929070b040201030b09190b060c120a27141201020f09120d140c0a0c0b0301050103 72
    0x5911782420040c51a1801038411301000044800296030803036020400058a02100d601e044000c0420810004255081000309802e146e8032055141c101801880300d06030408001e01198001035060030444c840d070007540340c100c80c030f204a50300a190710888184648286010a031400d040341d03100b9002d00c045252484c0c204140c408600101a001074001c490034402000c0d00e120035440341030ba240c2d080002c20803511040606600c003507000c4075040380d1501881700b156054050144c1130b00040b50000140d10b020000c0658a03210340410702c0c0c000c3d869084034403a40d19508221054035036420252016031000c01c0459a140c0c1c842ca81150014141007540c0c0070082c05141d5040001e0b800400b503041207490072120308201c10b000e41406a01580c805207070030785841c09100070401407070f8400c1d0881e00c900540341004160000381101143c1034100f40306000c1d890b0b40c410403030020896000400c40c5c444030b01c00c80c8580f6110846100030580c51054002140605200021714102c0d60240d906000c411001142c0c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 399200719 1250 399199469 399199483
    0x405010801050c07081e0a050904140f0a0c0e060d02090a0f03030f350108150f1308221505070507060f020a02041b0305090a030801030609020105090d051e 68
    0x3e40255002c0c402c40000826080040105201a9040c620280800f0801040300e1784151841d4020410014540c100383c1014040c02010040444e00040030789446502400300200c01024500940d54a82041750f486000701d10004c51510041e041c0e545071050041501d009512400c8903d224800003100000d0303070300707041c9001d0065940c1a0b6a02042c50383c185416100c400190051105204d0540c41c071903a0b104006109a0b0807083e20320301c880040d40340c07013181810b04045104400d4141d240508020202c504910001e0f0000f05111001c4109081400c1501041c0200f1814600389402d806100310556030340c1c801c038011341d0341e046203800c200f60442505032080d01c19000018401e4020080030002c1030b0042c0c0a0b407441d4107690041e40d5801c901540000e0481d049094880f000c0d5a02a1000d00d1280c5e0501c20503501a481c040101820000c07900d024110740c40500c80140700f0380c0c5070101002164801d600703440341d08802605040c00658989400703a1200c0c0750420401c5500c440c4410b059204100241034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 399201969 1250 399200719 399200731
    0xb030a08090105070c03080c0d0f1d09091f0509100905100b0f1206160207050105030a02030601030212040f030e0405070903020108040602040e091c0c11040b0f030304080c040501080105 81
    0x2052a0070740d40c0c0c0054030309030048001650320190180700040820480001040c442c540400500a0600f50322406020a141490880104156500d81da440b08103480035074100400200c0c1c1360f0350196140b9080e02d280100e018069140b002c18136865407011105a041140a84140c4050b114140302c03503040300c41291801000a0b1099220101c0c03422a40400d034480c102072800a481070210b0980080800c9d48060440e001d660207a1000d002c0020081002c00c84040c0c1d8042c43c809050141d14100009155003c060b10407400c0070b034000042105617009a040f500500c281202d4003580307180504000981035510001a404114000b50b00003103844c01d07208440c424490364548003d145c0c00c41d001154004001881260318643c2004003080503400059920310414420009104007005035549142c2d1003000b14505050104000c0f8450001d0111018841400380c15a00001c00c0240d01d400910481c000c081c3d055018000014041441013000c500c074065600180d03010320241c0da841c6035580c01c070340080f10b00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 399203219 1250 399201969 399201983
    0x501050a0818100e030a0206010b0306030d050c1606091e08210903150106020706020d0801060302030403170c09040e07080304030308040206130e0103020a21150f0204090506040b030a 80
    0x1041d1121603208121410640c6045030f5250082040142c212440394010360545d031300110303005046035030420990f0b014052210f06241942800000f0980c0d405500c0c4000051010100d800481d4943c02c00036080b40c141c4a84131580030f143e54103405006469580924142a035182c0e10000d509840e031f032002c0007201c400340c00a084e01d074824011160308583e4030100d0786107003404002840103940c08014003840c8605e034451a072034551510001030b03e045c0480c1e0000084d904141980380b0002e800141c81c41c115070546c00c0140e81c940e0303540340c02c455007540980c0c4032555030292400d1050086491018181543c8150740c10800240000c07086941e81580d4230404034268010081800001d08c5003550a80092000c0d05090034039040b0100384400301400c1d04044240e0481200400640c9405000340000301100c2f640c901c0006086004039544048064005d0840c8940d07126905884040e5031180e1242540440111744035a1540482c07405090305860f1981300d2410640d11303440d985000b10340911041c0e1b100369 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 399204469 1250 399203219 399203221
    0xe0d03021e120604271e0b04060b0310020f03010b0a1b050f1005091e0f160503010f0b0913020402070b01081020070206130f0b070302070501050a08 65
    0x402100a9801201c101c002040c02807451079145034104050060200d000307401201c0e901d003039018401101c2810030452040c0740009040f04c0e8482600c1800b40c2415007210131301c2800300c0c00c041c5980320003080c2c280040040303441d07030b0401060040a5010710302d41c0c64110152191550303282c3c00c010a9010f401c01900030342d04104010000090b6150041ca410562400c10801800252040002c001c1d80004166260780280d5070864a4200c01d10114211402c43d40007045030341001d44203184c0e11010004003540c00740200c112440c1001040291f10800b0340321204a941d0442116a400c0c2700c410607103d1680a0360800c0c2d468603001c88a03026603040e99174041e1004000e0366400020b070f45100400365060f42c100e6400c0003044049003e0958640c003801030b2000901104201214150440d108012801c140040911040501d4031045084520350b6070101d0741303503440c0c4403000c5120045404c603a101e01380450200c5000544181c1c0c070005002010f0007074007510715940c4e94000541e0305201d04045e982c00648184 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 399205719 1250 399204469 399204493
    0x7050f060105131a0319030e040218010305091c0c020a0504110a050a050d0c050a08060306060105031902120403020f07060905010903021005070606090203150109081e0a0803010608010312030e 84
    0xa4801080700703010340c01102c04500c000e4086424210301d06c0003a03071580c0707000101000b1b240c0c2181c803c1c0b98817441503d04503c2c28160320415903101503a00c0707035141010b4071800800d5024008018140f01d80b01c0d0b003a0210390707010000f04080e0101c3e10821040340168402030700010b05141c907118000064580d20103040c42c04020003011141e40d4469200c01c02881070501420f0086a2640705410140109441d403d90b244442100901100c074002e040e40e101350302600400080e07903400019250440b003443c03040d0102003000a81c44000e070281007020380205905801b040285940002d4a03080d036014102642c00f0181c540c00d08482007050380c080c240c0031482e0804100010b0400440341002d03d00280381c00350801249568000075039006610910390700b070b00842440b90103038820078a103200340800d0a203412818548040c0c552141085e881d080700c411461504600c00352170034411140501d030300c02d82c80340d603944c0c40b404003400200d004e00090380d40202c4481c940d49207038003c2c4540900440ca07040249a250030318 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 399206969 1250 399205719 399205721
    0xe060402040903140f04060e030102070f06050c0f07050124031a040602041e0609050a0807030b042301090606090e060402120102091017070206060d15020f0c0307050f06010513 77
    0xb030080702000b59106542244d54966405072000c4c901059070340da41e0b149050b100421600b034400031148242d10400c41d410002c1c028445040050b6803084022900b0303900e4045110700360080510000c5d07000300c0064444200003041d803119410401000c8142c0e400303803005030700e20a40d101c9400002d00400c0003000720301340300221354600d030340c4030388114005807401d0b8585500c0d0565034000d608901d001100b100080c01040e4105819a01134442603e07140b40d281d01d0108000d680380503520014280100820104040c051f01d4480c00e500c42c1c03100441326081c4c113071080402c4c7c002c01d07012005035085482c007100400c000016015911483d4101001000103072956001c1110b030003090316070300200391b40c02c0000071020307126120b103081500c032292100c0207001801101180454401032901c0110342003481005034a507100e0b01d030391030040d40151503840041a8503401c44024820860038400741030001c109440d0703010f800030040038980d00c60781c19942d18450034811641d44400c2030281c030b503018017400055052494a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 399208219 1250 399206969 399206981
    0x180504060b0406060315090c0e1e04022a060c0a0503060102100507020f16060c0f0f0204060f08191509110a0f0f060e0312090f09090c040f0e06040204 66
    0x40d020000d09007000c680010201c8015901c8080482d484e0306030000b001c205025140020400140c0c01e202030802c1e040d0042c00009800c0c0d20f04d11039080404480c50221031100e030480c802401900031136a4102000981d034070f11426400490241280000c0301004200c0842c1c0e0b02e0003010340c0515181065141c1c403055510303800080280c1c0c110300c5001d4081800388200e005640c01000b4030b030007a040100851100509040b85403c8010078207680c800c08112040c0d00080112400e40c01102d548071249a600e41031100d01c0d0042e4010350300505041c800b080760020701075541c0c110b4000b081192015241440c800070f000e0641400a40003000102d0505e0080b6900d4000002951003506c290807030f4003080000030301840b10b50b04400d41825403000c0a1041c0e04812581e034002d01020304005050f00b18410010303550755500f0404002c00840071402c1d51280e00c5100303a40c9418003004200c2c002f14505100180d544420780c9004a00c500e04040c200d01079a0214828508140810009410b00307640e40d400784005414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 399209469 1250 399208219 399208223
    0x4031a1305031215030109080d0b090f010626010e070905030627030f0c030903010b090f0a0914190318030f1709130b0a0b040b030a05090f0304060519030501180504 72
    0x1c4c01c0c2100c038103942c1e00303105100003144941c200030784401881c0706010888400103c0d00c5d0003400407100740008500803141039411038200749400e52003907004500d241d0201c0e1003030400311600c4401c80c0000c42c1d180440c2c480f8a105501c1030341c42c06c0041d551081050b40d40c40081d5500c07074005800060054000701c200440e0000c06c0081ca048900c0c00300050754803e01b943c0310400201054001041480283ca820701074100c00a600311413a140c2418542140220084040c009200d0360790b0794410107040124091440c10010690800e1b202d440b038480000b1280650024021000604402c01d200070010440e04804141e9410004400c0c2e00c0c0d420350741d1a04036031601d036503c2210440a010959071652502d04e04060203840d001c01190700c0c81140244074600200b0340041000710720511051051030414015030398400c0680070302258035100d00c8026814102e0400c10014940000940410040d400000400511054070082985805686411001c850081c0241d2200b10b81074a1078003c41200d0750402a0042c2c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 399210719 1250 399209469 399209491
    0x405040309080f0114060910090f09021503040b07030203010602070614160f050c2b020a0503060c04081002090102030a12060b041409090c01090918050304031a13050312 74
    0x2945488000b40340c0440b52140d00201c0e03458070b4040c00ca03481038240058001d2410b48030303420306040600c23044444600c68000e421184e5038400700c0d94100c4403980c1040b840190082c1c801d801001200120304c40a43c000c8500313440700703039020000c10070151203403084070304844c010b0380034040c1e581c2000400c681c0402c5907202d01100300c0c400c1c0114507040c151100c1c4030103d280304074000810581c15140c4581000d6007008501d00c101c0000c20341c06e08109061204440d120070403400b080c3d9000c1d02c1d100003692b6042d141c00080e0184240001c0000b2401420000d1055408030001c0310362591000140c5030030b910a400c607090040e00284020156180140400e41c0b40c0c655030200418040d4543c4140507898020b81e0103840100e1641482111034104010354580201d1041e014007550200a0000303480d40c8180d00c40c810f100c96071000f002442c003400041c50701069510809482d074966507403d000307000e03d03099070310342d1040300802000c194815030b508422000d0541c018065400c04204c2c000045041ca0000d0221b2011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 399211969 1250 399210719 399210737
    0x60315180109050609011d06060f01030e0a0f142b03020a090905071701060513051c020402030c030a0e0304080a0605070c05010216050c01050c0709090303151202030c09041104050403 80
    0x10301e013440401d00c601c1c3d00c80b0001840c840000d0b039507214900000c0007082640c0010090100c151200121000c00304005c1c200820502020701340d05140412000028201c4103012418a08200c1303240d200f007040041d254212442c546582c0382003009581d0051144a080c3c40108079140c001b40070742c001d41444002403c00d80c0e40a075030741000a042d40c0b01107500400043e841c2c0f0a0300128140d1046076405040d461500c00d04040300e4803d1000390003210701589104594100d0a42810002d0703050340d0a825501400654803414911a030b900940c0081c0c1c0c105c40400d003008000c500003a07000083d102164040d03401015013500a2300c50000400000d8038400c108041280e8050200d242400102a03000d21103070340900d00d03422414514100004020014100726040100400d101c40014002e001c4d100c15071800a805c0c0000c0ca003c9c0d004111518405c80b03c80d0303090b400003c8207412030b4041042e1600075000d544101145000300001d1a0007202d001342008022000ca0505007025444070754031912030f040020407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 399213219 1250 399211969 399211973
    0x303180f040b0a1202100305060f011d060a03060311030606090a050a14010b0a030b03010c0e04050a021e04060e180103111801080c120c090c1608070b070305060315180109 75
    0x1d0141240c0103e0b56800c6403031304c188114280f40d004010f041400303103010009810207900081d1441c032541c002c10304106102c11551202003104400240c850070081c0550f50b43c040006014000e0b003c1480203407612001d0416110403400c0105209200b940010100c5a1956541c6e6000c03005001c081c00c80e810032a65002d52000105061101030b003e05850a0161b440c1c4c0c50201c00202a0303044846010300990500442c0a8201c0e04850400486802141d000c11541d40388560b103030007401000181e585400a008a403920140920002c201f5210b0303da4410411140bd4003e00445180c244103480241401340010000b10740d2030303102a0f00202009040c1070140740c0802c480320400000383c105d0002a081810f503c55649400e07a03000b5040d02840002d400288020b01c0003846107540102580c0703890000003440112070004000440025500c10300e00b6441702140e0a14036141c110844512010a180c107011a0443c81c2c001261041340020084059195440702050350000c0303102c41020034550740301d4002d040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 399214469 1250 399213219 399213229
    0x90207030e22020a050304060b010905031e0f010f060f0b0406080a0e01140a060819020303041511010f05060a1e170a080309010e0c060c03030c0f090d060c08060303180f040b 76
    0x4131107140d03645d255183d01f0181003440486200310742c10b03030500141c0c650411450f1000b0a13480c1e108005201440d80007a211b0040c1c6d4140040800d05034829403a040007c031009440d0b03401002601c102c0895829200e444074003640051241d40140c502041c0040002401456039400c1810031201e41c0c000410306030b1102e04000b840c59802c0d070b80d54070425241d200030701410104002100d00c512543e00c02210b81d8800e9008261a4803550007044402038403103c8440b11140100c1d086c43d42c0704407800c02008819058600c0c40010601074890314855034069000140c0d1100e80301500c03801c1040a0184c240491400041c180f11607541d2504808074021741d03441e080480d03202c0d0003451280118030004540784c06914a100d0402d00045951445801c2c01d004101d04801c001040d42c1e4030210741d07803405642d2a90007040d00501d0040b0701841d03501c50110810941000407541100d000f04ca01500e50342501d444000415031203000300c40d6541081084184900e0751890224000002c03000050400200207800b400460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 399215719 1250 399214469 399214477
    0xa0e190813150804051605060912120c010507021b060901030f061d310b040c05040903020c091605090d020d0b01030b0f0601180509071101060915090207030e2202 71
    0x440460081020801804003d10010695804046d0440d2040d0b0426002076054003c0f010b0303890041a040d25000c1d02e105081098904d91080c01484549548028500e203020303000441d14000140141018000f2003500e0382c403500e4040f4001059a401d15005000440003030400301d9903034000c00d171500720000d4010140000c0c215440b80c0102e0800152404e4003000b84100d03083d00c00142c0d1038201c0624203c40c58030031194000303151b5118040c511940c4640c02e014243d220b0580245038004d203044207170010035030002024007044030103480104495480060841400e41c08244aa000c80c0d4100040320700380c0741040615042601c002c0c034079603003980e00e0f80354940c44980980084a1521720344082c40225826a81003590140091a0802e01c05041d0380c40420b465005100f0140150101e001040a131401072181003501a80c86008009181d654104200a0b10500c40c2818288031410008a0f890825000b16003000c4e4150700d4060b4409100f4040c003110a403038981007440346020780c0e180c40490b00d041c0020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 399216969 1250 399215719 399215759
    0x30303020c1626062703090303031e071e11010e030a0201050709211103030d1407110604110d08040b07080703030506040e0a02010f020c090c030a0e190813 68
    0x61001d190340805000b508007440015070b10651301640800c10407800c44d05610070f020080f8901d00343c07041501c0340f806185020b01c00303030281d16010100400445900b0358990490310702e800c1510400644032100b007a614005c081040004504e994205560194040d400e401340d9040100d0000513508089890941544c008880500050751500700707000c5a1342d4420015405048032605140d01103644810000d01c81940000060000741c0610020300d05640500c260b4594004461050003018040880804500e00c1200eaa101060320700c0005a202500010071600c110760203402c1c00041c110b180f0070480507580800085a241404200c0881e1420345400604004e038480c068668a0720420b180c013405031180241894003d84c900a0086414200007a040b00621380a0034180341000a94808900382078403042c0168110340e986e0140203c40e4068801107214440840040162072a0004001c0d111000f00203d2140b0312110a10000492200402441d55481e0040c1c002c03d0310790b6803240007052445c2c018130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 399218219 1250 399216969 399216989
    0x10e3a1401110408100f0609090b0402030607030e0c0f0d050a06141608060f010e0402041d0c040305060708060604031707120230040801020403210305070801030303020c16 75
    0xa1146002000d00a84000381c601c1d0010030300b024180722503556500c1c14007174188003190302d03680890500c211642c0f01802406080e48180070100715030410034174032001903c0483c0a03204030000280c07418400d104d207000303540c402406092030020540400401c051103800c0d883d4819041c1c840b00d400100100301244c9954468600031500120340c561007407054200401d260251145003040e07050060740f00f174140da0f01400032a841c80c450600140100e41413426400750a030850310000307010a0517034580c4100b01034440c3c07410307064845a40d0b01aa28043c1c1c011b610000704540c0c0403e02080906010f2040f43d50b0001000d0900ee007080d650361101019611003c2c04245c1c81140054200280308103000249101d80b46400244100f01a4030000900e00d902b5820042c038030500c0c52709d5140030034640800c58000b080360100035510746460b414074800c100b1610010040031810b07084003400245c000c0c0a1280300744030035210459268a5520158080d50082d46900e01600900c01c034912060942c002540c05450300c820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 399219469 1250 399218219 399218243
    0x12060403020f1207080703120603151e15181107030305010617040b130f08040b030f0a05070210050604022b06060206060906121903030515010e3a 64
    0x104080c1804070100b001c8102603810013070400800d92036400ca4041550514002c40145108103000c001070110750402172000140d9922500c04020541080a0302901007076503c942e04030305c440d110121050a896404c6004115400b000901024840010000c9410101150007810b0ba01000d0941d48084070840200e07542d8001800110b910052404610300300c2c0c01c580c0510b0074251900a00008018251007074100c100e40020204040c003e024038010b68403080840e02c664807006d2101c0181c004035105c0e41c50780003840004800120074056280150090b0b0054805a078018410401404008103900c1c0c22035020400030354000e80d11060940d5216064060500604041303000c041903e40d69400301d01190b01c00e00a01c5165580d110040e81c2100d411126800d10b040f42462041c1482c1c403d0800d0020203000000c0007040c1509504098460a4040c00c081e828042603401550180c440d001420740001203084c0303002d05841c0848454260342081c00c1540454901d001000140b5201c0350011200c1408140b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 399220719 1250 399219469 399219493
    0x60d08130e3d0f08070608060303131404060b16060b040c020c0d06140c03010609060c1e02040209060a050c01050a0c140d0f0606110606040606090b091206040302 71
    0x1180c03160071035440c90305207841048421420b40200c010341c0b01e00d00c0c6542c08210345580c04080000041c010030108905901c3c1669402215440e0341d914451600428903050001e441c0b0b2170040102e500305107000810909075410900101c1411100102c1c01f504613039070303d10204603001480b020700004c07601004804c000e402249000b00079200403000700e0b401542050218180141c02203515121034600b03645140d8101d502e41410000391080c54980b015841c0b4003030a024103240408001c5040e46c44a40b540f0190580e1044c040343c01048604019008050b048414100c40400c0c1c8802c40070078ac0000c0c80076040c00030110015050742e124884010206800046030070f81108213006440c0c0c4225040010882e509280c4d4014140d04031a0708074520300c410019422100c000503502000a4091201d42002026112100a04101c1c040c2500b0b980742e01c1030704002100c40c41d180c0501020398500d0359800c801d4500d404400503a5800c948221a400011034070000528a01040083e00c594000d50042c80265050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 399221969 1250 399220719 399220739
    0xe010b0109090b0d0204090204021201150212040e07050a02010b03070b07030905030c0105030609070c05070e0403080906070e011d06030718060804030c140c031c0207051c020108060d0813 82
    0x10740c01610300ba070900b080c2400660f12101d0141c440b80e010785011400200e02e1000400910032401c90000021a600001c11064408549051400c41c1902109c5081d856010500154091407056200d0300c00c0b542d0004d0442882007014000090540c00042560703400c0b0800203092580030741049038500004035801c070605a00c110143c0042006401410844be100380000b0401e00c8000c100394010040407000c1083d451050f86000741094020042d030700300320b03220006070001c02012b450a5001070707903202c0460402040482c1441c0140e10f1a241c81c07002d44414401551211500c841d4201c4000c00e03481c0171500c0b901c2d11002184128090382d80c0d0003000c481c0d00b40c4078040554940183c4100000f030820040040c0d0841d000c5504a070b04088140500c4514070125843e2080a90740755801d4013800300d60301c0000d24542207080c56600f2540940e84095213070010710500c0c418014404082e94541042807000d94080c0f110180c100c40040c0c01c20072490350a407900100d40e4821181d2111000320800104420080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 399223219 1250 399221969 399221987
    0x6020a020c1f0f110d0f032901111204080a02100f020601180912031e15030b0408120712050106080705030f090c031203100806060303030c1c0e010b01 66
    0xc229081d0466450103108054030144140312001844503d50703e584002e4000c0160803038502d070140071220307010b091810041580f403401c41040042400e10b5002020036240d03111025682d60101184031160304100011a07140e1017a50440a035401043c01d103007500c1c02d1450050010b0041d07200104291205481031048400c00813420204100707956107a903001d5640800c0301c904561403416000030038512800c0707040050a0300c2800038064000b4510043d0032a030540c21441c1d503c186401054841c00742c0c02030300c0080c0c80c000e11407441130a081601c284005403401c40c4d5290001e0083c00041e05140e284015010081e101f0b40380c2d18045580d01e0b050f58568070080c01514054041403510740c3c99410900e0b0054030358040500b240540c041d16000281d040042000700e1141650020704441c0032028004400d00b0310381c0166811400e007000c40001040308000003401d140103d101034011450350340c990030a01c1d600e070403a140304ea5980c242c03210040021841c601030300440d03200c01d400000b00411510005030128403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 399224469 1250 399223219 399223243
    0xc0d180603060b030f0403050405120a0213110a1214010806010e0c130302121606030212090f0a02091b0703031a01020f2e051f08120912031606020a02 66
    0xc14a42c0c240030800e015810b0300e4000d0058102c52100b5140c0c1d03e01501c0c103000d60b4201542100041444083d0343e41d0000700c8240040c001d6a03c2c603881803070000518142c40d001b280f50034203540104041b242c8244141341000c10103404482c002400410500e10800c425001c4e4480c41c03c60f8030800041c0324540148010780c0c2c0004440808516020441c0c50290401c929448040d02c40c24023000007075010300c2c0920642c16280c43d00040100c031b1907140d141c00b8001750001d02c0c15a041e40902000a10b20140019000c004010410010a0600010341c200000410028488038a01c42d401141c0301c444c40c4148060400c142c880d0310f010480001c45482041c19045c182c15881c115404801949030070314000c01c250214000002414094149620611884c0d142c010a81c5400c18603007020400442c510303501c3e00905c4d0200d030450b0401980c0da40307641d03a581e81900300c03580103040c8104114002c624080100d4050a0410310549007414a8001100c445500365201518003d400091085c00b0030f0341844010301680e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 399225719 1250 399224469 399224471
    0x305270d0507030c0506070923010f320a030b180f06130504061b021b1504080601030c030b06220f090605041a060303041215110a030903121107170c0d180603 69
    0x41000d00080031410bd0721110428003031070f00e050310700c5040c0a203541034000883c0003031803c80c1200130044806550008000b80006440e21905408515000324084901e0b002404040f03516141c05184c0c024401000c0d00844e44401c503445001150201405082e12607130180c8000520112910440f2441054020000d0215007120101d05681c200890034001c00c0d5030140e600100c2220b03106600c00081c80b41c0e4000c82000c1c400c01000200f0410104801d2003030f28800c8803516040d1311484240041d19107002000d82c4245058000c1100c07504840d40403090700320a94102050005040d22114204c030410b07070b016280c980d46408052100c21130034090135040301381034006604d03191030b1244904001d5000c02005000c1c00c8138504180398184550002502c94000309400c0381e403200d50150103001000601822000704040c90882e60700d030344481c40b0720070340c2458800700700349010381955032040e0078501c1300d0f41c840e9078890500581c88003850801055086110313544418201108407038540e002c030007480d40450209 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 399226969 1250 399225719 399225779
    0x80f13080d1d070b0301090c020304060203030103060903091214060c09010e040504320708070b12100308040b0705070519030f05030412030305270d0507030c05060709 73
    0x92958000c45641151500000441d003200c003142c039a10540341c00d031210062041180116003034802c44019030484440c52000c02c04120020001d0340c490189100c0d08016800500041000c80c0e07490300540132984c40f034544149030b01c0e01c41007139448981c444041079a40c030300441c8005075041c0f0304101940c0c01000030801a0f007400c0054000801042c416400701d03004030707212400b0070f040101646c0310440c001d403030f9840b0200c2d10b801020441701c1c0c0f414950350304a0718440c4038000214001d01250000580398042040703460a580041800c00c10300000d003200fa815111808000b000c220b140c80500090165400829521500f81c2009882c10700c05420161240c00c07190b140c2d185400421121104680d880004801c065005042482c01c5005991150120032403c280342c00416074140d000324420b00d540c440c0b1104070340001002c0c120449510958209640c000303d916078126000d5006030218074070034076029003011520740c0c8441c01d0240540e1500702240b201c42081c00b4160b0120b441050200c01d0810380800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 399228219 1250 399226969 399226973
    0x20c030f030a0309170f191b020d0317090708010b04110d05060d080c0a0314071703060d08042306190806150307020d14040f170c10080f13 61
    0x100c2c89911020b9041c55616a070020030010a02e0780303000000303214505a503d8058082ea8214207034801c88024444551401e00c0700f0020f03000305451400344941a40c0b010600700a40c0c01e01c03a0340c41c041c00b025003d000b00a06107208418004080611404c0c07894094110f03e45080d505a094415411100b84540c2c1400041c0c0313000c100d06801e55a41403105000401c041d186c07000030804502d000100906041c10003c2c0e40007400d0400250000864440c1d0784100c0700aa48094202450113807030402884154011008124060b222000c1c64101c9001449800f441d82c45035990b482c1980961300458050341805521460a55001c0c42d508804c070040e1405c510341421242c41d50354003800c1c10049428007820b40c000c50603945801344c1d032203e40188140225628140100302030358407000e0284c4000040c0c400da035520800d1110300e00392000c0700d1007000c80110b2242041084428891301c3c2000180c0c80c4240b81c009505039070b03043c218200c1c1c01d41c140c480d8079603400c00556010b40510002c000f10b50014002c139000340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 399229469 1250 399228219 399228223
    0xb0c04050114070206070b070503091b09360105180a080f030c09060d0207060b03121b03220f060201020711040203040c030b3c070f020106030602040b0406020c030f 72
    0x11104001c11042d40e40741000e01c001001806540c1c00549020954410400001e4000c002140030300390240807907521148041c001d010400140300219040708401c404125680382051030150700d14891075a10040c5185a10008410007415141c2d070706c26912001030108070248a8115001c050414014150844240d12614460300c615881441d494a00000240c0300350ba0850907141800d0f8001c210550303402d5001103010103900507040a07034540d841c15a40c401c584c80c00080041d00710005901d420704081482941d02d4991020100c581c4450000300031041401144001011003000301c40c124249490801c00c09890728003c80c4c000b28103582c030400404000c5440000c01d03a54054007101c016035290b07514509070128800e1548002c00a244010501c106180c542c90340408412598000340c0c1d04e018198001d84032b40c041e41c110402c45c40c21240c0802c0500d0302c65802000801c1c01d50001042060340c0340d4510703040360300c96070114903042004901400b02c141e06001802008004800800c40c141700409440c1d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 399230719 1250 399229469 399229487
    0x30608060f0c1c1e1a210106030206070609050f2425020606041107080f07050316110907050c1b0a0e0406020301030327090504031b0c030b0c040501 65
    0x8580c81c401003400c90034030f10014a1400b00f100004030501102d02100d10880140e440c10042c83c150a00b840c100d8003640d03030604108614060001c1035500c1d03106450006c5001c03a4200080d075881c9540790038010000d80c0380e040052039142e215002c000740036585401c0003420b142c09140c0c10f00f00341e0401c2032050800c86554000d108400c0404403444440d46541e044444102c007003082d45031400003140b040303402032038012420a206e10401da400303104180d05e00441003020320510100401c415000d10440c5c07109201407003d003800502c92411203140101a031210b2007c0302070004100c035440d92140441103a814600c05c07035500140603040c010b0916042c0c14005803542441100c2c4c44500e0144108101a9502c0407008001022031100041480c2418208a00a58401d0009030049000c120407900050141200300500c051410703054078500b414071902ca006006c024105804001d00a003200780c50542ca080d00c01c0400b44140c0d8031201c414958508175003404001403164080d10402c0c4010000d07030f41c000c541c3c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 399231969 1250 399230719 399230731
    0x6060e040f020105090a0e0f010306050a090305120a0b0618010e010503060906010809250f0f0612020d090b010603050915060102075910120501110a020a0201030608060f 74
    0x105491301481700c04a10b4481007644040c0e201408041804500082044118140da020314000d02441e6039140f001025581400f000400003441041401319601080d4410380d01301445410124800140400245058114000f10305510500e080ca0102d02d680060020a1054003130034128218508000001c00014000300814140a082c00000e108464244064580307420140c05d4150300c4c1d4161400c041a026007801480309045400101182450042c0c43d030704110f403040d035240403101c40c80f4440907021f900240c000100880d00c5141140004580300411406031049a800003100e283c100303401442d1100c0e01520042034460302080c04400c0e6404104c190544480e0300300c0c0e0701b9172030341c01070346045030820348120700782000c0f80000c0e60340c03146e0070640300c502000101c011104000c0c4510010b02c020708026504501000c0c00103030700300400b006407440601514040c03000010002c0302d08070706541030f41c8550358090041e0003175602d4104561b05441468043c100380801890940792101e081c1c02c42c60005800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 399233219 1250 399231969 399231977
    0x3050306040b0a0305060705180609090c130503011a3c1302070501140a020301062102130f050406080f0d0503131b0504060e090a06020c10090c0306060e040f0201 71
    0x21642e42600c582e4024001103901004480360b03440c0029006103950445100071001c29614100d03900145001c2d801d88000c1940101071541d60380b9040b1708031350705900ca03400e0070405904a240001307180d6800c1c4604c450b00e0700c00098610100042000304000b220110101c08003207880d007803002c030f6005490515280060a04040c030314408140d040080c0180360010320b0ba8100e40d000090450400034190803a14000c1c0e4102001c015a44a420390310090380424004c010004940c0910022a03401010420600c2e503060b2400500c5c3c0751035416142c41c07d603110740090601091203d0200301a050030301c52080203240880160024102d10007245031240200d010030000c009001c40407500051a01b20016078042c5c0c070203503440c2403030042e1b000d002c80c00401d482018403c07450400c1c0082c0e041c584030780341840f030b205d5440038016154240e030b2240001e421158090402d8403030a2640d40410301e55220300d0030068081e400300040240307580750050680c0c90039000941d0003410131052000180000110302203465090030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 399234469 1250 399233219 399233231
    0x30a0e0909070506040f08010617060403031d0303090d0e03010605090a0b0120060405010c110604031404080d02030408010f090b010b0c01090606090506090604111b0106240215040305030604 83
    0x118842c07514080ea0005603105100040015140851501903c2210103000007030101e5035a803402074401c604d252290503151703001030000400091007a400346104a001840300150100f4081125295800890b8080159406070080d84141d0382c00c004400e1001c4800c0300240b1400342030102192100c0e40c0940b80903901c5455213a0101540c4c010015810b018030700c03015504150031400c4801d075698800b81d030241d0b8603500e0030030f090552601c514426a410400032004045a0711030341d500b10b952686807079107014540c600303010208410405000d1160b98440550056850380e0924000354215029002811919440c000c01103000034120400300341110810380c0c5150b1115030543c00103000d440c0303240c0008e0140303141c408080703482051644600c2c0030b0380040e6070074882d6039108010701044a0041c29504078420041c0402c41f090036a0884855207224240300100e403603a601c008201c5908810401003103211a00f0722282800f40d4108441c0022004212480f03e00f42460b4601400511018124500403501d0341 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 399235719 1250 399234469 399234481
    0xa0b0418150302040212070e04020f071e380727091404060f0501051302160b090307020102060a11040306020906070c0e06040c0806060f1b0d03050106030b03030a0e09 73
    0x4402070055801600c29552074804012441420500712081c80c089410350307a00c3e50307490600744241c4410100c1140d4040c0380c600d49841380b04000c88a01c1c184c00e01014a07001540019404018068a140c041500f182030014010310203008502043c81c2d0300303d564115800c01c49106d502078a0705141510a103418007480710ba00c911007504d05000d8200321141d0f403c00b94800f07e92241100013520482c000c400410030249a61a1b0500340c4100b0f2050540c042c0d48100d44194403401e540c000d1101c054112603a441d69186641c40300c00d440e60880d210456038001103419004d43d40c040c400f1690080c1a070347c04000c0d56140030030082d854006c074040640201d60201d508056506c071314003200d0386030303401a03162101c00e540c1e090f1804112800b181c8103802142444c03101e02c80140100100f9001d80c000030056401e2800d1483c4440701e980041d02c261400e840b000c0502c244c0401c00b48080440c00343c40380d401048039030501d003003e41036440c4405020b029502c10480b12100560100c0d408203035070021511603000c0c0c1c940d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 399236969 1250 399235719 399235751
    0x110315060d0e030415030903120c0e03100f050f0f07120908220b0405061605010b1008040b070908060f101505180d0c1505040b03090604020a0b0418 65
    0x201a0100c50900d0140b911003004400000741c01200d085914441c425001c8000442c142c0fa502c0c28001c003c01d562406004c0081090742200d034150380706107400c0c0909400080000e02d481c0348030241308141030352074000094111903406619071011841a500406040061440d568114024209020090322918070304103486150000c03070342145c1000c041c1c1e80741c10342c0700300c06c3c1200502c4905c0070308180021240050300c1103081041d242140c000510890806200000c1001744007006070048030306560703070b0f800039145599201442a481043e41d40d50459451b092070300380b40c0c01700058091428048440010411010300140090744200360b1071603120b007902c800e030000301d00a0541d0012b02001c01141c0a114465a001c005032100748083c0200112440c80700090001807040718a0103800305542401c2030002c7c1c0d001c842403100121080c40c0c000c0c507150351212400c809d13400550762411250001c00612056140840a000107031200811852405191100c8003586035120800d05107415101ca0107603405141d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 399238219 1250 399236969 399236977
    0xb13020f040218130c1b0602090303040609060e060711040209040b030f0a0201230702060a0e0d0c0302040f060b03161e1709060714030411040e07061211031506 70
    0x6841903450f005460305101da2a03401d02c0d0042d020b03140549040051155170f000760014011540c0303c600200c1c807454800c00694144940580c7d0242d000c0180041c903850070401000200303d04d030b542c0c42c4814246080100707440b001265103881104140440b002180c0e008950743c2500714100c0300181c0d0348071841c000c5805092026003c59050244000000100b41c0c00f09038041614401d1380c0301d451400740e51105904092080460001c6408140040c00060a1200040110a8042c00d01c1c000c50200700000500b0300007140002c030784900c1c0d072030b03820021401c15024408960041e524240842401c0186903141400000c7c441054215180c000156030b9018507140c104944105904150280d40000094230201310480f5070401d01200701c00060030b81201180b0f0314000c110765a90080b2880800d0005c6140c1e400150045e14001c000017408800c41d941c9104108207064254081c10985140c40c0300600012100e411a0060354200401e07070702c603424081c048039801500f42c01d105004000c1100451342c1b40c02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 399239469 1250 399238219 399238249
    0x30a0e0109030908010b0102190209100f2903070c02060d090506131a01030b010909060609021303050f0a0c090504060209060d0b03060c04080d030b042c0c0d0b1302 72
    0x441c1c40540340c241070b0720081c0c000a80307024400901803084030300c004a0ba900d00d0301c1c0031441e1001d00d00700710000500e0030151040e00051461a800210343d1100c108c01c80040155000b800d03940d11403482c10101210000002c01d1800d03038062018250711703004001420641181c3c4009200780341c0040d1110925034143e00881070160401c0888030f081c503054540445440d950803040d17400103114100c400f01400c0308039006050700d501841507101030b464440500d01508541c0303807c03581c0640354200418600c15a1019068400c030100108041c2840d50400c54188a00e4101c441426007010a0100c08952800925011991245030000700b90783c1c0d81c07e0140007805050050b60348400000303006080a00702d078000210213502202034408685554500c4022407049101d080c1c106d030440c80c01e03228410b000380c0c48608508006000822801070b0615101c210080c007a0140400807120544c04070322000c01c015004818900303643d01002c401039034a50300b0018074024003009140e180d0403000c200b15201c3c0d18404842c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 399240719 1250 399239469 399239471
    0x315060f07081305030a0515090a0b07051207080603071215021b070504050618040c2c100815040303060302090c0c1b0a090c110a05250b030705030a0e01 67
    0x14007403801002e0742e48001c1810243c1c1c01c0d4084082140e140c00b181002a40d03074008010a1048503003610025800e100400c0c9201c28041d907400d0402147c42c00f46c0c2c07144240090b544150b5100081c1034450202d00010b400b1500300025142004050b460000d0704038242d4201c031590348010109442c00480d0140c0315100758030034500105002c84940301141489408299090070758040603100d209010440e04100c600da980401d03644134800c3c82d020301d0002950040e000d240d8a070712080c3c850402c40d0b078140702c42c844203124900c0b18a1080d0030402c255800f98004806201c0f07110818078008440381c2c1c03808142520b4910040507000f05080602940c810401580d014060040c245842c1c0038202c0c154003c0341c6100f130540540e905603006044045034203d82110f000340315041c168103106404d07008102d4a0020414014001d00078401c0100400030300d403c0902c100024020f1504041000d40c031140c49500070202044c010f8018801c4603004015290710140c940780c403a440e6690f5041080180011100301302c155 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 399241969 1250 399240719 399240727
    0x9060a050a2007122d050d0c0506070305180a0b0703180c030210051612030b032d0a14060603011103070c080d02040510030c02070f0e06040e03131508060a0303050315060f 75
    0x4040c1010320303401795401001903c145801c40c0304103948103420003c005280e60000030000b41c5e610b0180d445160400f69000c03d072100d41c1254850f05107442e1074040d0035182c0c4030311001003107a60f40d8140a00d50201d040c01420b02c7c1c0d40c102d55076940b92031444501000f4032038980d18411844242c40303142515500b101800d184164a0000e0500d0300020b028038001600207070405039907001d18200003461301401c000d25410207e183c041c204003483c10220509017650140500480c1601207014500d02040f803810150240c801c0c0d0070141b0405007142c100e416503040c0300f82c0500070058a1600140c288800503004518103641f0004c607036044000b0f1081360003883d44024001da00742e00c5280e059010b294041d0b400e408403090b145e00e440012054550502c070fa0354664400354005806401d141e0807081ca14500380d01100e00304000708098419002c440d41011050640f05401c1c4a07a0f181e00000041d0031020640ea04c004090035038500504610000704050900440200c102c24583c4907041100d512610002c4003d0712 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 399243219 1250 399241969 399242033
    0x60504140a03111b0303030a09050c060f09040b0d0201020d0c030311041203031118060730020c06090d020d0c05030d09260d08040809060a050a200712 66
    0x60340c0c201502d0500c1000350310761001184d4901441c182e00024002d60860340c90701101d02c060111103400f21214000d07201e1302c001ca42c0f903150142481052009082c1c3d21110781c9000d02040b9088a0795407403081500400d440d0250340c01080348400d0150390b2501c610030310031604081d0050030b400040340c91001c03000280064141c290703114400003503101e9602071220414040804049000b20a2101c0703a686a01c0b15801c01c5240110017815080d1045541c0c01c010341a4140f480040c6e4040a0416400248501c80c05645981404030420301c40080780d034541840f0581000c00c40c41081a40000d000711101400c15083c045800084402010010102c1d003c000d40c0c8140202161950701c80e9808219245c03c003040942402c0144403007400500e40103200031080030703904a51040c009001600c0c880e1040044840b10340fa00002081052119103880c0d0343c6808414004002c0d101f601d0005050103140c403d80e024640f808100c0700c04030b440c802074610540c423407400c0200300e1080000c1308601c480d81516100030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 399244469 1250 399243219 399243227
    0x50a0b0f0624090409060b06030a02130609242007082811131503021003020903070317090306010f061106100b070f02061c050603070b0304060504140a03 67
    0x1c45500203840c18007810a280518851103091601000781c070321070030300c410a55802d080e0b010058030707400703140003040502c402804100c0ca5132060300c1144a19800142810081002403a043d008044928004c01943d10300411407440d010b00e1024000c01c0303002100c500a480e0700c1030321040c040d8211000c0c6800c3e044c540c800281e94803051840342c01b000d40602005a20101c1800200d20503219804151020146003555201c4006640901003640b0403001102811402114031860452034034401841d24140e0550040001c265000840c460402d40100306030030454a010501034101d0340e01044d4108600c078140d4000c6c115004665895425110380e40c000600b580500080034101e80060326084203c0f0840c122082d11050101c0e070f600d040d4280d900c01081080000001408070ba40a89800007407145a94005141540484e00316071f03458851404154003042e80b813181940000d0124020040301d480c0511500685c00300034400341000e9610000502407100628403e9131080100f41950040c0c10140f42c050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 399245719 1250 399244469 399244471
    0x13050405070918020a020303040807020307030f0f11060a020c122a130504210e0a0311010206010b040510030902241209010501120b130602040f030213020304030e010804050a0b0f 78
    0x2045201c90308048150880084c822070f000241c076680918910b981d50307100c4140740d50104030203c1e0503110f20500000460354a00c046900c1300e1040004410710680390400c0c0c0001d00d0b0342d95105100e50802c210b4040120340001d0040788d4403109541c0c5092a425070022181031542045028500a0304010943d40d0250705164aa00204085991000c0d05a00c08018070417034108603802890002844000354210086c40d40343e5005e0003061030a0101802c0150200b03000880b03d034000c81d0a0161030311204650742c0c05004041c0582114a01507041615250001d030f5000021074140062581e9202c100c019515100c00c0189401a0840b641104400e000609211030b80002e071510b10b084403580206443c8501030140c141240c00f1142800728000740350300ca60040c00310150004408212a0f03c0d00e10000d102c9001420040c81d01c000005881850b40c0140b25120701c04094810311070713104204000000741c20041e041d41060007861304000c00d03925840c003240303094406003010345407142c15000c00c0240320b0640d21803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 399246969 1250 399245719 399245729
    0x907080303072607080408070f080a09140d0c0b1804020703080717090c040222091d06010807090b01020a080c07090b0405090604060c0e12060406060623130504050709 73
    0x2080c1010110003c0107070084099a0341000900244003240c042030001c0054070a90f800fa82e400c1c0c1c6000c01d0790b6074800281c1c0c032003d8500045a1105804c1003407540150b68085480c100341e40701301660750309a07a080c2282c10a4020034134a00d201003010f0000c1c09004034444207581000e802196190503a04000c2c2481d642140c40400240b000021172141060844400c5c3c0100032035002814a400b0080421002c0d40040c44000342d2115031652101c003244072460a84000c017a00d8a0002d070a84008140c07800d1003101e1914004d0070b5204030010450f050000030001d04950603110002030180359a00100d05102c400c6101030410340c4085481d420b148000711310b000450304d9070703001080040b00304000c1c002503603003c484014280c1c02800005010805c503801111079002c00c0d24003180703125602c0c0002002c4180d28441c004066110710304010030000c2c1072145001401d81810124110309100e043c1c80005e004820111a00340d0300440d40000b003d0003070300310b18090100140180710502e07010300001c2043c1101e00c98 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 399248219 1250 399246969 399247007
    0x31d130510051e102c01031b0801030f0c151101051501051e40050a03030c05030d18050c1207030303091104050421170f090708030307 59
    0x2000801d4503198500301000048080040c203d0540007041200e0f00e01c1180381c071020310007106109410241400140222501c0800082e000345144000040860f882450500c0b602080ca014103401d594111348000d0450340d01c503800f0502082240b40203001e502c1c05074040002040160b00100d50141c002480007036409085008106039034038141c000c00d41140c92250340d40444c0c2c0400c150180400ba0f2050007900d42103410103d49811040000510f041150f00000042c0d03482c1e180d6000c4400441e1040d1164105070000c41c102e0680c1002c000941c5122140720081c01c2c4000b01c0c135404100030301441941c051582544040052100d0306008580e0f404500804580701d006500c10000c15141009a0340e41010105008000d0142150303010b030001c041d441c000b5030b000c0110242105180e5a05e0046602c201e00c1403d007464465000030741c42c201805c1c1000035005002c401c001c0c0c0f01c0d9201181c031240350302036046010944140c40c1c420308c1d24280310030341c0c21400c4140800010021020780000c50803035840c480c249 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 399249469 1250 399248219 399248251
    0x10219030b0303090604060e010c05070803090a0b0405100f020a02030d0309031e021e010f020d0b0a121a0703140903130b041206020708120109060e09060f04031d1305 73
    0x800d0380301d10461003145d50119040c0030612010740724135114002e2900604001d1100c851603152149458500da002c1c101c2ca50001580e111542031070079410700206100b800340c5040505280008204078008d090103810084803103400300c0702e18400c201c8102240d0300502a43c2e4000b140110090141c0340642d820b4020484429880c00422060300300e1044201142e4040d0142a04010f074100c8040e0402c1d0090349a992a0301d001030303181040c4d1005042d0440e0761500007030310f12a07010912004140c0c0d64802402d03041c14001c0c41c070104000800e04120b1448a42d0700302030742c3d80c49410036030041542901480c1d040c6108030401c41017000001c020900d00c0c050718103c0140942c0c600600c0780c0d901c19070007031480c7c104c001401c1000088003500506601803042da21b140c03c0c103243d0b00750150418426440f68201c3c6071500700c01c12410410b13050140e00041d01001502c11850700c6a44003d00700c0c0041c10040c1040302c8407100b10b00707006000d001070344500d00040071500640881c12568018050580d040d1801c101c000e030f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 399250719 1250 399249469 399249491
    0x50f0f030121030e10090801140603060c0406080a1e050403120b0d0c120804030506090c0f0a23060c072c0721140109021210051c0606050301021903 65
    0x581c615610310f605503281114408100d01784615034444091020500080c400c0100d803001080c040d1901d10a0160701d4121a4039100042614004000d8074014090744204070501c031150b400100541d10800c4d1000110711030304030080806e06540c11900a0a025250401f80030401d40e01c00d810081c01c550840c1c040c09000518820006401c20380c1d40020444103c5110070400781241700d8240d004280103a02550409541c0d0310b541e420080c0c22120381e000c40e04440c20001041c54860400244102c0c1036038981c2203d424400410044844140080c1e805042114412540c0c0d4030101241c0d0941600429145040c0d5500780d0040b10f03880c103d100c03121410443c0142008140c42e112440e100b0b00c1035664a0070f6050710b0300111084110b403414414941501d41c66180c070a01e0114030030314020000b0200059907602c204a0350170ac005000f5081a071040407400c0c04100e135503a20220f011005030312404500c050843c07442c01100821065104a805500200e824101d9a408880304803c02d1402c2d24180614800c01d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 399251969 1250 399250719 399250769
    0x8041703150913050f160b0703050a18050a060e040b060c0601030f080d2a0905150901050d1121010e0415180602180103050c0a0e01050f0f0301 63
    0x44540780e03401c40c9145500101440e00380350342c40d000107240b0302505019040d0f8031900e007044c4160200c0c07025640041e1022040c420200c20300e6000700200d02c851800c00d0341550300109030344164440304003004100301c80710071614284109440200f1f8001d185181c059a0b901000c1d002d001c003003c00a128520b8038044610b0340c00d20308102d03116510480060605a070850b5140c48511603800c500742d4442d9024001d12034416140d00c200404020b40041305000e00d440221030010150302d2107a4201000620141041503807203880c821074600700751522003902d404800700120780d103000d0b10280144650604445240e00e02c40200280b0081c610b8604029141c50802d001c8030481001b032043d03583c6041c4000c0000d000c64007210100c025150346080202d006030022a0400d2684c6d078000058035a580d00007075400041000100c500ea03045020309041c489843c0104400b035150051403407050501000744002c032900da1003a0112401c1d62250300d030301354441c0103550002086400c00d010b00700b00085c10600c03001c0c040d619 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 399253219 1250 399251969 399251971
    0x1091a03070b0d050c120a091203090203070b1606050a0903031103070504060c0f020306042f0306041502040f0f05010f0912110a05030f03090901060c0f0b09100c08041703 75
    0x940d00515201c45000a64002d00e0010700d40310b5050801e0121411489030884501e008a01510000c200707400103081c4a0186412740f400e04041c1742c03030405c1c038000503100400d0800448401c1c1850a8848900850a0000d800d40c600001c2219240200b0004104165840492641c0c06540d0400910300c5140240200e807006482040104009000c20072540d403048600e694414419203a043c10704000d0b07804a0702c0d084083e502101e1082c91040f503440002c841a070703203e130101d0700203404442141034400460303120346000d04094018500300b40000008996901190b0040c8505207a5014880d90703116501024007540c0500ca001403044016140014410041c2d0025034002882c80404003d042c1e49010861200d110810341042d0039a43c0010141e906100414044a00101465994200070100110715505810603400d0114102c1e060b40440c1e00504142e00460303010602d02020f85540d03480600c0d004d100c1641c0c200560a001440c2038603680086090300440c400d50b454002416050124649400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 399254469 1250 399253219 399253229
    0x1b110606040903080c0c0a0206040e0a270b090f15041403040f0b090109090f02361c0b1003061a030309010f0903020402040b120a020903031b0c040501091a0307 70
    0x213081804941800c1d41030000301181c00810b42191503010003980407400c107800662142d002e0320044030401c42c111445004015030203448080c00030b0108689680a080c0360014107015003445062000101d850004003c0500301054078011030704898405030121101802c110390460320144018100301030302c800041501d0a403802600400f07a00c0c1d00b011041c0c40700c0e07008543d0407410425101000507480d8401c1c1700c1c40070407402c0000050b85e01c00108041c941000d00544c444007054a4641c000070342020b00e10030700e5869120485118400f82c880e604600041083c0b14000342c0280f00e074009000d9034040b0f0030402ca0440b8820481400030104400401403035682c859140b0760543c100f04462403070b0790310403050681b84801c01e05080c0a03482d125000311f4202c0e0001c0e0010524141c1c0020098000b11416980d5540300c58400f000f07624090700300300425100e000d052900a01030694944038540c1c40e0040c00f501c01c024002410800503903950342c412001810703401a14280c0540080002c404134100440c100303050720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 399255719 1250 399254469 399254477
    0x7080a120c030c1104090b070906021204050d0314071202030a030b01020f0d03020a0516050a062f210403030b090c0405030a12200d08060d0f0b0403031b110606040903 73
    0x10310036490303591100b4840d040103540159240b00d6540040c0741e50341f5880c042c0695940d0841b0301e900b0120064074000c0c031075040c2f284001e814002007181e907551480c059544d541c0b40c07401c0000d005100b165114203000d07040000704000703254490380c010035034004054000881255414410f1403000390045e40c44614401c40700e1010f4200b84880c00031940079800901000300b0a01d0000d107040000301c0c5100342d400c07420700e0449003a002280c40b442400801c0c0107070044120040503502d9003860703a408240800d400c20250b21240b0002003035000105403848000e1101084182350700381d2610b020714005008101030b401c6288030f4141d400c00305070b082410805035016188054000c0490402c2c645540c41c20000007211030041001c00c901c20400411041c14038604103080d2001400e04211120015080f81c3c0020b0a0600a0140e01d904102040c0036003030120003160406040c100c02d45560908030090700c0002551401c12199010320800c6a5210380e01d2a0303202907000a5594a48450301044143c03548954050001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 399256969 1250 399255719 399255737
    0x8130e0903030612070807081606140415030902060703030b09010b0c0a02010302070c0f031401051b0703030207020312041d06180610020309130204081006150f0e0307080a120c03 78
    0x4c1c242030342c40d9100c144844003100c2615035076045035807900c4001d401240b002e4102812380308000d40c1d012034583c040d2401d41410307802951f0748440c280b0503000b41d1054000a0709113407030402d07596000341d0000141a801614290340c5429600340580501050101680120143c5d00000741c03542001d81620a145603003405080500302c681c00440103900015801c1c0d4012800581c0000e4040310a0000d01c0198801e2451408018407000d85908550004107080c010358201076601034140c0c4407200f00d80c400c5501d4240140c4469040c00817078a05003c00800881e0420001360105040b0364141d04201c054040035288149a5100340a1101c0b521043d20b600c042c0300c0308400410a42d00d0445200d07100346c00c5070310482e03061200b0300000800700c103503181801301d1060340041c040c4220f00040c0700441c2c02c0c1100340e009101642c40d0850b180200304010f0041c0c0d00300400403c0b0250428810104000d101c0c074010200c0f82c200c0c1d02e941006860350b1003184c0803101d01440d40280b05240b0301a540d100c24007a0152210460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 399258219 1250 399256969 399256981
    0x801060302071b0e0405100506060901030c17010609052b0807031115040b0108060f0a24081b0a0f0b1b0616020d021516020c0306010308130e090303 65
    0x80c2d048000e08036000e6030750b002c0ba1003140c07040b0040c101c0241030400c03000603942068109a4213000710001003810f40350a1204009240c0c541e41c08a40f4403402c20319000a1044041c01c08503123510ba400d007000381c16400b945c0000f41655100701898244c60b01224229001c1d07040741081c41c1c40c0c80c0440c2403070201c95101c0702c940c804241340b0030180c9100341c003071b00b004e44c40000c001c1c51040c2041700d82c0900c403004603c079205220502a204c04005d014290640040001e410181700c1e01007200c1c0c00403c4818065111034400d051302600b20409001130515041e12070f00c49481c0d4208076200d0f01043c203845101c503640e940c900303640e01e0a00c204004603000090b68880f0036040803480300701075201b84105030211f609034610080d00a4100403291007840702042201c2d020b2240b40c1c1c004e0415220001c030b1030843d400340761501d1980001c0a509504881e8010040e06040c0414101b0b0b800c010104000960600540303000200740b180d2503005003504400540303040d900984070505c056008100342c03034486440c4c0c03040c000110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 399259469 1250 399258219 399258221
    0x30311030913090204150306060905010f080a0212120a0306031a10140312070b040b2503090c03050d0206070e04090809190b0c010b1c120f030f02360108010603 70
    0x19180085d1010a0440c500e07805d116040702d0760341c421141107654200c1000b1034000d5104140c00b5150011032030310348034540b0740800d54601c0d00405c081c0c45030b01401d5500000c810304229600803440e900800300d4a4011703140001c1c00814980c8000d5800c120000e15414104605180541c03140d40300c2d04451441c00d040c898040708010941c0304064042c810201141405000c5202400f0014810385e00c203003075843c1c6860300030301d280307000b030b082c4031084600c01d0070103701e01140009445940a54580013569441e03070b04100d00352442c60303800030b480e5000310781550240c41d501050700d0b0710508240e258185240790480603c0f04446010741c0141c401101481702c6119131400c608120050b9130021104640a512000c185516a100d01446078440e03540b2050082181025042e450b40c1182c4071000d00e038400382c1610341062010905150404000e1224036030390416000c1d920800c0308641c402411500e45e0821509840a40040c181e100411010400200c00b00400040d5801c41f141040e520f2034181e91030010103038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 399260719 1250 399259469 399259481
    0x12060b0a050612070315030c180903051b070b0a08041b0305060106111f0204090c080c03040209060d0b01060c0201090e270a08030a05010306110c031c0204030f0c030311030913 77
    0x1804142e1a18401c0485210180c5920040c50044211540e00b91901c040c500f07a129044401c1c106070781c01c0400c01c4000c0cd42080a40380311020712a00b0a8a00e5030750a2031905004d503d030000040759070003251500e1314960150b82075104502c11001000200c40711500e0045254641c8002070951b402000103201145c070075907280c0a8114950100c4101d52440c046c4540ca03a1100b002001844d503001c1420444010140100c4418403520300b000c01132400d0850a071480c4c1d100041029000c0c0c10b208001c551991234074ad54030803020307401800212041d611a2001016840d622130140d000407060040490004408240e0718050044201c4031304002c4c52544030901d00d03442c2403802c8801d5018516800c0049800200154841c80b038001d0b00003038a40c15071401c403084445030102d0b000002c805010080b8000710010888411000001e4050701e00000002030b0b0380a4441c5400040070058864031010400504030344a0003a24480c7e2103c68800e6442071a51b644c0c0c0c090b81c0516940181020500000520194001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 399261969 1250 399260719 399260731
    0x30f0615120d4406010e130f051b0a08060102030405041409061b0313061808070203010b0105090f0d0606080102030708070e03010203061005031f12060b0a050612 71
    0x15000001907604103640388030b409010416071900c07102d04207410f0b100c6000303040c01c61070352155003036a01004a004044245601c1d041a800d5408615260702540c419192604003c00312056120740c6601c040c081c1907040404000c4038108070200d100c041400c0e0001c44403030072544046003003541d070f00d50890780e616001d07141d103056003c10803010a50361101d00aa002c0030850003014582800c0c00b4134418030300399008012a05440d000c0d804c160440c03030300000700c0750800204880d42411907050b04080f00100342d44a00d48120850b1801e20714208036502000e0920540201d00820080792460010346103442580350459001c1c240d00c12103aa18502008414110303406114000341050319019201c0c2203a0054803200e0100301040304100310580c0c045040040e891003a4029411400c004021840100c1b403850000240000400058041c980740c3d44207803034010102d0802c605850380d03580401e001400c0325200752a481e05188071881d241c2059000201202c2d00544694a0090b14580b410400c0e1400f4201c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 399263219 1250 399261969 399261979
    0xc02120316141803070506030709060f030608160e100e01060309030c080a0207170a111c060f0605040b0306040f0303020a0c0b10170c010906031113120b06030f0615 72
    0x1840700c2801418000d4003d2070490070392500034441c43d800f01442c19069500162203101c0400c100300c0c0c42c0b0380c00042a811203140d420400040d00c140503080c0c01419040d0040442807141201012003800c01c2c418020480700b40c0e4003081e0503900d0300c21910b03040041602812058500391001000084d10940c041c0c1401806480d00e203180340001d070780d0440958414047c0c080180d203d60400e10078402c100b0810380c41600c45d60300030030b0050100c0d900c95801c0c1c440c00100b644207040140f0074400400c4000b26440c080d0340c0c0240704010840c1034400c2d100040c140c1c0d01819010b20702c5c01a005400b82400140c2c40d00442d041000d559102c202960203d000c0c0d0f00443c404d40c1008220b002a900223030b0312003d41d901580600c5103540e050390070410340c140c10b50303284900c51449034001d0041420690700200c0c11415a034803894040390603011080d03401c56a01c1068006031690a4684000800b8034078902e842c0f1405100f815440c100780c5407201055a00d03400c8030820401c581010000c100008114009240300b0900501 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 399264469 1250 399263219 399263237
    0x3120f041e0503060601111504030e09100f0602010b2407230118030c0b0402060c1615111b0406050901030303090201020d0201050c220506030108100c02120316 70
    0x850003455070000454081c007662212070a01051400b44407040d408002031915909103a50085a103503a141c00c04d1103a441038041e540403030b092600c20381d000108100054200501d5041100905040e903080d03114054448048000103e0010700c180980c400000c801070414001020180f0344038441002c00115400c81d840810010780007800c021052108400300003039020940103a1441c590035a80581000400a115010b110f00081c1e04420300324000c03900540c00800e19603640c030102d1503e2050102d180380e40e109001000004c025100380d0b00058606a08440c1000c5080607001c0d140c4500c0701411241c660002d04185495a01c0d00700d0307003106404010030100700c0c1030780c03800420220542078005a0000b911503a1100c10765030100900503500015100810181c40d16400042842c010503449600204039139401001d884103405049d005080b00420b0250781796507803102c541da90a0340e500c20582c402d0500c540021501d0010a40010000c01b5149036813450f525004910280c1340f145040c2014408152 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 399265719 1250 399264469 399264479
    0xf120b060d0903050304061515030b2d0102240c070507050d15050f06090106110309100503070f020c060912011503031d040203041104090218090601060f0e03120f04 72
    0x2000b00c0c01d5181c02510361a55904242c02d207070301600d11400550003a40c0e0000420000a400303103000d02c0350344a2034680054056a0a4009400304030030312542446240c20003100c103140141c80104d4004003001340c01315000b142c101d4025400c8011006000c900401e40800040c5404424000401c0d145205070241e9103a0750703c03400055640c0000c0390040d00c0946601214107007808181c0302d941c4c1c00808506610b250b5151290026403508014003070396081140510b00c4103000340007002030700c810440050042c803074003a0426004200303030421250600041e0480c028181824000715403c6003446000d4540e80c680b01c1d810083c042040e0341054000d070301e903590f41490f120030140703507458401440c426600c0a0310b07440402d843d682c60003824000e2620903481002407200260406030303098082c8005440102e128421400012941042c4008a03041d0060b040c04108080c400451818169101ca884d2006d900f2940d100171240c030b00a04041070b41652180f880140b000e482c90028202d24064415480e107456203070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 399266969 1250 399265719 399265721
    0x50405010b0406140a0e04021f080621070b130306090807050c0105030103031409130f05071d0a03140c06040902030415050f07111f0e060108030a0503040f0201091a0304030e010f120b060d 82
    0x52701840c001039001001e02c1140d242078080564602540300300c8000c0310b030501d000c0546400c0c0c184a409a1854006816865508854001d900858120400b08000400c60600121503440010704856500454580c454558002c0080d281030380c1d059564519134201052800321540d02c08025240e01030068810145500e4007130040e0b4007011113228001c900c07410140e401801c0320300015914407440200f5040d0182030388a403451203049036009204017104912800001d070a0800340d990f42c5030032000006002c80ea042a50300198020752003a050349070004a000740c560200c0b00140c80c03c50035502d4020110344514030500724903144050150607502c9a24540070703140d600003004c04111110075101c010581e4200410300c041070040c20264040c41c42c1a40b400c030000e01070f1100074402485294920009410359226480c02805401d0340100e00c60810748840c403d4505410407901203000030302c010854901940b040810355010021511403aaa400c12941c005001e84602008960004400d2041e10641141 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 399268219 1250 399266969 399267019
    0xa0911060a0c0c1a0906160605132105090108062d04200406051806030f0a050601030b0f042a030213080606030307030f0302070204050405010b0406140a0e0402 70
    0x546602c9060700080c5803111002c181c5512008003040a455074604030300704503044880d9018121215503440c034202d02035041400107074801802c49071a1904010401c1c01d9640c0100072240950107441c0300215001d8440d40320400604e80303031b000030814001070010794010300140e82c000e80014401d0f200d03c41c0e0b0300780e19a08054071404560400362555103294030b900300f9126641d82c2c48a540c1c409440c0d094144640d0a8a208074461142000400a4403031428a410f100c03040e400f500c0100010303620700b044000c0c1c41c0902415100d000c0401e1910000c541213600078861708007074900281c6000c64003c1032904100003401112059412501e15252103080820145c050290098660b200141ca86a000c800c1201c0c4880c1da4025405c1940f10a00303214203640d001003a544216814a41504990a00b4204901a0188020081d0014200424030080100c103402002e0b5101f03040c0e608120342959001142d894040b404460764002d218034800344002d11000c01c0c510340c41030020b01601000d02e04e142380400f009070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 399269469 1250 399268219 399268237
    0x7050a06020406030c0504081207082116030b0d0b10080f011406030d0806300c040c0f1b020609060a05030a0c0906270f1e0e010803030a091106 63
    0x7600080c1440500d0b0140b2030000701240d02c0c03500d281024240390718a59100b5064050f08000000811005c04010040c0201c601525500c03e03075031410083e01000f1320360b1140c01d07103901a4610003078070703c0001503109101d502c0f03005000515030f030481185910b405103c00700140800748082d21580d80810342d01700400080b19101c050300300028101c0300d41e0701c10341007800015040034400d1300152501d603502507005420303681000c01240c1d214541e10424800854803001d00c1514a0b80111585803603000400c0803030200c8419005480034420652001d1048178841160f8184c90003040a04207030145001900d814401c0c080c0c80134000a250070045000034034181c0040d007140c400254004100301c10f4030214000c00c0503101460604400e040d05043c2c0c0901510340c00c01a45519222040000180c0c0f4a00410900201242c000742c90380c07641c48030b0403480240c02008a0020084515400082c00640054440d040b00c07203500103141951202031229000d402490000e8510b011940c2131842243e88400050144030b03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 399270719 1250 399269469 399269471
    0x1c090f030c030b0c040501091707032307090209030a03030e12030415060603020403030c1202070f15110a0f080c0c060f0301030204051303052209060f240e04090807050a06 75
    0x9146240440f4402c200601d854045801480108081d9070800440340c00d40f07916107000950b4100124007586004000d41c4090074500c01d003504920190100c248659400d103200c02a0303010141c448000c0d10991144000d800c2c0c0503440100d40310301092180d03200c1d400d0500050140c078019460340c0315040a0b9002a541512102d0039030714403044514640c440c030700041c03031603040039810702d840c540b0083e094840458000d40b08a40943c0c1928500d4400d100910240205507400a0380c43e48424803000c0150894040d00d02040302d0050070b2603104800254000d1540e4084a5041a0b00e00d55a031240c0d290442e01000310307544111940c1d01d00310354592002c1d240038080590720030740300d42c554010071040d22006440c460600c0300040418001c680c1c004d0403a83c51000c010070816141c0d041120280d041c40103680301d41c0f4017515200011440288040500c012180110a442c0e01090b080d02040c206003504240d210201c0c030b40d41c8144d60141426009150103a0041c0307011800c18820f5204c0c00d0620010007411568a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 399271969 1250 399270719 399270743
    0x60902040b190201060605090913021003020903160f050118080615100305070806060c1504062c030a031503140106030620041403010912031401171c090f03 68
    0x462a040380b2078403480441c03009100b210b00e04a0098070501c20086410b002c2d80060000596003000c1281164903240d0207000e140307c41098090060003908118007079807080c0078101102045054489104090b41d1b104503000440c1ea160000540c1c14010ba1002e003120001007440001c1c0400040c4205807107805004100c0307c0885d040810070400030074201d80c07002418500300a200302140c1c0321040961068065981c581d6070021000c0e01403805900d0199004054810b804001c01c1142640000f1038425020000040001404684504101c45101c002c1080d6000f440035035074081c403075000703d4900c4a094199848041c0c40351140a10442c1c080503d8809a443d02070400400555105585010000c1d021802d2241d031029003480d240d1107184070b00c6000d007088041c0b1106030340d400e501441c54250322065100c090840c3d9000580580401054503040408400002840d00c215030131000d07851500502070105502e00c412802520180d2034440c3d41004403090010580000902403c0041d43c0501200e0840c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 399273219 1250 399271969 399271987
    0x40606050d0f0c410a091b02060105060703120b060309030703080114030307062c1509280f0206030c130b0403082704050a0204080d080622060902040b 66
    0x60b0300b2459000059241041c25800d240c003409065800c8030700e803003095140841c200c0202ea070800e81d102004003580800340703200002e2003c4a50b844070307e03a4820303030048032855102c3c188280e841c2e0809100b4113030000010400400000d11510b00302c4500d1036585000070f12003040740f004c00d643e900110b40d0780050350720000b00701040c1034000710864010b10415100c0300b03000060101003034890181100c0100415110ba12581d0910100418180c83e5800b4080002d1040300c007008040c0c4d02c1075049600c0190500b4a00441c9600c400810541e641810341c4c43d1811144200708911300c03041440761805e90b0f4040704010072000584c0d9403001580195007903409030751500c240f49a602c0342c405403640406074901e0300700420000070b40340d01d058070300d1150350329540654282403c0380040b120300d283c0180c0d0341c01482c103020040e11609950181c0261040001150410301e4170110070766041d075045d20340d01d900103440144070034501100d031075282407902ca00f900415030f075030380b4104d680c02d03600b0603000070720824008102954 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 399274469 1250 399273219 399273233
    0x10e1b1801030510080726010f02280503130f0f0510180203072601150e010509191e0516021207030f0e0609130b0a080a02010905040203040606050d0f 66
    0x600b04c02000c81c05980c09103041c980e581e07910f03018803900b002c80d03140a0058900301030b010020201740701540c0081c481c0141100c10030380254401e20107202c0003240c03880c00d071070480729442800c4140007058544600c3d54489080c80c803d4031001540842e803015011103600002600c0f001a01e01070703440307040208100700940b40c0031016150441d010280054004c0b0740000981da001442c5012190a00e03400b030301c0408013026400c004c03880d40741d402900d03600b80094512620400ca0180c0120381c4d04a43d0302d84141d0720b4500b040860340b81a140c51101c00d180006110b0880182da0003801030f000b504d5004800c039070301d0a901200f6968203c9105c10200c0030741e8888010107805124000840401e180c5240c5003103544d43d0b000c0d002402d0341d0080002c01601c1015406a5101e20086502482c401010201d040070640120000f808042c400c0342e010f50480440014916000542805815070503110120143c1c244400c0c04001c6d08014001c1c2da241c0d03103031440040c05403590660018840d0051458012054141c10081d07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 399275719 1250 399274469 399274471
    0x506090c0a0c080309070308071410020313060c05090a0b130b030402030706080408040f031203061502030a0507020d0218071e1b03020109140f010e010603050303010e1b18010305 78
    0x158510070031128030300a80c025090011076902c805a140c0303070b03103600305464540740d0341b504010080c00c000503041061221040308800040400d100302c4208580c011165416404191420090a184144400c1c002070b0f03603412070001001e65250580c1010203007000074841d40c1841c0d220860b40140019070003014410142c0c02009040d09090551031070809602103a0b40d080e4500c542c000b003280074004101040101000c45004100c0450028070710754507411b0414100034044000c00201f45044c00002e42e501c010070112583c4081074019505101c43c55205030b071030381d02c400c0040703910814200b403080040ea201d102800b40780d880c000030700c25189422040503000d801c048030b40400f00d410030070a0081c0326910101c0c05d8090700001070000320440ca285000c0e401340c5001038001f014403407800801d9248480002d00c040c03003000340743c0003403089082c2485854225803a40c040508160800c00042c4440c90684c4415070704480c214a07046611520100410301c00e0f084041e1803421101406580890796038980901 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 399276969 1250 399275719 399275731
    0xb030c0405070c170c0115090e0601030506070e030a020d0b070f0512190b12160b040f051011010203010e0402010801150206070311224502040803070303050609 70
    0x40000b03040c100009040305110b804020301080c00c090202c919030540c135081c2c1d01d040c5203140c028095810b200e2021701c80841a401050805807030294242d521040c0055498100c07900321015291315250014200c0d100d075200070b1b4154151090741c2c240e400503102c04031001c1c440f03400355901103024240035400400c10840041c141040040c00d2203801900c0255000e5150807918078a0159000d4801114410241c01c4d1080007540c0007682d01b820710844940444c58040700c4402c04c4104e2405a100c100d4031301213000d94001c4814951080a003400a400e1030001c24000808038180780354450100040542680d000760040d4004100f0f001c1440115600060a00e025141c03503c109460b403000c0c0310009545800091000c000c140e103801c4443d03500250b6108540700440c050340e02c00381c00d403540117401032911054030829404192003142d840c2d1103001b40030384442551040c1c04402e10303080c840240c8004264013070ba802c00115420403000a04480400c0107283e040d00c00e8401245929024040140d001d100400d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 399278219 1250 399276969 399276971
    0x14270312040b1b300f060a080f0a060b031c03020405030c01030b03190206220815070c082b05100515040b0711030d02101a090a05090f030d0b030c04 65
    0x180580210081054501e02c0c0781303400d1000a240c1d00201d014107100c006441300007a6050f86014070070460846003015220301000d844400059a48180040c0d445141002e00030a030780005801400141054100b0901d1810007005c0310f0040d0309151070f03510150485101d03480425400581006113080074007060740d80340803d08007085011107070001300b86c0740c0044104d000b1540f16001c0c0751a04540d241003d071810800c18001101c0010040d841120a50f501d9004e511040d00c5150385852440040c0030b0210720666195030703103001c514550355414003140c0002c0852004041591503006607001d10f29110303c002040000e01003a14200301c18903600c03256054001a0080703100226503281e00c103243c1c0c03c0b1012a1411440259664401d06004000300e41000c021303903060060102102c3c0450380080d586100e407041040420150b4900801c00104e220980c21254200e00c400f40024201007082d40421352241221003a1307540308045101081c110391121103e0302400307030741d0701d0050018103040028041c1014107842c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 399279469 1250 399278219 399278251
    0x313150503011a09370e090a030c11090412171b0703140705010203010302130203040320030c0d050a120204050609040209030709090b150414270312040b 67
    0x3e818100c0e161618282d203030408000660054a49400c001c0c06411100d4000020340350082180038441200701c5d40000c021032041d0320b07002c01c0d0b419400c240700c0d00a40c0888020a41d0100d196015100350344440000d840c1821385007891511a100c0d064064461486190b0341e6800c7d0000303d8000d4050100138040c403014015030010080000800c046582c9a03614140b6255184e94081c9412600003c0500c02c40504140209124041280540145050703030701c02c484804407482c0c84100a070032030008a5025000880746050001a02410340150300c2507805081628900107185206030b2400000700350a500044001428581ca241e1040700c0700103d02003000c00f9032130107240c000062898058076901501c03d035800038168505a604001c0740c0e004142c20241071201c00d005040c000350442048800c1c4602c80d8004640c0500c42ca020300c1458841e40090303403928041c0d01c801d100744c044106918503203241d1140c0406240c410305410400b1300280d407440c42028450b842e1900d080014600050030703501650301368030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 399280575 1106 399279469 399279479
    0x7020402190305010503150a021b030a0c051e1203060a0e0c03070f030615080619140301061d010b030910050403030209100e0d02130e031315050301 65
    0x20b00c0800c616a80e8606050b00c400d04c41000f00000161603000448420070781d4044c2004510b002404c42040085060b2140755611400c440400302e05420000002c0140410254490b5040c45003620f61801d49040341da6030700c092035060880c1c811341c040000380f45a1110003002d4020f14110300d410f8030364102003140c2e20403035006032140400581e00310104002a0302a0140104486a400465860314000003046078000030250039036501c5004d0341000c5400c0c028020f492009000d60040ca5007024030488105401c42c3c806074441784498a64030f07080246080d24402050440b0030707052800d035595652018540c00c200301c80b082030011501e0075060206040e40f6a000e0a4598400d6502400c050b040707d00c01d403094031804408551042c9004140070050409640c01c80182200200c0030034016030b92101d082c290f402840e90580c5003017400071f040000702032502d00425283c2407801c00c185594185 = true := by decide +kernel

theorem cover : BRFrame.Cov 399100719 399280575 := by
  have h0 := BRFrame.cov_init 399100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 399100719 ≤ n) (h2 : n < 399280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
