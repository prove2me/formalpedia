-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2444
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:04.515726+00:00
-- url     : https://prove2.me/submissions/d4f81247-4605-4127-88f5-513570bfaa55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 439388489 ≤ n < 439568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 439389739 1250 439388489 439388501
    0x60503060102060114030703060902010c0b04150b061812160f0f0603050906040605061210091a04030905130227040e0a08040b0306040e06070215010509162d03 70
    0xc00d900380e03100b6036610001c0020344141c0c5010786605800801081000445d1303617101e18900da1041c10302c18440344103a04c4500341d06008560681e1500703000c00c0180414482c44c4110304110394100c1d0700e0b03070030315500c064002940542121014000e2207920207009040100300002421640d11041c9860344036191841e0080140352880b402c09504550400820264000e0203901e105e00d031000010041a0381d5510f0348030143c1009498550003800368698108802414400c09800012100000c0360b0400c4600e40144802042c540d02104400d10f4010700c800243d00242100403103c084503480d0764000b102800d00300134401c10340120300702c0034205c8101c1b014200e112500c7d21031840031142046001035681d14030b03448d8205050000c154102c100b0050040c0c041060155804c80c0000e0301c00201807120380c001ca03150a90964450000d6845400003a520644130302140d030141005a8840c61541026803030705010618a0000ea0180612603210702e2440400c00d44800c071a060740d4010428500002c14050010300e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 439390989 1250 439389739 439389751
    0x3030c0f072105030901030f020405030114040b011a0d1104120f02131b18080a1416060818150112060506040509071701290102010506030c3304060503 66
    0x500e141d226145010000070760011680c00c60f014614049000c1c1c011002003440208036404682d0a10021071103031024030a03031800c41c0c1450882c10487c103060070070baa031060050f84400c0040c00200001e000c032041031415a91400d0000070081819107030a550354446000e190020342d084950300c3e98450a0103c4c00b284030078424003d440d1040c3c0c544500e51140182c0c0c1c2c404408080400c0d850340e8449807984640c0b802e8011201840b1140800c0703844140c00317820040070391003c0d907a40006c12198180c500040c46120700760785015820b40d00051411002a14000006005010880340c01c0a040200c94050004600040000c0c1100075207686030b4a04652440c804101a03d643d03140c4000030b070b41802c180c820540113844600003043c040e0700e4031500c5001501881c640c10095503d03031f0700d000601c8194621110300703603918001d0304c0b03c6481d21400090131a4030003000b9a2090b4810502c01c0c006031a040c914400d64440c8460301030800460841c0f0103401012103850441c6000000340000c0e00341d900001940c0949 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 439392239 1250 439390989 439391009
    0x4410c04030b090f0d110319020106030c0b0403030e13090c1707080c2809050108030a030507080712052d010602070609081f090204020a0206040b0112050c040b03030c0f07 75
    0x244071051601c0c0e451361181d89022039588030302c02c01c80103540990048000300c461b441c1224031b0102247c00c00900c9240c03452031030300540c3d1901814010410082c0a007c050078100403080c0c00c191958500901c030481d00003101c1e008038202004040c6203040c9420003401d141d00003600d1000c42e590381d10722010000e040301514149000303c681c04905840089040914584003d0040f4101c0120f00810000c02034000c2101d2040c0000c04070005884540e801454000c20000b070107562034410b81c80000d01601c10050070070f030801840c1c0702000011900076a0540106140c00000100d5941c0c1d0591541d0314030007000c850b00600c515040740c1004a080c0031446050306d0855003619901503841d4801e481102c1c0c3c0340a666030f0f5422141c1030000304601008501003032424804082403481454004c10300701c0c0c1c801006540103030170400c100800c1c800501821401080010031400ea4191151142e80d1030702c01d240d112922503901c0741c811500a940401c1038800e2018040305440e6051515200c450743c9401d54800e13030b4041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 439393489 1250 439392239 439392241
    0x308010503161509150c060606110a030c140102040306020d060e0408070f062007170c15040206120f0901050a0c0c0308040219061d04410c04030b 64
    0x1410302150740004070500c0d01100e0121810f140184010f2058401008200000c05000040b200d510380c0f0058801403040c1c88091000b000c50900c602910020b4110700306100e48a0b02004502030009000c1e0038054152520900d00c86561130003800109084209120560003ca008014000309a00a1070400c00c404003c20280340e441c424020181300c12074018003034020074080200403c0040a21720b041c188141c2c00010b280c03000078003032008801841540d003140c410104040040100114640b1a540d0b01d40700800d080c21040285c0d02c2e500d42000c074101304c06124010218003107441700401e076801403202040c03c1780b00345071000780b42c00c01441c105c0d1403203400e6090101160f4009654811400511000e669524000d2203a44007550b890501402c201d8001c7c2c9452210000020031200d104041e00c219510520800e480080703003201402400f940c80e00c100c1c504002004030503070303040f01c410003030600040c507405507074010b42e00011880c0c003150240b1820440348100413003140410010419203118a10000311 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 439394739 1250 439393489 439393499
    0x100804060e010e2406101803060501091d010e060601051c05070f021501030f062703080106020f07081c0c12050d050a02090d031202071b051002030a0f031503120c030801 74
    0x84c1920031303a08aa040704802c1003140314248a614900452061084844030099480d81c4450031507000364855040d082c1c0d00c0844184502e0382c00c5564004c10032101c000e21004180301e00280d11a907000d450b150511600260102003200156050500504403c1c1d0030485450a1301014088120b44000540140030ba038480000001205030314a0603240c10510b4224086c00030745e500001007150340350080c03c800309100680c9400d2072036030340301000b58800d43d80c5c1465945004406803400400090b0b40480303400c940c80a0190290024034500101e00c08110f04080403000e02059404032103852f40604000402c5540e085829081001031101402840f001c1010380d8440500030308a000c0d09010560004440542d440031034482d00c14914480d014480041c0741003980d40e90742c3c1420180d00324108a81441910401c80707490825003c50821500f400a90b00d0103101541c0100001236080c540428140c7d903514520100031304e02c14a101441c0c1c0104200200c2c58080d034041c1040780781c48401c40c0050741010022407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 439395989 1250 439394739 439394803
    0xa0f0905010f0b1c0e2a0f03060a09060e060112050c090103030c151e0510060516030f020c04020a050d050703020406021002090607020a0e01030311030702100804060e010e 75
    0x20844042907441401c14030301855280143d0000341c135140c1559100c030000c204203401406125400389a8a1107240fa1003100200140d0004290800521902c0341484061040c2c07404140c01d60320420400b0001409104c601e0120020501400e10300c005202d10000401d06002e402801c240e0a40518111803040c81d0f5541003048210003400f009000078204a40200020b007840324942200314007100201b2112805c2540349083d0408400383d9244540700c109022640f43c010b40800c000c2c00702403500b64640908001403109041d2004002010004080308680d6524828400b500d0648402401503641d5007144000915981018501c9808980f07080b012400b40c0d070080c03080714125056500903080c4c0300c1e00860418029007041034410340004041055100696483c00030b500a402041c966040307950650400801425003150b401031558010007030740025a484003c0600b030b904481c6007500d01d0341d9892070410301034400d2804038170581d804c01c901803d69103001701e004186180ca00d4200400302c4d0268031810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 439397239 1250 439395989 439396019
    0xc03080a0b060d02031801020f071502090607081e0d02040509100305100c030902040905030703080c030c09060c0a1b05010f030519091b03081b03090906120109020a0f090501 76
    0x581c0440100070b40c3c40302c0c01c0e103a0059079001c1841040c294540c01043c09913130036640700501c8011407440c000f50900c100000041c00481000f2251011400c00000c140842c000c3d215003c0050200e883c0402e0724545420462107048045c10303021082d649681224402d08060b42090080b0341c803030f01d985000240204598038800040740d400c90028000c1c2900c20518100030b006016549040580362180034000d600c5031701a0300c2e83e0620440c0203590b00c000e142401412000090041c06200e43c1c20018408030309904410394489500032200c0c2640c800540600c0c0b8509000f00c4402081104207142c8583c1e118811811401107c07001c2c0c913046c1a541005000324219502102d0119610340c003641d121400103000d602c40e0440610800b2032100e0308030011540f4002c118981d01c22101014002800e42d80c403c007c058030001000140c008605140300100000c220440040c4014000d0503101c00c601d00001c3c00350840546a600a0440005e40380c840d00480c0c02c00d121800303445102c034105800021a20003074241d003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 439398489 1250 439397239 439397261
    0xf0708390f1c09080312010e0c0f090f041409060106030b0607031e02031e040f1205100f021621050408150601050f03010605210907030f0204110a0c03080a 68
    0x16204a03a50648401d8000001c14500b00801002103c0401d080200b000200b100b0360110341920700c95031400100307038480c5400400960140303100b8808140b200328032030140c070050361084a40c0250300b800b039401b0400a0561203880b581480444080c03000098001c682035043c1c4a840e0340030322007030a041e030070f00c051f511403294014002007828925620f40301716144442e50105403881a00c2c0340a810702603007080c1c0c0a181a07a5154504001010401da03440c1c0704944005000e0300016511400c441d840e495120b40700c8001d8640c035543c42c3c501c210350300e40496044452001c40c101242401010310f080c511041e01412030541750300308026003a08178460141054070100e0348548010050401e1074042c5c600c0e6220060040c5c0d05000d424801c54044203c50000f07113000e401d030396840c0350f2500c2450508000301c0c8103405a1109408465042c880100c0d4040b0710141920b40201012181130a14030200b40108105840c120158401040456030154403000314094a40a503644011030384032181034500700c0d0b006400c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 439399739 1250 439398489 439398493
    0x906050702031e070204020d0203071e020d050a0e040603080d0c020705180c0a020c0303070b091608073501142202010c06090203010608030d11040b0f0708390f 70
    0x104440f0040c1c400014103440788060000760500e500c1d8a401d0301a6001943c20801203407600020403840024031500e0000c0c103d0317510041c80030652580c800341c850302c00d5070909010000c103007040850035101d0341c0040c802141d214035072541d217224003041ca40c000e11304408154014000d184000034603107010095021108010f08041103141c48980000c20306500a00040c400d42c041c18801d106190350600103040640d010780d11070381503494003002c100d007000144920041040d0040c002032241d120006004800c0d920042d10007825440050100c4c40070a46400914540c00c14003140001d000b10103401c6415194905c000030506078448000c41c1502022001007214020a420040c1c0301542c0300d0000700a03000c1c02003000240109040d0003203425101680c209611542c0009042c6013680e0f120b100e01101d24500c503104604083c00d0050180281c407c05040700b0100102060110901c6183e10803103d46480c220004070100700c680c01c80c0e00c8402c01e00450750b0403007240c110040d000ba440200c3d8551080310b031100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 439400989 1250 439399739 439399777
    0x327030d0e06060a211b0911190e010903020901170d0f0507170409050f07021b15070512030a06030c0e011215110a02031c14040f03021f090605070203 66
    0x440703140d0900c1c0d00a002c0184030314a0b10801080d05100000b040b21024004006c90600b001210429610054607408a210081040311483e60301f07802c0c5028542c400d4501803500c8542880105d85610700c43d007010754000c007064000a41c1d403041285409154020905580606110000a840414155510001250042102d00d000440c0d03852245004103808000506081e1200c00850031200c1c03c5401416054960082c81601a010401d00c4400e91129a0304240e06c261240030801c60410740c160001800300100707581003009024816000120070a803d02c58480c43c100c2c3c0c0c20303406000c0f24802a01d0442c1c90140208100c07145d10203517410789a001c0c503101005917407130b507070102d80780b145d8071991480641e1000c8807410f40078418000d200d040080d034015602d8001c84005e182d0741c2804500410f000601e041001e0400580404090f030f446070b00540b00c0281c1c0032242c28140d0034104450a9038060f050260f004841c140000e500008034a8002e2a0800484d40c4410080e6540d1003840810300240407508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 439402239 1250 439400989 439400999
    0x14010e0912160807030c02031b0a0e1512070e0c0711120a020301230a05010f03120203090a0f09050a050601051603020c060d06081203061003020327030d0e06060a 71
    0x3400030080c002650102c1030854001da150081c0503048590100c1c0010310341191041035203410071518549403110b40e000b98103003402e0000201e005006103d02000c14034608005040c40d05000e006410204000d800c500f009102540789603180c501c6401080e40d00c200384c034045121101000706072100242d2020042c01400300d12020844000048448e84200c0c1c8140d80b00200103841c280600310751803040d458403103880410b24405289250005200300000c07407504004004440031080000203c07500070f0500c503404c805e1014103c4c110301c58006030603041148242c000801480381110b50040b04e415030405c210a8861951810a8880941e8564002071040c080b2810400100030b080143c20f11038012505150380440110300c564022189030040b09540300420840705009000c500d181e90745104e0000e285142c4040010031040c2d40c90b1440c0100340d030110010354185191400400c1050114030b00c841d01030546422607649038041104013140c5e604000508418907000101d20307025a40042c0320203882070400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 439403489 1250 439402239 439402273
    0x90b060f03032101090c110a0201050f120910110a0f0509030a05060f040203240106200105090a050715090b07050102090604032907082404020c0114010e09 68
    0x8003a02a6050104010b14000a01846120b980c01e05020401400641c50080f107402180c4a00c070303400090007070030742002c60b01b04004240d501c20a582402c140c1e07186d0051a06d1464070740621035041848054050900c400c1100000c1c03108000400c810040c41610524601e0b4900e50182c00541c0d400f1641502c600107009016801500d8089000341c12142501c41c1a2075803442c142040d00c0104020f402c1030140015824280150803c1c5074900d548100000b0840044840c0c0032014810641003041d5001c041c03420b04a50003c0c0c0c00c0010a01d0024407070b80c241014200d484a4100400315814030840000142d0b1405d28124000c250380350b9216506203a141031214150342d8040c030707000c413201d55007008500280c1d9106005400510301800b41d00180d41341c070072000d940c0c8008840c809048000340e2b80801c80078540c052886035009401c8070421405001843c213480700d0030307900fa000d10f81c002c0c001f06100443d0481540b0001c290001c1146244441c2d07640d0096106011080d01d00500540084c3d403070f20b00101c05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 439404739 1250 439403489 439403509
    0x609010c050c03010c030b1008010b0f0d0b0d030201150503160b030a0204091d1005101701141e130308040f0f0b0f010303020c03070f090c030204030206041d0a090b06 73
    0x50019070320110702c290002400c41e11250450408250b0b6010003620038200303040c40200d07500071801c0c400d29035414010709010760301520302e40000644000070200d800503c0e91704442c91a42c0090720182c55031600e4034000e40a000c08000c0359074806010580043c081c980010f5460030390b51a803a904000707604102100002d41e1000f13101c070448603000c00000071212242c0c4903001c028881ca803040c005040780740e003180c1e040c5841c241c242c0520604180511070742c9403038108032034101c0d44c103000c9600044c600440c2040c003400d52210315010440c021820050803000e01608148a4640001c1c3c00c2890f43c0c1e100300741140e41c628034102030001450903000800056029801060141c01031400c0c6e00b450100d40d540c074803042c100700c03001c1007600c070002c00400070180c040100c5000140200c015002c85818016a8900520b05102d42110151180742011646000e42c1c104c5001d0343e0064651552180c850b80490403004915004a2080d0b01d140009281405e880c45081c15040d448004080c3c652604410031a0a001d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 439405989 1250 439404739 439404743
    0x150b070f050d021c08010501021b0409060609050702101b050304050307050102030405031810021c05091309020109081f0c110105070210061d01182705010b0f0609010c 73
    0x1800480e0041081040b8076400c29500e540101079003010600340031296600c408480003030090040c0107100c240c0e008280c10040d510240702c003040300c010b00800540036244090024191518182003c82c0c4c41505411091203162141c0071075480c1503090746010110b0780c541a810680c10920030741c180d041445000159001401401102d0403c9050b031500b500321303401030320200e0303056000054400d621003071010050340e03081701110f20704040402100040c1d12030b22018556038031009000d000c00d5405014005565136090301174021032036a54004983c0c00206a245016404200007000018807400002402c03058024000c40130005c108001e0f08450240c1050700d419403cbc0310017070390203403044402482018810100e6600600b41091141100000c80d401604507440d2380000d80d452440c06000050701c5811904c2041ca0f680801c1120020358004103c0f40b0030110001d07103c3d020f0520104081c05010800c5030140001300840c2d5640d00801203407100c2094007030342080c000d20503000c40e0360203101d5815501d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 439407239 1250 439405989 439406003
    0x30a1e02011b0305011415070303050c1314130b060d090203070e0703200a0203070305090406030503030403020a110420070320010f05130b010512070f0303080a0f150b07 74
    0x200258001101000d02c0128000000e50341e400411610091100d0008607031429030f06101556084084401c240c4502c080180038161034402280c6401f40880884240c40424495515266141c100300c2074400361269080d841498051140440c10403d4840e001c540000103015904e80517140c20460f0140a8000307090f82c0c0340c003c4590008440d115a554a0720907403040e0390000e00361441101020400d1018013003040218420f200e05241f05030000708a0309000d4040c10005d40300c0016a0006014200d00c2d00000c00601011003804205900042c060745002d00c02c83c40001d540300301c0d1087c8412124142140d010707811003e02c002021002c1c0384010001c181c02484d140000310029601c44051105956a2030381070fa55458103150041020721510303800c580e8403403d0614805054440001ca4401802250701c28108002052031240080000000070304201c060001c1907650303400d02404a00b4100d840000c9070f414020001410364a0307101d8090950481588008028281000141640c1104004880c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 439408489 1250 439407239 439407251
    0x12010f05130201110a1515030c06051201170601090e010b0a14010f0215180316080405040c1e08150303040b0406032306040504080702091017030a1e0201 67
    0x62110380a100d10611200d003408207140000c0c4001003000782103200000f1307990410a810000200b4420030842c1200b48081c2c00301d011412076001400c9811180d000a01c143c01c0c2580c00143d45400c0f502801c41c440040380c3c03c0c801a030b41c821b0841d44d0550300c0c20051031142c000400502c000c1d00d0941c442c0d45441d007003a00004000c0021000700e0720f03480c0a90030281d82e00c610003c00844640c1e01c0956a015807840e44040d110b00c00152101550f00352024140410f00d800c038801c413004c82c0c40d080064502650781090700300d041203954103058419500c580200d03801942008498061a0300440700c0c00c0c0c3c0d0444d40030003c006506800030440701c062000d0300401c89844d00c0054841300d660100b01034005401e021307a6a50741d4504d0404094210383c9420b822200d0405402007102d8807500b030360140c940c010810340c0c021880d0b65861601c2c008600c10318100962155801c014800b100381c04240300c00996840c81c4a008060b18100c8401d0fa0b03d000d4101108005050302d0703010458040388074814a24160680000b14407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 439409739 1250 439408489 439408511
    0xf06060313060207082109061807031214070b040b0f010501080a0b010e061209010c110312040303020403061a010801060203090321040801050f15011404090b010c0519170301141201 79
    0x2c240c046d4903140d01c150000740d05004030343c5820301803260800c0034196100b0085840401240e22482e1911019101c10700b140d2403d010540142000c814a918220006a5954484c6441c0d42002020741c3e081d200444403900145100d080240958141d88050310707a03103902e0f611400f0081c042c03d0414200c504010000350a0442030312004080d000150705020b5041c030914010342a0b6085640100c006820084903040c0194030250100480b11065680c2c4a0030405030340740c2c1402d60280c802e5034001440c3c90f1900c0b10200703d92031580034018240301d00766210b80d0b00b40da0301e5408994a01401c1c07034442c1c1c160003080c59030401070a28007101c8900d1250110460810350f441103e1400c4072401c41d0000324403544001000396495404200c10042d10003400d01c82c1140c400c0400c0c1c00705a00480c090b174004581d4603100e03050301d0b0b0300812440c84110f51110032641c10704000d00449070382000658044502c110700000c03447c001283e02d02528180d400e41d001d120a01281d020030012603c0c1a44042e00702d956803040c2a501c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 439410989 1250 439409739 439409767
    0x9050f040e0f0a020103050610200c06070303060305010e1f02090a1a03011703160303020d180c08070f0305031801140a02150a14060609060903010e01050f0606031306020708 76
    0x920780b0600026000d00f110350b00014040da800242070710b01c00d000e00003074101c01c0ca401512221b2424100d0440f41c4030741c0000d1070583d203070944841c85a54000c801040729020076506810420036030b031290009124003c844104241d40d140000c61407101e140740030400041c01d64045d03000d8400140d004200e4652603580d00e030030b00840c0455452300c0903c2c4000200600000e11020102005103941c9170046d450700d24001d054403c1c0c03420940300141016000922100e00c0402c513005004049401403c078807980c20980b40c0400004942d2040c0310880c011041d00240001113240d10408030382c2c00401070741c60700c8070064898455940b01404503041c40300710390f21807800300c030707001c01a203ca8043d6070010107010a0000c180300014034000d0800311020704050342d154035810381011403a084407043d0740307094031110310400064040c0140d02c115505986444020301e000401508000c0c0a00d40401001c5050348940b81481104c3c031044075050a070ba0204010f402c0003070450350003000114004d660071400e094101c0135400b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 439412239 1250 439410989 439411003
    0x80c150306101209022e0c2f032517070506030912070f03080a0b030307030305090f0f100608010c02060c0901050403200f06031003020d060f02030711011b09050f040e 73
    0x80011b200880d0400c0c0b25843e000010034121504203c01d02c0d601030780e02c1c01c444a207890b8103000d9506140003901c1c8013014408450368090402010344070a5001200000c0360103011090f51200103400510002300d10484c442c0e19000c02510402800600b81400c1c14003003983e0014120409a10070b10003a82e4000e0b400e000500b42180c0703c0c100f440e440004078140102214002b80815480701d1405960190380d42c0d0010440d020f050303142c02d0102d6981d548210950604001021000c0b56008041401c4101500420801d4162100050400086d6214104107089498014004d000341e400640469914142000600b0364003505150461030a80c07a60360b001090038031801000140c00d191260040946086c6003411103000d0142c400904514001c0b40380e4481c580e040c84083c1c02254110522814080c054004010501c41c10400395520300307140400400030b5442035000e1103554a030920a020720075005110941081c25581c3d8130440c0d030704050402601001c00580300e84d119544026803041040144842 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 439413489 1250 439412239 439412269
    0x31f060909050f0606091e1002150c0c030307081504020a0509011d09130201030f020c0c0a060504030804090c02010e0a0506070908190308060a030c080c15030610120902 74
    0x31412540c40c00700403005a0b42c01410309440b070301c081810400381e62100e105592003180111000d0034449280c01e1343c3e0035a45200907010381c01100881111103202e400280c0d61114180d4486060b074165124040c00c10180150152000950400c10100b10410321610a041e040400340f0b28140340c1c500040009803c80e80540c030440081a40454020003a68010320b00342c050342c000560b911030040031400013580e22403004042072001140c001d5440c041d64465401500550107034031046581c2c0080c0c0000583c0c80e8a040b119501c60056140c001c10441d10510548040341c1d80144080e0400b4148245800500041401c26085650b110104042040104404582140104050038060901940c01808140160000c91030340e803107006a40c28203280008500700036505882c207201d086e100c4000040c2031401d69880940100f030301c00c4000c2000307640030400c4440140110b440851034081c00d504e584003400111406135109424001c4403c0290084415500e10b4212550020360302e080c6d40c2c0068044c600d01901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 439414739 1250 439413489 439413497
    0x70201170112030f0c0c090509010f0f050103050c150a08070c021806040c0507031b02121f1a0f09060415080601080c03030408060c0d020403120e010906091802031f06 73
    0x100e541416000101c8260250040c43c00240345203694075240c500108922480d0b1240b40d680c00000c9c01d045007944082c0300020841405d1028903071444149000e8030003030109070303081d01608a4486052610b0500411203100031112181858010035040d82c580780c0003003982c820300c042e081c032000040e5110310007202d5001043d088100d50f03040050078001101e81c0152240c0a1002c01c00c20b82c40401d401c1881c50418082502400039aa8103500c0400c41c48545042e00c40001d11035480302d0f0030003400703001284200c821690010050540c00d018058100025415900c2e00107454000403201c60a115100941c45030003c2c002203000d031844840e041e5007403e5903001201c80e41080d00103100e0300005000c060301c0f0031400c40065040c64103107901540c407450003a021210000c2d0004400d040d0a40c00d4060350004c5400c5904180381c1c0faa00d140140c03070a01d040b042180000d035181000318516004c0c03169041561542c820400c2c03c0340041480c4c000a500c040d046010789822403281c146400d00c110710000142034280c3e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 439415989 1250 439414739 439414769
    0x2a0c0a0308070906120216080f0703030c0e090f06030f0609011418120310090c030f0510260102070c030f12020c10030f0e0a2a050d06020702011701 65
    0xc00410040016010108106040704100f01290b4400039409025100960041e40c414001c4948440482d08290041038500040740003a108010000a450014002d80f401c0c07101e90700101d0202c4404da42048075a500c141c540000c6901d04c580d070f009960740041c025044a003201c2e010601c2e5031501c00119001e401d107a4550000b02c000d407600c404000e42102e441010000403100c00c40206466180b6041441d03407590700400040c03182c0b1384080c41c40b03004200310300c0204080c0c82c480000402414032040070303641071414007004c6810301c00b1514094048942103d14206100761000007407d80318410608014559024082d90340400d691440703c01c01076110710340d159528941d91500f031621804916041c0b0a640003170200c0d454070b031100c440202c0c20700d0940c0303000070752454a140780c60010800c3c10065049841607540c178404004402e00443c3e4040141490714110702000c83d810003007001d150103442d40141034240100001007407a00030304140e520504007160a40158480f02007140401d034007800320320038811 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 439417239 1250 439415989 439415993
    0x200a110418081309050c030103020d030c080a030f1d0a020906010c02030f010b010305160801050105163306030f0b04060b0904110a06080405210d061e1202092a0c0a 72
    0x5040014940c4c0c4000340810725002e40c00070310b2408144000390041061035141d174101031240f00041803940e440040140c2314407900e58001d0003031443c0600c0700a01d0345000c6c10f00f0000c01c095074034034001d002c00d14028003c06010b542030004c0101b0280100c1d06105030b4441103401039038180150b4503c24010800001c895260320001401d80790702501030b004102c810405a116640d001c4180ca05607942801c0c0346558012121045044e820300c10301c06001c0c6a00081000c0e280903421101e150100f008440d8944030340ca15003040000c41c0ea8034070006082c01c2c000a00e031000910030382401c6520502070b40c0002000200c981c0481c02081c41102c00b19880940003807800d1040c46c041344810060607145c5400340789442c1542e2055511209030001d0380e140e1042c030112940c2c0c191414100d581280c604582805265030302c490035a142600b00320052002515000c010592261041490304400e40007003484070183c44200c01c40c21880b51440d0910141502102e030714100c1c81502004181c1611841d00508109101d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 439418489 1250 439417239 439417267
    0x21e100b0f10031b030b0d0807032607020c0603090d0c14030705061e010509060f0d062c0f0712150921080712020c240403200a11041808 60
    0x70800130b0074145000031111440c2c0321a514451499445034482e6a02c003081c1c1020b0700d5100c003182141001010b078140000e8041c055211450140002e502125000d0200800300f20303042c0400c41d14001294042c0048d00c540354429414a200c5070f0080c2038041100c1c100011042c01c59200710806d0381d0319480b01081c00702520b121701240c06840903507401c2020075414400000d0240c030f0083d100512a03c2c66005a80840d90303141c8948581980c410806c0051069581100c10300c00f000c1d11a40004400e80021940380c440045114031414101d0300140440c1d90525095800005e142a070a44800202000d03145103010103105081103180107500c0e095503e0f4509a00312034415082707840c1c000304410b89051001325500800d001c644001161005612100d40d210000c1c40c001c0309015240c960300c0b680c200c1140800600d4003032400355001e641d410304401040c1e03402c9003000121038180030150340200400c42c0859400b1000d480103110080010070001380180b20043c5074415030703c007a5820700e4002210740e128030310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 439419739 1250 439418489 439418531
    0x309011b023f0a0f02011808010605010e040b0d02011b17040f0b0a020606011d060d021b0a05100f0f0903270e1503010902061306021e100b0f1003 64
    0x2032030704201c004251071000c9464080403c401842500465200740c116070240481810400000c008003400940e10388201d03001c1c000f64131425000c514a071040301c1c034505003806144c0840308040d01000e054000d682c011115202a040650b4036280707190700c4440000c1c4600e181071460300c103890000351554103160324516581225400038488210401c5811360f05500821400c0d4400000d080880c0001080b1451344142c0b1461104240d000742c0003e41401d06541c942d0103000c0b58584410401c1d5007201c0080d00c1c3d130341e42c40001d2001d04260704c64600ca00180c001500055182c941c0140d0108840c0d81c448210b005850100c1f074214049202040300400030b10300c0c0103c43c4081d00c1d80c0302e01421507a01c0e1070210303000d412000d451009182d0f0f104400e51307e03c0d182500100c2d42d503580a0141540c44200b80c20b883c0014440d405a0001800f5044840225484401210203000c0c1200c01074140c0700024408c45005000b145a090b401038403c0c56451640d82c0c0e02914542d40030f149480104010180395661920010303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 439420989 1250 439419739 439419829
    0x20a12051215040e0102070c03150c14031509281e0b04090c030c170c211615020124050d03050d050112060e010507020309011b02 57
    0x4014040c0c11201d24410318419002403066644028100828000c60007130800380915940381e40c00080e00c4406c11001d900408106e90107444aa140043c0c2c11494100350740c00c0c82482c10000f047c0c580364000f00c12219005542285103550f05041d00c403110404540d0601c400c445055104811200034082100120b51a01c00703072074844400c002403450804152000701c00c0e02180c2c1c0c8026075034804540e903070b200e5501c01c1c0a1517411008089403284daa10b4214129140c90068210507004808085405078002400c0a0307043c070001c000c0c201041091900c44030500c1e0890034503100748201380b1407007000b48404c200341020300a446041140c442c28020086e082d501d9031002c030801c0c10295502194001c0c5099000c40613244201c51100000c9481e0078211118011581d081040038034080c0001100881096181c1056119282c140405c0804d0b019032800c8031b40c2161440096001003010802a40c8250740300080103e00c0082111130802680100c0c2c4001412148d20441c804110041d81c0144000d08040d103540d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 439422239 1250 439420989 439420997
    0x608070c0209100e0a090b010605070303060902030f01080d0201020a0e040506370f05030a0305210a0207210801031101051e030a0b0a032001110a030c0b071403010e040609080307020a12 81
    0x30a2647c90b1005480d0500c510790030800042409401c0502c2a0015030040a04503815526810803490a040001017840342c04036074807980c040381c5040340c010b00a90710143c030603841e82c0d8000d0581100f40005400010311a07640b0001e0062480407504919840380c003200e00c5008040555804070548000e504140d0304030703001d42080001c082125075000242d042000d54145001d0f1303200c451010b4020400701400c034600708003500142c20080813041c0d0f64050b00c6564041c0e001301b040120740244150540c20f00c407144600080300b0300014004a036508403400c0c05110103140651a0404c1010205454802440d560f40da402c0000140100115039020b02000b004003240c402100710f1079640e81c1d0707480260003641c1c051002e403001d414034000e07805003100c1035070741c2c4040040d580316410b58580280041c0c00c05a01301c4042c05c0480c0404e90003441000113185410107095601e00d540d003840c020703000d400c030010812a80c00e03488101030400120700d18059405107815800500c0442c3d01490502d403000c224032100d030104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 439423489 1250 439422239 439422251
    0x7021201020d092f0424060c050d050a02030313032303010302040506032d01110301080f010c0e0f010804110d150e0a150e0f061006020f070f0608070c0209100e0a 71
    0x165011340094070029011030b0002886900f85540c80c00913803207a00610001e018442d0700052040d0000021084184200181c50f00d5601c041000d45040c00fa071403001005a04c2400004c0d0100c1d608040d82c0001402828020b0200e202806420a40b00603640203280060002c001041142014020300d81c100d4030860181580c01080f4096040180e40b420264029558580212050000a41c040420211554a42a42c942c1c544440c2c0b583c908400c01d14000075841c10071907041440c803d00401031040da00401710500b58404000441c4c881070301410944034164480c2c00c1c02c81c0c5560f6a01c071515000d10440e082c80c901030b2804845803c8405440b08241940c10081d6040009210038482201c0d41542c24400100000303400d8070705161440592920742c0e6445032400740011140c2c80151841210055800c44040c02134115845031686207a01c40c0c182c91840982051010703500902d00c02d68032080070700d42800c00041d00d80000300911800d031101046400d459505000c01552201e01c5a071251018209200c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 439424739 1250 439423489 439423553
    0x82a030a020c150a052104060b09070201060b0415120e0f06070306030209012105010e010f15050d0303050c0c0111030a061205070506030702010e030705010509070e0108070b07021201020d09 83
    0x344c401c0208503010880b00042181122040d0000741908245281c011040351070075103072a200902c1c030120001d129404503c0040c0350a441409800f06441c110315145007001d1500104001c4894810481c4040c069a6032001c40e50045500c540c01e9400581e000404a4500c2e86982da41031080140104040504204003440540c47e411b00160440302e40c039000300f000a0600c05418658100e00d40028050750800054015044054000741c0812400800030401551911542e880d06c1259205a5821038000d00000002c607000341d00084d40444200c80e8280b6189002d079aa5085420078101160344100220600218840c07601c07400b005082a0300e82c1c0e1940c003c09445590391011a48240341c41044004000703480f071817003904171400000c40e12003281d403504854a0800c2c06003004803540300241c425888001002140008050b041700c41443c0508011800e20794459500c2e401a070003660801c01c8200101c0034444244014400c0e00d601c0758000503d10010b1800e050503d003108881c081885022840d41c0c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 439425989 1250 439424739 439424779
    0x100e0c130b0d0204180b0a0b0a020a020904021503010303050a0306090c020a3c110d020109060f0e0604060f0815181801060303200303070c082a030a020c 67
    0x1510a03030a4020345401c0b8a44006010b48070301d411500300d504207241d00448181041e0410881c010003180d101000c41d8071007401c2a220300901084000603400b1070042d8001d400c00b165182d800a00103001d60100c01c2119001c464035910aa20840024000151148450350b141c071501c0301610580b10207120304a94004025907680704900f01400d0320a421103891041080d25a1800250401c01e0410903400c905002e0020801f81055068460503132407800b618480c5881c40c983c081d050380c140c480c0da11032820210201c0c4d0800222410800b4028095000c0d410780d0b40341c40240004121994819804070213803240149075013000703004444400110912540c0316600c881100c421184250441c2003079030303510010201880003031502040903500c0c0100200505910000c202800783e011841390306003800801c41c0b9039680c4400c6550344000b0351000e440d40002a040781c0103000b82440c2214038601c0c441916880c1d90300c0c100074903182d902a800001d0328841c1c02d07010700a48007aa4000c4403190072070a500c06500c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 439427239 1250 439425989 439426027
    0x30f14072003010501090b030715090e07030209030105190c0e09160e15030708010609150f030b0307090507090b1c0b01020a080a03060f0b090d032006100e0c 69
    0x800100c80340001c00080c9411100044507250020024071043d69101642001820420b120303500a01800a001c281c0b05a0004211800c03207890360f40c4100c0342d04d441c1c05414038200c0541f26004041d001c0183c01c405035024082c95004043c0104600c508031b00761030040044a29548854081c40004002c2c00d5140c4d07078001c2e12503030296505110440420800100325401e00d900c200040d07000107001c0000e0700c05503000c0041c41c030035402900c036080381e40d80710b03002030700d400100f4440c034807982c5165071221a50354400c0a004450408901340412440e40ca03030700080c100a4150850f11616030303621304004009521031600001015401030381c600d80401000b600d0010000042441c134016140c84048000e41d1081000242c82500180d455469145114008010f8465842a480e4082c0e00310808107580155000721804260700909004044d04240d6090700e5800c0320000200455644110511042c101809813510440d800246405c03890706009207201d00360000341050317603000d0040c1b041140c0622445c9800e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 439428489 1250 439427239 439427243
    0xa0e16030209030c09091c05031306090f08030406150b070c0e06030a050f0610060f0806010c0c05061b060a0b030d110307081b012a0c020f060a0804030f1407 69
    0xd40e4502074400404d241001d406801038101410900700149800b011516495044401503100b1400020103821149800192150040041040c10803000503a80da03104a074650b02c02c580d050030300d02c401c4d140c3c000150800c49040d1841c03600d60003555002e0007504c41d00e00190404c4c0005c40d0401c2225150003d07610304902600161741d8108000c1005035404000901980381c0c00f00071214104d240030815910741c0b1003500d9452800e1041310021401038020705034610070407401d580d580d00300d6442400441e0152085803003a0764000c54401c001c0f4054507800f0003090303200040b480c0750020b030f10440721492524038020550766099161a604550035a030125190046005500c0e2803da007500d0030300c0142c21845004401083c074800000c00300c8030002c403195900c64299005000f0842409228800f200710082c074511181c0101c8400c01700b54481c1e016a00007140680003500d02031080b032121021910a500001d03c143c0400d5109003004209944031007954410721051900c412003000f282c0c400b0380700340560000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 439429739 1250 439428489 439428491
    0x5130b0402120307080d0c02030f070813030804090b030c040b06070f081201090501050f09070504050112020c0a0c0302120705031207080c061f0b0415051c060e060a0e1603 75
    0x840c0640d81c030075515011036080c103416203544034810b1030072400503440b40b101500b03504d00b0088150103050010041e41c11070000250781c40d142003800c0e91100159030005c0d92022081c904c0803400720200364040050b00142001c0440010800c42c0e010805140c0300300c012807107204509006188d002170705d030203050756400c07030344100f200f28100d1807450940042c0c01845066004480407000005086d11103820007412510150340368041c3c004c00c40d007403140c0c1d400304440c81c0c0c02080007048101f2040d4841d090080903900c5060005007840340d80d01c000c904100c2c02c01300c04d4a001300e90300002d1043d860609480c0c0040784828000784191442c02c00403d84540400501e9032510034003080510a00c07030700c60110f6101c90302030415200301d807406040b600d03003405044480b1110908940004034081d043c030012141924840d521102c007028000204491907800703004884200c010056800c1c1d0040c00500076000a00451090001945025014021007448907809449502468400d12131030700b00d581010b0b0038061540c58 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 439430989 1250 439429739 439429741
    0xb180f0d08190207050a120206060901141809010f06120c0b0a030b060304030807030b010201180b182b0503060d1b210b01060e0603010e0907090903020c09060405130b 73
    0xb002c8402055080c1610900004000c0100940451000ca41900c0b45140b48035a0319200c00c201d0b52032130304070b0ba4035811060600040c4450850440d41601c0080c0c010301c2180716454001040461030310540d03c400d400da445043d404a0a00c0078024030006d0401401f080072404590344131390350307074004a01c91008030400000320b040880d4480d0304210700c00d40001d0a09540c0c4e051910b00108000070840d6a50700003407911280010b1756106000305c5a020000300100568481e044d1070704a800300c00984440100b40003010b00101e8030200f072124001105560b0f0380f08003580c0303070b001c03112900a59080c1d1040070480e041040010540d11801d14101480e0402c49060030a07000b030030705009010850b00505d5800552100110b6542071102c0c0e00d200640c4240b141e030f01e10b66a6007100ba1000e02c0e000364030540c40b00051006000300c81460210381d0740b1030903400498211507030b80d00d40402118030003a01903006800000780310280d0f00b01800d44035008003044e20204214540410421565403203c00003c01d6440c1c040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 439432239 1250 439430989 439431001
    0x16200613031a07140319060824010b07060b1305010e0f0c031b03153007030209010b0f0d05010b190f021908040911070510140712090c030b180f0d08 65
    0x7180d06d41c148003420818140c480c1c01d000d80d5041c1040508070b02000000030418030f82c031290f0950303040342c0c03010307080b01c0c2021444d0b5100000b52007942d07500c0e60000b80c04529a01c1c010030b13a014484c0282128400390200d818074000002c04440010301d1020504400c00078081008441d4449681c1c03103255404032602d0342c0321815441506050b0700345450388800581c0b00b40140c1d00320840c642e9100354003c0d0100070450100741d0400e0302d481462002039440803081c0010841648000004e20000b02076460310791038110403080035001c071380b402e810814078140040b4407003868601e8000024050f0b0b000b81808050075210002c02561850303020300417503140303494004200c00c001149080d01c0140a807440203114070084104042c4061b00400d0f4181e560384140d070070a901080540c0706405e4114800110610241d481403002c1e151840390a507444141c555030410400410301d2059140c0246204448454060070b1000b0754203944280e90840011680000580404840000803060b45030b407091f0420280a039501 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 439433489 1250 439432239 439432261
    0x5070308070e0315070306052b1401020708070b060906091501090b0c0105090114090304030b060f0d060b1f021c02010b0a06050702041116200613031a071403 69
    0x40b05810340c1500c5502003250780030b000b54107070314459800d0b681c040140c80d54840070442d00c02c101050140c0d900c04540020540c00c81d41c0e06150a0b15401075a4006501c001c180e0007508992000c00180c034030920104110042203903e20480d03411440407941e110302c1d4204440040d030188000340c5440000a02d02841c0201c2e41d00031901c150003400318000d0079403a55140003c0501804040318000314951030003010054a00c03005013518010f0710064020343c00e05080d6074549030243c078040d01d116030105001175504030703c0d07564201c1413215074032800021901d105a442072004840312042c3c400705032120a0a124115030340002c810781d9554030f03148407098034200484264010640c1e250707400d0708258150400b2039005d03000001000703920310a4804007c1c0c00d4a008503030f0485d00408010060404050b5241c40c08542c04200c0030710180100c84958800c501030a002414641c04106001031800e0310110420034841c0003d030251212208442d1004d04d0b160028004203510007085200604080100101e5903804807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 439434739 1250 439433489 439433507
    0xb2b02030c03181002220b130e09010615020c011202090303070f0f051c0210020a0806010c06060915030204050609040f0f0c0b0d1406011e110a0602040906030b160507030807 76
    0x1d520115034400c071030604690786100340160403000d22000302001030080c7c9404111500c26910b100300c03210003130034080241440c00c0040c29420710740d900e8200208883d0900401600000c0d0030b60001d00228000301d0005d40000c20222070001e8042c8140311000e010f032008001c89d12481c1e0300c10906003214050f8540f000c001014058050310500c80e002c82031038070911181c026281c8010035021249118050b00c3d031581a4821448500c0000341110045080d0b9409902540350440c4603000105160f0b84403810102102e0030380681200001c0190710030019400d0038414103401c401c088d0383d00600c601d0240c0380d85403401101d01e0010b00480c404031480d01400041c1d10390340007030718100f452070b0750750003a01003004060100300c640024043c3c019030102c0c1d0382e903001d64040210b824043d4004941c03224150416510700b2070012106655008495802c00056450310080020b0019090005000c0d41117013402c0062860041440d0144d6202810f85200c41e40c00c80300b9603480c283c3c580f4003110941d0f280c0d1022500c4c0c401c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 439435989 1250 439434739 439434763
    0xc02010c0b07050a080a060f0510050c100203062701050d0203070f12030807020606210c0904150506060f04030210030e03070c050306060d0c09050c040b2b02030c0318 73
    0x31070410b106815901600800d2112016a6261840c0e25040728400440304144146800c90b03407960700c2008030742030001c64180510482e0801c01c0c00c1c1642805903608048030300c68800f0750540d0000c02c02585241c0701c1031600340a00520800a1001000001080c3c101030602809100d40c140070200d0086503410865440640b25415201182e60b82c1c4403004942d0241d032100480219140c0c070001350341e261000030250301c1201c000b00540c100300101c02c041c5030f068a840321007000d10701640103007001c19100d1f00d15103401a8072500701d030f0307040c208120300b510200c9030050308041c81480c0130000e00016003001c0302070318148ca404507810140403282020540c02000390008407009408007069200900c4051740c0c40b102201d030f040e0155071490382d80c90208680f6080841c0001c002d00b004080510940d21258080d42c3c0c001284000103241603142e900c070400503000b44200c0f58000b0948100c46814003401101141003641103901542103092a4a086400e8040180401d414240180441518540402900001d0342c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 439437239 1250 439435989 439436003
    0x3140c1f021b06010f27111b0627030304120306051c3509190e0a0605030a150222090902030c100c0212030405042a0914010c02010c 58
    0x2140b00300d045071030302e038248914558a40c0b0440d00248890800340664080c165600400d17107114824890100100f40c0ca00e11302241100c1030000e20f2400c0c0000f1444112004d040c2d000b0469450400b04010013041c26281c450701c0c4c0c4040041500100e5030000960781c0066108001e2a10881e480f00114020801544455405441c8483d41c0700c0c02d0140041c408001d81c0034101410f00c1c0c10260103242e5120105848000310056440d00700230024103000041d100e1400c0050080940d21892002d1407580c2c50550080380b0080340706402d008100d541744c4541ea00806003a4041c2000b0000b0380c03124010240c06100004c0402c1c0c000420307000309108040405481c0520184031005030f40c94203401401800ca24004078028400d28513001c00c00e00d049800503415488660751526061007079402e10101641d202e2000c00248818040412565224002c01c1e00e120b9020003104c2c60303003810128808040001c3c0600006010805005020715031001a10101425084c244080c4441710b610040320f2030289024043c02d80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 439438489 1250 439437239 439437277
    0x8010b1605030a030204030218010f0b09031515030607110a03080a140114010e04020f18120d05090f190b0a091a090907050415031d01021603140c1f02 66
    0x3d560198084d0080d41d00036200180401034801c1d0b14108080d01307014180c041107400f1020003802051800904010f80094141e841d0040d0042200d64000e1707080d10407202032051000780402d242810007020784d2102181c4ad10035130315018038107042d032500c1101d00c000d0104820000024070b60304030b039081402e0320800d201e4081190740e511950085200150088a800100840103140192425001340c9007503803420000305280090940c0800c0000825109440e00b1285518003451004800c3c407551011503c281c48155441d80c0351070410080c0e55042d521a4810703003039410100f55000741e4100070410b40c1ca28030b41d941c0c0d5641c1c00060555061215900410600405490303449803072004401a0505d84401d8903288000c0c0c442c1101075030f0390f003e03d000d014941550071503861003161080d00003807070745c550016001032000140544542a684100b0100601c614488071440070907034064200f0000e00e405508840c10422501c5d1001c0c0c03600143e000c00c0d4060740c4000c00403a03c07020aa41110303201d1014160307981d02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 439439739 1250 439438489 439438507
    0x507170f040201080903180d0f15020304051504030c0b040611040303021510030f11130e011407020105070e040b18040c080c0604030c030305131814060a0608010b160503 74
    0x45a5007100c049000440d0030700442c121007000001e588140c07035030320380d103403070038480f420611088036902401aa884101c0c0030f0881c01090070a035000c1400f5230211005652882d140c10458a48240015040350742810441008040384d401801000380b20340c0040c40040c0d548032814040c000e400b110360200d2101d9000600001055000205d0111030a1089084900e80e520f0318a070301c101540c030388000b5040003043c02c09e800006a03801005e81c4607200003000807400c07d5110302c031201142d142c40760800c5207030b40d40c4d16050607800040251907405401d62009005500d00187c0c02080d81401e40c3ea000d000c1c2c0d480d00f00d107000da40c1c0e48041407030003002c81361018920752625003407511281d0340600c00d403c1503000380114900c65041050880e001d49401c0300c01000250b2440d50100c6d407ea02c01c2414140d54160940f0114405003110081900c003445d0700004500f00014584000d110b000c0a400d152181030344d0744c0c0c200b043c150031188041c1180c030901c42d00b41d264a201846024240c0350144d009145000002c1c0c601d103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 439440989 1250 439439739 439439761
    0x60f09020a080309012a031112040b07050609010605130f02040302031b01140306090103030e04020910020d1d0a09020c161211120714120303010b03041a0403050a03050717 75
    0x30041409a881002c076a03083d0902c08800e1b50042d01c50241c001c0030111590121740034040d082140124541195801c2c0c8855591141c150010342000009460011720442408002c200d805c0c0c001404c08000c2045034a418002180c400011a80e50681520344204954010650341620001d58014094030000044d880034035802e8200104101d005c40d550b080303094078004160095070710a0302c0162075800c1c0340c0d0a40d02d0903078100d9650400d60364040d40800a418550312200c0d04000c2e031028580040420b5a00d9660140c4003c007061003548240101c400e151116030b80340c080490844e4044040180d5a0b07102100160030107400290340720484080c0351000030030455064640c210180114580200032544500300000f413070340c6ca0415031440c0e10a400610040f807105956004d031260041c0348002d0410305541c2c0c00e065420907445034609107408010841802602e00c004000041003845000340c51825540160183c041c0b20075540400d580d5200007400d150141d800030b0705124181c9041042880d21841c115 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 439442239 1250 439440989 439440997
    0x31107080105130b180307032a0b090c0d0f02040209030a0215040509070302090f190801110904060501020c18070509040204031214030108120706110301060801080c0f010c060f09020a0803 82
    0x2c503040400750001e540111580d41149071103441c5c6020358500a81070314121140000700500c61815680392824242c0b82411041d401c090710b2180700c0010480c0b0340811090f00341440c042c10b5601651100e101c1200284031401110035196048a0040e10b81147c4000b107403414408100c000e400641c050001d000880e1400040c10445504540280c42e980d290f24040342a4000e9101d85508401e4a2071500910b00e0f1480407d4030300c403c1c2c0b1844c8950650382d0300149080d113581401c0d0800056001a9440f15400c290296001034807013030000b007203517801a402103540c00082b841c0441d1081907101c082a40c0f288503404441003403000402c255152a10b03420050500040130021201240119580040d00b180407003e0701d0488140ea070142515902008080b000703940860000c0311655644d4803581d04103103113a0f010354081d003602e41e110380c119030420f90341900c1c0500800400f885103185d600380d2401030f0f0340180003503e61070b480000810002014010070b0003504000c403000b540700da0441004607013260300002030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 439443489 1250 439442239 439442243
    0x180a0b040306150b0d0203060f060307050a1404030309180b061344120a0305070f020a050d300f0b090907060c0c0e040b0105010f030b0d03110708010513 67
    0xc03c1101254424190b10b0036403442a958102c0b000d0111080100b07496001c0d5030303c100080d0451144460300340006140707500c200d07011340205401140700c000083e0b0100380341c1c2c02d00850140b02841c286c15a20050840342e92032040521011380710f60400780b1300000d90842110540301411481c0c88044d0b441a00d083c0420900941000204110701600c41181c0341d010b055034440703012080821031000c42c4900c1c2020349030b44440043d901c54a038041c140c0007401001088124400c1d81c00142505203003400410050b0010301e103504552203e1200400300c1d80c003040c00c00d000ea07100c0c02d140058542030560109480c0c0c407428903080142c40c403000c0a8801c010740c0c01c0381041c459240f02c1003003039500d40c81c10000c01003c15142d028141d0300446051044d103005081d2618514012184001000d035200750303a0341101801c41d400ca4501c021940100140d581020401c0d100e080e603400c1c01d00c502e0140c0d50100c0c10300700081c100070b0700b081200302d41d800c540c5038107004440c041d0048200a110a14183c10206000e001c6100c003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 439444739 1250 439443489 439443491
    0x106290310320409030e01030b0307170a03110a0308130c031202150105010c0c1e0e0a06080105071716031506021b0301020f03010303080c12090a0b0601030b15180a0b040306 76
    0x2c61002c0386040d1289500040d4983c40b282181d1302c4e02d100440042c00003d003c26003500c14030344041600c41071889047c8902d14124006c10360100107250090000c46002092aa036911542d44540001d41090519900c00b40c1e881c841c00385140c035800c110b030400c40f00d0ba0001d0031961000c41b480205941c086507101440020b5203502020366a11401190220100c00c0080c1c0303001d00d21041404105040261000241c050402c01c0d81c00980300e180280f2002003d5655800b450340d5030404000c802000c1c056140d110b0004e0070b003012001001010001800c030010701c0c1003081040c9444404050307010b40e01c01840d12081c002c4845c101e648882003c3d40d80c40c040110803508002900550b620340c90140200d551203900d045105045910b590b038103940c900c0c0c0c054030b44800140107210104061003001c10042c410b1001c0c4004020a04c040d04101c0c46a5070701618080c101418030207080030340e8640906882e650819823900d1540c84c404207041420348a104200c06a06c104000400a49070310b009c000341080d1307406544 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 439445989 1250 439444739 439444829
    0x507030e06040506070602090a03080a050c0c04050118050711010c090807050d051c09051503072c01050d060806091c1107120206090a030c080106290310 67
    0x7045200d004038421a5448081000a100020880d8000e1310070504040c0215680300e490707544003515a0410000f1400040000c50b603090850703020000380c02d07809000e072420403495041080100c3c0303064110f020701040b81d40f0350300403a80d154800e251091016844000030803416000400081401501c0e10078156144159400803a551070f2055010843c09e900c10010000d020101804c0c1e40034690a6a04406000b10071034005101d40b80e90900b0b41101c40803402496403850a21005030903d50965040300090308039101041242501010601040c0800d0070015210740b5001350000150803190005c03401c2c1c0c050340060210420002819074884010141701444104441d103080742e00300d0140050200d80c2e03003d4034003008000503e408002d0001e001425540c40e11841e030000c00e41c0e031304055100710b5011208a504100b441001c2c80340f171001d1700d814007208124000104282580d101c1103180d500d800440000802c840d0780b441c1c903590004044421030710700100d01944003080d420400d9841c1c18100300d0144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 439447239 1250 439445989 439446017
    0x5060a1707031103162603070f03081810061d100608191401081b0607060b060415080a0605040c0c03030e101a040b0a050a030605130b07050703 63
    0x844944a25080a00142403040c40c50300c60100d00c11038148000d80500458070711700d001c40300d4007404101601100c0025110000c2c0c0da0350107003a40c0015502080150428094800060000359060306985d8052820b4851030f11000d030502e03020f4000129016051140c0071550070034846031b03000402240d03224818803c1c02628030368400c0c0419011180024210448541400114020b04845400043d94103007401c803074501c0402c11045500d040c0204c5100700c2c2c10801003000315000c0000b1030344000c4270b15120720400d1882c4040f88035030040840c010300b096122810f00f0f40c537891b043c007507400508519007442509a6144c1e006080200292106280c86007440004100d9080c580038000c4001c00568403039000f60040c2d20128003d26001100031118087c00c1e98484030303000ca9004500344052034455007020451080100001c441c1d008040741e01500c489002048165144540041100d0300540041604e54400b0b14540700440142c00003440c00c00b804062200302c0d41d110b806001500d00c0b0b07458441a905c051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 439448489 1250 439447239 439447259
    0x21091805090d030b0a090c02010b040c0c02090907060e060304140715030f0c0503060103180c1d360a0b100503150910020a0e09090a120806100305270105060a 69
    0x12001c0b03034204000c4c081c2007041d01c126600290b520780031f9200020b4461108400941602c2044205c1c000098441680c0001c0d40762603801e01d030b04403500000030086103207040340c00b41c1113040c401c60343c0d403041c1d0380400050244441c0105400b402411441621207040e1100070140a00400045140009183c44803424404c603186c0700303500700ca040c1501c03100d09560343c88004502800d00d0410042511111944660004100b4804403025000491040700d40a240303090082c2005801062003a0214000d50100503446176000c05e800f44120140700c01640440134512032b4071740f032507420008102c4e010000c10002030351b40c0714050a09890044082d6002001146480796100d00103544060072500108000000d12802d0b030300400c510329403410442c14403000d000c0040d280345412a41841c0c907401000d80c4004202c1d040ca02d40c29001280c1c1450030581c00c104000c01d01c10440e004c07108080c1365444001c076400d02e41d038000c40008100d0701c54440c00b603640b2101103140680b0f03060310500c0c043c00c0c081402080010350 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 439449739 1250 439448489 439448501
    0x30f1501020c0418020d0602091e0a0605090303070b0a0c09050904050705060c01060b1c0c1805010c06110307090501020d020111030c03040f140d020c0105040321091805090d03 77
    0x10507801414807002100821009107032502e040b422812011404e0b50050f1a1000354081d41c078083c1c80300584a0b041001440151240001007080384e440c000203c60050380da0519940c02c0e120300d072a20320327110859000401d00d107204204001d0400a1400e04202d150103081d003205040c1f01441da9502e504a41e0b4405201002c00e06850050840d00400b805101c0c900740000900038251420001203070030b9030f44c4c0e03501d0201a4040780b141e40c418204046503480390081e9001c0d904030380800e4500085507082c0f101143d4414003003030080a0410110042c1c4506000d0641c20081121101e514003503036a007440d1001500740307a000d20459016024080c02e03e904280107200d6135400c10b150a0030780c0d16560b2034181d92000c80d4070080c81120904c0248000f640490440d6151390001c0c03851030000c1c0182040c00001078a441c246d800c00c00c6c1003050030001440003542c01d0702d0030080c07420450010300c003615070b00c5419151010307260020396801602c000004410f0516410941c0201e08210666050716640b007011819908 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 439450989 1250 439449739 439449781
    0x629190e06161211150702070510020106051807020a0305030907090c081807080307030309020406090501030305040f0503061302090603010b1002030a08010e060a050d031b1202010e06091c091505030f 87
    0x1705034428258050300381d0240e0b200d4024410b46501c036494800082e00c440d501e45282005030f650348000d00441c284200c0d0f03400746420039903940c0383c2441c0280b030080d0364190050f00103081000c04408941c0d5a001007010340050400709601740200c0d09100c50042c00742c0c031b084840901030402425074880c0a880400c110341a112014040d503c2e001c01038506401030300ca90034040b40c101da500d410018203804c4074411103018520a90b51541d485180103144400c4c0c09050300000e01c82e82110741840660490401d48102d4180e040d02d50740c000f41d81d4400002e0061040300c8206400c42d000c000000015076001c0028030000340e686e1141c0743e603662a2400381380010402c9a1190304105103801c213202d9484c040342901e442901c24503000e41c00312400402404600b4000c8000c0320712004035560180c0d0140c0a00070200010360180040500e0b00d40010322075031b2180500c580011035280505a03506a40c4280181030143c1411551900c0c41003070814001e003103a10864518000c1700100000c6070b528029001d0000040c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 439452239 1250 439450989 439450993
    0x503150910050f120105011e06020303010e0a1107050105040b10060c0f1b0f030507210c14030c0301050c180901060c0b0a020702130629190e06161211 66
    0x1d061070b082c0303d403c2e166009150390101518210b01c10b24031090107114040c001c0780040e8201c003803034140a40d00b0519240c02c0102503400c207000500005404002e00342e8400c8410b0400328000d454281071011a100c0c504010b0159420310040105118840510034000d1101c0c3c03541c2506240c0e14002225034a40002e0000e190104000c0440c001c14950140d8240c1d088880311004850b1340d85010b81d41184915500c01c6481c0d80007140200300c0d00004ca0149817007a050a10b0f9441084400c1e6035256a0280c603004029885c1e880c848441016101005108985040a0002c02090070411000f0999801070b01d43d862080100745048505400d00c010418104c88054030395442c00440340d5128420400010071a00100d642801410090313550401d070100c0611040301e000800b030741070010042400006d4080c1c60162040c402d00d00c6070580b00700b8100c4800b80c0e1101811341030031888040841d102c0034841c0c0300d50362060001c50381104080c0e52641000c0d6084c407801600002c16500c403400da0b14100c119a00c03090076 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 439453489 1250 439452239 439452271
    0xa030507030609050c090f0703050a1107022404030803010e0112030c080d1104120c0e070e060903010f0e03030f1e13030207091d061e0705071109040305031509 70
    0x10b01c864101c900300034401d0702034448403e400f6000c1401c1000813540d03080100001c0c02841006505449000c0e04408007100a0100c1803210100494034445e0008c024090805e0b200401002c0702c110500c40c07440d50b5191800796031595070741410015500280100c03910245501c0000540b05000011070090f282d040d00c0d5110a02c1c5680c48400c0c00e80c010034010803246413582009107180f04100d00a1002d4172071840d152502050300d007800020030348160007800b95020440180071425400c00d400303544140044030b42a50700c0203240d02103405814074080c610051818082d1801d82c00c1c0700400514450000e010391208d081d9a0170460110500610052103412030341403000c54400035050b0301c84400e150007401203034501952072504004035001c1d54a00d00c00d822001e03030101c00c555028041560828180711040b41e200ca15a81c803005840d5004d0412002c1c4075000030a4402c029240c54603040c0054001c00340c84403868039080c0501141e0044030803d1805d1030000d0201a145031451a881c0518810f10784120741d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 439454739 1250 439453489 439453493
    0x1240504290d0c050d030507050c030607080a020c030c072601020f0414030c090a05100501050405150c19080a03060605130b0c0f0307050c0a08070e07080604020c030a09140a03050703 80
    0x181d0311460200351460745883c0000b04081d181e804104001c548203503501c40c0e856040f0b007416810681940c00c1184250442420b114059500400058200d5699480141e0703402207440028610720820b20300c9140e0340503c81001a042c91004402c003080e00703450342c00710020070171001e08034200d01ca9044030203c1c500b4140401c0c40b01031046147c40c01b0940010302180c036560550000680f0040c021101545c2d251303154020811041a84034038203000301000c0c03d24038242820400003801001c00300c408102211400324108200c6801001004200d001d202c003000620300d01030411070a107030300800f101c101180c20000c0005d080b80c403400880d506440e240520b0750903181045202e200c40c0e804440d00c21041d00c1444580e13100740c5410300c02030865502c10b600030030200e603d03041031044420280e88142c0c6160020501003020050391010150302401d81c0c41e0802c06659a000060000d014101841c500352101180341d02805402280707003819900040300c0048403114410410801c801c107404000c2c090f400c103d1003080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 439455989 1250 439454739 439454749
    0x3060b0a05031512061f060203070809060a140403052416030e010609060b0c010c080f0f041a040b07030608010e0d050708070b101a07031706030124050429 68
    0x1d98800028600d4085801c4c00f9401450840c1c00d5580f201243c21401d4a1048101c0007076003a00101000d0024508000460301d8040032400351501450148500160020160b81b280c0d0f07102500310500304a1075101c03626401c100d680e49841c054000c5075030072481001101401001c01030f9202d403030622803000f280f40c080c0004502038038001c150324000f9900d400000c1344100075402104083c10614003515200c0d5401035100e420f40c0c0c603030280d4405001c040d006100042c0048583c0960015401d03100e80c201e03072198a0300711204240c0b040f03075540251500080c04200080e01002e54047c0000355000d018883d01c1d00d41207800c0300c0040503441b011340c2c02080c030000a540900040c0020501558003107080074120340700d105c45001c08990342084008248070510040c025a04410401341c860400726003030601e255005820102015401c481c8241070f0400200309039025008045c0ca020b061803902e00c60b03402404c0003940d848041c02103a00c5141858a00e1138000c05001440303440c44161502403080c90640d000f800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 439457239 1250 439455989 439456021
    0x110a12030e010e030414090a02030c03040803072c030d08060a09150302060403060509190c060318060903030b0f0301110307080c0d0e0606211005060f120304050103060b0a0503 77
    0xc40c155200c2e0141c00d03d41030180040c0000389001640c0c160420701c07101c10810320600040c0f10b520f0061060050080d0110240e00390380d809503228001a960340c56941c002c0d20780804903401001454004070851141d07502c00580f00d031100e5000c2d0300f240d40c00e49100c2020307600724400700c51090700090b056804000000c0340d6000825410340c0f9042c0d0031407040d103039000b06120350b009810a4030070b503840d40c06000c4a00403c0256021441c44401c01c07074104e00007a950700c009800c0c242300b00d20805031159a02405004000c0e58505140d0b80248100300e0040c4510b40900034251100c040c502c02d005a06084485080600442100f0144604446e01d5640c810406a541d6400a00084401c0c0000c6c0500c420441032845040c006502c404002e050503c2c001c2c04101911286420040f0100091692020480c8001500e10000e00c500300000c150740c1d070360f030002c21080a40040b002d903201115070500440812f0200c002c1080d0780c2c0aa0741401520380710b50550500784034504003940010b02c104001821204045220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 439458489 1250 439457239 439457261
    0x51623130b12060906010f0f1503021e0c0a0506010b0f071e0506040c05030118330f0605040b010f0219030215070e030c01020606150c0c1f110a1203 65
    0x618421550111162610408890700b041300e5020303500600078100f100c90720300000c1440c4646015801d0401142d0075411000d03003890b405054000c01d0740640503100000b8130845800741d0764035548610000c90615650f0008901c240e906004040022070200b10182c2100d0361500c1c00701c6003e1602c080c03592581d0201c950b000c910035402c206107850000241062011501540c0100c409000081c1040205421603a05124649840040c03c49040c0000e03003149903468140500076400034004041c80c01039150200d64450104050301d8a4440100c002195010340f0031390b607095408101111080005540c101066100c850142c1d11020985002c000c0c2c49000c810010700c030b4415962811140180c40480032001d581401c0898038241d49075030f0700d09003000303c0c42940307009200a118908004010032850070003810502070001000411040308801000a82ea104201814103a110340300003115200140f076480b00a000242c000107050440803001481040340398222a509120b01d100107030940040c8014019 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 439459739 1250 439458489 439458499
    0x60a0c081303050307120f08131b08030a050c010b120606280e1801051501110304120c0513110a050306010e09040b160206150d0f051623130b 62
    0x20200010700244040e082052103200303650124001c0401c007800d244049182c902c01c014036234003084a00c02c03403091066a45904190740282d910001c820f04580840e00e07400040ca584000521060b81315880401002150418002000560308980c100070090348100425080703a03004c240810058545440882d403090078807009040c03801c0f51071041c3c2e00d05903455403002e060503027400c08011611851440c150220342c2d040c4020880c600d00160b8030305403000309280e42410004041c200000140301002100d010b064190340100b4203050524003561280c0b807500400c1d02802400c14402d01801c054020000302800824445080c8111702c00111020b802c001c006030304201548038021b10588980710200d000e140a4408001c051034020303501c4d000c940c3d882c800c100071503000004000080d0151000c3d0b41c0c0b8114100c03440c201c2d0000d94180b404145402e54400742541c021001105007041907000700703404440901802c01aa140308100340b200f81c41c4035480c1c42d9004804c0603550441d190450740404025000208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 439460989 1250 439459739 439459777
    0x20c240a051b0304060305010e31020a0b0c07051e010c0201300c050406080606030901090c060201020a0f110a031404180902030f0604030903060f201206060a0c08 71
    0xc00b04154049102d64001c1d42d00001402e102070790b41401000c1c09800f9240d415495403c0604070540200654801c0016a081500160350305400c010384542c24260000c0841c82c1d10b40d00c4000020b42d60303002d0300383c503007162080b030600250604140444008103072044204003214121711005661200c1035000c128104020345251070301405440c0202c1d48a030f9580c804100f481444103030340804444c0814100f4042c440305000c1080b2441e0301c000c1c00c5500901c1640e03000d881b41c07038154215015001c98035000f40090301c3c501011604903415030142c00e28424903039441c2d041d02c2c0c120100356a6000030003080020360b00042c2a01001c43d001d07025014000315101d010a15107030341c4407245003400c1a1548101c4109440708490b1065140820001840952000c044c044600301640d026091040310f00c0024025070701c9207000c00e009059a4001003a0b11007600003000001d5508400c0c9500d07070310003005074451103022400318400e1b003070100503206840110388030484091a0390321207030100e800010b03401c001240c041c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 439462239 1250 439460989 439461007
    0xa0c080c030a0206070306050a1205190b09060f0c090402180a0f0519064515020c01080a0207150906021c020c0d0f1e0807020c240a05 59
    0x204940d600080141d601e403800580700a0506602410071010103040203010b100a035144900d41e011502c1000b003110f014a114640507040007504908407182c90302000c0c20109002e525060548a514182c043c2c0e12540c0d188a84c03400c0c8400c0a030f03000c440c0d03000c060140a17000d06050b4018842c9800a01561300039642e204000761410003680c000340081a0741c0c1c007040103281002d0a4030202c8140e81043d528105080c5400248130220300010325901841c00503004d400d45e50182400c10807040034022440740800490703170b030044a800c0c0f07104020021009010102c1a03034400300f04c1903071200e0160350304112901c5072403040b000707500040c5040c3e48000a03004548e940d0103c43c03090360507480c41040d0150b103e104035244410440601014040998010006c00100e0b040100390035115581c142000c5080380c110000441e01d100c00400d10790781c52800071406182d020340000900c0d11501d147d5007143d400812503010f100150308403800c20690341c40003004026103e51100040d15040396549841c50500c50b5403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 439463489 1250 439462239 439462253
    0x120507061a0a090b060304020103050c040902040306060611030304110906120118060b09040525030f050a02040e070602031c0b03030412060c05030f06040f0b032a0a050a06050a0c 78
    0x5030307191001c201c42200c0c00c1d45090510344807907001080c20540030469400980c02040041c44003e00090406a541c0001451455100705440143c010042c0464880e909ca183c10402000d40740113a101107019110841190f00700002101d00c2103500c000d00caa00410458144094403501a003d00c4d40040320b001c425007255024804c0c855407c1c0d0381414101900030b24206001192002e13a605806040e6030170400010820008200903591009035481101801c0e40032030380224905500001c12005400f0914010f10a00280406003203000f21401c004000b004181c2d80d41c3ca43d080e04c40e15015030801e1084c0d50005104680c94401000740203404990500c0302c80010303003140c1c0b16801410382705154452040c01e120103407141460b40003903030030301b94513508000b1780f19601104001c1440d0320480c0c0300c10000e8203841181d041003240f90070140880d0851a007010700e403059901e01d00700c0803503032442d60140c082040c64455088002c80b800501001c0324070b070a2040c110341031340c000000e00080c08010281c00c0c00190078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 439464739 1250 439463489 439463501
    0x30e030d0e061006091a091c15060f060c030c060605190806010f260c090c07050609010c0c0201081f0914091b01111501090915110712050706 62
    0x65040607040503c0c01001d6509112481e400020400044103000d1181c14076a2500104c00c460030f5410607222550403000681e034020b11b013040132440c41d01014800400c82c2a00c4001510301e815030b41802080c0e1194110306016030507116500c006640c107078a01e400310707000d00d0640078094000c0c2c4000ca00705882d4000b00c1c4003141e907086007031030b4032841800400c100c0700103000c040e01406c40300543c000054540404000000c2a20440c1154103580e1103040c1b0300724008202c1c0b110b26002c05040c1c541246003048142c0d0f01500800c80c107541c24000c1c640021001c180610074448000040c0c1c4400c04140c10507001125600d0f001484c05c00d1002c0c0348143c218000100800901c01800e414034045880d060001da0318000c10805401200c069001400350080b081304800c1380305a2407428038018000c400741d190054070b00009019400345500d114400840e080b03c041e0448034256001e00c588032549040302421703000320303115150003030403410052002c100051004046561b0010051900c20304051582d00e410048601c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 439465989 1250 439464739 439464761
    0x20f0f0f0304210c080c0307140f010b0a080a030c020a0801090b0402180405070605180a0f1406030c0f0706140a0b040606020c010503010b1303081201062d030e030d 72
    0x300200c1004100720760070542c02c10403142c003070311040708414402010b020b00d501d0300e0b80100100004606040006010001e80c0c0030942c1003120500b003030780218120f540728031601c000e01c42d0550030034881048a00b0401640da040317455090040c41c040420380c07000c860030004220200e0380b05036864400204448240030b444400e80c00346e049580581094030400c21981200d10301c10312040340507010000480c8020483e03101321041810495900c990341c000020101e407400707043e694030000340c520100d5041c0700741c0c49180c1035810102c0c0b040603101c014010025a03000498003800d0850341007084107206c2842d400600049403180102107440641d04a07030116240c0c1c00c45250461694600201e896440c060159500804090000e0203140c01c0328030000f00a81300c14090810000000940216018501200c076002580c0081c07440f9102c116807410660401d10038443c100009005650204142550134004001401c1c80c40c03044137042c21441c825009880032090b9158240010f00800c21048218090760245075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 439467239 1250 439465989 439466017
    0x40f0501080733050f130e10080a020f010e0d03170f1306020a05120f09120405061b0703050d0206150105091c0215040f052713050c0409032109020112020f0f 69
    0x3034200340c210720090f40010800b00c600c888c0e08130300300310b856000315036090b03e25010344400c4458441c12006035000c00b8040c00c0c054000d020400340e00d007070541c4250b4201a0082d00e0821003060b8a0b400c18814070550f065986068000c0c8441405000860a40c02480004128140103013042c412140c05203403500106c4100c2a1002d180f03081210004082c02150b8600c0488038506040608080c0840c429001d10154170010f80040c0460402d03280003041072000650b80002201c83c0c2c500140c0d4001c1d1079600544210140c0d403454403a840f41036000b4015140300e9007010b00603010040104040310060070002d034050b6000444001d075540b00050080c02070002d007490381902002c5078131741001d002400d446003214021543c0e11104605010b4481c070700c102d411213000104070712441c1c07560400070b00b0b0400e44c000c4958801d142280100415400c15021b2002030007100c0400e4002070242c0380c0000b500c07010040240003e41a940c1c030500c04140d60301500c81d602982e450b26003441040184052300340c1c41010800300314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 439468489 1250 439467239 439467277
    0xe0a02030a0b09010b0a03090501020c0609010e0d0c020d08030c0c060c0a0e03062412010f0504020a050303160303180f0804140d12030203040809040f0501080733050f 73
    0x15011a000b4040412000c0c1c039140340703a40c505801e6160398012240380604041c1c9075554101440b40940640d4815440c1605480c0fa03800e0210286008010758034810f10180260742031a81101d0141904504039500500b0103030790700d4941da44104195200501141c1070312014071004040c00c2042000501c951448603843e0780c4c510b2040d0300544502c80c40d2020300d10a600c40010414501e0b200340c07214008081455101700b16051002c00608003140d43e02d0012203940c6010b04207940b031400c640100380076900a40c0c0d25403035542c41e88141134580c814154009107503200500b1100c00a40b2a23841800702c00c6440ea96081da03000300e035650520300e80c256002a1011000400d042c801200807102c204c200d00400c603a000d40c90102542c03805c2d04150118250002e05502200181c148803409086604810000b4010041203031a079090400610003070054482a1094840101d1140d030050841c1b12801e54558100704008040311a0500c0011258002e208014080c0415034401c40707100003601680c04140d0070b2100e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 439469739 1250 439468489 439468501
    0x2070501080c04120206160512030604110a02250b160b01080f0a11010207090207061d0138030d0908060c1c090606051e0411130b130e0a0203 62
    0x66010142c10301148100421013002004075240d00c1607441c0740e0503540241c40e0300c00c400380310248040440b03000d000c0d0b0060120344d41321710000c0002540b082034229400c100d2401252210600d078010b0300d5003038001d684608001004010310105544800e0959042c0d4100942c465000103180e40081d030814403032030710102801041060f0358030124003400c41e10b0000c013070070f90410305a03613911004024054a004c50b05820300300300c1d91007848100050285040b003927503a0310140c03404130300800f60320084001201125842c10b02410060007802d051040000202465415051640c02c80c48201341c0303001511858000281a651403d000179203c062403520340c0f0100d0b0386405941420010002c10b54142107100300f02d5070101940560744041030400c89600080d402803285011002443c16410095100c001098801c08c800038203940c40d4150841070700c045c40301c050005034000c0c1c21300440c0120805424003090500400310701c040540f24400c41c90402000182c1d1740c40381443c03000002d80e19041c107145c0000030080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 439470989 1250 439469739 439469747
    0x21c05060d0302030924071a0601030902130f0204030b04051c110304090b030f0f06070f1103030105010e03151e01060c170f04081504020f10020715050706090302070501 74
    0x1902040980e0111003150660764001d40b6441041c4003c1d104503800c444000030900804c007182c1d4a4060146c20580d0341d501c03420a004505841c001c041c042c2d5000c074002a80d0f9510a000300c1940aa019244081c200a81c10000d0040c0240c00728074803450754227001c00404511001040360185025001600c4030000080040c014548411094400e000c1c140840140189000044a080381c40389240000c081905d100040e0030070308404a00162803064050142d00020042021400f41d403007078892010b071400006050720f503d030074400c2075201600180010051b6500840c400d600c040c0d0000c003650110783e414160545400300a0302c0840ca034111442c1c581202e1a5108211800740c070141c01c044c2c601c2d260700d50307441001c101c00140c40c0007d00303004244406009049010749018000c0d41c0305898400306c2c1d000351101c1001d01120180d1068401d50049211818070b0800c40e03170f000c03089074054240c1034141b4010350702e5006040241d2040110410501012406900c907601e182407095001e0709800d407402c00010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 439472239 1250 439470989 439470991
    0x16140a02131a3106030503030a0e060a06120b090c0a0306020307080606070519110d05030904230408090a0515030636100e01080d2c19030204021c05 65
    0x81d00540346000d0544481c2c000030121084140c0141d105000c3c8007105044201030402ca5000030a0380c4404814002407050503048000b41217403800854078580c0c1d03400c2c9920240c035510b102d40442045040410740203d02c42500180c0c0c010703030782c00450f44e1155801e400300d44000540c1d801a50555404401e111203a503002600b5600b210b400c494650400b10390341c80c2d0301d40b13a2545988450004428882e641e0420044074070440409100034140c0d1400d000b2404d01c19282d0340514602881140380006000040c035074180b50f904014120b07200c1c1e0741981d80355501c1301200e900c0120540e5000c880d10100040310b5442c440c0310030a51848012032a2a400d103070301400034800780341004455280540741d04011200e4a000ca201883c0580240c12a17103031501c90300c0c4004503a4039044040c12441c45400820091400580d0360400d400342c2c1e50b03804905407100a01c029160684c003600080c645c52030b80d020650b16144400d007038207180007220b401c45503691740d0024049a03c1072445070f8071300007010318003603000030907204d00307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 439473489 1250 439472239 439472291
    0x30e010204031e0309050913020103060806090d0f0203040b041202010e0f03030a050d0f0e0a0c0608040309060e120a050c010e03070803030c030c04091e060b16140a0213 74
    0xd40c2800d0460791014000071910000303040c10114007a0758028140f060003200f0003440b02800e9a003003401c0070206211046191441680032900f00240000c40400014013240304103c00c101030544240c660f00100d500180307080100341180b00a0002242512208004000034025074844d200c0a101c41d2002500135a840c8000f00d20505070003400b11216240842202c01c6000341c2d03d49159074a0385200854001c3c482c40c40101541ca20f030074402d21110b038000610403141c3e40203010f140c60ba03a94545003121000800c54009000034a420b00801c1075500802807045054401000c3c052071150350745401c0d141403c07169040d1800c0e0f00070240e039841941c02030400c0712050345c158058640141405000e07947c03844080d00e081150000080000c007030755964020b55019000b06c140070700c20006c07145560040c1e611301e04100b8200c20700e4082c00148652200c01200c1050383d6100c1d00c0c028510858031000210307940c81c402a9601e00404c0c0b00c00c1d00582d5804420245c0610310000007c0500503610001d1a90783e2500e12 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 439474739 1250 439473489 439473491
    0x906011503091502030a091401020304060b0d05210f0a1e020d0503040b071106040b0a05100e0f0a0e030a050d180c12050115060509040b0a061407080c1903030e01 71
    0xd05010075009851841d04040e007450150790303902e90054410041001000c00748c001110440b04e00000207064004501441c01203c0038859040100c0030002844000c1c100204541e112840700d000040b5031240c0d600c50714003801c105508096188414102607407080c10074000044c00d00818007001a0380e000320712140d40603440107110700c4a103424042c00910002d04003816070340780c4000203070b803051190404203002e4000030103880140c100362070b00c0203203c041521811007081c00c1000159420342103d80070310444000301c842e5805521109081d0103190b0000e04141a4242c541d441d40c034107420200018501c0c2c40c12540c540b5a00c09031a40a50300b247c164030141010380100841c0c02c40801c81c0e66070700ca810703108031082c04a481c4119242580c010031626030400314501d0701342000111150440b0161200b00c5040d50305000501d07071002044040d440d14001c0b5000308045030360450845423502c001e0f2071400e206140c1146400c0c0c22000c0180340c50000c0700e551650382d05c51003120f0300b0940c0c1801034880743c80e48580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 439475989 1250 439474739 439474751
    0x105030304030308060301020f130e0109110d0203040f0b131505040503190314010603090605062d04020d1506020f030f2515150f0332060906011503 65
    0x80d45a109a1001034100400e000c04141169030039411a44016401110380380d032a0340176010216801843d109611800030800000a501c203003500410741e4401c0009807051500d81d0880e400c0c030082d00003030030a0764070149031752010000985a0f048a409441680022111401d09290140650b072606140c1d0319428145410301000400c00010b45245640c04004205041c1c1c0780d500442c0145500c41150412005002c00014102d03010360203102040c0c0500350920039030f96980203111240e140d190b042102c16130441c040c85503a00103282001c8250380700800140c44c00340302d1184035054a44c18aa65043e03400440700c10085142c04000b259900284070f0091424071807a40c084429a00840c1d0020040802000341049202003040c00071072050b0340102990061190b44201400038a04a8190498891101008210540071090107011280d200001a0580c0c100500540141e044808000034200a44201c0f440000301031000034424500000102419031501040b20001e2070140c03000001d241c0385c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 439477239 1250 439475989 439475999
    0x180405160305011a063c070309090e010b010816030204080307050309030607091202130e011a15040302030303010b070606030203060108030703020723091510020a02090606161e0209180106060801 85
    0x10604500000c861b0100340c821100f10070400c0403480c41c00d20346248100c001a0000815400c03a13800c2081d02c40c4c20004200c80c1701020907160880f0540c2c86940c6c040340c0050001410580025803a50a0442605d00941056510302e00725180d604106000c0b1403541000c02c0f480d450b820f080085030303413013846881e21011140ca00448202e03500103482019020313004000c00340f071404c0d00f51b0300b1483c0040404c00c000c204e00340c105412076036491103850580381b1a006014901e18040c0240080d9810740b030700240554a903928104030045560b0129030200d860031b03103c82c0f000015aa083c081c0314000c11100000d15515145854001d042007699001100c007400f07000144200149110902e0001d2402640d4450b1152220b081800e411b010701000d0704d500c8803422260f4051142d02040c050b162520075206184135864010401507103000c0c1c1d1005603018414042c1d42e4004c520740002c0e1010200c005000750903004259004101c110a04031010108440b50100b60302d15103c091050400400c142d1400e600c41d54101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 439478489 1250 439477239 439477267
    0x12d0b150a0305060609090a2a0509060d230a1b050f090a0e0903090108090607020307021e040f1e050f0a0e0c0a06030c1b02180405160305011a06 64
    0x1c400201c080540e00d40000c0c0700354540034200c600b5180010249000d900d042c00c8480090f01000003e00c0d2600b11203c8a686000007515514080d01d03d43d40b2100e081183c004103000140c0c1101c0c11140c0c2d040d4a80e000070000d812660510040d141a05041c100203290410380c5005451002109405040e031002c40e0910607503101d0113440060740c4403406641e03105200000074107500020340044118900940c14030114110000050103801d60a8035280c80c43c1c1c2e9200d213801e4480c0001c0364001e015070000c000190061401d0000801c000c00032145030341c910b0481c100450115004400528482640d42c000928040106e0304000c0c901c001048080c444da25200d03511103094900508022001a1542c0f920301041009001c501c8040b0f1001d000a09420f5552000801500e031610220000c941e000c50b840d00e00070a0b64190030704241d000303840a803036800045460f00780c00c10020b06c15266030081c10811140342c2c1e211001480294001c01c0045140582c140010088900c0382900e2449200100320910070b580302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 439479739 1250 439478489 439478497
    0x4110a0b0f09270901061401050309060c07170a020d030b0d0f0b0910020f070605130f020904061d010b030106060918020306030102070209160311040e04060e012d0b15 73
    0x90b00c400182d41c03c0a4180720030410740c01c0754054070403c00c10401008400c1503000400720303124496103c400d02c1c2d052006441a10040d114a03405400000c0010f52000f0003030000e01c03c0c00d124031840c82c5c0460100d4101c07a8640c0041d002000103030003c40340914501d900d401491080d1904a80403403500c221603968640c80c100f41c0000800841000e1700183c046a000d0254a8a240810031309550b00e950070000c0c2021944004000c441c02480c09010500325800310994049081d4003600000c05e25045800300656584014400c484103a01c2d085841c4800d0903600c20002911501400071842001d45c204141c2512402d030000c00401403c800d00b0400e800c1203400500740307450104401a50307501ca444c0440e0180c86601c0c00650040003500920a000903181c41c2e40380d1100c0e10f035404000c061410070001e00a0f219521074138080f04111408140400d00c0c0b6400160000c03010000012000d84c105100e080c140102088004034204480614003030150b41e0103840c8210900b144c14030343d40d022100f240681d50103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 439480989 1250 439479739 439479757
    0x91b0512150103180506040b010f08060a05062e021c090603020c160b07060f140c0a020a0506010f060809060103050304180b0a0f061b030206070e010e060304110a0b0f 73
    0x3001c103400c281980d01035031060144001408820f484205503041140da50402510300310f0700e0010110000035040301c11640c40301903e012002038030854440f0b20f44140074080c050f08046e070121035100d02c1080c0384502d544007050703c001c4140d004503414000c600030f424207420310240e81482014103484103100340e0003904901620000d040060321094402c60381032030182074010641285191240c041071160301d000c007910120344100000c1c0b050075180c00428060320000f140c8201582c1101001c40d40005003c4003034000f001ea2841211500c100750340300c252503c1400e9100c40c2c1c3c61404500103000c039643c4040074507403014803000202800c2d45581c0c0d07140c0e036074840c62003400c41c540c26600c11051801da80c0d400840c0c039940b00800b0002c40c1c60711030740504010700c041d12422010500c81140d07524505610450a400326030982c010307007156554118151121513211980e81d040205020301ca22140e669800554011170040c01e0f141100702c0d400f001e0003841129500f0103010f0103800e121001070b6030701450440350048c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 439482239 1250 439480989 439481011
    0x20102011b0e0d060906020a030b150c0615031504200109030809040e070b130509070e0109030605060301060b0f0415021204090c09050d050109050601140a050607140304091b0512 78
    0x8080d0404c480105044c0800601090002071601c10362a03054000130020403045854200380d40d95012112401d114003415101d4035003001c0b0010300c0c110501072582d01c1401015064507001868035040e00035038a41110201d0b004400c5074801c5000803c241c2c02012184000e092107040203041d61a46d07c0c480c058403820034806c03a1034040d000a00729051040380f00820b02410020344440c4407082080c000c0c2e07201e0196070301800d2042c0005231802c0c07003043d00d2081c1c840e0603141c841c20982944c5503440913110043c1202d0b010743d01c4550018032505010300610380072224202890715281043c8803079000c1e0070f019541c0340440d4420b61ba20f0004800150840b001c0f40e41d000400030340e0440388441698958802ea0000e54003c50300c5910b81d05115042d0400140e0a101344103440050f138a5400d40d10b9141080c1c406607410001c900380030301490400600602086008010006044401d001c60034590f034080c0d003100f0041521500340c2480208280c0b6009912007603403c0041c140076042881c4a0301150040c4036154803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 439483489 1250 439482239 439482259
    0xb03070302091305190510110a030b03031c02040806250c020d08040e041a100504050604060905041406060f0d260a02030408060c0903060129030112020102011b0e 71
    0x2040c92075140901c40fa9211007034070200b4000c0044034511400c0c5c00340a0307640707010306420403a00001034842e04199a514480c8a4101011000218020500119003940521040181c82c02801254a2a40b03215405440241c1c1c0d85083c40603941c00d0060190482c0940c1c000780000c14081c25803c1540c181240061915090395086800015030460185070054140b11002030003048030b0b81c02d01e42480c032683c0140b241e02d141d03c02c00c1550b5460b60400322000c00001c00e2000090103949840c1d00010b1300110300400c0442c1d1140c41340f941d030f0112001a503040300c0e4080d000780c0e030740100c3c0c800740f2a0b00d9014001320b414200e0340c20801c0100b00118807940c00100300610103e10040e008100e06140451100d000c40550340700c002042c0041d513203034024003500c42e031841040c000403005007800085a80303011000e400b42107240d1030501c10f4050f1490702582880b543c5039415180b01c001d2403010145000700f0b00e0909030703140701e065400003900b1548004a10540300001541c00380c042604a614003200b039905682020300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 439484739 1250 439483489 439483501
    0x703110703021e010206070c030516111f1205041109070516260309070618080a050a021309050a12140d05161e03090807151e0b0307030209 61
    0x4040407078100950100c480301200c11a48081c40b02c0c0c048020f070a8088480644030203c0035500d00c400c070710005001035420405181c030b81007100505080b80b8490709403101c3c40942d01d0300040d80720040074040c9240081000e02c240d1000da00141d804441c1d640301c00d0401c850304250304c1708407030791300f016a65070300420300200450100c5200d5401c855030304000c034044444500395450301c007414991031210301c1184080924101c540c04100c8040700e0242000030020700d41c680c5400401c0d00d800001d000320020055114000050081040c0b21102005100388060410308045104100c800400e01c1c1c0d0f064144c92070024640001000001d2100101390440c04441c55502d28110480359402c000340d4081d18410003164200341301840760031041c05013580e40e010f0440481e04413804c0703036440911720524820301208044410032a000c1d910000e002d03402034002c03034a050500d44954180304807000c0018174959843c0a6281d01d11540c001100441000b09801c0c024070f00c0a4000990b184050302011b80705610403000300704 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 439485989 1250 439484739 439484743
    0x406061514090105121e0109060e04021009150302031e070f110304052e0c0203061810090317060301020f0418021605060915070c03080a1509090c09060308070311 71
    0x202c4001c5ca40c0b40c0d41507515024012000398115400340585a00c1c5110001c02c0c3d06c00640954404d0700c00c0800159182d030340e50307001c01038000304510f040420f000c03000c1c9000c1000d5903610032001d044100d80d14096528113119006008441e014214041c8036040c03401441260341d0b00440450760314160780ba09440e007440c5040303540c2c2544159801242e1210704a140b8041003200c40c041c0c580340c040c000d10010a4040488002c0d07a158912280c000e616411840000791a010951340500a81080000710348043c00c070841d40310100d03000c1b00f10030f034007003040741c0c0c40405080b2000d085140e002c0400e400950400074005c0104940303000728040d014901d0450304100c48071722010f50680305413031945186188000403c3c02d00b40c0e22210140d5502d582801111101d4025501c1240a81c2c081c0720940d071100c200361a035460840704c500c00904010b58154841403000300e003001384e04154015101c0040f00040000c250701c1c004910004030351021030030b1400c0c498100701055070306094458141c0c040c1400c0654000c1004014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 439487239 1250 439485989 439485997
    0x4020a030b060a02011a060301030b010e04060605150309162301140d0608061506030a020a02150a230f01170304030b040803071103090d060c12050f0406061514090105 73
    0x19008100490f00d0101c0740e50540101c804100840da2015045e40300c03c06000052200340006041400f042004002d981440c0360160ba2040c000c00c000a072007516000000d1840300501104491181c000c02030120000f010f01c03050708100c4910b10000c0c1901d10308203c0711000a00001ea015a0030240050340905074010045030040341c10402050341c0d950390280c030060081070f903801011842d104110001d003005007081c0310480c0980006182600f15915040707000701940c010084501103008010580c0c1085090128442c090740c1c0141d00802c0b0400354015400d5000c040d00d600c07108450484052041510a000c002c81c1900d040440c102c1d558040d40460510354800c41d44014107500f80b1808100600010034059401b038012959030b9852510302140d5260b49001d00c4010a5000711030640340c000041081d8451182503d160401840d08103500240e40201c4000310360241140120600f0002004400d00c11a8003420060620180300441c09200802c10f52041d04a44626480020b452060780c2c0118280c0e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 439488489 1250 439487239 439487261
    0x101101092301050105092e0b07050601080d05070201080f1012080903060c04061b140f0c10030e19030302122a03060d020d0206092e090b0904020a03 65
    0x4020040007440e07052000710412215025954038140001c83c503440d0860310b56004080003250f09040b500441800013440e1401a000c0700306180640b400542041c0a10243c42814050006000765624103240743c0d051141072140c030000c00404115980060303030060300c04d54019110f0034441881e5590b1140135a501c0805402c61041040c2d060034901c108880301c8001c0081030b0b4103905035451034481c07402500841c0034500440000c540d4000406680301465441300713070b040340140c90000d1030300d039210348183c1049130054603550160007200e160707041420402c020300f000d03900f240340803c81c01c91440070300344d12006d500a0f0410303082000c0d0581c0f0203140c8030750103648848075811640001402c0924601c40703030a03c0c0c09507211448104e805244141500081501c0c4540c9000e000c102d81c03120b45500700901c8540005089a00020502c10302100b520340004071a201249546044021030b0b980e0110000401c41180f00e900300116180e06000c203401d038802352540c1550607600503844404020040d00a401d4010300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 439489739 1250 439488489 439488503
    0xa0e0406020c25050108130602180a060504080c0a0510110a05011b1704080901200703031718070303050d180b1006140306060a021513150b10110109 65
    0x8410b4008000000300c186820180760888440c1c0e13120019110386208440d01c1120540c04041c0101044140e001025014a0700e58241914500500084d140c4029504070000090000c102400000c0c0104458000420116038580c11249404c000450f0b075200c105080c4200301c8402c580a010140800c02e001c6038a5021000340880d030039088030a00d1201b10f82e600c4500240c00a0700580f42c0341c08071644280140d410010591038915000c1c01541c50560b10500440030348a03041400c0401d5009101000145100343c4d80c00001001c03203941e0f04c01095016000c29240c0d01070303a0030320350307495400038032201100c1d41810441e8a03948030400010040c081c0c86030004110101070071400410805910742c0d44103a03102880c960605031581d200f01c07000721404a454541000820129070f07286000d00182040d400688104c810888400403240741c01001584d00311590042035841100700110b104003080d050350105070400075404498005600c0c036022982513014010480716000b0704010031342040d101c0f1504802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 439490989 1250 439489739 439489753
    0x4150e060706020d1506210b030312010e01060206090d0503010e10050301050727080c0f0a0b04080a030201060603051e060a050607030c05100e0d03020c03130b0a090f050a0e0406020c 80
    0x1321002c007034240048046102020b00d00f003c2400b50269541c410402c422a1000000701032004c4540014401b070118a07078148406c0c007012200740c01020b0041c1c0030300b100950850305540f40c498040d00e410405002036400740c02030001000c10036448001e40303045403100101d0f403505443c1c5201a00d02c1d091140c01064040d420001000125904441000280c1045d03040d01c003041c01c6000420170404c6101e0060a0203600f14041d15901460300502c280004540140b43c03203401a5141820b4080e0b5006901c640c1c00364101d000008181034080c0b08220081c0503600303081c0054540302c9464540c84003540340d0425503100e038901007419900d170301321414080c2c20080d28a03580c40600c0d00340946900712400d811103c901c50180304005009140c001c10481e1043d040090880c40c0d510030041e8081d4020b8540c428007403200744024800e4030b446090050042c0444a030140c3e840d2101507001301101c1a43e081141480079240e8200030740e40301ca1000304120740ba030200e0050192034514280340030717100d20400301402d48644c0d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 439492239 1250 439490989 439491007
    0xa05071809050717010807030f0602090a0f0f05060a0509041a04050a0209040609020c33040f0b0901050c030c1c06090e0f0714010804050a020d03090f06020304150e06070602 76
    0x80e0110b80241841d13141c002060902444550341c441c02405081071a03040608100700003021094260040c41c4100405418050810040b40c0e1252460340100741c1040403401c00c00c2609840c030900c0d4086d04040d513407140f800b80b031001c02174090700c102c035000c03401256035080423120900000c0d60012030320301c018801e0045003040e18081000c0c0d0006240148030b145880d00028200c8094400c0b600c00f00744500c0504009011402403241181d0f002500181307220b450390880c84080007000e28603108034820703035070091aa100c504000b419114000c0241529a141c64148803000c2140d1054950080c81c1044c42c45d82d4a41c02003d2000b2910700b0804801203600b8001d010a0a48240d000400c2580e03880d400c03500300100001c0825074442040c80b910011648440500d00c10f5481003180c0f546c058001d004640c0380c1d060319404180c0d98181c1d0a0f003540000d2003110188884410140d0010080c2200d20046003001d050404400c60f018402d1030031404c0c0b28841000502c241c848900340c0b4080c03904950f085403610140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 439493489 1250 439492239 439492241
    0x90c090a09150801060305151009050f2203020714061c0b0f0319060207020d081603080a06082d0610030b070311180619050c01050603150a05071809 65
    0x10000d942c40c00407004000c519502c0501c5001c044980120040c0081e44c51804410509640682141c4032500c00c0d010224034240e250203240d01600d01d03030200172004c0c540800440f01b40e00105000d102103034103100c07003800401e5000814034240c0e550307026180105044039000406c0b80c4640b240200c8924002941c04203a503d4950180003180015924203002c003162008040e1603604040300c40c0c03419181e105c042c4004ca000c1c0d41c042e2174914409821803296410a8a5606140e040049448401c021601045041581c080800e5030040300600086c40802d040982190b02c03958010b2007110911905848c0c2900c00d0070350b03042c00d41101002c2c0c0540300c01c2d05148102c482c44620a000680c1c26140b07172000309866920911540300c64421518005042c00d03000c000c80140e10501d400c1d030030350100007807211341c0041c0c003c01c3c0020b0304030f062901c0703503591082c0c070501c214291000103240600c25000341483d04081c107501580254008000d480002d140c0e51000c4081d5048262034065505d10741000e07001051658003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 439494739 1250 439493489 439493501
    0x509030a0b04230607050c10020d1a120c010507230a03020706020705010e0f01030905030a0c0c050f0d0b0702011103010b0406111614060f0c0718020a0e090c090a09 72
    0xc0d0000c9001c40b181404480c450f8004000d6001455211000099159100d0710103003079080e05940607190411031443c508020f9030041025000000c1c1c1d22001540005012004040c0e40308090b6980b03011802589000c07522084000320036818880300040083c00c00000c01c0050141e000749440b00125125201805075607524484d40072405807190190201e20b40d400007400c082180e905031b6800f850f5601030402c0c001750300207118200b41456260940c2e04002441400608041c459983d2200c0780c3c03560900380041100525030147c2c0c0140c0b401d0901004948a090410030040c0c0c01c400052101c0e114844100d004180c1c0450742c80e01c0d40d801000101700740442b100144100c1d105507a619078540014070120781c80d4082d20805181d090b1300040d08005042c4002d040998a400042c14182001920f0080d00703482d9004400045403604404010710050304601080111154240411400e0080c100d0024144c015074280e040d03c00c42490002400c0151a8000c50303011100103420910511ba0b180603079409801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 439495989 1250 439494739 439494743
    0x6020c070302030d090509070f030912030203161b0b1305030a0e1806031e030d06090b030d0212071b0504020a0f030e0a0302070e0601140406083301030c0509030a0b04 73
    0x40c01c2c142410300745c0303e004218144d4800510301da0258a034000c0903500d240840750740d0410700d6212000600441da107940440310300c1449440150344d9292045903254405420407a07030301032050b84000030700481c0110240008a0b0351100d59920141c4606403003001d00d840d407080051030342c4000510400740c03d50180301c1d501142001c1ea98000707882d4a2022a46000c42d040316000d130140d2150401a02c1c1c840d00700440807140040d001520b00e404000b148800a541194000403103a0351940205c840314203040140082d1f1002c24805007002d00b4400c0000c1340301e0302c5041c1c030240c00da8542000405001c01c07400c0044000740002442103540320307108640035040144042d5040c001c603207417406031815040302040308074a4a506a015040c25070030107990806041c0040c010b42c0c100803503400184482c0c216400140050581074940110310305d0a02038007648c50f446a81d80700e80c01c045290320901f03103441c00c40e5851040102400d0120f23f00400002c1143d0303d0007011503c541c1b40c4919100305051080124481d0b00940c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 439497239 1250 439495989 439495993
    0x7050405010504020f07030e0a0801110702090c0f0a05090a0e13020306010e152112070507050411043f0510022110080a111c050705010e0a0306020c07030203 69
    0x40c0e6240100412801a1031551124040c100481e2000238400c5c00307000044036000704050300054a60190380d00b11950008aa0011140001c0c036500398a44032038842da01980250145242c085602c070010800c1c092060b8440500202107102625941d580b45401c0290040c1900441a40b070304454080d003403072160340300340d00038000c540001c11b020b2a04840707584a2800c0820b402c0007910741c8000c0c419495181d08a01c3c030a40808652030312802c000f0300c4000044003903000090b0b101d04681c21b1150400c0a641d00091185103003241d48160509240300352800c541e030441e2018520b064001440b0582d0084240b591003c01d8410b040c4c4401c20180d003120004a802581101d1702d201e00750300309204a00c190001c80f1404560312703c0d81070500d05004140d5074032440260344800b21680e120241860300390104411101095040041c040a04100c60300d40c044404204100010310003135250313a0307203802c924040c81d410040f00c103201084a854030400400219400300d404c569035225050440d80382c80190000b00c0c824 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 439498489 1250 439497239 439497241
    0x1b080411030c0f01050d0603080c16080f060403080405010e12180d11040c020703140319020607080a0c0306080a0506060f0108010311010c0213051303020c060418240807050405 77
    0x38180001c01a9482c0400b8200c100d0500c038110064070541c0001c07210301c111a48074003011001898440181a01c1d0300c0c000020048508600e5914810100a400c090840c0d4401d04800b0300a8400058081d049909801c000815071034508003e405402881c04490312803050441000864010000810098034501021b40d2000c00682c10004510041c000207050f028803071b500200d1030319140d030084811200c180104c1e400036907259500b407102c101500380380c0d0f0a90004640044c1e111400d251000325025184040e105a2400023009003c0b600e002e00802940c603525086da03181203000c0d41c0102c018080309011a1a0070303140b4030348036565480841c0d403107016510001101c1e500e54010302c4101c0c16240e1003181d0341c3c141e007008001107482400e0000160fa02803010b442c0008254000c0c03050300e020749030b40143c6100d03801c002e003406480c060141c042c05005080c00c1004110080141e08a0900d103500c2c15808501c402c42c0c1464008410325000b44c2d08400c20b401e07035000515290000d41c2170101d94044d1018001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 439499739 1250 439498489 439498523
    0x40c0e180622120c0b101503050709080f011505090105030307110301060f090f06061803030c140601180507031802100c0503030108010e0c090702070e07031b0804 71
    0x1200116408059881007021903425515021600035662a008600302c10204944a180c0640c1800e52058041041d00400300c052041c0152801d9014000d200c0c280b601c0c9240c2048402a800040980740c01c00d6598000b003034019100d1020440103040c484201e41c071800c00e07400010300900c00410400e10303000c520750300082c090410b40c02c098102c410042c041d5040400e96110024804640d61005525541c2c488000c140491110103040c06410510390002c0c000200000d044d007164030540100003848513034030301e9042d50514181c10405580d03052408111202440c90036035641062200d032100d0030f0040c42c0010462949189000d1024005420b0522445d03d8841d0194111061900346405c080d050350b03501c10150818001c482110b0781c0c24601801c0094660b1141e50071b5400c03e81002e81c05946510700c504154408009076a080a402c42c0e252174982002c21019666120301e20400c0010000d03074000440e6603000307621101d0082440c01050101c0c4482070001032100c0c02c1124101c034041d41c2e459030892 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 439500989 1250 439499739 439499761
    0xa0201140709060c0314030a09030305070e150f070203030d1b05091008070203091503060f0612010e060112060303091a070b0f15031c0305011205191109040c0e 70
    0x1000751403544680707041909060044490221160094007448084021040c802c1441340007944110010785001402402e503203801826990007500d01c0c0704000c0c24041d2041655a2002e0b003000d010302030fa500c81e41c0d540c0001c0c0700030194001c12402035858040450701401c04141500250000040c005a800350716855110540d254028202e00780c0d0021126840308150a000d1003a42c0e40288050045a0030041d4080006444100c440c1841021040c040244036440c145010f401170785080c212001d40c28003c03000d900c5448898141300c1c2d06041143e00001c2411a401102c6a013039a921141c400d2149580745c0c20301070107a40a0348142e00c401800c02004091610400c800d840b9001d90103200e0385030b107454020118031100405403401d80d03200190020a400d80d6407c020030301001401c89204810403c11000c007604403081603104403070100d1944040d80015002040034204c4180c5803030385d4180c00ca90b6040405c4581c05580f04207820215440a0005201c40d03209020100c6420a890a507681e958240c42e41d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 439502239 1250 439500989 439500991
    0x60b12060702120a0e03030a0903060b101e0302040e090d200307020d241e06031509110405010611010e01020a1d060c030f0c010f1401180e03040b0a020114 68
    0x10380003002c4004080f007000d001440381034210b190030200350030940d00103415988031068210110320500303020810000140030b595928a401c03129048621130b20140a001c4400000203e100301d0094a20140c0b401d0081c0d06941c040c0c1088541030046141000100341e58103001048603001c141007520821240c40c41c0402d0b071914280b004051420444503500b07000b02c0d129002011201c180c407503c0c4c6441c07509500c002c003045038044028007207501500035401118000d00710040700b18032820702d9002c2c00401ca1024000001f40300550001424440d035042040c206842e84c001154080d09050000510039031011081c1a0a42080020494005c18020040c02c078410380720420045844013181c10051162a440f41c14040c0001e0a21807900c42c0c0c0071030450443d07000001070103600d00045a45d060700542407003005001c25032075808120300104242000004141403250808507002c0c1d160440d40c1c10051f812600001da00001100d0701c56072502c54445031038002e031002000561801c2403a40301084108102 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 439503489 1250 439502239 439502251
    0x105040207170a0c1407060e0a032406090603061e0e06070f12050906010806070201060311040b011e080a0b041404080708040e01180606112503050109060b1206 70
    0x50202d51040c09003980d402c044042802d10440003600c0c1c0108000b80c501c1c003188507034103000d010f06d1b82c2403031000350031040b82c01051350007440703099003e0000611043c00004a80d4182d605081c0380c5040c45410740c0039204c1c90700416106400c180c0000104800380c0c2108040c507802c0400c00c1051281c2c844103d04480c0400c0d01101d0660000000c40c02403401150144400d10304d40c80e040b40080a4031091400780c40e0203480001e803aa1100300104075040c000d2001da0380094280c070003400f85c1031860710303940c11001c8643e0302d65100f90360328603d0300601c2c0e00444600c9a5010700e00312107012110074135030250226004450381d58595041400869107840c140c41ba11104402c95014034410b9200e0792210001900003060403a02004100008140807804031040d5008003940a8035009a040090580055400c2584180e040c031100c2074115100d000d012582ea400e94038214200e1484d0007031191a00800f00b95a400904154a81003501091010340e400004a01c01c00307640005440c409804116511b64046441c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 439504739 1250 439503489 439503503
    0x1505130303030b24130510170c1b1e0a08030f040f050604061a10023d0b030c0a06020604060b040209120a020a05030d0905120313030c0306050105040207 67
    0x1040c80064000e0340000b00c1400094103011884d4488402968803a18042c15407406080100d030000c54003000c20b4400300036240a6a5030710a0b803001c00006000c1c10304d09420125500001c0c000525100d41140a40d4074400039166611071a51000b4029503c60801036081d0301401c1c800032915842a00000d540f980055026a809285aa83c0c030303000c42c420107019008568510227441040003240c07007001154015405502c0004005e944669002c16110a00140ea8000d020040c541d071800c0e6001f18002c0d80303a14248220340081c0038401f03a203040e03442c0584804141c85040d40001070400c000c030b5001c0c08110202350200c85607042044104580380ea154403a000041e0300080c0050b0015000da00300b504102800381025003041c80b11000100e0302c4a082d00c032805240e10508218007546000b800c0da600428080e005404030340c03881403000f4084c5a40d80146401590002403140f80c9040800440300d46140d44080c0080d169242d00e45800780158910080d82c045040c10000300e4030303141a20842c6c5030b03070b40c1c4184 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 439505989 1250 439504739 439504777
    0x3160b0a0e030106081f05070311030f0402131d1509061801090507031a1b0a210e0304032105070201120e060705040f080a020603070305060d12091505 66
    0x80c0031500c0c103400580c1c1c150103548800c2d00042940c410003255150b0092180d0599080300f0411402044a0005108000f0503050103030700d81c82d00380180110383d00003002c030440120982c5c860000c1070302103400400c81400240f9060a8158448442030f03803180c0c4000394016102404110149e1240700a010b8801c0390807030b049040807806902c0c0814420b40046c46800020403100f132503803205802e103185a401560300d810000313181c0010340004020140d00010341542d8410110304000d0a41756401624480c0c004d01025004a91a078403220484008c3c000160006000c81c040c21301085031203070882e12007140c2c803521154242c0081a0400e10483c080207055031000d0400300b00380c00448170035280358507458100c0e50301c805108466005110351031107603a207511460394451600b081c4604000b910340c400d000f250455102c2c9001640c0c0c0c00100c0350868100d00d40400d01e034440d0b0000840804901000a01207010074001c2942503800c80240e108079840c0ca000258100701e030620a40303091040300000420f10715000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 439507239 1250 439505989 439506007
    0x210907090b1309170703020303060a120507030201080705070c030807143415020d0e010905090f06031c020a0506060f0d1b05060708190e1c0204090b0c0903160b 70
    0x40d004124140c0a04c00c0800220f142400340c24103540400d0b815001600004204141d508200c02c1c142e0040c85410550300301e00569848043e1589100c0c080241001240c00124200c0d600c02c1d81a0b0f841c160700480512205517032864000000d92003944101c1b220070015441019044000c104000d02841602c000c4200745801d040a41c40e08032040507442707166202144c0402c2c00441d00b500d084040c01190004c0010f0300c1400703006044190681c034000d0400c13240c802d0034001515903144003a0007658981c48001d2a44031640060700341844415580008185128000c0e200c03a030024451150500480540e07000e5121241400442c030303034030202142c000e01e00401b200e00190403882c5024100a02507200c030039854a50740068440d0380200b20980d0709036000b0405814080e50f40d1070b00400744015003070142e00114860041026400c108400100a00a1402120a5494503080142003640c840c151380c1281c03400740e071541d4075a0004103900c0d01a100c0c489407054011604040ca109031190f03103079800e007401601 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 439508489 1250 439507239 439507241
    0x80f01060f0506120a091202010c1103030c040e040812040f201c0203070302100c0c0e0609042301020a0921021f031503080301060f18030303020d02210907090b13 71
    0x1502104034190359400c6c0001041c0c50818a43d010992503001058106420100601080d0a042480140e41080041c09120b6003048111340c1201d04228507020304c1d99a5061465050142d4000d40341d00e1403207803042008006160030050000c5c0e01c81c200c88078200d118008030000400c0c20f022060b8010040d0118000300700701440c1e58802d07141c401800c0310041c40d169400700d074407003094078004801300d0101c10583c420007102c20322140c09000098201c10307240c41c1000001d07000d904041c00107004041c45090302c9924400700a0b0621078500008000e541d6038041c0b080040c541c0000d0312803d0029071084d1080c20490403000c0b180c100b8140c0040c80399804502d03021842604400e194500070a15580300c00510030109c000c00810700560041c0d400688942c907140d8003501203440076840703004220000c20a42c41040c90813003180e099075014070300142c070340c4c6681d00181c0c02845200704290722803e070940c11310405070840e42d08601c0340301c00c002030341d070000c0c0e5540c04481035410000b802ea500240042d004408600b42d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 439509739 1250 439508489 439508491
    0x112080d02031e01150804020d061503050c01030c0302090f06030426090a0503060709210c08010209030f0f030f0a09080102130306180206070b07050f210f0403051b1204080f01060f050612 82
    0x404c00000c00c400c0f01031003282f507150154001c031540c1c1c0003045030541a6805101d40c0c090003442d81025464600b0341000294008003901d1090b12404010010400b400080d202ca24101120381d804243c42e6035840240d60f5050700300d030342110311448413254003240504022501c00c1c051181a2074882d820341c00c1c0041503d000441e101880c102c11800d040b0310010401a80c1070100401c070700360006036140201d00c14182003190a40e541c165030f40c01002040c1680178008102d441c20007000030825103402003030204958081656001b04003135070011801d682000c02240502c1d0459109444c01c01c101c6001c00d82950022401031006944081d09204000110340b8440900f54084030074074202d480d086520404c000103410040c04120318451401305c0707200701c015107802c90f50070010b0034203102040c1c60255001000c0307219401080020500010030740c0c070354502c10800c204d4101801c0c20703850703203407516440c840d55254009040e1725419800c00000003000c1d06100419000d4840182c81c1c140383c268003120020640070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 439510989 1250 439509739 439509743
    0xb07031704050c0409060603020a050303030402010c0b070c060c081e010b0f0f0408010c170603191118190b04060f050603190212040201260112080d02031e01150804020d 74
    0x10700d10b07546644d540301d104003089036200b0a0f0003c0d10b682036006000d100c000c6900a540a544104103104c00b607131b0000000049280d000c42c001c5000e594046003125204601800280000c0c10f010b82d208290707400002187c412607010404201142c203920162a10003400c2c4205440f410381008140c0702c9019080007004e412031070100b074a1030150b9902600e07084406c80c0490800146001c840030304100890700d11250000d00403170007030408411120301c00030f00021086006102440320104100c0540b40c2030300942848012001d21900ca15202d688035549415501c035201c400b1b440d0085000c00c030300e450311407001620303041c000c1d1a080354140814810164009802080c14402603c0091107520990005061880300000e521640341810310001d0070307240c004089030998003c60b01d010010b400b1144c1c01541101c0c501e0300516000401814548074501c120390130703114480d00000420104004025035a101032030a0014000e240c1e0781d6106010a2141041559000800741030214000d031502920242c8024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 439512239 1250 439510989 439510993
    0x7021b0d0c0e09010905070803040302090703090501140c09011205130209190e0c011e080a0c210b030c0102150403030c030b0315042315090c0a09060f0b0703170405 72
    0x42e114045030196000c1128a16282c0c0e4440d01c0c903108004d400d115400050215400841c20281103030b002410100c0b00410010815070303901e0b000c0042c003130250032101c91260440f00d00901c90a24442d0424194810601180854040c809441c0381406911401e03100e0640303c203034201d00603001e508100342280081c1104203c5a4940d140c0f00084181b807049802101003107000300a18102078001500300007442c100504940c00d10b4409690a40c3c2014060342e200985034400070b0b03401e07141340007a40c400d8a24400386002c0310b203c03101441c90610a600c030052840e0110100d41030341d10f810300120390b5043e04081c4940340a030300030b0100c0c0010b4025000541940d80f9801c01041010140d4040f81c6040718582243d5884014481072005014400004005540c40f601d107204030341c2c1252010a941d101042c80f40400015910005400048280a12010b41c07400400907045c00d80c1c0c600b060b0380034010380c1c081c0e0020f0034905100020048c06410464210582c551101c1020302000c10030140c200d40002e200b0707207440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 439513489 1250 439512239 439512263
    0x604020d06020c0d05030603060a1e110c01110408060c040510230705061b0f041a070f0b011a09090f04050f0105090d0306080f06060910050405040b070807021b0d 71
    0xe41c800380560030460307050385d481765201d140c454101854000c019010b0314100b0b1401a02001403401518012080d41100c100401c000b810380c030581c070040c844c004010f0301552800300001c80840c81e000082c4111440749045510980390706c02150720a01c110701c1451780c0f000000301131a600c240540050103004600350321400740a20782da881924140d002880c00c90fa03a41002c0c2c100101715249484104a218041240c1414490206101c03111486603015400400c68440c0d2150600d50120042301c6003180c0c0440c1032203210b00340c1c0c58101400e000038061213268000401102040d0344c0e0b03070b40540b0780c1164028105c0a05450b0055841000803001d0015a0a8002c990300c003000a4001d0050302c0c040c5088100602040300d42c040b000b0116001d940100382140c106440300d8078114030009109402c40c40868034070761035417906244402c1c1c0144603805a1f0300a810101004144166194001c0c4180c10780e482d0300010703980301c2d1412601e506c803004210000b9039000e020000e03141801c802c0440300c039100f0b000d0311a107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 439514739 1250 439513489 439513507
    0x5120a020d020a08040b1602060601050d02090307030f140c06041202060d0e100c020f0a030e121b09070305040b0117010f0204030c05010f02071406030c0f0a08180a02030604020d0602 80
    0x6030f80c010310a85002c140d5030300a000c00c0000e504100d40c1d0000006210030b03e031898240009403615000740280741003010100e94421400c0d00e65048400d03d0600030121040e02d507880c58a020044030070841501c400c3c4a0501c41c1c007a078880400e600b51500b0004248514060814820900610460000341e0700480280f100b101c601032207100d055144038110004083c0d8050242225068804e1020a4411904246420788209200248103604554181801d8a41e107090740003223040e03405480c4a4100e544035204400c1c810041030314070048411420f40710b40d142507030b0381901541600c2054400170010280381004000c1941c0780c8504072103a444203400410380700c54030600301050340c11070b40040c0c820b084440c03001c1100e580c11005100000550b1300103014031600d81801403032194008003900780500c100000054403181010b0031221a8006c0641d45030f2501c00c6250000c1035960708840100303614405c0d28410100035000107569641070350041c0100410f40c1c5a1742800201441c40c1300444030030380c0030301c24810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 439515989 1250 439514739 439514741
    0x2030a0e040f060b1809160203031305120307030203011404060305030717211005040b1c02060426010506010908100b0d2103111207050a021005070504081c05120a020d 73
    0x80096002c5d805070080c034480c00c00c180340f1806003c081c5c4040d13140800b0351030640c010003903a90003c06041608102134450800d9410600d8804403000d050f4000030402c40c0c00e503019805541078405540e001c090b204000350501081307038814080500658000d0109800044665150100300e40c01a400e039801c103030413421b000c68000310303449807200d440c20f1601c2000030010080010300c005100498042c80300030502f8000c41c0b0300055440c410000c0d1030412481009549800703041707034014000000441c00134441030b050032716440340b0a11145101e5080c000800c4540d84912180c0b000d843c80c00c80640001c10110107200002d0042c80c5545400081d52004840861050158455605200008002c8802d5140740040c21281c08249081080b1424440c4d9058816904020360f405105030900e02d5503444881c5040c3d2400308108003403041a0704113401c010082d588040a04122076055048564500e4030340e090498240c1340390300503c0020020301051003650380806000790400c5c3ca11000528040c040d00900c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 439517239 1250 439515989 439515997
    0x1008070603020403020315040209010b07030318210c05030f0d06120303050f100e06090a090f1202071d0c070827010e09060a06080a020c1c0f02030a0e040f060b 70
    0x2030003196003c00c003002942814445c090044a2000312141540352583c0020700c019010302450200c1070010501804040c00b9505c0741c0074500502e0340e0f400c09a62149064409103100d40342072055040f0344c008041c00240207414100803958044003650802001d405840d40c81d07003158107041405911100c00103101c90000e122408a0f0b406584c001c15685806203c080c0101c0c3c2c0940b01c40d40a044a0300204281c0f90240d010f69045002101c06484d20749443c24420040c001c10b01d0003400d50101d0342c034900c1c20004001803e00c0351450680075180c029941e41c8100f961040700d24038510300005200001000704145400404076580300d80c03686403d00300b1403840607000341d8064422403100300d210500b1580568209440c92842c3c40101e4015642c0e190200c0414101d0446214640a200b46080407a0040f02c103601941c801d80b0340c020443c0d0010140d44e441c6002032000038800d0000c50401d441d5240002d1000c02102c00300e0f051600c50906004603041800000c1c00e864020303041007644c407080410000d83d410014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 439518489 1250 439517239 439517249
    0x4110402122409010920030408040303080c0d1401050a210f21080604320621100b01050a0c08030402010207030c14040b0a081e01090215071511030c03100807 69
    0x161100f1808a0103c01d994941854501440140204000509e40c032044a01b0390f42c1c10700e01640d2544901c500b22400340103c0d00b509908906040b003802d04580b0500c281c0d4126501201d5000c9242d503108891643c643d00701100322960300c030f08512900446e68502003030211070701c03807400d0310030003085006d00180c0d4012308002c0078002000041800441d1805024998806800a000c0500c40303d100b008222600c2d8000411110b0781c0542c2c000480f241e84440799140e100c4500c0c6c2c1c01c0440c401d11208407a48802022030003030030891400358400629441202507410924036a1581039508500740c40b188140d80000344100d0440c42550303000700000781da9802c000300420814802215070480c65040200740c0d10041501030140320043c0701041030003000142e0341c401d00c1000348240506803100c0c0d00c1901410030f07070038046d4210381d4200001500f01c030801d00401e4180c2c01068020300e0540d03481281d40540d0203200440050413414000700300380c170240400171034000511208408800da516002c240c1450056801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 439519739 1250 439518489 439518491
    0x270904080d05070e210703051c1202070f0206071403280c050309010c0f0f030206010e01080115050105030a0e0109110406080c0303071b030b0f041104021224090109 72
    0x200840240c01c41c06440c0d0410024200f102c2c00d01d041c3ca0120b146500340c589400d400001c41d00a02031202c5003404003074040c50b0040143c540302c140314000000001101194800041d1910111010b003203424404d44481640c442060703038030f0040c103070200301c6140c10000041d51032005a00242103681c2c0c00304024404840c00001441c01214100d840c0600500a034081c0000c0c8840e2400d41c400003a03002c4111200c440302420300c840194400d0401d270001c0c10028100410510500103290281500054068100c40541c204215183e803a800c40909a80d0a00100d56103445600d10030f01c11356000c0c0c00030710352000e8010b00025111502c030703402c6400d40b44038070019250000903102e20b11550406000d001c0c040e15440c1c0c01042248111004a51f80b8400c040001d0000f5605040f1080600810700d90f8800a54201752035684904244101c06100c4070250b808966001c0d40070707000811803c1c1802562003100e10a6a04071070381e5034201c04501e07036220044c06000c10404a180c454079a559842185001c3c0c096104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 439520989 1250 439519739 439519747
    0x705070902120f0a0207030c021005040801060f151701050f0d05011406040f0204050102071a04030507080d090909030c0311011b0c15050103020a03080f0904050a0b2427090408 77
    0x1180b83ca08401c00340034054070394010402c0401007500729180400c225030580c1e541c40b071200b20f0a0216007502450b000030352594280345000890f80c4075448080c003a511008002000000600420b03604c00c000b4602c0c50701e41c042130038010800307440c240310002d444400180a540765110705903038440c2114160011030b00310a5032002880741ca810300b03100e000700c0010084001c510305410306001070750782c02c001d210700c460303022400c406d041c80044024103540c000c42c0d200c01112503040d1281c054a44882401d5a01000999405d1000a85141d10300400110680507110a0102c161685045035000c0054120080941d00e0742c001440041c0e1152015005004540d500e40c50b404032807424040d00360b14949442125410000180003681e542000030b03003100c0c0c4c010203460741c07140e1020a0208034001e41143c1e1b50f001e8078007420001030000d1500303c441c00103001c6075001c40e06400c490315a08920720a003201d6046a07818440c0420a440c420420340000740d0000c03d08840001040003d00040002c4a0441c1c1c1100045 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 439522239 1250 439520989 439521001
    0x703050604090f0f120e030309040216021c03021204030809100314010b0904050f041a150301060f060809062403010b131407140708071a04030302032703040b070507090212 75
    0x200b1420351700d00f24645110f10300c1800000a81d00e010342c82c2020711456002401000030500e041d8410303c0b855001c0d240400d0705080241c2449125220300c41a005030007004040b00011001c2d104582c1503c1e80140014101318500061001440591080745c00f4140e03142b00106200044290550003850802c071029611a2610b0a00c400d03242c0140c0788500e00c20708a000c0c40001518003441c0688c0e00b001c0e520300c0c00300d0b07a1840c0d100b002000342c288055416500e0100c000c200081200031a005841054850f296aa00d0300c0c3c1d000c50b41c509049524442c2207524005810340003201c0c012251140500a00214100750103030009002c080c040074003100c00650f02c00c15642e9808544200321f6100000d82031421044062002c1103080f441800ba004116007400240d01c0100328001402c0f403070b01c49207110040500c0c605460068000e41c0103542d4400252001c014001a1001c0c00701c40c2e01c0304600c86405103003014500781c041412030304020b400701d9480c06610b0340400c0b038041318070141060b4500c031041490141062 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 439523489 1250 439522239 439522253
    0x80408070b0c0c190b0a02030a1b1716080f07170c071404090b0703050420030a061a060304030905130227010302040801090302100b090106080703050604090f0f 70
    0x140d2040c0200318050080c0701450030049070a43c8501015684240302841c503412548419a603030304401300440c4042a0b503000c0c20307800070150141030025110204112015648115000714040c001481034049802199032030808002504030800710060750000900c15540b08005500b290700038010610700402d4203818402c500c03c1e42e1181c2c02e81d0060540c03904c00000310041c1c986e0824011000f0141084c002402c0307584680e80305940040c8c00c08024419400d1200300140030f024140c4045d1100b0248e091407590201003400c0700c84030010b0007402014020302580c0c42402400d07145121120488603401480e2240d1900d0008510491103903641254441c2890100320106400d100501a1503105118a1052a084002078010340000a081c1400308620900482c041d2180c2c0e00103005550038002100209500000d400c81039020b0f03001d080c084000000180b001020742445440c000403002c801040c40310b4080c0d404035820960180010418862688416600c40041c542c100c8844c0e4038007100109129038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 439524739 1250 439523489 439523503
    0x1109040f0b0310090b0703050910020403050a020a081c11070806090604030f080c070807020a180207050c04050408030708130f080c0d020a020f0f010201270308130c030f110d080408 79
    0x44804c0201c501141c85805040c0360003800d10b0141070350703140400c0c41c10b80204041c2d58414042c01080d503440362217242c42c54403481400001c9000340c1426001052482c0003040c0354540c1c9081c1d40c91140000c001c41000c41d1005007641c010140c90080110116150b0810310803e846030040f02c0082174941090301e0000d054170300306240c0701f08000390341c0148100c40780b59104440c045a000070b50591102001d000144122805034006942c0701820000e400219200380c001e4140c00d4003400c20380d8a00300c013100510007580d9045400810030801000092030307541c022031020350001400705e0b03401d02d003050310f43d1111549101ca44054441007000311b064829448100540301e84041d591010300309400c66580810031803200d0741241031017031048240c86580c41c0d20035800300624005035054500000c511031001004050010001c0c0d00040340d0348001801c000343d4038140303c0d01076132003502d174000b075031454584916040762420102c82c41e502803604400c06503292801c08203820b010b175030119030315803400040b286440340c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 439525989 1250 439524739 439524763
    0x7060608120403150b0901120201051215030f0309092e0303030b04060501020c030d081504050c0c0105010e1b0a0c0203011401061b03140a05090a06030207110402120a1109040f0b03 79
    0x10511704102e445440f0500c4003070448803d1100101d91450313510040e5030901500140c180008404e1003005a0742c504441c01f10740781324040e02a03410121012074034646a09c5101c01454102541001040c1020310701441181c0316030f20100038251804d0703c42401d1900e100769034000ea002076240c400340006850688900d1000f02400d000a00004c8006004692030f02c82010507280ad001036007000544e0000c10b5440140d89080040040015281881e01520b05402c6048188050362a01c0001318140e03000d1310240780244c03150440c1240072000c2c403c90030303002e500c030b0004581001030355181000180c50902480d10003000140f01c80042e0341c10500c004004240e03414bc188c0c860100d60310f070400800c1d0031400f5020044040c05849680310f001c00021b55061240b0340360540c0060220400245695050707010340302c007921071a0080146640c0b0001c01c810b03070103848005031140350a500400c81041b50f5511504c004440300e0707400390a1000c40340008080b0b50180050a15040d204d903089041e034a01031102c500581 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 439527239 1250 439525989 439525991
    0x1206130908040e040303060b0f0711090f310804081e060115021002040e0405010b01030b0d061a03070f140102010507090b090d060f0213050d050601050d03021c09060f0905090a020706060812040315 86
    0x201e40001058440300024180201d64048000b05604002d610f0b8140c9880400800700c44103a0703013a070714102c1e015030b0051c0301c0c094460040901040c0e4208056652808110744080200066420310250841e18405c0120500651041e40c81550054110740040c20090100350218900e500e0709041890a550070f540c4014105454081c3c800d03002d5458014924140e500400002083d8001e200c0e402c0714103905104180d8144617400c00020b000000a1b071680035522410400c403500d103820401a800d071034003a20701d1800301e01400d4083c004566044c0c05405036100c02044191030183d95101c840843c0c1c9543d080300199a000100e0032a040601d041d00801007200f42c50070b01136440d5540b036064a60f034041c0140c5111340041e03103e03402410b04c00c1180e417030524170102d00d0307402454035601c000d00060003500c916004034010051035205030703005410510441710040d080c2445070b03440094940082d8401d004c100c410b01d40c1e900700403407880010808081c0d020300e4008013541e22800c5040c52000e0381a4100c444040c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 439528489 1250 439527239 439527241
    0x1060e0a0b1203270306040b04050d0306030206070201050705100905010b03240402092701060302091e04140f0115051c050d0f0507081206130908040e040303060b0f071109 75
    0x2814000211070184150b0384041d10183d0004041c807540300001404d11350b051090740240810b0104140c40203004900c07401c01c944003141081800e43c00d03a0010b00c000795103d2010700890016500820082c03803c14400c606403108200b04401040c2141e80c1c02c4003e07901c60f035540c410b45400d81000c21012520500c106901c9500c2e0a0b14490100d50b128014002400343ca00840030403060900910802401688150b116680c07005100c0414020000b030b1006034400c921010102d8200c0d480911040500c4541040c0b0290355602d54403001c481c0c1600841ca0391151040c62083c02c2e40450a201e10001c5d1801c04c03c20301d03242e030b10f400700b0091a00e00c41264031701c5003030b642c0726008009580002d8020355811030b4180340e600e041c9144401d44480c01501805000c10400080c2c804032640d903030707040314441c0b03204450841c80c01e2680c04140040390074043d801400300408000c280240c2900b17880d240d522030300c80c0c600804c225440d0948943d02d40c014640e25540c10340080741030030030400d00c002210000002135502c0302807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 439529739 1250 439528489 439528519
    0x61f0207030201080c2b0e0a061509050906040b100f090f140c0a0f12050a020a08160504121103010905160b1314120f0c041109010c1b030501060e0a0b 66
    0x92200807040d800e41d001500c2c44064044445800901f41e118081040d9014041c982c2400c41c040c00111941c0c2c0e00b40e5550690104007a14203100e0b45000e0004500103084e941d5070f40e9190b0b0300c03031180580702c2c1510710001c0c41e0002d424945c01110b80042c4c411403101081202500070301074295000060410141e22803c402c00804411100a03941e04894600e001c1c2160090848203583c40c019591800050031f0805e400c02012411540041240d1491591120b00d90303039940703840d19581d11405120307070300042c400c20041004c6590000044c070468040c455a0901021035000a400c5800f0030100315816040710781c81414010b031a94403940200b400e8420f00785014048002100003240e2801204007030850030341401d12a0300e449001c0c03a400c0300c10804480310002c41009180d540c0125101c0244103d09042e21212402d0003c001d80b80c032030106850300c140d01d024658500c42021400c840003034403e2030504000001c0348007401800028906e5000d80d5401d42000311440e001d0719250462540104103c11026139 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 439530989 1250 439529739 439529767
    0xf070b03040f060e0118050606010206072102040b0327030301180c0203090a17070b090f040b011202040f0311220c02071a0301060810060206010608061f0207030201080c 74
    0x948140e00c1218050b5640d154601500140b0000751003c880e0f43c644030300e0000009855101a180c5401b039421220a40c0d590001281c0d03c03a4219000c000141d11031508140c84400d0040c4441168100034000d41020345504c0318500c5a00216461410501e0540300c18080541c0c0c03011060140c608803025616642c10031400c03218802d637404405038559035802040006600c24000d841c0b6818000740f5980d0724607034801c070521030a80c00700040040750040c24400111000400100c52a0600280800a100103e001000010041d010840b414851800d0445401e140144018806041000c0e00c4186850440c100f503690816a2103c080c05010600f200440c40d0340640c0040103140451a4049410056034000b00c4c280010f03540105488512212481d0019402002660503a4425990224560f1f00c01600740d030324080314403079640940c10000060000714400c0320081ea10140c0605a01c40c1002c190300311141940c0044070741401600018014030456902c40752150b0001407400c00f0600304080700e50004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 439532239 1250 439530989 439530991
    0xb0406050307141e10090e10080c060313020d050f060601030507122a021c0c150c05040b040303020303040308150a17070308040602100b0a0b0a030b04060b0d020c0f070b03 75
    0x80c0b181004225000c01e40c040d000a40e600700c54060040303000750003184d0300507048040c18002c035544000c0707480010340e483c811401c0c284121162a002001e41e2000380b400d0120bd44e1000d08803d040e2880300e4011401350711070290200c0d5080c0304000501018090b0007000b8140171014000b1810541040705002441ea0b200365421702803504c3c034000090080341512440311100c00c040d400c6842c0340b001003d1105650300822180340380d07800c40e01011460f400c2c14030129584c8801c0000145510007441c819030801d03503141c0c0080e10003c45c5081813072070103454800811054025900840044c1d00c000f003004100b550018613660040b4064040081903900180010307011603990041e0076810095a860564840c000c201c50002143c01546850365247c40f40c03c004d44071b82415000c4108641001c605041d2424050700c41000c90b8800803030b06040c440803240413805420152a040d511030307250000440e224104000134140028000700041c1d4505c0740860300b40c01c20050088882a54000300c0040218001c035030708503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 439533489 1250 439532239 439532279
    0x20a020d02041a0301180302070503030f040b0307020a0819120e1c050f0d090c0b0a020d0503040201120501090605041d0c0f131104030c080f1b061c0b0406050307 71
    0x2003034402400d5443c865180494603410b5043d82012801303004110403440b4680c949000342d0a0710030a42e12503007455940d10500001c0426545e04010421002c200d20004d141c008180e44190780d1030310384a13100c50442e034200307281183c064031110b01120700c0541c00c42c07181c2200c00d6281c0c0041c01a143e009201a071102131880480d041c4004030424038407014030901c100c030805a0300d0501542c4481c1d030f400c2c145006008880b01164216034480c0d01264400c00802542c800103a2540140740c542d50892080728181c001402c200c2c11303c8400744d0050000303034043c090340d0701030300b802c0500040141c606070402c4240c0340a42d003518000150000ba0744104480840c455036100d00640b003840d6144410808602890f02422006c4001c40c9450b10720118050100001d104482c040c00040200507241d8200503150a5a88084c180d5540940e06000c0b404812a6240743c2c1c401c40102402e051051070303090038200200300c0c05a103004079070707c603140f2260b07103014400c010103020254001c201242c204019003e031910a0102c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 439534739 1250 439533489 439533491
    0x90c03060e24090d0c05070519050603180d11250308280305010501021905071502070306140c030406180804030b0601030506090613020c0c0a06050a020706020a020d0204 74
    0x990108008104a0341140800c0007680c0550300c1990a0440040a020f442412441c025040b1003035034248642a220195a004405010614602010041410b800e003545480c24040160001002e90724003002c4c1d0f12031510310301381c2000b401040d0703407a5007044203c00c0210103000003001c94442c480c40008005603a418541e800518444101070320010011855100908500e00021650400c2454085a10300d108181d80e4411000c1450720040e810f0b10405d0140c00d00680c81004600d2101803c46c5107122028080c0781543e407410348552200c406012050466805a403101c00e081040101602c960000105209092241c0b81408803924079a84005400074000303623202c400300d9610840d13034480400115072204110f03a88544c0d0303140c000c907a008103e82a0707000c0791500b40080c415083c50084507203c0c680007055881c8402841483c00020741040c00b40340b40e140329503030b07280105031551450000074088a844040d02d41c90031160003842c000180d08000c00719000420190010784a1401f034180c02907045074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 439535989 1250 439534739 439534751
    0x117120c0f0304030507031b0e071d031b0f040515091824060901050f13270b1008120a0c1a060f0904050325050f0106090f090c0306 58
    0x110340e00d4810758155501c10303800002400000c00000040c90f1040300d01c59842d60151184404c44c085049640388034807040e00f9903040003c1c80241c401c825a80b010808403c0050b180018400400e1070040e480c010303c00c480c6020441c40f500d41c45c00100d071080c1c0f5082101c040c0071526080f9441c0f600481c00300321080c00b0301c2c540800700c1c450141d1030030394803503003200d150848010390031172844617115000e18510b09031001840c0b0b0100b17141c1d0401410300b906803517014080341d40e0306284000380412054004c00c4404035651310280b0360114034010410604460500d0200c0322480104d04040c08456005810140075008100080014240102d4180e1040c8404240d058662540030803e8900303105101c0002c00c41d200a4000318594500c6a1070203006000507140300080c0342c540828898106415140900541d0040c0400d171500c1c229404503041c0f030051b01c80c0c00111480160744051a00310301d44140700e00769440b0f000034055400c043c0b140781007540c111502405100510784030000401014080500b100b07441d04c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 439537239 1250 439535989 439536007
    0x80301060909110711030f0d03020d0b121b060919080d0503090a03120e0d0201090309080309090a0207111e040516050313030207080d0507020a050d03051803010b12030909011712 78
    0x1107c0e0310000f00014098440360416080010005d41c40a90f000f040d0520784000640c450130300068442c03420000c600181541c1d5524201c0383c800340c0b043c1d20081c0d070010042114452a031244402482c2c80006191007643c2c903410480e5580c04e21920411a0003081020300821512000001f00e2121044c0c06003016039400c00d50b20502c82c050300401030b40900c3d07440303441d98442c0b255a0550007413000c103000340d5442d9511074449901c1926840f0b044005544051040d0100d401c071403650307004208080c4100303860002008188081040d9059240054040d100c5c0c5445032103483c1840e018255210b00c550b80300d07520a51a001e00503120703000203402001182c0100001408050017001140083c0c240d010071140b0f42000c1e81e600400592140b0012401b400000d00000b03210304100411400c0e25515480d850704140d03400c104c501e102d0301c0710741000d680740d07403551403800c103584600d80c3d01c2d00d1456000c03010710783e50f80342070061112804061b8400c8852035401401c00006010115103c0c0314030b10710707500942d0381d00c24038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 439538489 1250 439537239 439537243
    0x315010507020d0b25090b180301050c031009020306010f0503040201121b0201241e030b040305030604140906060415150f0f08070c0b0403030f050408030106090911071103 75
    0x54074000b03400a0405160340144881000b2180c401c0400c0b00440c00307600500284074403851119180c90021405140042c000f1210484c0500701054949009440703506040c40043e0035207000352000d000e4030400109000c05092602d00c2c1c01c0142c1000c0d4025455800c109000800201c603424082d0304205000c4007013000c583c812107038a041c07180c140390284145070b0450b00000082c0d003084919400b41d0310741122071100043e00101409001000c1c3c500f50680391410801c01c1c5203800f54401ba01c00002d081c180400001d2550305400e008074060b039112500ca00d0140300b0311044402c0c5200940c162141681002400d510000c0d585920400950b80415030901c24030f8450002041a00309500346541e40e003020b010766500203056100607009542c0c4144614003241c055415204c281d0758040042d0301d8840308030201d000101c1c405e8000b44039150001e80840c7d10902c0f0422907070192002c61303000c1c5001004102495105410b60043c1600980820208450401d462070510a110000f0b060384500f030580015640e003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 439539739 1250 439538489 439538497
    0x1e0e030a03030c031a09060d05121204060608010213050f0a0503100203060103060e09031e0d05090d080a181b18141012061d0d08010302030d030e0303150105 69
    0x5821100240068a0050b0142003421a90b81c0042d242c208259111143c02c0f11050f0352100140c00702405460300d000f404640c4440020a072910f1040d01002264901040c00030148035004c880308804501b494641030003038841070780c002002a8010301000d51280c01d0454494100e5000720780340100d0703282110106202784516442594903001c1e11f03503c50000442500290700c2000c00340c0c1c01304409a00c2e001f85000d2280705a90b50301555000344410880302a402c01155078600030440c446042a400e03126110560b24101c1e07540d805900700da114602090741000750350b900709200c06400d000d00281100f0035610642d1015028242035030003114000c2d00204100d040010341140e6444450307040d0710b80100302c081d04480c1c031200c00120442d0001000c08450072020400d82c0d1031201003122001b40c584500d0041c0a161140000300652810740055100d820000c0941c44096902c90b000036600d903004040c205040f0140f08424181440c0307a814030b9180100449500c440e0200b10135440804510040300e071805 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 439540989 1250 439539739 439539767
    0x1030e0709060e0108010509191a2d06010c0204180803180706020a0818040b0a06030c0809030f040b0307030612140c03010902090601110f06010312110307031e 70
    0x900080410706545541200341074a030714000d0400307141d80c0c4072946030803210221144000c5030450044100c0443d0317604074801e240350250040ea000c0c179803080f90700c5480f5132081d02c50010303400880a00c8d00c94454060001004203802461051b294584074002a000e140303088402031045580b8800e6140300c40c00d407801242c119402c24103090b00c0c1e1400c0408241403440344e0460302128803400d50b00090040c800285000c01a603c40a003a090419001d203001d13040032103001044d0b02075120003042c0b4090b01c40340c1c00080100455039021521600141002c2c008980240c840d0030b458204101c40708401c0300c190f0458080300ca0b501d4215a403540c400808800509441d04940000003828030301da801c1c00302d0b0701141e00d0b00c441d000050f01d4040440800309405c8070340841d40203400803100300020f001c640c06901c51070341000240040e10089401c480510b07061a109800c00c96022448000c04001e80f070b0300610051803625044011454500030b501d0140c9140311800704107aa401030824000c01ca1482407001840c181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 439542239 1250 439540989 439540993
    0x806010e01030609020a030e07090b0d020409060902131505011106040803040c0e09070e0a090f0b06040603050f0d081305100f020c0a060608163f110315010608070e01030e 75
    0x40c221b170300401802c00031400c0429840fa046021981c01c050f03108507007540000800d11801080c2d15400d02010340310384a81034600310b9684040001680b81c5038004076103511201d000203005a011039072a0030282040e04100e04000340307001c0d2503140803000039900d60070039080708126483c3d54441ca0f107500b0b10324075034000c003640011502c02d0001e0120006100c4042c3c070b018030070380d818554982140c0000c03900c1b600750240c41c00e0352001c01d420101d0b406180483c1c010b00c0c080c0002c6403094a035255130345050f110741d8904029512600100c8400303903020f6800b82c0c12800345001d440e010491915040e030303103a010303e00000d155540c84400030700b00340040d41128189100003059611104071805c04034010b00c03184c402d0b2328180c022510001c4c04040201d00200980d800440c655459040d0041412101e1204520180341486401800440943c02a00002d0058400c02020008100c1d0405141c103100380351104c4890060001c0041c0000d070b400089240d846540b03417a0a41a255550004030041c013910701030760035a4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 439543489 1250 439542239 439542247
    0x1030803040c03120f0807050c0d0f030605030d120501060905101b0f0303150f0609031704170615010305040809011d0a14031b0102030a0810090513031805010806010e0103060902 78
    0x50780c01c10721768480503000e511401d4660740c5400c811b84441c40f509650035002d0300b1182001100600035220008030014910300041d5407602e800c0032914102d8061000b0700841d210b080180321b105100d01821f07001d84110f2904112951074a000310b0150032404034140d0a010400c0038003000f030300021080e4440d06420029021222441d4180a401028100c3e19040d041c21402000b1036008030700c01c9004200c505617600d152042d8035540ba208010300c0c1c61b0000e140316010421000480c81c05550031404441105400343c07400d401c0c25010f0703d80d41030301512034505040c00c000c02c00001c01d40c41c00a680c1e03000001c1c01c101c66516075a51203031030300c0003d05a40b50f60184440d00f0103c0c01c0c040b404c8124002007020340c00c40c2e20028503440c100d010007610805c020f0040e84100403000e215441141150740000b8200c0011064646800800d07081c0c980407612040700703501c205030100a05521004000c140c200c408001c14809041200007482c08030001c040d24140089071580c10901e900c40d500c00001040002811511 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 439544739 1250 439543489 439543523
    0x2040507050c1608100e120d0212010807030c05040207050c090f0702070503070b0a0f0c05030d0207020a0501030b0d11030a020301180209100e0a0513080a020a06060b1201030803040c03 81
    0x40c0b500186064040c920489004071401d00349000310000b80c5142e000101005104017185101403d4070744d40c030700954000d6804a00351b100180c8081c10240031a11805611150107004d200540c0405900015590b8041c0c64104003186040344039000392002541c0c0560f5903502420220300c0c2c00311749012981c109200d070080140040100706464003030b01e20b65094071f602c03c0d520300816a603008940200141c03000100203510049001305000c0d40f20119500302444814207c0c5c0b180c905640104040f400040e800044540031803800c4801c1c132015002c00d0071300f0030100c0c110038042496504080c0c0b00621034641c6940700c000039501000600304641d4018020b10000c1059050305030103555034101280034504500100b42c46c20f15800b400c40c159102d81c588904656191880100600006041c0d1480c0c81c032a2103005000c00c60b40001040084181e40090424101c0d40c40c11b141114426400381c0315085080c0401c40b030b43c0d8100d40c28181142d030415021a100c0d240ca09040058010303503480200b000500c1d03048403034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 439545989 1250 439544739 439544747
    0xf050d170a0e04050601050a0806040e1903020303071803150e010b130e0606060306090420061209060702030906070b1e010e07030b240703090837021008040f02040507 73
    0x904000191001e000e103417140001500c0314003552181c9404101403100144041c24550f0044041540000c100c41a0f5010001001c0310104016400d9006030000410004e2158203d00d490440d890070603c81e007101880c40d102c1c130b055140041112000b5940300c0500c030300ea1040c01d410100c0802d0303005000d803c03040301c8440140000d041c1d00001c8049401030b40001496131600c0c0303054038440c58001d880300410f60b44a56400404601c400b11001c0707681050001405d02d500e8841c090010311006c1c0000c3d00741401e102281e0752030000000c06480465004011170f80e80364651506541074658005944000d0b600c1b889500d14042c2c40200a01e01119190000044c40074201411140034032041d071010400541100c0c10b1045510032104030454681d00011060b1000d8000002441098003a242074809151140b002c20b05040d0060303083c2031505007070011304100e645414000f0b020503018180700071002d00c555011510100c0c03511101c40501107420005018051a8220112000d074000c10070403003450301c00070249c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 439547239 1250 439545989 439546007
    0xf0b090108150f1e0c12100303020f06010326090d030302040e0708010312080702031b0105070e09100b0a0909060e010f050904050c090705070209040f0203010e0303010f050d170a 78
    0x5603081c0149404903080711410b0b100f00780607040010701e904c05910004101c0101d202c010f4108440a0740411030884464805101c1e9805a80c5c0b0401602d105403031030030b000340740082800748800190001001040042c488014030820303000c07400c100c0399280a80032030011080c0101d4800c51b8024945803081d00c2010381c551b00800603246a0720303000125803035005085580384401d0100404d80c5001100c04450301380600343d12640061940304036032405030301555a002c43c412540702d03015183c1d114070503c00002e03000120345041d41400d403942c40c060300c0c18100809800005102d030020790030000039000f02c250321444442c400b4041d01c1401340041940c030b4002c641d44c4071092092400c290007411000c40c3c00c3c50003e074214000c540260040010500b801300304000d030382001e095901800030030020749005803158030304148600e01600e40503c2070421030050509517031030201005102e400c104010701005812040702d0065400c00e842c41039002c00c1c1440c00c07a00590005000242c0002e020400030704682e408001c0c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 439548489 1250 439547239 439547263
    0x9030908030a0e0d0f0f050604060608010903050304021e090103052b0807030f02090a0b070b090f0703030f140c0a060b0402093a03020d0f080c04090f0b090108 70
    0xa1228503a84100103601d07401940400e41c0001c14100c402d2580349010007107040d1680c09107041810011003669110140c8001c01811140c6400075410001802190f2244a00600400000307001005041d038004103680305c000d100906c240300c034a840355507070412174428024040700a40403200d15612030400568510300a6101c00389000704203030020851210030f19411360030780b141c0c49400703543e1170300442540980154081060090f50901115a2958941c0075113030041030400c03202503032401e00341800d41f5031f00c80050035101141e0104440e0b8035000070001b404011640c240c640304c521801000f004035562903400e2541c40201c2000704508207410700208111034070301c0c4241d404002c08110001444140d010b641c440a50010400c14042c440505013140c04c0040d0740785a2024006115a224845181241000c140c005a024140c2c1c45122074001848800350706407400c250314030f031510500f22022407245000f41d074215a1280030562902506030411440400c00421220041da1145201540d910140f458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 439549739 1250 439548489 439548497
    0x2206020c0f0604030c1e0c170a022112070209040201050c010e010213050111060403080705090307080607020c09100305030403030e0f040c020c0102150c0906090a0b03010b0d0c020c01080a0b1c05010903 88
    0xc0d0406c50341c1c041c6038207242c0c164042002c0340e03a64944001c220f50740c81c0800880c035090143c0c08926006985074403140d00e00b581e003110690024180080c520b4a4142400e12200c014402003200c3c0c800b60742e40001e102e0b400780c0e0904c0c20640d259616580075000d01030f1801e03c1ca03819070001c0b81c005410303e41d0340340c00400e0303810030703030b1002d40000c0605072030b40d03444c03400f074401074080741703c03030780419892071055004100c0d4a030090704960302140d0351450180751a80c01c1f180ca40060300004584442c130310b4034040360340e0803103401200f10461074210b03119542c40344200c1c4801024054020840100741c0c4820013407500c040e80041c0104610712100001039102c00c215085c0c28014028031300c0e00c85140b03200c00061030055141c0540c01d030511070440280103090303001c03d41003171703010100c99000581c2c04200f10007503010f0203030902c040344c82e03180344c403075400a5408030543c0c1415504415804016668041140d030f511040d00c010201e00c070382415000c81d21a5100149640c41c4d1504c090985062000540100c07070468400d6131 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 439550989 1250 439549739 439549763
    0x10f05010f050a171005030a05010e010b011404090f0b0603040b06040b2407020301061a2206080f0417070b09070911030106120b060a0f082206020c0f0604030c 70
    0xe04503024032416aa00e00820b079100d4125807440d10403c42d195210b210000307220030090312080000c0c231b407502c500012507940c3e4540025001181c000c0c040e01400d0b090070b09007054402c0d07201e01c1040c5140902c1c0684842e42e59900350a01990031135801015510b20090041542e03800c06041105005004407030301ca00441c10204d04010504020b01c00001d000d61202d2140e00d003a540000703010495112100c00c0e80e25649038003001c600784d0054160001c2030018410042d540704090812914408a030202062810481110400c009900100511f45c801c046245c0c4d900d0700ea40e64540400c2c80d040e400c0e12442d04181c0840c400040080c500c0130180102050030843d20960f684420007010b0310005070540406401c1403004020b503030b0185944114444400e0b501060300d440c1900402c2d040d401c0b841d680f2001520040e084840103400006040d04600703c0201c0341c1100c40441c1d4608000c0c3d20283c8010b040d95030011742d401890406204200080000380300b070b64014202810b0003010140e8010055a2040c1c0c030340 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 439552239 1250 439550989 439551017
    0xc0307020a06110d050c18040203250804260906031e070e041104080a02090c090301090c06030c0e0105091c0c060c050d0201020738090d090623090a090203010f0501 72
    0x5060347c1c0060780b007045140c1c4108005c030600c1b020350006002c1903c6c0c14003a80c985d402d05c858550140440200c150307101100c600c2d0034180f20a40ea0100c0444000450010b0003068042440100b29841080c040e1802942d075100c080c400d8143c2c071000d0200540712200355050000903640820b961540100440e800e002c54501000f0091f800d100f14440c1800a5002e24040c48c0103080041d41030b980528510203140c03c0020b40408603003901d000281c200c4041d90003110034803600d5014072035802d0490752440d112600f2407a400c00605a03205030b8400605c00c04451080707000600705400b04903243d0307520408520b130382c95686801828404410100b19054024921260b802920501c03d0781c1c00d81d504892591046408480c40051010010b00030a00002c042100311036119000c40019000d0641040280030104024200904250b2950400c104012500001881d2101c2c950720910002400a030510b070354103002000980d8070b041a5000d004070500200002696040040e600d40489100f0788071944041060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 439553489 1250 439552239 439552261
    0xf06080d031806090309090606030506040c05031b0f0409060902030702190b0721092d020d0213021606091209120f060e0a06050a0e070308030c0307020a06110d05 71
    0x301400c04503002ca82031803240480c01942002c900c99000703003004c080e400c1d1034614010958002d5001200403076102c009205050074988581c0040740003502e80682541890584400011604070300318004510101c6c0118248101400b00c3c0c000f46131a80b010440c1c2c0361f880390014040c0d0030031100c010160041000390201d10204500704120f440c0c2c005140f0107103079602c400546a040c6003007182c80e1a0000b414440c1500c601510652115600420503000c803c0050100c0500940405d802c145103c12422000d00c0140c43d122040700030b46c0d5048800080300506d61810381e00030300413130f84241d442814500b04002031010b0f80e40489034081c00307540031325a00c0302c90900c00d03141541103201d07895858858540b2240031600300c141000b070710f5120301c6000c1081e100c10310741749151803000a001c0da8401c1e074a03800c1c002c42014078401c040705600c5141c00352101519603100c6070301c14040200511101d031030000008071498801d019054002d94410ba08000b494502034814070a5040f0810111580d441c100200740d010400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 439554739 1250 439553489 439553501
    0x2071a130c0605030703060909050c04050a150303030f1b08071d100e0d02030303010612060807060e010815030a081908091c0302070c141507230a060f06080d03 70
    0x300e00001c12440c09804440703950001301054101540c4d68008120b0340d0040c000c14455901a80c000c080c82c3c5014401c000448401400030b082e079074074000da0039400c89852401c0700112078150900003105110b1035182405000108001c000700340e05414421002c50300242d4a41c00355003103942d803101503109105002030f030441c0c42c1c420030b5020030034075a0000c8052103000551004080070300701c10004ac070550301181c5180c2080e085880401c01001555034646198421080101100e6004100359071030310901801d14019164007504001030407000818280c405040c450b03450a02600310b8022140c103007401c4400ea0004144405011414841845082c1c0b08443e81d5000b5282e110107080081c40000c90304806080400c1070f581410780034406240440d02c180e00c2d100c0100082c178254a080d0303100da800c01c4902c80840c0c0300c090192000f801048007185940c000300742c0041144406002e41c0c00c42c250700516000417a074000301590f06050001a007010203400040848454404540d81c48800c10425010740380 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 439555989 1250 439554739 439554743
    0x3051f0302011b322401050d021804030c030306120506061e12070f050102030f0304021005090303030a0c030e120d0b060f0c07080c060f181302071a13 66
    0x35a841600f0b5580149001c4290305500c610412410750190040488008080209004080592a0024084410612601030921450a054110900300401c010ba103200f0600900307000e0092103460b1811500e8036941049640c03220310581e81c91b0300d4149001840800c0080e41203000a04000c4001042c1c0b111110800d4420f42c0320307002e00031980d143c0051020070150010400400c4030380800001094840d41140b0080c1e10f403240141940604182ca03405021b5075940c0405c0c1154030804c2400c0c2076003001401d036500190b048612020310f42050f035080300e45020351140340c0c0d49400000244812030340d03d0b43c8000c5401186460612900100c0103081e5115002c02c00b0940340c1001c1088485d02c1d54960741c1c00345d0345030440140064148408011503514982200e1403020703650f8042c001c00d0008103170401c20100c1e244421241103180281c0c0130304180160050200b0110500b000030741520a95843d541e030b05d010045800c1c001c54a820490500014041504151000e80360000700801d50318007442514082050b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 439557239 1250 439555989 439555997
    0x30e0411030f060a0512100e030c100b0a05040606120c0f05090402031e09070303030e0304060509040203090a0b0a0c09080c0f1e180f0a0b011202160f0303051f030201 73
    0x19075064841c00805000400c1c05078041588200800c1d19606c00200001200000d4020160003810405980444490340c5510a159000b0711070b01940c104001030100a0129568020620075406000b24400001c250030565101c1d043c50008035150342d0100c0b4018040c941c14101f40a0030003801401e6603540108100710f00000d10030807901c1d00c281442d4008580040703441c42c000220021174494800001c5017035890100d2a005030078200185507140c0185a45040300f90302440c6824640480030f001d51081031002402150040009102200f00313124a0b8036003600041c0d1030740d40e803600c01921001042c0c19602000803411003007000c900c3c00c10002e0a0801a200034284400d011000c00802445401c20a0404186040c189040380c858454106800760ba60000a01c090f0a05000411041c030400003056082013038541403491881f85c2c3c0c403003150100403180b804016a01c034141d9040c3d0300344141c0c48402902d49940c0d99000001c00d603050784410300c1410089d4410300b91175030b01365030007403640d070544400b074006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 439558489 1250 439557239 439557241
    0x1818050415050f13052119080c090114091e01020706030204050d0f0c120609110616060507020a1a100506042306190908060106090608010b07020114040e0103030e041103 74
    0x7200e03440c0b07000071131600400440d14080e440703013480f88440c0303500c0f801c091b80c920012500c03091541e010070754914520010b040c10301103458010403590007030245821a60410a00347c06e98502c2e11051000c64030118030144c8000054107101000343c16260034005014018400c6980c0040c2440c801d20a4800352030004022089164a940794864401c43d90003058070105c7d8030400006848903941d0307210701078078403444001c6198429800c1c01e45045240000c840d000705010002410310450403c540301205a01403800039580e1114801240b0b17010800c04021310761406000c0b010314404038081001c0c400c1c0c181540040a8540711824008940110f1149a01c100d003d04170212803203040c03480c9941d0f10200940540d0070500c034465045812044d103807840011581c480d5090010702d90038407405002d4260717801d20901d000d1074044018141d01d8140b007041104030f00458040c0c21a0f01c12151a02c00b41c0542c042c00761501d032984019144910288800c40210744413800c142c156040c180a4030508280c444546415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 439559739 1250 439558489 439558501
    0x60806040f080903030403110a0b0408061305011814010608030708160215040902070c15020d03150b131502070e0f06040b060315041505030d1818050415050f 69
    0x640c80c000000b01c4004105010080c02c5403020009080150b01070f02208120030003120030301204e04529040f860000c80104000e000503c00044c0c0c140c1c010140540e480a481c4445c2811801444083c1c40c40c0c2d90403200b00404020701042c0203800c1ca90203a040020407c0a5072100391030794074031030b0300f400030f1040d9000e207c04410050748010031140140050403d0316030385d0960f00c107020544d0254204850032035001c90080140003d4126000190003030f581e044001040000029664001c894000c0f030405440b0300a82200c0008610048028041508800c0c0c54100210b62400d61301c0c802d008036030043c00c50500ca46410b40c40010b861080701c42006207814a6180e00080160b000c000600240e003080c0c4425451045840b040025841a81d41e064107410890390482040182c0c0d1900881d00c61041c0710303038400d10080e54082080b40d04410a814840703400300e900220b10b8100103a1358030011141c1c152070400c00e60504240c00c00d9200314403440e000ca40c808441da05a1080344d00a541c0444500046070020396 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 439560989 1250 439559739 439559753
    0x30804020d0510050a090302011b0e130b03030d0204151404090c1107080c03010c05040b0301090b03100501060c0b0106020a030906050a050d0e2b230d0c020a051006080604 75
    0x100c00d4042c90644010b40c00d42031105041d2201502d0a000440d6200068000d050303080c411150010f43c6011004c1828105500c02801141c0c4510381c46d108910001d6030320284034241c2e1108850120160070b4075128200d010741080250400d01c600890070001c4031800070f140784182c4000070000c070750854803405d260411220b9401480d6903120ac0c0f0a10401110005540300300b0803204c1c00070301d0008010008001003905040c25101c500700e0b08001e0013424401400500188419a4191441f03450005550380e00710001a01e0f105841d91140c1a6626240002c030303403680e0001b05c11038543e028511204503641c2e0f80d00200e03a120b1402c4000380003d1034241c0c050228a01c40c0d002000030180c18a003150034000e9107405c281c1100c140c00500400c0d44e01c0707208040c00301d2000308801c0c00c403540e0304e44500003141c00e200800341c6600b0340c060344208145600640f1001400d4180165444003d100b401013100c0315220f04040d503584c2d00c182044c1e565100d8420f400050000600500040e50204d0020b00121b495a41d1820 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 439562239 1250 439560989 439561009
    0x40c0605071520030f0a0f0c1d03120f0d050124032a021b030111030417040f140306090c0d030804020a0306110714010203072c0306150a080a03080402 66
    0x2120210301c1d10080f2100c0e0380c0301020713500943c06402c851401d0700300b140d038000881b60302c1e0048450490900d044000000d40000040001000c2c1c240805a00b0b04020002410010801e420a1032001c004c41e100e040d200014000c4c00708400450f404001998039125000494000d03010700c01c0c06c06c144003c00b003003224801d4204015034510240040204980300741201622300300c0d0380e0210010ba019040000d4181100d006a50400400f47c0c020031003800001d820740242e100042c400351551484d5290308008030310180c200e034001c000c3c4d5100c0007202a01c0e01040200001d003a01c2c0c541c400d10841010a54511001c2003d41c01d4100c003c0a2075807105042d90195425000200305981c0916040c2d0000041401c0d0700800410109116035207944010714581003840b0820819400e8040c0c2c81441000b00d1550081124a44403030416401000c40302000581103564224030005134140c0a103405201b01c8603505240c00004480883d1a01000c545644040b55035400717628014002810400c041005410110014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 439563489 1250 439562239 439562261
    0x60d060b0a0201021206090112080a0e030304060302090103050a0b061603020a020d110102061317160203070b040515031005011412090c040e01050702120d020c0a0b040c06050715 78
    0x850050354488080005030007003111030700540d400145d003258154600354020391080d07045606401c1941800c10381442c4200ea40707401000300e200050704c8800c0e54041c2c060365810343d40007001ca9070303299200c81c070081c081d401c10720441d40405d00f0040484c01c1d40c0d4042c040d180900c2d501400c0365050080c41d440304000030400c500c060b000e5020b01301072f84002d030301c0e40c2022040b0540a411340e01452115075000a18048001b460359010540c60307034543c4002070a2000e0740d0031828000d48501c2d150003407210090780c903480d0035038003e5051080c0c460005041c440324001d40103c440c11035003100c0c3e440e40078412407090300c402c4402410b104142c01c0306101035802107070031180d001501c0001c40e0402d080e00c000702800d25416602080d140d480400f55004034681806600310540c14000203001c00d0a00210296139425200b2905460900100d8003159204080c0e056580b45a85801110400c1c0007604200324141d17011740b402c2c0c604045594001c904a0300810460349240d502070310142440501c1400e03d4010980780c400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 439564739 1250 439563489 439563491
    0x12280c08030c090a120506180a0f02011b0b0a2009060d0b0307090905100603031706060d0c050702120d050706020702030304050d050f07230909100207030c1b03080702060d 75
    0x20403140c94550740c0c411030180c174046a440200140b01c0c20958540305004082c4840b442611504041061001c00c071480b03503542c8800111900c1c00f15100517074000e5034240c136190600c1c04051400c1c0a014007000e1250040900100401684010552a001001c800c00c4c03004880501001000c2050901400030000c076075003800f001940c600c841002900307002159001c01caa03030340c4511008040c000c0901020305080c12490301005041d145560240180701c5080e600300307104c1c1c85800024480e445450441e0071078500c50f034040040f403080d400c01030b2080c3c00001c000ea0281941801c0c44640c1000000d0071606100c0b681c8416050102d6607481201079400300d0000c81c1c00d40070a00000401c2e4690300e440504051082000c0e06150900380a0709103007407016440036a80c2408868070000000d000c8024110750b41050f41d031481c0c10b6581904d2070b454140280450b5050724400103002d0140b65112501a43c00707403085214020b04110030300c41d1300c690030f45800050312181042007a0001454540d005207418044904 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 439565989 1250 439564739 439564747
    0x10080304121b091812030504020d080c01110c0a1a040b01150e040c030621020a050f182d0106020304090c020a240f09050307020f1212280c08030c 64
    0x214000f07035249a03000401d00728800d40b02104010842c94407101702c3c0c05600e0200a40d1801e1f40014203100000080603206010000c1c0c0040300110039041f001030510307646049a5940130180403103036a130b002c0ca0000d0340e604894020b14402c41010461144c00b07143c001e6444191a420800f005035405040c2b0040760500040c1d4120403140c0d152801040d444804588000421618058a0500004403034400c15917403005090383d480165210301d8004103642041e10f580002e910401d010078401c44000c0ac1000d9030a030090304201702e50380891403864911082000d107101c118152091600c2c107140070300901700940c1040c0310910201c5456406030070500c80e94812200e0440345512400002500500020aa01084000030300f10b0030b200e01851014040f400c6003005503c00355180c01e0b45038081d5010081c412500700c91202c1080d0743d481403003249242014165a9050b081c02d10b00b0030142c2c003e460075401004280942401400403000c11003516220f42c540f11041e4000d03503140f000035403004254041c2c03180240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 439567239 1250 439565989 439565999
    0x30506130507031e0b090f0a0209040e210703021b041e1d070501020c1306050a08010c0201150b03061011070803071406010315020d020403170310080304121b 69
    0x3001c0e95001e440191000140380b5a03e911001c88201310780c01041c0b04c41d0810402c10680c1d15580c03e0250311114015040f0b000c0d44450704048064482d0300d400e0740c0d0060516520700204000800d040c07800ca000010741e10743c10200d003151640c00c0d004684001d07000d60400013550854011001540721003c000402c006208114008905e01210a040422442942c2c958000d03020200030449055204041c2c13004215542c50200001e6031046440380b003038000e200c804070410816000d500640b01600000b0046a10a916048510300811541c46117100541c20641444001400c2c00c1c81e0500f40e8141c0d0761075628642d1550300740210820300810701010001000c152145240d028032040018104800265584252505008681402007401d810403a0000b8004100065000c0b8405944034641d072009a125a40d030b403c4080240540d91000e80040503c0d1200080b10560b0f01c010362040500c6403444810716150074202d0b40e64007a034082c0100101c625208100030422614200d100314801d003c185884d90b8540d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 439568345 1106 439567239 439567241
    0x906020f0d0e03010e060129070b0106050913061509090501051c0c03060f0e010c0f08360601060f0c12110102120f06030d03020c03070303050613 64
    0x1248120042c0d480c290411030307111074803100342c0315150781d43c0150301e8007d050001e14618030032804d11000c6202c07000c40140c0c1c0200c0e8101e400b0b0807043c0e00f400001d4a080c0d110b201c1d903e40c06500c46c4406034004030300340030f20f0010b04240006003145401c2d030800680745a2107034114184190070000148140c1c0c85010544802d00b1003020350400c0072059041c880100c10711604040c00250401d00c842404200e13941181c03001e4164040204898804e41404940780000000004000b601c000080307003000328207100300006400071164103108208800c103480c801000341c0080c0e0f22550007441c010010182c200440012200741030908007240c5001d561510350400d580c2c03204078180300d4000c0507140d108009605940c0301c009100c20509842c203245c08803001020048800611a11616801080051080c000d8031000c0c1d840c84015400c1c00d01c2c660302070307002d800014405904680700315400c0e801c403522 = true := by decide +kernel

theorem cover : BRFrame.Cov 439388489 439568345 := by
  have h0 := BRFrame.cov_init 439388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 439388489 ≤ n) (h2 : n < 439568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
