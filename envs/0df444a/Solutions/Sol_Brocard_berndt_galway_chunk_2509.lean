-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2509
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:29.077126+00:00
-- url     : https://prove2.me/submissions/9b1647d0-11bf-44bc-b17b-69146e93d8c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 451079136 ≤ n < 451258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 451080386 1250 451079136 451079141
    0x30509010e01110c070f0b19171e0606120a020a090f08060f090609070b03190f090c060f0c0b280c180e071413030f05150105010f0509010315141201 65
    0x2254003015a90b402d254005038034094060721a60b810061001e050440c0f002781150355000d40c411410031441400b40740f154402803201d024001e0669100b0141005001540090748401d603070441c0c03010000503283c035000b500c03e851101080d0080955662501e100090004001942c54840c00d610610716403691622080955503500c2502e5a0500d03400c1030340c041c4803c80d4000c000e10781c000e580712490075411182d0161041250b408103048541141c94030549428001030702c001d0f5005000d00d142504405c1c9411400810800110030000c24121441303000c10504004c8c00542c800c002000e0180b298100b1840c41641c0c000c01c0c03e0382d2604d01040e149a604280b49242405503000c03100d06001414080d07603101012140c0c10880650040000720500c07000403c1901c003803508014510507048059062114100355281480e0200303c1c0c0e09441c0401b006000300c0e40d000c0b8000c2a40040c60510f9529800c0b07a000580140450a03461003608035010000107a003440c0701452558483d0a4400b001860610fa007010b00303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 451081636 1250 451080386 451080389
    0x12020a02031203100b0708070b010e06011d030a1b080c060906030c09010c06020d020405010212031302010c080d29030703110d051905011d0114040201030509010e01110c070f 76
    0x5041e04403140c50602c0640b24002580d12000e0036a22501c0c117a00c0f000c03c1c68954010200c141e8001c1c0c0d02103400000c10103101000c0d07001d0495807020584514008000a0120450020340040d641c02c10143c40402d80741002600302007a4402c1c401a4004072000c028000820140b00702c01ca03c0c480c1820071900346c103000f001c486c5051005000e40703140d56a00c40d08090541d200a0302681080400752103c03012441038806850419040d01c1c0143e41c0381c0c58040024a06003003e0401d030140503080040c00300030b00140310007028881c1c1c20b003402804d00503e41405195405840e81d041082c90800c0b11613182c0e0a411200b0003070407007403810a1072855140e50103140d0345203128000100f0780303074402d0700c10039191809d00540111544100115803112030303e911030810003800704008891a07134480700346521070038030300f002c16040c11a060001c114400d42803051480315071007c3c1000c2d052517601c50100300822020340242400c8483c0030024800141c03000d82c602080e5000c0000070269001c2e070710000c07a040000401e440f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 451082886 1250 451081636 451081639
    0x1306030206091c050a051605010203040b040314160b070b0f0402181009020f090a121101030f0603140d021c09030809041e0f0b041803030e0c0d0b0412020a02 69
    0xa00b00110386052041da00201c001404007008003c00e0000041d1003004105c0d5024400c1c400b8101501c80c80506084030300c1160412410342d082070100340041842c50050314100c03a00101000250311303800443ea410039002080c90525080c01c201c004c10080c00100041100b54031502c40e0404070380c1c0f580025100c50300181c034000e5004c42081265990305120001545d0044403002c801c0900c070350795030844802c0364480708105c03c1480002c41d2040c1c50340380920500c802441c9220001c64800c4007640c80d508a81510240581410740d1040c044151200b00e902c144051356200c1800c07147c4000c00001c440e034032495400c41c10014440c2d01480d41104003401c04100d03246400381c0b20007200a095a80e1074036260045416650060b03550155000c4413000c03070743d041d040007110810000714075016080b200291a0b1503500c40b030150f030a007000006411380302d04110031903a4040c500000c501c1141c81042d424070700c1c2011501d0f44040d62804c4001800010000301c2d010341d105413410140c2403003903c0d00782e846507001400039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 451084136 1250 451082886 451082899
    0x5072102030c0412050f0c04090b0a2705011407020a080403080a0306170303060405010b09061b030d1b09090c090e0a0e0f150108010b0f10110a0b0910060b0306060f0903011a13060302 80
    0x80d500c0c0086400c0800d4009080cd0070040c07103000ca03c0984182c1191041c103032010f0703440d11035046180fa503803404640c1201c0144098240c00c802902c801c0340c0c0b403185110007003103c68002180704550b8441c0d0300500250211181c50000300c0d01207046a652a00150b84046c403d6142a000042022004084424400010780082e0801c1c0c000c0580400c2c0d00b00121501c03900e808100b241505441403881000418131111304028103401c4e28507030080c1500c0a50304180c180030b03e0302800134a0542c05c080c4280840b03030a40d010555a5030b82e098000c0190500c4545000b9911500101d000800d00100c1c030701600d0082240d20002c0c603a6216406402d89112914090300711003070503860501414600b852111002e11814060384800c8685851460000b25040554078222480180030b2192018040303141a094070200a02030366091500300017842c0f00242c1424800c1000058051840780e4100a4591b80304000303000304204103c0314116030400401c41c4900d0310988546100c103090034001c1c4500740903280c018011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 451085386 1250 451084136 451084141
    0x73201020d03020f073008070903120e10021c090e04230a0309030215030708160c08040e150306090d030b060d09031205072102030c0412050f0c04090b 66
    0xa0b070003507200d4000388000d9502048100702103803129554801008a00c212076200d050a881e140089541004203442008042014003141d541e0040000098035081495144861244102919540700701c484061300324028401c6268016004203207450f040200b12120050600841c40c101d80a500a0181d92140c010b0308010a02084068610703c44540c001c80000006041203290203291200c2c6590440018403070103010b10842c2040540c224403140d900310202d00350b08240702d0240c2032590040010318139660300128504194881c0e8200c0700303041d41085e045590f858940401d04461081116420540c00e1856174410342400e0010340640305e045142d0103030031760418440c0214060181c141c40c8907885401440000a182007074480c0003c80391103615000000900e0740d102c10700f42c40c402095642801304004c40480c0f00d5100d0110081c2c22080c1d10001030b529500d8010803401801250070500030080803503800e50412500240310709258000c0412203884080070b03c1040107035481c2c070340014801c0010801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 451086636 1250 451085386 451085413
    0x6011103130e07020703050316030f08010e07080c090402121005030708030a030c0201020706020301060c03030e0f070314150c120108070f0b0904091b05130c0203070803040f0507320102 81
    0x11241c2c00803c6481076038111507032a00c85501e507412410750031000d1021100840100b68028420000c14169030400442d658900010141703005002170088040c000b00d00d000139614070381c1d4000c484844400900854a940d2240c4454000b4a8111061074140404440c085030920700090214100e035007078802580b0344001704d00114042d2401100010a56409100030070008880380003941c041c2c2229640c64a100b000c5003401019a0080319030101070b60881254000301d036001003000f40c1a25003100210b203003616600342c0580380c600c424448500041e00e03c402d00001540c0c003c01080c64450766003640c0c10301d0362210210364a814181c454040300d802e081004100311500ba0014112402009200051041050b100c80c440c042a01d8034050546c1c01c2c81300c05100c42c0c50441842e400c40f5140c850304001e40106d5240103950303841001d1000d005010b003c00080c0800a440c00001c100070b51107401d84203280da8501c1e00580300c2c074221007010b0324583c04140c40300c82c90090000b0407005c0700d0164010443d001d030984 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 451087886 1250 451086636 451086659
    0x10209030d18030204110a0818100b0a0806040602090108151e0103020d060e06040c03110307050306061c150e060109062019140a0f1e0605040b0601110313 68
    0x12540b004803201e000001002d41d40d9407140c100e4a1300400070030396a442c0380400082502e41d0041601150b2000345c41c0800181800144080d00c4500e030300d6001554a030921300040405060342c0c041072452141500700020840c0e50b4010b803141080030303203030b00350603803070f1054000066298540c90540003400e020701d072505142002207600d803c040c1030400518200103a030075102551411340150544a4070030040c014541080e101e01c50300c01180340381c00c0001d200c80c400024614803015107080c0400101002041a075030b42c08080b1001400400440f0b40510382a0f1051000351010b0010019480451b2a00003034138020842c0340d5124101c1650744413503290410006660200602915100d441d811416080314203904100f01c40c81040103401c0301341c0140391450042c1c94800e090007100c0560b00721581ca4400100c00039840c0700400e500c034541c01b0080804103110480c414110f0b0703002c2d00d11424541440140300020b14090700840382071782c92820038a580c100d160368030303c0f035401120350996480608100c0441c455 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 451089136 1250 451087886 451087907
    0x70308060f060c01091e030e21070e0106080a02070213091e050601050405071e03020a021f050618070c030804050c03030a09060e0301060b0a0e13151403010209030d 72
    0x2490101008020000b00d4900d4008100c2011103a5580d42e070307401800b4002d15180c1889a00c06100390300b02c04645d81c01030a0b000e40c1c1d030310300e8040ca07a40c45401070000b5034081e06c240500c0c8083e00b00e03074103a95600c0c07031400041400c0c0718050100c0e81520100d20102c80c1c1d07001711030580d9006403014402040c408441c8000303140c404000d4900e805034080148050061104907031328a0b0080300240307103d505001c108001c541b006040c1c1002d204074105041440100c1c51003890807007100c0d080060f01d5110001007a1b050071201c102000c201d071600400703210094460b40c41580183c400740c0f0292503803024001140e401550650b083c2d008542401041c0000a20231341256a01602c100207680c4420180800300340303583c114403050360200d81845424051580d1205803817400800480007484054608003040003544aa04209001c1120840080c0c01c0307502c9600000d040c00a8841042007100b001203400c02c4101c00360b010380761000d00200f184915600d414026603081000080162030010002101039801d601c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 451090386 1250 451089136 451089139
    0x6130302030609030403060f0b030c12030409020a05040321020318191d160e011d0307060906110736050708040b060102160603020306060403020d050106080106170307030806 76
    0x54101200503282403014a020b41000300003103031a9421413802c9015a1031281080a41c5454604001090b0368000342407110284183d5401c10014244800390b41180300f80e411403c0160700000d800e20645910000400c120b90184d07514182d03d08221805d11504040c0e00009801648280100b10380006003644400a410009003003801c070150350140c600c002c00d52507010320060291200c025080303032035142002d5030020103002206181d051812015114401c041c070780a04200000010381420b0822904045414070000c00b12804144c0d0782c00002c00030311550081d4000101520b48810340050001742c800140c40408051590b86c949440c0c841440803842003669100c8180f01c1002012034401c1d2080b5801030b100c40c1d0714140780c2e2401e42040070052001138102130440d44080c1c0b140c1b80440091515006a6505140269407500c80c000040c0d12401546c002a6109a114a210041000540c4030004407880d10000f03000c800c0d0307030710051031400d01c20802d101030a0304104088030000c4d03c207000f8640d12850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 451091636 1250 451090386 451090417
    0xf0c1b060109020711060406050f030a0204091d07150c080906070f1a01170a020103050a0b130911040b0109060804030c170306120102030709051c0503270301060f0506 73
    0x1204011034540102a0b004810140e0700180d030009001e815140e1481e0601c0641d500c0745403910b8070340020098410f10303c03281002207012021820800d0f45804a6000700100c0c0ea0a1140703c0501c011103c01e41400b402c0c0f40c21502c02c282001074038219008101d0190b90064075128a60200ca07201d00070aa8051030a036588602c003000b0007000075800b1310080010034015904c01e940c02c541403145d411403890607000081c00320500d902c000141400098040c890a60a1a000c01c990315074520103406001c044028030340c00b43d00b6101c0d080c54144a6480074864038011241640800b06030000d110072070703402c100800d00040d8a03030345c1805201d00880200780c04c02c0c0301e07140080140e0041d4440c400406140d0210280c0c406000081c005146402c80b050420449005c00071807440c1450480070701441030310703c00c150046810121004c04048605003641c903043e0442e003520380c1c5400403c10441da401c0c84600c0341c544180e201c150380440342014803400082d1000c0075585001a0f08000800480b500300f5030041c5c41d00c08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 451092886 1250 451091636 451091677
    0x70e0c040b0406090f0902030f0a0218061b010b040b030604020d15020a0c020f041104120503040b0705010e0f061006030b030f0d09050414040b281a13050f0c 69
    0x4030280003000100701a0361800350480c05c10000844a0b0b800b94400c2000b11f0051041c8218095075002041c1c00003012000141e03030300f4035507008038800484601c2c80c0742e1001010503100446074841103400c40c0f5841e400001c1007605018000c1000315a00111501c2c2c059001034002401402c242502100321800b40038901510001102104260b07440351039004002404040c1541c00c5050018140390100c008135030601c00410b0824601c03c2e613024500c2101040c55000511034213000d41882228060642180810b54941050810314040e14400d8440e040f41d100c0c1030203003401e00c40d0114640340a81c3c4140020719500e40f40600840c00b800010124070790502525951080f030341c45c10017030f9070465045a11031810451170901000100d860760012a9110b603281d80402001400054009030b100b07418056070012001010740c00c000341c814003808054240c0c5010f07620400381014169040c8444c1c7e003210024020700f1881000300543d03505580000c401c1da81d6001262004141902030303c110300701108010f9030314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 451094136 1250 451092886 451092899
    0x50405032517070204060608090a11120a0807020312030103110120060f040302010e1915020702060c071511030d09050309040c03050a0c030605100f0e1806010e0108010503070e0c04 79
    0x1071410324100064400041c14804600f00340c006e010040142d8281040302c0d02c2d00e070401586800780000001c01c00c0d00c46c609903024039070300c891150111421320000c54150602a251041666212003810ba00c64440d0039503008001300b6100440b03041e203901c00d800e0300e0701b13850020044d07070800c0c004500c441c41004900110702560ba020040c0d54032030103038240300552078206810003038212004401c41c0c0c05660491460b001000a02c008801c0300c1c1c550000007040c0b280400395482e0024080e040c1c001b9440140022041543c5000007404000e540c0040c0e078040145011190580714100307440e000c5080c68000b80711803030010341c1072380c0084040c60190042c0c03460040e45c503002800710389c900c030080c001090791041400240860f62041c42c00840d12420100080340c00d010015640d0b035030318250042080050924030304050302c20200080d5001001d07001c20100c400810a00c40ca4031405c894240c000794864114080661041e40d00e58101e030405009850440d00f4941f00300030a51340100b000045540400c80010311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 451095386 1250 451094136 451094153
    0x13230a15030b0a052806021207032105040c140103020a09120f23010b0d0308010e07020115030b04120e1309060e060403090f06110c040b01120c090f08010504050325 72
    0x6454030b0820b00c0c02880c5c804246421030405401c0081190700020707510403141c140404540c4641d825060000e803546442003140c4203112401c2956028a040109200030007030058003540684840c03c4520707030000d090600450407070098901c042c0c0040c1c48640e04000840001642080c5c5c28003820541d801c070f1081e500c809182012940100f0400b110a10364800200000c2c811034120890454501e102003d090301c0041104034180a0700c2d00e004142d9000c1540c440c004d52044d00444448160400c17201d9480c00c0034541e21801300c0d01a140b005843c00445480b5226a0901c140d0360401405040c10301318401c0518002c06015008440c4540d41e05104e203481d4100704041c920a500c2580e411070b0300760420402030380012041d8130990501038400b4032a4004080400c10092107030b81a100050f142041d080101c90a4004084d407101441c60443c42c0400c842d8000150401d50b0b604401e070010103030f07491a0390382c00c8420844020f01990014407000d411000c104800d618070310003580c515131400e011074440660 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 451096636 1250 451095386 451095409
    0x2030c01090804091109030d030e190318090e0d050a090e0405010f0e1603020f011704060c090510050702090406140f011e03050a0210020313230a15030b0a05 69
    0x101150b01007010040a811405805960440d61070b41da0306082400c00480c0d562200c6036060014540c4a8603a0004003004001500310040f01510284511800d0b00b009015034518004802d050325100001040e01b1906014201400e90000d0040c0142e0080034400c47e06c0350400c2c50300d03104200d0609000078280c00a0980c0310300441c0104000950307000701c000750340300300c803940403040c4010740102a01540401041081038100c980594890502e00c403c1d800423928a8080b01c0e1a100e0621030030144400d21111340e01c036003440102c41c0c541064840e120010442a8101c000c81d440008504006e000d00504002c0b4650b5081f6110355004500401d0f01e2075514006d1000b110710705c00303282043d00104020b00c0c10074009002c04c5c10a5001c5801c0c03030300703549070070b038403001800703c007a00481e0b90900010200381308008850015062843c0c1c1410300707848203d4514212411207600402445030103a40320107107403007220941110303841342246c075144a44000a8010340800800141d2024900d032001461740c039030015136030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 451097886 1250 451096636 451096643
    0xb030f10081015090b21011404143d0204170a120804020a050d050c062d191b05030304060501050916020619200703090e060102071502030c0109 63
    0x2008041c4000f01c44040056610440e0755500304000340c2e40b680c88110b08080c00704d0803205600d44481aa00310300c0d0141504480344131a17500800b082205203c42c03000810116034800f001e4480450004140f0b00707040404910401840351481c1410011402007200694403134401c80c000b5050a070b45408020980c480704a652106402a41c41c0c0e2080003900303c000d018134500340c02c1202550400380c01291051256024860045096078010001d11400300800780380b000e80100090307a00c41300c500c00307035802c014070500400f480c201d41502000e528810b10241c0701c041d0070010304e540036014030900032220b40d48030001003410210381404071004a10144021407280c1c0c042e200224071940b61000344944200001c0141c1d212074504003803044920340c0401d403290840c030143c00c0c00d10003d072420f141c0c42c01004c101481920301041c070b250f44c5420005000250a295000f40c840c2c10000717660781440414214110fa4550060b04880e20038007c24044000c8141000f00c83d104590038580e0661845d42103410700c040a4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 451099136 1250 451097886 451097891
    0x203010e0703030f1e0e0108060301092102010b03061302040507050d0c021506040c0f120b09041101020c190b0d0e010f05010512070602030f071a0c03040501050604060b030f100810 79
    0x40c4640180d03850302060045940c140c1c0e50217070020f006140b9450343c00028104038404002c0b6509507800d41250b824590407000d004546900d11408040d0440f5026906000d075003040c802c490f25280100f0024400d000c81d10ba01070302001640d003000300604d00281000d050041c24004009034001c00e1003041c400e4040760b001046007000358659812048401010540f05600f407a860030082c55001c8030103042080c0c81d00b041c0078030750110400b401c003030031501d003002d0380094010081000b03000d60b001c50032500791002c0c0c00b40c4240c00c6440041c0302100e001158035142940c0510400c10151000074002c0a6201184100240001d02c440c0d1590950343d498034040d14054407400103110f03500c4d1101c90381c06510301c03410040044a141640c00b0f51680559a84040644c0020401c001803200c000c100302c4440d074184c1c0315850185411080d025481d0001d40f41510f0781d600c0d20300010800d050600c90441503400e09125641982e603805010713140c1100c001c0c071350344c1c030355214031400600c03100708000c0d0f080d03c4101c00901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 451100386 1250 451099136 451099157
    0x20103020c1c09050906030d080c1903090b0f010806010b0c0c0907020f070b031009050a020408030c070603050109200a0c20011e050a051b15160801150c0203010e070303 74
    0x20701c0d143da00d400c661712614aa00500000c0d0764001031050703041c102410072000c150b59186507013181d07001d25401160000041a4681d42117a071580c401004c1c1e80c0300e00320b0324038252500d40450340105c00c24054200c807170b40100014480c0d4011200501080541c42c01160541302c14500460b0075a5019203861000d40d004220181c4041400e00980c030141114111032411031a0094209490310064864940b2041d5500041080c141003a0111400b0f02600400c1325521040c17040340c50341d20381e80c0d1b00c240800a45414004151003c090084070f8600d4031907101c005100001c0105500c80d60f201c19000e070144802e20000314001610b40250309284500524041d00030751960001400442112a4001d440074040364040615908134080d114000400d1030441e4807021541d075140c40699081c0c84020151140b503040c14081481d02a00c45d206490b4909100600321100f08150354404083c010050754140e240003100e01c2610519a400c0c5184c0018000300f25100b00c4690f86003440600e410590010710095003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 451101636 1250 451100386 451100443
    0x1303060e0c0409020f0d0f020910170309012c0d03050c010f0e0a0b0402010c080c0303011a2a070b1611010207030f02040c050d1a04060518010b07020103020c 69
    0x41e1020051042c2c4080c4071842e49540003840280d040903409105a0140521000703004850520311846130b406007441409040c02804407041000303911401740300244041c06416001d07804070503102c0c90b507410307110005c000d03600c1c1003000e8202c001003401001e43c0e441f005080b55681c0d10045821780c054003c0c0c90300ca9441400d00800d0342510005036030760b0496400e0000030b000010000410900c0e040c0c1150800845031614401203411260b0f200010300b0380c18010400c8480c100c0c0100c005c604032179440d981840c10503100a8012400d006050b0000c018003404521581c07851140300001a01c40241410b131152140c403014508403a07005640468040701c020f080c000204248034a8540140c0c00c24002400c503280f55690b4014412850301c1c0090146446030b0702680118064425521140780c1d0300d000b07110729441303036039840e078107000740ba80c41480349047c10000510b504003c131041d520b924980c0c1686c0352036070a012a08217944c1c4003050403410182d08111464144205126140180e204c5402e14106081841e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 451102886 1250 451101636 451101643
    0x90f100f030b220b120d17130b061207050303040e040c0f15030903020a0606080f0d080601140c03040f170f0106060507120201090804081e0606030a0312021303060e 72
    0xc0303228002c4182091214142040c41807814600201d9080420700c14000c0c0040b8120000034403510205e885400c42e00c0c5c4820381c0080f6407117119845001214410741e0390807901c85190000d03201c0a84401030340400324445003003c002c1555001c0381d040848004070b58480c0820301e1540294071030700c800d0700b04206000c100007c07d90606e0042000d64100c244e1582081421445d030303001c50700040c040c507554001d2001054001e21034504c0c400d8112204022aa544140031a200c046402280b80540507090f408080a4003510b0402d01480040e580c0210103942c4e1904856242e10010100100788400d000001d9407070040f00941024005580092a20381c034050071442ca0300300b200c2c80541346039041c01c0c0706028044d402010f44803515088180141045031003c0b00341d0041c62110702c064810540060b01081c48440001c042d56444c4501d00708c001c3c490a10003515458131400d0761900d43c15080b002900740800c1c85160742d0264028140c0d401440c140d40e190203010104000c5d88104d5005407a280c00105190307051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 451104136 1250 451102886 451102901
    0x909010504060303050306101701150206060316060c021f02030403021305012102041401170d090803040b0a18150909090308010306180614010e01050d03021002090f100f03 75
    0x141d41c00c0c401142190740280c04c9010051074039010390040b000c07041403284108420046041407140881d90355866410308010300d4048007551000d4466680403a400c0e090000d49107a80e2503501a60001c9103003010000c50308071801d0b90003070307900281403444201d030309548440446462045400030342e600ca00d107106112411091841e0420414a801e00410035001c2e5032101a04841030004115000c03119031000030020300741c198000088114080001c10b40b0808143e29007031448194003140c80b00305c02c5034000c5902010174003582c19140c200340010080d8060f000d02a01484899051054504414000d5005440280e40c00f5000049100810500311030b002110100600a0408248000c620f26203001d040c0a00620005020580c0c0c0c1210302c02c1d4600e0012003100d5030f0380c00003040c84944220081025102c4007030240407003008044000240f40e192420744120650340c19000340010724111a82c0d8030094006580c2070350010b0502d514640c55545038040c19506903034548403a50300f03584a0344010304549a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 451105386 1250 451104136 451104139
    0x5040311060903040603051b030a05241f17041a070302090d1b08030a050d050106020c0d08090a1a03090f0d0e0409060b04090c1a030402010503241509090105 69
    0x12200b80842e00a0200444040e5080c07030501148070b0b214905000748400d142d01070b00300f0328000401400101083c580040340100b19540b030101d030300e102c03485080c2101050780417410b0b4021862920042d05512300d42c040d0f0140c1400b0304055480588400b0400c00c0c85100700c40448a60340800e8002561115840321903400c20518501103003012845804540c0c030340e100700000340c109404901c0c402c2c080c4400c1e8450901070011081a40d841d07038141e0703401400d5074028000c5601c00604000001c40c119100042501008a00a1501c90241115115000103900c45245141c0026004001080444142e0000c01c0032941a103203607030b0b0340d00c2e00d09886810058200c5180e0940c1c0c201d062201034165110b5000040030307038220380000b921115884e003000102840b88969170001d00b050815024070090030090001c4810074040b84040742c0d540d044240355488110b40c000c0c0406c0051010030600d0050548010740c40480550080b4500281e0000883d000d56a480d400c000e1000010003880e241001603c05005040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 451106636 1250 451105386 451105393
    0x91005071205070f02011101060f0f09062c0a090b070c050616050307050a0504090603050109050d0309030503010b0703170901051e040203030d0b030304030615050906010e0f12030f0c0105040311 85
    0x20300da880c0410740501c0784011b41000380058941111920a43c03040c4020283d403c120790b031655481c0b14100c070684d000d203d401b41082c039101c030000b48603940c601c0f04038181c1c1a1071440e14098208103101d507100200a801480041d560700a03907000103444e00b000300d000b4940d039100c407100e4031240d140607868030700c5c01040c0390580c0c400c441c0340a14035034010782641d8002c4101d0502d80c1d1160302403403089609005030fa100d0440e00d402d060001051080640c070142c54507004800b9100504003101013030b01522030070300c80140004c6003040100b0454640e0301c0908650381c0b10f0301d89000105161148c3d101d940e00141d507059000d95550050203030000e02c60108110b86007107824141250302e4641c00103510ba0046010501c90b440d1140038450555030b09104131006164810000c000b214409078100030300c000c050240c44d006400d41c0b07010030b410358000e07050003102600041c0305802d0380d94081d05004000412000e908041d1100f4000c410710f058024010740441075000d8000030b410b24040c14020100000903c000c2c00981 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 451107886 1250 451106636 451106647
    0x321060409110f0415031b0b0f0904020706020403081216090302011215080a030309060b09060f0d03020106050a09020c0c0906060d09051c180602030901170c091005071205 75
    0x800d9a44288a0100c0032541000e43d040001d0110703016218040000780c442020b0603010040100401010340c40103242030a008120b9124616401e1038442c103114031040c0402448800c4003071a06400400c24607204503000350130207681c1c0d514031043d03400102291800d403121034100001d03d00c0074030384804141c0e0545408000e070341c079640010305204086201c59a2181e110030307410800b10302c1c41221600820f100c400700c4104040d9401e0040090400100856025080180d255060301d0203a40050081c14000d0007807050681c0380301000302d00d00c40010300301c095540700c2d100024507070340d040711100050005440150b551814142c4881c00d00b422034003030701e100300e070900c3c01d000140d00e5001c25100000d443c2000064418503a00b4141e182c41101e180d1b0044c00b0614080c82e614503a4000c10310a140d02401c2c441c5c815854650310243c1e201e010303008003e070001c4c0d8030700044030045a0690b20160400c01c00981c031481d040c0308002107100520301e02d0201c00032405c001040410400c000440880c8102c00b85003550a20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 451109136 1250 451107886 451107893
    0x307180b130c0e06090301180812010e061c03141c0f020703080c03040501090f08090108070905100e040f022101090216081c150f0e0108030a140c0321060409 69
    0xda00b18181900030342c0302040f00340311a1800d5000e844040314031040104658060315002720503030b210940107901814030800002d40c01c040701c10498090310009040c01200c11082482c4054400110000c1c0c0c20850f5035481020769058400060400520102e03010b1800000c4003881c4003038618011844403610b10400078131010035405808140c00c04034a0110303981d2511141821405000e00030b6001d0910f0480c89801c00800540ea001441681800e81359103540340d5500b40241c6440d000d61103240d400900c04c0980c000643d12074030310a403c3d004000d00001d107036030710a0140400c070303005400d41c105180b40203643d03100c2c0043c80c00c0c0002c0c010201c1e0a415442c140000450504501e4103c00c001c0289402085480d0307031980c0c15400c021510180c01c0104500d245030300c00301c1c1e0040618450305244c1d001d18500868108900000d05050b00c0076400258034003040a001141c240d0f01050083e0302042c000d003d266084881800141006008002e000c11910034640c0c90728403850020380304038890340c909180070000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 451110386 1250 451109136 451109147
    0x50c0601051011070e10060806010e06090301140f041103030c0a02101407230c0109140a080d0e041b1707051b01090b060108240307180b130c 62
    0x1518020b45528a20800c0603100303540b260002c1d4100c10f030074001d100300403482c440d600049502c1511900c18a40510740c0d600c900366400c1760305a07071840c00112920300000c1503040c6440100b9125401070000901d0005400580d400d070001522030000b9040d01c081800148107040002c1a0210012009985807070084071549503902c5210000a0081c481000508505401041580c4181c04d1102280b9a2080945809180c010f0700d1001c1c01c4100b240c0c804600d0051308001084a010b280684406090b5400c241c0b600c8245400e02e2449036001d240b80e003001c603040301c0501c12040c511150b5150068110400d078104000d4941c0246005c9094518405c074040813648002d841c02036100081d91000d164640040403070703031840b4480c40800750341e03401c00b02401c0004055000032011070145462400310703100c0400445030460150b503000503400d0400c5c98603050503040f05030b4003400031009080300c5020380d076131240880304840d0f81c4803550540c2d40ca9aa0580c3c0381403120030015180704556040000804400e0060078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 451111636 1250 451110386 451110389
    0x6030b0303040e04031b0503070210021b040b0307030204090506040605060102030a08041506051f170906061c02040c0905030c0d080307110f1024060c0b040503090a080c10050c0601 79
    0x58103003400444d0515000d0f44203071840707000c00f802c02001084a42007441e43c036840b0f010124055116130b01003940e06440858950b5038041d040030300c41ca00c0760702c0d036080101604844424640c1401a03000003c0180d03240d02c11124854424000760130b2074905814070100b12840100700c40c0c1590420060500140e40c8199504e07401580503220200d50b40080c00600d0040c41030780c01283d04047c02d000c1c9624040400341001445e0394036035a4403080b60948424040c074400d415568261a6802240800d04c1868211500514401c481548c001d0461880e0005400d4581c1c2c443d0100110700844400e2042b400c00348407038034001000f0382d26a002c0c1044c9070307220030340b520004000004218095241140c00b400c1800f20409020a140454200640c0d600c1158010301c01818000c1c1c001c11118080c0503008a140c4104040700c5050300e402807103511030380b150406040000c00480b0103001c00c10084851f69100e038410400303400c14000410151558a0902c24403000c40040e40c0107004062000c101ca41500050290 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 451112886 1250 451111636 451111649
    0xb0c0306030a0602031e0106020f0d0207030807020907050f2803090b01060f05070203010504080d0b011716050918070206090705090115140a030c120507021027031806030b030304 78
    0x10795990390301e02c1542241c0502402d03903004011b6040009005035000404045039103292040ea005203280c41801d03030791200d4070311004141d400107002103c050b242c081030241c0d004486003490742c94454800810302580d440405028100c00c841712303c00c0e4124200c14000e00c0403145c6401c04010020668a50801c0d5240501c00c100400005004103034240788624140c544807540030700248818201843c0084094001070591300031a880d0802d200c0d420b40c81150000c00f00341d20408005a2030310303040300e80070b00120390144840078400100884845a140d0b1001c0d1125410007885c1d1345d42c9401c240000906018028159050641c00484181b0066880c01c20080c1101c4080c01080030f014004541583c100011224000798607001041c0c0303001c400d8041e003021502008940d13801c41403403800c88810040b184192081300c01a80911b0240c9a444001e0303005000b40c50500f00700c8200d8100c0e40c551503100f000c1220381107000901e503204118880c80400682c20260100d410184011150240400d64902a501c00c5c003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 451114136 1250 451112886 451112891
    0x5180a0b01030605060c060a0b030a0b0708090a080d0203040b0a05060f12010e0102120708130c0e091c020304031709010e150c012d06150c110910030b0c0306030a06 72
    0x14525a01030f0340480d00078080645159120306040c00e01c0b64503900103d503100700882c2007101c519110320b008946140d12a40c070003444c3c90343e511103800490390f05000030030100c824461840018041a0307800d01a041c51000b0b40700c0940d40e80b40900d80320443e0310010385640c014038108401e000c40d541d40c01400c80d03500c070404d0391040040d03440c400c881e50141400d44c000c102c280d480060308000721400540d02034441d002e29101d41038140c41e15144211449171060001c1e0903119402410701c101c04080c840190030980b850102c1da4240003000710050b104051b40380300350160307000160400400844584003000c02e10443c0301181010301c020000381005035000070991048980c15115503080006405848000f61080005c0082100d035440c4010721000003201c002d0381103465003a5070681c40711805024140da400d6454136200c0010500e003078490040041046420b003800301c24a4a40f82c41d0040114420201c03c810f120000f86036081c8009000f10103005d602da072620030820450075440002e000c020302603121703600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 451115386 1250 451114136 451114151
    0xc030a0f0603020307051c06050f220816140d0207140d050606040b0a1211122b02010e031215010f09030201081015020f070807080606130e0d030f0605180a 68
    0x107100c3c03000c0341c01c4002300f610346444184a9861140780d0740364400c00640102500c031045189024200481a06005141d11001c001c04194103c400b080660aa446288420710002e42c5034282401d2008090142005070300c0788030104200c0b1300010064894050a03035003450b103140b26441d0581c1314075000f01864080c0361540700c3d2000680390403070b000700101400488800c80000d00d01c0c061826010301c0c8201c41c825401c500703503000343c04008205801c954040444120707a5940c0300341031004016076101c2800555603106030200d1450001d0005180c81c0c0c403030001c0e4089a180c40e40c51a03034881e40d0360414a041001e80140003500540002ca40001c0e01e0b0242400d207250340e0b8014a1400c0440c40380c000103620a0440080e001c0c1c0c98002a850888443c4d1005031000541c90340c4400340e6442d0688075100480d0311080219440741410308210b0181d1084030000308002114640f040c0c60b0200e00103a140009545026003685c1130483d100b103001411b011501001c0c104a00e0050000b080005449011040e41d110701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 451116636 1250 451115386 451115419
    0x1404030b06010207150e03011104080d08060f0a060806120f0304171f05040b1f05010309080d060e0f150a09180611091212070818090c030a0f060302030705 68
    0xf00900034855010f041031170103844a002405c800409560714040c0d800c0c42c0300341031316840e02d0042d5410740d03a0100c0101800b01410204588409026000303503000344428408006030740b00d41d810180034140c940c8900c0544e060110030302c244041c04a04101c0913400c0249801e0520901008031030484030318080b1207404250040d2801e003000b00c2d42da01c8031182c0c03900400c1e05d840100c441e0000c034810340c007881c1c10310b40c540d076010030000000c100030490b040407011070482400190302950002c59100c1c0961130944c1002c4400224200301c443c40c5e0032050742d5610310030030402d5018103400402ea00c0b00b0101c0c4c405d11486450300205a0304051070244690898035106202000e1000d00d041601c584c0d0410b400340964002c02100d40c40c2513204c10300060080030301c0308401e0007418000030602042101d804465103021850f440b070903200d80000380c91403100e40c20704209843c2070352050035050207800e61482040e56414008110f100b02d807001140710080f58204030082025a40100f240e008880c41591600e80b000e800fa03030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 451117886 1250 451116636 451116643
    0x3160f020c0301090c290418060b1605190c03170c010c12060f14121603050c011d0a03060c020f0a06060609050d0807081b030a0216061404030b060102 66
    0x40446425601c4c000c00d050521102003460011100f410541d032142002c0e1050008020540d28013070306146000f080104404c07014500c10341c00030583d40500044a40c3c80d40c40e07410341a400300c4c80002c4241d84a0340341505104082c04901c044105210100d04640603a949181e02c285d21444090000440403900350406c4980380b0454452143c0c82c002048401100c0e00042d10f01c441d0b100c00d42d000b00d4a488404240204440c0303221058603510300040200030030000c00c0110451041178600010302901908114540b2441c807944003840c420000b82c006090342c400014080c0d03941007060000301e1000e1086050360b440314121a03003503c0e04400082035900300008103924003a8200400c800a210b1908607005202031603103d041602c0c0247e80d40d0301d49a40c2c0340d04120041c002e40130042c101c403a04214080001d000c2030000d000b0041100e0385076010b25403040c8018250381040d01d4040150700248911420000c0207081d020250803641441c3c080d0424a9110740711900403400010140755040c000316096038000c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 451119136 1250 451117886 451117903
    0xf0c0b0103030815060c01090302060702070f0e0c0c0f03040519030819021606020a06050108030f0a050a140301090f060b03010819260a02060601030b0d03030911040e0c0f030303160f02 81
    0x182c417480e40c507010b900c8040d00a060040b01900180211404a54114400b20380c000465051414411041d42800c240d1603100300050300e401800ea40410501c004000c042c40308c442540140c10140d0f41b554941010710000c82c4c802810080444e4543e541400050015420f490340c4419071000b1002d0b94080c11826454005400c0080a01440b074940001340c2e90707400500f25096074400c400910082e40d840b041d1f5076070b9000b40e403405500c00f0420300c105000c26106001500b4680b240303140a0f103c40091010345e001c1070f0f1080e04142002601ea43c3c201e29210044d02500c4000d00d54110341614642c500000b060b100d414013122880f0b402e4107007004c0c41c24805400c1500c0c44165008404902440d080842c90a9036400704200300c000d8015000001c0da00e6010b81f06a04450802800c8466055010780e030032002050502c10485001e20071442c8504c1c03035121840b400d5410030300d04000b8146c0d42406c40800036617080d5960540d00c694001c00400c0f50300c00c0c1c110b801c154542c0850404004900858030141d0814584 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 451120386 1250 451119136 451119139
    0x3270302150403031722081c0e0f0708070915050909060609130c091d101e0b06040e0402150d140606070b1501030b150a0f0c0b0103030815 61
    0xc00354880000009070041c41280d100381c8403145520880b01c100e0088001c100d401060300340d850100306800090b0081c3d000c0c019440b502189181205800b5044a100403030445160329a0380c1e280358645401040060320322800003400100a034601d80520aa035030a5680568440300b038441c40c0240d16145100040c402410004144070700c207280403000190344484c122a92072044405402081e4000000c1c440c0d400710710b8000807044059400d041240000e0000503101601c01072503452001303d0454203000724045402000c0d40801c4100485081e00e40540c2e01282403520f035840c1501041d403958501007101c040b00d4902e14000804d40c0c40b400080c00c880280c0b4914403440c10006000b08445400d603110720600403480c8a002c90302e89030303001803010a004031078000f171204c606040401d5a035a11418100703c82c90052401195080c0b2030340200303981085440c0d0410074144046603017089150007440555116280f4a882c0100c800c864659004080c1c040c8806000e01490301c010980b15034075140d200b440c03c0300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 451121636 1250 451120386 451120399
    0x12081513090f05010f0b0901031205090a0e0711060c09010503131403040f0503070603020c0c0409020a080a0c0f060804150c050409090b060f0105090a0e220b07091203270302 76
    0x686003002130180010202d08500b4500e040580c14a41c07030300c1074031141603079000418240e0380741880700c00b0303561035200c03814151740954030440006010659582e002c0c840c00750707170b91026051202121140e290203005800071382c0e060014008584c10741d9000c000d4a600c560060340d05010ac1070719040400b00340c000316003002400e000004000c43c0700029407007400c04a4200360103c460a42d071300c0d03204070b04900941c41004000d030803034200b00b4841e11f01600140d404900080c0380c04115039540c14428601202100111080d0350035000c104288400c90100d03400900107030034044120702c4d082e516217000d0042c11040107400c0342d40e4551805403c0c8207070300782c4020f040304030b008204064240c1040d00900340d00321003284c424050361f0001402d95100300d007940d24a61001d00301000301030401c00c040c42c6010005107203400150a4180340c0d0a520203030040d034a81c40b4000c82180055042c5110000c054916540000000c40c10344100180000c1e405070400058440040c1101c1a140030316944e0344294940c1d03800130394400d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 451122886 1250 451121636 451121663
    0x210a030e04020c070627060c0b0a0e0706030c0306050a060221090307090618110409020c03070b130c14031225060f0b090c09010e060c0f01091208151309 67
    0x5030099404020102c82c6c03940030381e448500c2207142018683c14010580001c0c024060140007032010301c2c2c203039009140e140f408206e081c200f100c817a282642a83c001c00c0020740720469141d58503014415200038003010356a00002600340600a50b0b40c6851035034008400f0504a1200c940301c000c070040e0b80f04044000e06440c81250b840c070600003d0031590103260807014a00e150350b220b492244c421461206020580d01d4101440c10180d4002500600129004c0f8041040f81c10000f45208108074031030281e03080012514055401c28030460b10080d041403000c00039008000c2000d07500010300025986221a42e0f5035518820001340030403c1115491410404072107261100300314680d0440a011040f4800c1001a90302590400444150580b03503c41480300030401301c0000e5105030b13402031049074050022880c00c10049045440d0581c6000b072070582e0b0f555001c16004014100e0021990584580740401d100e00f44420304003000b613148208240301d0124140b04100d800c3c896001040c81d0340c1c00010151195 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 451124136 1250 451122886 451122899
    0x4030207030c0e0f0403030b04020c01110c0729030601110f07031502210406020714010902031c0e10120903021f110706091e050309210a030e04020c07 66
    0x1500e031030104030b400c1052028042084110551018860300e2503581030032982e00d40b500d00f600142402045940c0050f000c103c1842c91807000d009004501e4040b40e86d1941d02c0078840566400e11b07031150481505440ca1189611040b0a80b01044c040b40f048244c80558940300c0c40b0042c0c4018801c1e19851240d8000d134015080084000b0800104480c0140d040404040c02d40b07045100300d10802c2403001710701003101250396402950300035441d8064802c810040c548946501c400740440c1907800f25592aa44a000310000c5003400c1c0900800a00b043c1070785019102c10640c007070644900810320901500b0147e04c104080c40c82400b40c2c0b0309000348014104201d02d55414029101d1941844a0440c40c1040b007e6460030415807040302800ca004054540c10141140d903060007400c05410706680840300f420030881442000740c440c42c822445a4001e50340c44680300c05108010213280764803102c0c019a004030310b450f0a070100385800b03250340c140342c00d01203036040c90009002801419984007c078803e112020980707 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 451125386 1250 451124136 451124143
    0xd123c0809060c0d02040306110a0201150b1605100207051e06060a0504021602041a0a150c0305030c040f06080105010e0118090b01020a0804140102060a020301030510020904020903060c090415050306010b0f12040302 94
    0x32b540ea154001e021b410503002414126904905c1380000c122010401e20000560000305254a548550141d402000d100708148051ba0807042c010740706c94000014a40410110410305810040403501402c550700d8000c001410704007482c422a40510f8001545484a512b0201194206a4000c3c820800b103240c11030380405404c4450f90b0a4090b452482002c03502e01c00c2240c518845006655a51591140b607580850302604080d21031110b460080c40003103800c034040305580300500b00c0380d83c94a940390724003000117212503400c10342d20341400010051103920400c1c14400b601a107035083c1c40810026901e0004030b107070585c1d005010f05030050214002c1060302d80f09078840d107060801da00300c541540715082410304030304c420701c4000c0c400d901c181d0103080c4400350368000d44490000103100506100b0f0403001b103410303c0001c80d03c0003100c0c50005a40c2c542c038a420300c2281e041041442c1003225a41c24000400d60304c0d441070042d11a0f4a901084081288056000320359003896800e940c46a141002e282c00303550f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 451126636 1250 451125386 451125397
    0xb030a02040f20040e06040c110a0302060a052a0c0a021c0201031d0a060b06070b0a05060123030f1803040e160309020d123c0809060c0d0204030611 65
    0xb5403d004002002810180c0141c80642c1d582a0b01c0c1a00c2d512800c0411004104060303400d002e00c03070f180690b2044c1d29028001d10003c02d00a8010f49158503010500c80304841e0020499200f2942105000d24441400240c0d2080700911801e0b407030390780d60140c80441c5041c62000c4004e40c018490103040c540d55000d0300b0040c58441c802c0e2010310440c0c40303000304110074100403840100281c0c4a00c0d001004a1080d401504540c8805003c4510f000b142c0c2c1c9944104510441d1140c02240d2910180320440d60b1141e4444141c0034640d00e11a443e0000411480d654813018110465041400010035034075070080442e180d80d1503210045954561f5181c218546c08902140c550b07115901d8201c035000030501034015455030a500070301d800c211604a664403040c6010f4803600e54200111455039920366034006a41200c029a86036007101001841440e00d0802601c0301c1311482040407030828000708600008100e50000d10032444284c43d89210b4002c40001e0040394409030640d800e0082c0203499079440c138010103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 451127886 1250 451126636 451126661
    0x303111305090f070c170f12071106010b0403060e0f070f080709090b0a0c0e0405071d061206060c0a0803010e0403080a0c0f030f0f09030504060f031401090b030a02040f 74
    0x4400369a1680c202040f250700300c4100010410110f80743c80026100e22800c801d8030b0700315414508110100114000b140c12100381c40490311805410311100a03049502c08541040650003049650b051001c15001806588030040c881d9440e220b00080400062104a800301c8035802107601703642d654000003503490011300c10446035008419000c212440d4038010024519009041c5008a848000102c0000c10b1242c140a08101d0324039109c41282c0d65a02600380100c40c0c507940d09400c90342c00702c8085819041d29084510440313081281e0b2042c4801c1e850003e074802c1c0f007154119102c403010b09040d8201aa1007800400701c04c800000850f008015000e041c1c0103600954802c801c1c2d94801c8000b008840c4890360f01d4021810042e903483c00e89109400003180c0801901001c07d2094100c2d60440070b071540c0c51021000f14402040900040f40e21850a01e1020564a0280301141035840b00094410060061444864a030a2900c1030754500300040d82c09560b01070f2041001c0000c9101c110024202203a110f03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 451129136 1250 451127886 451127899
    0xd1e080415030513030c032303090c041a0108090a050f06070906020a050c06090d05010218040c02070f030f0c080d030e010c02031309271118010b090d0303111305 71
    0x54030070501c42c0c0300d52840b03074841e440840100401501c06444a400104c021000c225002c10300d1402084210420308032110402e9070f03240c0360300b4040e0f03159003070202c0d144650f809203141104520f140c003801034070302c0c0341d242c002e08005019481c2c8240f11030a146450300042e0107071180e55200d0a0440740040d07078900c660420360310180e00b079849610490b254844c5100103801e641c000000840245070a000514030518010660482c2c50b440e581d0346400d9820480a50b103000400c0028240e1604042c0244094490a0302c05881c1d101d060600904011140b400058100e6810701499420011500994006003134104d00f1101750701c0610500030050030f042c0501d0241c035420040006046da00010599011403c0042e0a0300c03041d08043c08880104481918101070003113041416980340d00c8000c0310031216000b41c0700718100150341c00c14807141c590810300f800703ca02080341c010000085501d003580d818840450382c15281c80040d090481c05403540c0c9412510101002401c404e0214070380b54640c08442098810 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 451130386 1250 451129136 451129169
    0xc0201080601260c0405180603060604180b060609040509010e21090d050709090803100b0301030f081c060f1701021801050a1e11060f090c0d1e0804 65
    0x4440b00030204a070f080b20072208240d00711440e030740c0303a11403540101d41c401124242035840b0f000600b181d100c020720700700c440207000900006040c240314107a4007140a0701e0a115030342e030a4500300980c0100c480c02400e0044c070040401c480ba03580004541c400c010081c01032119040c00700c050b42c02054002400505441012998012510214201c440f031031200d01c003450070f00000009100900601907412103040c06440e4002c24608890311405000c14010304050b82c69140c074501403000254960004d65200b072050004000007202a5800303400c003944201a00d4440c2040501d0545070707514540c80da110141809008151801d074107600341c044541a0056400c40740300d11842a00b00e105006210800000c252000302580d402000200000101454490441064968020b503a201c4c100c4003200001d40491180b0360b038a00410419401c843c5803075000c807172030401500c9182c1e030320103003200c1c01d0290a848803d5820b1200901c090a01a01254540240d6200368a072000c010340c4103009850122203a00740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 451131636 1250 451130386 451130389
    0x3010905010815070912052401060207080703021e240a021203040b0c0309210301050a170c3c01080906071b330507140d1503050d0c02010806 62
    0x4003503004c1e501ca03445086007141407501103910b50255040c00d403650300c00c9860074040c104201000204d010f15280489840f54100031000b410a40b1940c401c0c1e86641c4405010300c05a521480160500070750010784840000750031001c114000c24100040340803010404140c4840c0240100a00400c03034203501b43ca81080c4a44503d21085c04140ca001e4003065502000806001605009541051001007240d0070f007440c600e010403141040401c0e00c015040040010000ca080079a008000340000e080281408550005107a43d81c0304141d80d020711612003940c1e41ea90001000c401c031100c0c408a051500343d82481801420724014905188a00084591000582c00c050100c0d0b140d01484040e5a440381102841e060307158010100c81d800c0e103070010054082d4410b030580701c2a4001302d28251200005c002c801410100885100624141c1070241c0c8145034a048a030440403606181c10054000819094054541d001d240d19600010818860407440c20165030700030100e805414401d82e1218056038902c030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 451132886 1250 451131636 451131673
    0xa060801090f2d06241509151d0105040801140f09030a0c06050a271a060a120f0c03082709070f110601090c020106090219080714030109050108 63
    0x20440c0341c07030180c41d214000800c03e030400c04e171403816100c5032101c01c90500c181c092005440d9004400321504c08043c400010f0b04420414010304482e0000c4803490100b02001c0c04203e69a038038945441d400905860003603001344117480c060050036008200b540141c0a07102d20300241901d8007200810080002615190000112450099295507042040510f6a905400b620000d080d031034a90f40c8507a50400c4000c404002a0354000c99400e4a10b50356241d400d015601c06d86030b100300c154004031502080415240c8a514204460101c0b44030340c44016141090070f001007100328002d1460a80b80000024480c0c0d40340500f03e201203a5420210140c40b104010611078600a41683c0205001c0005804e02d07021f003805039080c6c6c4160924805892003000c50b81c0c01c1503826040038140503a90381b18514a241d0921610000c2c10b0455801c51811403059034508461203901407a004002c141000240528403131456100718651460142e6180d585400411001d0031090058035481d108000e2501c64084011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 451134136 1250 451132886 451132943
    0x30509120a0f1403160f03060609060c020102070e0709050a1e0504020c1005040b1f140d1b06021b180a110c0316060e030307090e0a060801090f 63
    0x42801860300d1801502030394a9a1600902020b00a0f91100c0301c50a402880007184600241c1d161040a05c06420300601601c560400705400c0600d020400c0c40304036007141504054a11500340190710700385520040740f900b001904810071641e600d09c140b098240c0c004081c0d000751031044a01040e410349411139080c41100d02c90905220740c2d00c00808000d0342c1420742c010007411b00040180d642003c100098281070303030010355003142c40034a000200410513030381a480700c0400e040c510111811600d4012038070310060321880103511503884402e01100300110741181c804489038450605200580c0c910010703440c0c0011142d0640b1132206140651258688000c902c40c0c2d0b038807600b00c60001a251900c04000404030700c64510780c1d1100400920b464100c041024019a82d080c1c480440d00601919001040d0394103440000b41c2c641c4180280140260000800030580711080841c02c5182d440c0c1a0850280500c0d61110405501e042d02403414007001e00c441c500424010407210b40d210746062000003400084 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 451135386 1250 451134136 451134163
    0x391b07051906050a0e0d1b120c030b0702011b0503060a06050405090a0e010e01020414190302060d0c0212040306020a1e0504170717030408010509060f0106180e0109020406030509 78
    0x201c682840341c58025406007024540c140381036071100c14000081103559180c8602a1001542c0141d20360341085111a410040d1064036101407070f80750315948a07902800a400000c006184000c0007500c0c9034400d5100703508008490450313079064030b00030380090116802550b49034005c52481078046943c0d4000c400b01c40441c0d03400780200c84143d40351003120000b0b00e003040800d0025521000f1100682c40b0034005000500b100444800a030580c280400040d420301100c56a50481c5940d030030805a910b0100351000f100b803036200403c92014a440c202d0a012090380c460900080115021060203031940c01f4008458039511283e1413088481c5101c0382c0b0b80005052400007030000c000030300c0840c04405050a0004280d02211002130b1610f81040d101440010000015070020070100202c000074050f00d504144c202020340320a0802400301907240d2014000c03041402640702e0440003452441c0b051030000c2514004c2d504035540c4a540a0b80603502238407920001904200c08664002404688803502d03140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 451136636 1250 451135386 451135429
    0xe0304051818010c0f2607080a06030501020708030609060a0515281809051003021011060f06040c050903030307180b0d06031a391b0705 60
    0x100701c156988070041c0105500104200840e409889040c00d0044032100c00c02c0351502c0d00800e80340030b0001e01c000b1511b0030500007184004841100c0c010208400e94000720700303141400080d43c981c00e1410180280f40d00040841d0310000b4801e041c800d00c080618000d11040b242a10380b078507180700300030010109000d42503204c2116501415103880c00c000800d0741c0c20030140341c05104160380584040e00001090000c000c5480c02003176a45198040400300007401480b0410409400d0054a0b0440d242d4103000003401403e4040003580c00600034030601c01007200c084119145403902580122480c1016101c0e135000303034108000d40f014030340a1015100c3d2104058000d50841d9200c450071596204c46160350450150146800306602d0070001c01020941900075003ca030491442c41c2114a417040115001d0345000d22009020101108611800071007900010203941210940c500c2d01c00f035201c160b20002c8501000a203805c5001c4181e0744016275141400995442c607a5503c10b1160940103e0700139840d001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 451137886 1250 451136636 451136659
    0x305101a0d0e0d0801060509030c040905070e0c1801030c270312020109020306061903150504260a140d1a0a08030307020d08040c03020907020f1002090105090603041703070c060e030405 81
    0x344964058223018200404079034180340940049011100080000e23102600301400900c02d602a00303a2003074000c0c9010100d18a0240220780142404445a00c02c904241c0c545030703880b4540c1c1c440c111095611420740c0150821507101e0301c0550a20801d40320403a1213460760f01200b10311900612590740c5450b0081d001d00026511541040340b00c0c0c40c40d0902c0107540e4007074400800810000203060344a01d00907500065142061704200c0c07200440304420300c0382c2034035451990050300014000c1d160b1001c2d10703003409403041100c0e020558440c041c500c81414690b1900c1d420076954841c58000e581c88003c29500180c016403600c05654483c40112203803805070380708811805007288104551580640691541401151a50300090030310b0020781c5d0b58030042c0e001d0ba501e01012007003444000a807190841c01180303081043c0c40040d0071400f40340c41c254800d1002200040a000014140c8081903a080081507a46d10b8940d03005080554500342c2500e00600d4210040c030000030000441e02500c100612404020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 451139136 1250 451137886 451137899
    0xe01150b132d051c03051b0115030605010f0b0403140319030209010806010207030201080a1a030a0501060f09090213050901020c070f060f080114010305101a0d0e0d0801 74
    0x264032803924080c41100003400020b03415010110307914402c204401c40366900300324400b46240c1e00100c1d082a40b15000c0c1c102d480d80350000c1c846030a004180d160505603124201c058204031f40110f01c0000503925400c4c0748ca103a86003010b00e00d0701c40076a845807030100031690303ea011000450b052800f900c501c445081200b80081440f102c00300d2590309240c001c0740e20700b10402e0315004100300301e08040008681c020035040842d68001d9501c47e4070500070301c02042e54605c1d580001300b20550141801e0b46a44c1c0d03400400c000341c44009000c00c01e501015040326020405864001d00a189500c24080001d560003c0400e1000c0780d406007070719041c2c00402c0004100b11502c40f40e402084003501a206e259800c100b070301d4012006028202c01400c0c01d29103115030f14034240c00505000f0b08203c1003820008a04014001c2c00031003091343c0d505003000c0c40e000405695409030300d0140e28041c0c1245151000308000844000c840380f00404105142c40b0080c0032900307003010301698500540c0c122a010500420050103203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 451140386 1250 451139136 451139159
    0x30601091107151a010302090117090c0a0f03030801080d0e060d0204120b0103060b0d05190804030206280c03080a0903051b0105041106070b1303031407050d0e0115 72
    0x2000c50700310354542100340c0d803000301c0340c07078850a2605111348520030f001c4003000d40c985031181c4c074030b0a08083d0301e08594030700000c290859140b07012090088040118500710400c02c0704440c2c40c40041e00140c4481d8135040b043c01020070a2000320001100c62001080080000c907581d510214151510307107140e00c808040002030b800c000c11003003a80341e081c1b0002814403500502040581c0c011607400d100c1c0d5046040200503581881a124000c02c640810340c80050710010b4510400b41101c5000b526144440c94000741605c144c0d40042d42c00ac40200d00900f400107441080399414a0140c2120401c41c0d070441c080c0c500038086a400381c08900c07801e00240b4070001c190803024400d40b00c1d2070918600702b841e513102c0024103414120030946a6450701044100552113824100156081b94844e05180e62030341c980a03d1400201244000e007042c1044004140c003a0b00040605100d1500c030024a240038403005020f0781060f00c11300c0c402801e1280b10158004103208184071500010002014281020300042d83c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 451141636 1250 451140386 451140401
    0x21203090c0a090c0806060301050a0911090d030207090b0a030f082208010e0c040b03060112030201090206030403080609100b0f130e0114090f0c12090f0a03022a03060109 75
    0xc65008a4140c01866542e09803080080d10803884005000c5100500c02000303190010b2032680a1581040103122503664204a0310484d00d24180104010346400140306460141d200c500d80c0107081d842c16041090b80200e00107094800301c07242040070280d100c0030000c1560070780c40081c00c140c00020824000c208110010015078042c00300410446020b610351141c1054640d1006486075564141d0b254000e01c1407200b8544844115801d02401c8410000241c0703d10061103080b50310f9104146d00340405000390808090241c00a05aa0f04ea1405060140c03000700308a41c00d0b48501c2d1190000b48600c58407158a00c00d5919008226003400c2480030400015408210342007008001c0c2e0000089500559210700e02078200c1d0324034030043c800c503030f410300440300c9002e00f107440101c0201c420080803982c1e02050303490f0341510010a62558031003110040c10458046800e00443c0a66100681803540001d010741407940700020040e00d09614551081843e801001145d9043e000080100060784a5400c42172 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 451142886 1250 451141636 451141651
    0x90f0201050904090c03060c0905010207050604061b0f05070f06020105040515102408181009080405040e0d020c2d21060601090b040311150409020d05040b0a0c021203 73
    0x90031307541e507442e21a80c0920381c6d4801c0b54155111800300c03e1341c0344d012500700020030081c0004c0c00121f04000c0040c0d004c0c01140908030800401002600b152104001302e0101e15400c103000d801d01e1036550400c2500d078101801081c030080c0f01c07000001a4244140725817442190454081c0c030030881000c0d103010354050080c18008403030518000116400c03052040340c06904004451742503030450085400780003902c0c024803402e2611030082600481400126000080c100c208070001004c0f4600e15000d032840c09181c02c0300d604030f8a00340b1076134a400000034041200c07070616001c40740751024a0b800c100e1022101c0c202c07412443c0f0080c00000d1182a04040036580300c01c01031150400215a016080c21001908002007090b4416418042e803960400c10300b00c00f608698418514050850301e4010a91042641450081c0d204d02c42e13800c41c549442082d94084c042a440940d5070341c0b070301c03d114809050166000da1300350741400c001c1802d1405900c03c0344000c1d404d580161840313006580d1000000d0f0001881c05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 451144136 1250 451142886 451142891
    0x40f0309090f02030a060b09010909020a1209030f0e123c150a020a0f12090204110406081311100302070204060b0340060b03060a020c10090f0201050904 67
    0x116040307000303005092598101003001601c070f1822a5004c000d42e00070368800034560408001e0355100e41d900410503802d5a014100146c1c0d0340c0007052044509410784854003029602e411004030030940d01c802848801031081d51503a181011201c00c0190350079521140381210391006442c2d086502c0307241803442c014501c10703c5030101d1525519161841c2c95103000c481e6155000b08140030251607822521603000f440d40c0c070045050106040c80541005a130749000c0051140000d0011000c481941000c2a1154040d005101090043d6011210350f003140c0030b140c010880c400c6c005081042d000c1c034900c0d89160861a0055520041001d00401c403509109550405408000100242c0c40358082c0d40000c0c07404803901d540e6440c14492071012084041072100f0000328107802007042408082046034151800d40000064107030300d02d49080140242200a9018001c00c810810842240d45c007421404503580155040c2c40c40c3e100442048031000d007401042c8480341158000554803840140c010008060f000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 451145386 1250 451144136 451144139
    0x200c06180103060b0f12070503040c090911030a05030301050324060f1f0801060e040e0606010809012408151902130b0711271308090d0821010608040f0309 68
    0x2841240d00c0080380131510000082c4071321b0b401d648446070b9540b11030146400d5045040c42d6a58015200301441071900c0d154503460840c00f03001a00750064804140102141c8258070320b4a1701350b8807078000b4400c20f40b1901641101d5a0025115075120180402581d40d007001c55460308100044111340003115900910140c9400042c0c650301800c40d070f00d125141d190200d042d0315000000b4400906180c50a00440c10180404c02151001075807940100090a148040d643c4201e017850042a00c5581c01110b010315a0051081307840125441045d5040c40054481c50346144e0740000034580c003070325940c030b400107108035100f80c480036603001c0e1001c100d40150f10504550384400c8000b9640008000750745407500d5110b0382000b458000304803003c414606201e007004460051102d841c600e0005d0111881e01c212103965410014900c0845212110090800c5d2803c8003a0401041d6030308940030f603090102c201011166a060b48118541c100e0741c80b41c1e40c99a0903580c0e070751200c0380d041070385604409104041c0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 451146636 1250 451145386 451145399
    0x50303191d010902040b0a0b16051c03140604021e0a170106030c09050f03030d0e07030210080103060e070b0403020d06060b0a11120307142206200c0618010306 70
    0x801d812201c848000319a0341d0040c010042100c6148900c03e100365981041005440300f80c10a4035401c0341000b0912100e140745040280c18007007107021185c1040f0722091005140ca405500c451041d42800b2080c40c0309035a88414441207100c1e2a0440240302c1140000904c143c030040c00030700c829001c0d0300d08440ca11107000f080410100080c2c00c0000800c1e100c001d4843c032103501c004c0e050003c0c401100c0800400f2000400b0940f41e00c118010185443d44079a43c8000c800d1040201c10000c50b07000c0c11083da2110107240090504030280402c4074400d0401210039111304c00040c508099132141074000303203082d1543d82000031200145500700c60603a11440000b82c0b04000e00e002e070540c01c0c0230307445d8100700c02c50780407805040c01c8070000c140ca40080c0520034001c40070f6004c038555008012944129035200d0900c480f41004041c032a500000204505101046540d0320602904581c0c0c5801520b0040c4d060041d9801d403074603140c1040741d402c00307010310040345103240a20038440c0c00401814000340d002d490742c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 451147886 1250 451146636 451146671
    0xd0f11060304110907020a080405010c03030b0607111306031e2909070f0e01060305090a171306030b0d0303110f03151002060f0112080405061b010b0d05030319 70
    0x40d0140d407015a00f02c1c4501490130303d00c0055900102d0f510242c0b0181c3c0540c3c0d504031907409140500340c100402c04240e4001c150103980032600c1040003c0190792100d0b51480c01c90701124105c2c0c1c0e0240a0695041c4078010403002e40250710503241c0c07121246081403480d40c4414140c00303a1000503101586907103c41c084203040c1141d1030103007490700d01c0c080c0d07160300c0c01810036460448182d00c40e8078541222013082000b40044544c0a056031040c2c500403490f030b01c03624442403400840d040c000d05000c41d0180680c0d040b007044e40090010600403200606100d6841109030125001c4086107500007042e594600c0000344284d0141e48041c60000c94682042c0060394451819001114401d06071000c1c142c0410007440c0980c05200c0c1c50740544028902c030300d025091682c00f06410710031200ca44a001410504000003442901c01924001d043d142d103c001c140c88009000c3e001d04121100b65182017040440382c00c044041d00c40c801e4002004610f5a00d403626500b440140210071040010756a01c2944581c146c4030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 451149136 1250 451147886 451147891
    0x30510020f07060f1a18061e1507031211030f0c19020a02030610060207120215070308180705010c140a08030f07021504030c08160b0a27020d0f110603 66
    0x90000203003040030141c00603100c0216040c401c0c4039080e030030319035801161a45a800c0c0e00c40c7c0c1c01d0751150300e80d5100c0e04a1600070080303403c1446e4041f030405a44020098200c0142402034082e50303c0196001100808c02d080700c85070411002e206030b0810025180c0e485000318203030002c08401c03102e450504041e03100140a50f40780380940041c0c10a81c03840c010761404004454000c0c002c1d009920a551030104045c2d40c40105114400c0301d0b03180d500b105001e40d075488003400340324085200200e030398048070f10303005000813003c8964201040d1580c080d034862410001e0010306503a010384441c1480d04e002c0c0c0b208802d41880c0c08040760305118003580440001c40d408041c5004881c07800004226060956000e41841035001e18540300240c1c00d020130000c40d80c085500c444554000811b95580d010b10a410000000d0149004e020f44d0303043c1d8240500002c02e80c0c4400c0b07121300541400d103001c41d90301d0520307190101d20010280d0300018038002c810200d000ad500580c1c40034418030400f00410307030217400305072581c004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 451150386 1250 451149136 451149161
    0xa05100c0b0705070b060a21030201060b0d06080f0111030c0c010209060a050a09090c021f0219021006060203070809041509150e091c110102041a070615030510020f0706 74
    0x1c1810b1007004004000142c00210446a87c04200d04100500100002c10000098881074400f80340050500030b61000e070181c80c9821110b40c1d01c0e04801ba05101800c030500c2505002c0c840d181003481c103070300b041c81180107150304801400d1858031184003200d840c1d0020f03042e100f0555400c100702c55640d9a034030001c0c01c060356203458494403040200c03006403005009501c800b0b03583d803d020481d4001980840c3d00e42c20303a4003c80d08901c0303941d203481c454402401030041c0c01d815815101003001820380c00081e808092600e228043c03081c0c81e1101e004903140d0181030300c02403420f0424415840685095044182c498600c00d85940750160b842d0b6000f0142c800d4058543d0038440d090406120108000d20070503032214181c0300804131050401c1010600359a84c0414008000100c205050ba584080d01100c0040054622452a40f5080320420f4004d52100e101125010f1a28440040c100c07004008582103a0b00b04001e0148486100b054a0203980182507050750860100880740006100c0d1003022604800f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 451151636 1250 451150386 451150397
    0x40203040510140408030a02070602041230021b04090f0b0a06140105090f1207030b1e0603100e010603020607050318030c0303180d0f120f0306050a05100c0b07 70
    0x359641c129003110303d01e01907440115002000c00c070204150004480d04120344003801a5220101d0412800900481e0041141c0e10300841030700c0d040c464491440041c0d91940320071917900958226850f0300d40d80c503501c0a480540c211300c01800210311501d603c1600040080e20104404146546000008505a10071140e5810744c07018000e03401404e00c10b0030094078506a004c0159040840064610f003d0368088601c1003c40700c140c2e0003541c403030b100120054000d1504030b4002a03142e103010040303280111840e11204030f8508020201e001d102d1700c03160080300082c0180171448840d65802018020b50aa003502941d280c8100000507200c51006060309401440656107440c404041c0c90401c82c64042c60300d10951040c400c0003c90799000c030840f052000101c564041030000c03000816007051400030301034646c3e1a40403150b001d104400b002c042c540c1100c0d60310713003241071205542941104d8041c024103030411a40a4107001e0390400c1381088001d0355003414100b14008956844010b400340488102d0300050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 451152886 1250 451151636 451151653
    0xf010312050304020a0509040611031302090f06010801030f0813030303020a080708070e06090a03020310091e05030a0e060915090a0504110a0e120102030406050103030f03140c0906090402030405 85
    0x208842400200d821500d069031441c20b040e000503417041524007034a031180b4030440c003140801586034001140c400f03c6240f81c540300e2424403030b01c0051a04090090703005420000c00030b074121300d20740e945500c10541611800307110390039901ca035a400340b032903001180c420000f002283d101c0d211400e81500118031070360340581e441c800071034010020700010b00040240304114040c0444650407803c4008480000d03a11030791100401070015080034075580c00650940190046000404510b4010020641c010049500a8500303210380068140001c44090b08681007030284074403146c13103940b02c151076901c0100b0441c1020345510000b00c5186914083c101643e00014080c803107800d045c5070f0080101422281000055030780f0101e13030704074482c0d0400e00d0708104402603100650307550a80300600400852000f1500c03803034249011741c0100803c2c007050300481c152100d0150310a00c28011007000341c0050403442c8a5131520211185171340c10000070154040d00611182c030460320f661000c0c51240c0e01510040001c2c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 451154136 1250 451152886 451152893
    0x50304020d1707062702060903010603150f1103011d130b10030b150d0204230127180311030c0f21090307140109090612031101200c070b030f0103 64
    0x480b171510300080d808440d0380c04011945020741d5501441a010b80350303569034181c1040000d00400480e0802000c481303440380010840300950b48401d81038101e1100401411281c0c10501a1600003403281c40791a82d0b00c007190401c01104061202c3d0011200780c211000041d66a640d03002c0a10101d4400c07032402c0a668080050160b2590604d0300080042c0e85030940d4011200800c0c60b100c0c0485000e40600e40b500004290941c20503800d1034980c0410075031441650f110040039000004401444d03529054070040c08140320014422140c010030244250200407052f982d0030344043c0d02565481c1520301040c0702260502400780043d506610429010340303508031501ea03032128115202c55414016903c1840a0003258134000b605c01e0075107044c1d652406900d0f00c0f110049400d400a41c00600b0014100000018040c080401b0f802484c1d00c070341c4400c09105581c400a5080300d1a0180e00c1000c2c01d965070058074801c02040080c1b80302c40d9020145c9400580364440c0000c10303403047d07072540802840702d001002030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 451155386 1250 451154136 451154141
    0x902090a03140c09010501210504081e07062706230903041703070503030106080907030f030c0b0a09050c040c11331006030f0e0d08060f0a03080a050304020d170706 72
    0x580008d003405a201208030310303403203601041c0c8030716400310780c2c0c3e40e10204040c025107070255170002c20700c0c09183ca00040c0001c02d461241d00700c03c00c100e40d030320708100704441c010414404200c056514a90600d801070401c2e21180080c2c0743e15100030002428860700c0b03880c0703220740032a9140b0400e05007004603603031441d0291001110007401201b10b40c54009222840000d8001300803203045440d9403405009517220301c2003660502c800f0f0340c4000c001880c00d03000c8404041d00544004a224000c500004c01a9a800c807107006907a0240401080307504010482c690354501503101c00c909104501c1d00c80007150b030b40e0380054a407035012031080400791b555481a000b10720700e40079055805031800005c2450303402c0080b80d0306941c18503402801c0c1407680703842c001d815240e841c1d405600244100011990160520000030b030501e0010f460f824044c2003403050921031400c0003000c45044903408205a846e0114100d1b086401e80c0002e481281c2c000710303070f0080001141c2607100100c84001d564120302c2e45d984031880e08a08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 451156636 1250 451155386 451155389
    0x50411031005221407080607171303080c0f0301120605090d0c032016060201061e090b190803090405061008070806041b02010203010306150f0902090a03140c0901 71
    0x12a81002d08010b0803800261495076550301407400d243c0c49916514001a0b0b14505040b604050b03c68130f1000512074100180c10341c0a40740c40d8581d103240c0340f010707201034903201c1c07003100c0c491307900c000705140103001a1060140c50740c80400c102c1d00c2c505120115001c2c40050b03000380c2c81030003c00800340c0500700b400514420544c00c2040000204510042c007400941088c070200d07005824412190340d20124818902c100c945010004000d03251340c01c010b100b00361000001c0d401810015031070b01f1004101ea6800d001c1030760403024002c07109841945070001140181c004090140d8002c2d000f40700107001c00c8141405034000c0d081c910051078840c40060b0500c021500c0c0100228810101001403200241d0010309207034004d052481d0110040da1004040382c050b205c07104420081120394000501d040341d0650155041c1c0380318034000e000f01d420145c0394803001c1d406405034141d00c806502c0c0802110203154010005114003511a0f07030368680c1d82c3c82d201c41984d0845e00c2d0002d00d8001d0a4800c400303103090300f040c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 451157886 1250 451156636 451156663
    0x6070c050f01022d0102040512030d051f090b060910020601030506060901030f06090f0b180c061206090910050a020406030e01060803180109230901090b0306130201050d05041103 78
    0x1480d04c0c49a000076003400304100300400c010000071441035000800f90110350141401400802c429052034150701d0744c980c0080050034841d07141101103104410041590740c40c103021307200da0300102030904c00c8150003002c42004081c0d01c51803c03c4400f005072a1a01045402521500075107100d41c03440c02c04504056008010f140700b0103d410060000a61139036541c070003140c005000081158041c980380c4540481d00c40c01501296030102000b207803c10030344600034450405000d42c0c0340e00b0071000138401140a210182089080302100052681c01c20302c070416803089228044030006aa14000e0710111802541d40c2000c41d0b400085c03d101c9076425000f1400d800f0513110003045220f182c02803c940703d001d02c500000042102c10707400d6155038401c0340c1080c06042210502d0420410025801c411119000c190030301030f0300140000140001036104a0707410342e0010300a8511a511045000700344080718100b203043c0002031000007010035152180303078400d502ca80038400250003900101889e182d403070781c0c002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 451159136 1250 451157886 451157893
    0x905100b09010507030813061b110c0915060f071a010b1306081503030c0c01080c040f0b07140303070216050a0f05041a120102181008131106070c050f0102 68
    0x105050390f8801c007281c8120f5018542100540c90300d056071940b102c01540080c08190030030368280c0c47c4d458400003000c0c0f00c100c6507d80d0505030400c0d0040603155140e48440c40c0d80518400c0c00034002c40c081041c8916031351401040d041c0b031f050b20b80311850040c3d0045041900e844000701c0443c24008044400140501981c0d0103040c101702001c114040d076101d0500503401080701c0807000c58044200b800860080110007001c0c3e94440d645c0b154a1607840d02109481400100d03a440400d80e1800c80004842c29a01c04800c2c1018a5040c105190000e500c00301e0102c0d40c45c0403600409501c030748148041c50148259501406000f1101c0d800d800c1c5c01510341d0807081c860b03d460101003011442441d030b04000c941c0c00341e40103d030403240d858030162008500740c64680c100401c2200f280d180c15041d4010045014a0700c107070143c80e0074640900c00d003035914007107200208488034041403050950501826680c2d200c0d003044001c001900d404502e954001d040d0480e840e0303092007410b2015280800410800907400e1006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 451160386 1250 451159136 451159147
    0x51801060f0503090a140f032212050d050307140403060c1808071a0f0708070606091503020613050307140306010806150d110d0b04060b030a081818010905100b 70
    0x548407a0b281c0d00003000c1800c81c4c3e2217070440003020301907440300781f4018003904d0b2a003060a5018150310b158082d07111001c109682c0100e203049030001940030740313504280140600c4890100a03200c0c0c2c2c2c405010002444801000c41240111540082c40030714400c080c04620003c0d0100d0207003800c0034001288100445007007007440744000002d51b0b04104d03203c0b01c210102104108408050900c00c000c1c410691150000e040c1d024001b201008001d02403042804010b110358460050040b00c5125a0080c40481c0b202e104001500d09600541081c02007040c422907000c3d92500040d03e03080243d40300c031000b11380140310040a46009d00c280c50040c443e040c05003c0b40e00d8003907400c01380c01d107442030458441c0c025a0034140912805480c3c04460010203001c601d90402c0d1800d241d58102c0040b0350480ba1503041c44d0303c00200d410081840181213611000c0f00d4145001f2004100e2401800141c454202a56111541c0040c003103013a51030090001040000b56420320191491a4410030f401126081c10100031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 451161636 1250 451160386 451160401
    0x80a060501051504232d0919180f21090602100b0f040609050714030603071502030f04091b020f0606220f090b0f040b010612020c01021b010f0b150a09051801060f0503 73
    0x24916594581d000009c0d0103954211010341d0710020078809400381209203200000c110320a0808400800c40c00b4126200c030855150407144e20780540500c100503000f08406062004440d080310000c2e00c001403582d03103000f2014020404403282540715169040d200d209200055030020030045840c20300341e81080c80c500d81940130039035030f0326540704140c100354400300302c2000e091007072007aa1036003109811403da889a0781c2d00940c2c080d2038003e9905110b20104e60075881201e00006044120000300c0015201d81d0399040b0802001c0c006501c41c0c040700c0f5460040c0103007070b80b14901c2160403142070000005504040750030490002100140400c0c84242d040b000e000102c2c810080d854110740540c904260950099400b20b4082c1c00380425400683d80041421000403014501211b14601c1e820000c00038004c4140d4a041074600740103031a03410071141200705d0820320303140000709988443c6041103a4615a204085100c040d48030704220f00c0d600320704005000250f4009240f0183c01058078146065003170112 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 451162886 1250 451161636 451161661
    0x5070e06070218092506081e070f02120a051b010b0d0b0709030f11030d03110d0f060b030c04180b010f050d06030c080a060501051504232d09 62
    0x2c3ca4042500c2d090780000d8503107101005056a0000b08046842008803014003040c03205605e0700a01c000f04400000040c0c07100800880004544c81c0b81d40f611203113807104501510100340041c0c860085002d2800e50594000b0044000c194500711550307940e9491500d01c3c14010000c00d901481902c5034140340e85003103640c0c0c517189619402e44d08107c8940840d2594002925a10300e254002040a802c0307440400c140714400d0145482104c05030251001c03802c110404070b0456076107000880103508140049000304400d80d101740a0082d2408000607015200d0231034100e1a007017150200003030000050309100411452403040440c4c9481d0b03074148080001e070000a049401c0c0020004100300022900705040136030340e0008002590001d404219903030321000000d4440d0800c1d5029980c80341010000030b91420b1038a4112069005244242d08203820000d85519656515181c0d00e06030540c04030581c00342c0e5452010758040c40019a10305842c0329422510405910070080c0284540c0c2c16000300070700c040307114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 451164136 1250 451162886 451162909
    0x9030a050a14130f050f0409030f0e060d110703020f01021629070203090418020a05061c051515072a091409010605030703031205180d0305070e060702 66
    0x18180806007440070400b41100e80240001244480010030000405480e0b011840341500c0342502c1018481c03145038248400d0310811000180051607104000b64030034070130701140c4000c42d0000c19192501d11950b9055080c1e03900c0d81042881c6000c00103c8400305034042080441038040403000754200041850030000244079020080c2011141a0702c084461580e00082c100c070925101281000b42401e4000950f02d0f002403101c640681e00d85a04190001b81e90751401c680c85078001e145000007030400050181e26042006401c14280d20340c0214030044203039014080c407071040304200b40e1500400308104424110801380088600404000d5000030a00c1e01d20300c0070030002c000d802c04031103680b980c00c200082d41c8103900c402d4140d0300d004d500d104c28410340303003c107400b843c8400024001d00b034880040648890083c07000401140400c00400503024031600101d5004000d490441e002d4030316490313568101030380d00b60990000b075a03400030400b10315005802582140b1090758010304181d1a03501040022090b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 451165386 1250 451164136 451164157
    0x90501062d030b0109020306010e090916080307020619050723070e070c12110318040b0406150e0118260106052202041e090e06240f190e09030a05 64
    0x107009074001e0810100414024000c1c01d000e24040d003a1941b10490003501c06c00011200f00001900307000007084d0c51249400602084c50803061a04400c07070000c080080c44107000e0140840360219681c0a0440850341c1d1405125101001c0c101e0b4050600c2a0390b00441440a48142400100d40c1c3c8240d054800651103000e0b6081102c0c940025148a50079403406a03441c84001180ea0b4802082c203620081034074160ba06001d240314007401c01043d282c1c2c0340200c07003408c1450310601c51568811402b04400b102e040c1414841c140340042c3d048547c03119a04000a410701c11202400003e000440803200c00c1501e2008010716400c003000103404c905d0604400461480341e41603804c203000b99070f04680082c4242c01a1841c42072105203001c2007450700c0d00c50000740d0b61910401c21542d81021521512507c0c0002407181c0d51600b81c03015500c07101c50401000d4000340214032180d840e8860260361b2207080043c1c600b10075070343e00c0c10b95082440e420040440301541c001344a0b02486641080581d00120308 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 451166636 1250 451165386 451165391
    0x7080c0d0f030e19080714450a1a01030902090601111204080c191a0304080706050a051b0f040312050f0a261003080904090501062d030b0109 62
    0x41c940029402c00d104070f104d0840e05010356000901c0000c00142c1c10308a034069841d81c1104d51003001040500305800250b13142600c1d0810401c4c480840b2190980040002e8020701c581680c0d003181e0210700080120341481101c0d95840905103050080320310030903070100c01d1a040c40421016404500c580c0b0024150505001456900000000d0240702e440b80445003100c0061f2100d0303840262554500011000900440700d1001e016032440030101000140e031980d5a10700d04c5018240000002944010f00c1529110402e004480c00a08140610b6010f450200808a43d90424000c1d050100d02d0a403403061082100300950040051501c0558044a400034071030156108100416103041c46580018050f0031030000d12803d4840e0000f0800c00d0380c071031600c800e203040c107640102824880c106594054040c000078104000183d081c00c010710040e400640081041d00307480d0b40f11f500b500c455070007064185204044078040c2690b0707400215248804209034041e064a0b503168250034107418014030b220141c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 451167886 1250 451166636 451166657
    0x1c210902032a0405040804030b010b0a050412140a0b01090522110406030b010909030e060a120506031f0b090c070b0a0c0e12030a02061605160c051207080c0d0f03 71
    0x82e0710302c0a10340c0341006082400507260038030b0500143c2d80540021a100e951400c00420600e0003d41070715560006911003915140c00c04824803100141c04400f10b401d183c8048010851140c02d000c8448420306c502e1035a400365060040c458143c0b0390007060000744d50485c46a91441c2c280205010760404e0304082c3c894025507030400450050465600060036091868000140307844103544601c040c14002e0341c1e8807441252040400003c5e01c90341c002680003070080c41c268000c0d461558013032504400018101ea0302c56005840b00740c0b46008200038058011b903100315101c1d10b4100500c0b0198004c10b00c410681ca4100345903a82194100c0c0074000643d443c0c0d44444c417849242c001d00e250148542c00a100c0c0081e801011516980c0303503c510a02001405502c2c00b04003a02540e0800c650042c10303984400303040282c0e4000301c024180c610081519610343c1450005041d8582c2d038800b40c50b00303110401810546042ca900c407490841e82080300f6014584041ca0351000c146e12440b40541541d03d450b1012491 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 451169136 1250 451167886 451167943
    0xa05010810120f0303140c0f180405070c0516050612040501140c04140a05130f06090e06100e040506071202090301060f06021e0d0e031c21090203 64
    0x80744942001142c038100c02e51103401d210f8407840042c03225100360707800d2010b0b21980760040c408403010b176000d114529081c0440490040002d01806010852484111030f10f07215000103801e8440a5850358003207502290848244603080c00b072000244111924040c00a00e0130300400c0303443c0702d504040000c401e04c0d580880c080010030b4100b540e00302c81d00959200d2904100049002c0d5510620032208194a980c214210341d0410354210021a0f40c01070801d00301d003001404010113003174200e428000f803990b107180101d60110b640c80703a00c00050b80b00d001413002c1d01d00406c1503694481c5980240d0600c09a400410000810001d21143c1c800703114a01001c0c100003215a520290040d8a50650b06500f03024002c40ca440710054108201c48840e42100d40e824081020b21030300440141d6250b00175002500c1c6800b0f00350040e0700e503109500026003145e24182c0207180cac90381e0400301189070000240700790240c1090080c14045120000300703080400c0100c4441d43d070003c1e54907079221140001c1441c0010410400303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 451170386 1250 451169136 451169161
    0x6010f0306020c0a170316081b03060d020306092518020f0904050a090c150203030426070803060a090c0e150903010e07090c030203090d050d02041502010c030e03090a050108 76
    0xc40e4031131041d5880c405500401e202c10f070412900000d01f20914000108010f10400c1d06901034035001c0006081500d92040c1c40d042c40e44001c01807178212144600701750058404000152284802d14054403002804401c96509110790721082e01c0b280c1c40300b03001405030f28003080c00c0c031030f882d10f00850040c1d464400c0c01d010030050190185659105285c502041086041f0380c01081009110320031102d2403507180e142480c0728003410307c10040181d0040c40008c00003119400200074490000044484024540c81880070369170100004441c49140031090084ca402e000c4036100c05400500000e0050010a09000f4610080d641c0c00d1845150b4150325420001407000884400100c00780003840b070000340341c40d10b0b55201c00d0352088440b120b20305000c0b41c800a00c24406d0b070b80140c104201500e20b03640e000c0803c9909400100b00e0b074410540c20003000502c10b034198084d10221010b900085590001c080020f82222110016446203402c00c0107010960381e00e0101c040107882c0c090030f155400d500d606898808 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 451171636 1250 451170386 451170403
    0x6161208090d1d040e0f010507090b0706020c0309030a0804090c02030f1206120714010e1c0f08130923070f0c0c08060705090910080d0305040503070512030a0e06010f0306020c 77
    0x4000d40385c440d54050605c80494103401d11400c10000307118a454003101110714000b684102883c0340011701422002920540041000c109500300b220b0800c81c0290001e418680c003808111415100080c0c01c01003400d16000351100460140082d41c1002100100002c2034482c0c4406024203400c40c4c2c0004402d651303416811044081f1000884072140e8448002d0000e40003103880c2c8a001c5003d10b0500700c9249042d00745107000844450100c0c0440c0e5195651202d00c100c542021035481000b8012100340c0c016561204006080d9040c0210f40e0a100d00342400044150305001d895005c0700500300f00010740c004040d90200803030b502d0101c1300d003180c038208140e500c0a607800010150052406011700940c2c02005821a0003003240c044140b070b1a0420454000260346c814030816421070300d91a070115009034440e69001d40600c06892400001d0360300c00d07080c0105241200c3c000d100c08014003c84c40154800d88076489070700c80080030f0550600a04c1d60814985200041c54140c0001c2c11480d500e81c203100402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 451172886 1250 451171636 451171639
    0x1303050901110a03111b060a0c150515040606020f0705090601051b0304210b0604090f05031c0b060c06150102070e0c041a03040809190506161208090d1d 67
    0x2203952005203001842c0c0c0000d02040f0741144208080040794070360302084c0c12141c07031b001081c8a01d01034142d1802e49101400200c10748041c9004036a00b0050207581c040c46102d0a807034841c030035919082c2000c000c100c1d0001c4d00180110f501642040742440e00c000303170b0441940c0c4122403100190b0fa600300104d5581c03180800c045c100c4084d01c4036030140c41c0e01c00405070041d40d00740000b000c43c1e2490039110001c0b800a00b00c0181a003440200072800600340b561090701c0007030145c0440245200c40e51901032941d8400401c0e07070602c00c0499480450100c0d18803648034204000c9600510301a40c03824000d0b9901e8020300300d42c0654001c510804a143c4c02048a10f0062814802d032082074544a03084039869000351041510014244030981420242d0b602140d100d01d612120080c00c00310342006101460008031001c5449250b0181e001c02c00e40d4a10000d04140c078811091400ca1000c5031400c0e081da11118502d41082c41801c0c401d010181402003131400003c1c490f031600100c803034141d007190a070f615030144885 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 451174136 1250 451172886 451172893
    0x7150509030c0102132102060a081005040606080f0c0423030f0726240a24090e010209030a080f070c032306060102061501030603120507021008130305090111 69
    0x10800078100c240c404200c81b040300e00101c502c0c03c0c801c000401e440d08500000e610a100b0003003540a14010070145410110900300039040c0b0781c40f80b01081c110b600680180300440d203103130700f008900341c0503441066001c2d442645e420f04203840c149102d000d540c00d001a810b11018824074040a6407000c004081243c070358801200c0032680d0310410b80c402c030304442100700e0a842540034035510307020000030184606403c0c0e07620040008040305071295024805819040001e40303d10900380e03004594201c1d01d04214010519005072440c0400300c03800c69210302aa141964010710800d550b079a00410b0901c0b240c0c0e0010300c095580d0589501e00e00c014410130070014201803500c0c0001c020f00000d0000a1040070400b2108201c0c56a0101c0f469a0707004100e07001c9005030704c44000510907401401d282c00035001c06040100701251070b5510111041c070201051070004101203100029031601c940e40e00d081188074200890507080c414a002425040408042c003070220000d41000701e03911071641c0140008140c400c0c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 451175386 1250 451174136 451174147
    0x130b04020d0f0518030705030405010e030f0105091c091203050a090e041227061107030c090902030d0810030204110904180b07090f150203040e1602070b07150509030c0102 75
    0x40d00c2c0180020355070644241c00054405220b504008100d0b4525070708680190b041c00c6c904001180c1404d100440190035000302c800c90410031400740146405621204054040800329908040000000c203040b41d00700f10340c00504119070340c4a070008020040c0c151030130540e40e0240000585c0c40490b41e50150b040d1034030600406c014420780700503400303028001ea074800c000700c21005070300000c0c0c0d008000382c1c07040d9015003401040494010032055810300d00140644000310b9581d15411000c01c8560b200d11906625580300c4002c61605002c02c505c503907824100b02c1c0450900d416040e24101c402e00009001e550f40d15a5003010075424016941210f40061042c0100642c8012142d42420720075000c50b0503e20090104407028017401c5c10f5019500c80f00c0100d8061032070050044e038081c540076000b0307042d8002008081005e0040c000344920813100d9403441c4c00c007a5503503000245000c2480e440075204090901500000884c821414508000481d40204a0781c950f00411802d6119031518030741150300c009074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 451176636 1250 451175386 451175411
    0x61903060525020f0c0f030613060b0d060501180510060e0a0f1d0603070819020a05031c1d0906010f030e1b0a050d0236010b07060f0b130b04020d 64
    0x806134001010741007500d658801c007901b0700030401d0359902c00300d0b41508190300049120710881c3c03140500e140251400320b00c2c443d44a011948104c2e0925007541d915403118010b001c0c1032652a0085024542a0310810007440c0492030f20062500701c0c0615020040d08001700300303080d034440003198041c0c049540785421241d1b48000c944107003140c0444c0c41c0901d4401b203000030054640070400a0031908404064800a8080d001030214900300c00c5040340d100061710300200e0b0b16203040040616022014000c40f2051b00c02003400b400249901c06c22094111101451a8a540f240030407960040001c0c20201c848203011036055018024065820100b4400c035104540c22021003120f004c8100020b032904588079817510203203c28800f00350006500000c00480c00c0300700000c43c02e00d50807040c108200a10181c0001440e909140e00203a0200c0d41380d00c0c012842c28113105e140e11403c211251074034030800680c00d40300c000c20511400c3c40c0900b048941e03584028285a101e580480304c44000001d810004a0030111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 451177886 1250 451176636 451176643
    0x170a120e040507031d0a110d0f1502070212010b0a03080a050d0e0601141e09040804030f0303021801020d0e04020c030417030c070503120f0d0f020d0c0806190306052502 74
    0x19400c0a5501001c0c0fa00001782c00803500381005a003010700d60f241d140b680700c24407007180e90a46c0100c802c58180301c112404128010001130307460306290b5001da03032030995004000784104c00a4200c1311607450232101490507501c040c065400c0380d6101070000c2d00ca0001c8001641c40d40240e6102000c0523042001221100c403010074994103031400c0c007452000d06580c107800d028441407420038541e00785200345081217483c507041040ca50711500c500c900b9031405850341d0314a4a13480001e10210046500171800105105401c002c40725440c0c420f100074069042a001e00070b11308810f101605015907030000c0c0b49141b400b020b108650191000e100151414481c40d00d8290384c2c0d90110b41100c034207014a074000f1032036190110341d681c0c080c3c500018140c1000d0041288410341d520200f0301d1044c1642d0b90170855031118450000d00307041c85005e0f500042d68030b035440003d44106002860030388942405018046507041440890080d03e401c5400050a82d85095264046070310400500140001d8890f10040c4140e002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 451179136 1250 451177886 451177901
    0x150518060a1d0f010504170f0301050d0609080d140a020712080c0c1f060803030f15060702040c120b060306060a0309050f07150f030213050603100f120c170a120e04050703 75
    0x242c5044607d511300d080c3c2e0f0710040c0101000c00d0082141040104698035100500020a41c0500e0740011003422940d520365242c0c1c01800001080c80c1c41d01419125014101a029442040c4000962420300e07640e6810001081b000040c1083c00200d8002c102c2182c0703094180e9142c01c0f061780c1101c500319540d445c10b0a5841c1402b41500c1150f050500100b0381c2440801983d020309122402c0c01016140c1c00002170804924401298101e01c003400b41c1c4015980d10301481000301c903691a030200c0c00801507003660540d840030340b01c81e008007420000e101d41c54890703100f224003030034070392a0024031101f8a180c550708041c01c58046914a101d800c40100b4012100403000203441202d80710000c0c0c0d203882c0e01d001d600703a000380000100700c0161200e08000364149200215807002400500c031303468a131501407500c0e40261f181c01c140700004c1804402820008054040009095004042118010f40300001940c1e1042004001c080000c80001010081d010f06003196081d00b004005224910300325000500800d0071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 451180386 1250 451179136 451179143
    0x18060834030302190f06020f0301030204140402010807030b0a08030706050718060203030c0c19060b0a1a0d1508060702010504060c17011502030c0a150518060a1d0f010504 75
    0x26114200560412080c40300c11264542c000d09a45001045580503c41c0240701c02c0e00d66141c00009140041c10520003041c80079002a00d26840e5410740c014402103a00c0b400116010000341000d100c00b503130700320b4101e9030312080c50b19002c2123002000c0d0100d1981074a43d8006881807001085540800100d0303048107114140b69070790740912120010100395642041d20809000d60410804920a0b0810344000c0512640c1d58044845469003c594804240064981590556a51a410010380c5014140d800091890f0403203900707080a0348400c82c0203031081e1004c1180d2943d41364113481a01c501c0c1a45c180c01019184241c402d140340c807a0019010b401c04450403900349203000b9060003c3d50044074500c0200c6440114070310309030b0a05040035a50340e00b8410000c103611007400401d210b040c0800c25a140d40d880b46400c410791754130a240c41e00594001401c1c408040074184007040020034000f8000d90300014004020541010584000e02c41d038440c1d241c40002030040c043d040d041a070301500510b000328170 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 451181636 1250 451180386 451180453
    0x130602040f290703200d0206040b0c04260111120406140705120603122b02030112030f090e0a05040201020d0318060e1203040b19060501050301180608 66
    0x1211401007010035584409040b089050180d0710101c1c1c800c0b8008080418035450800880e46112449440d021400c0c150000683c4100c0401c41001030404005400c01c50085079142454180000501308446150503401880c400c904503c100030825001142c84003504288241d8403281c0b000e40103800081143c2c151802800c05005109610104c440c5510841c40c0b59200c6051201c01422040c00da540600425454842d07441e03501031001d04030000301607049101500a10158002d8646c481d020304c800c040c4038046105100403c9180e0f2442c58800c04913605244c26584214500c8c4184d03841805504601e01c03580c0342d481007001d001404e501c5540128000d800319810b401404504a09540010079588660000900c4950008000c1d4214070460340640d0260b52032800751030351200a940040b1016500c2010b1030040c002030100c2d1314019150300d00110b00034001207041030000381461006101d02d84a40c0b261030441e010901d07042e840000681010010b070780b000c9038031240440b442c1c944c030001801d1064 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 451182886 1250 451181636 451181669
    0x8010303020d020714041a1e010e09010605031801020f030a0207151512060b0904050a140303091c030227030106091b050a1b03090f0602010c090e130602040f 69
    0x1400080c0510844900c508540090102d074802d110140207d482d0404483c00002200c202a40d0f03081c2901004c082000d80d01078440b003002d00010900c030f2030907084a00405401d0014081d80c1d41c442c0460b0360001444403407041444400c0301341c2e1300a200d480c440d1300240c2c1e40882409000302280e0024a2428016051121f03186105040c4c84101c400344100c00380c00714542e0350104009401c04a03482d8202d8003c0c04000703548035014000c1002c40104440c1101d258112040140400c00d111406c01010403505004505520300701c0030300307552060044030754490140180c101c0c0090724442d0f01214810780142c8509101c0344028405060300010840500d4030035401c00b10045101c130048e20032b542c0c00550014140c1c03002e50030b030101035515500002440081014503958140240c4030207007001420380c071030707901c511074145004054507820443d42c10070300842e4103104481281c40d074044010015180414030711391150329550012100a00840c00c000c04480c00410000b403060007410441080380c0d441d40c544099903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 451184136 1250 451182886 451182913
    0x309160e1006110d1808010204030c1d0108101d0a1a010506090102120a09050a080705090c0304020f122a0f01030b01090b0d090b0103061a0301150501121b0801030302 73
    0x5040d2000716203e81d0f1210301c10b0f504c2940301d04120070303103a40002100350343d403500c601145099030302a8205490070045d9510400c4000c0184407030300c1480c007079102000d40a50400141a03151400e000400302019100d0b00b080201406030982074a036418050100e482e00c00c0716151810648101c9000901d0401824000040606054040301c2441314140e02a03c9404404c04c1414025000003403a001040501302020400340c41d100d04c410b0140003554010454030b46020f08008040d00003e060300303900c0c6810b105100c0161140100d00314090000c4031031418822804190b60f00d040389200d180c0c03108a07401c0e08416180c00c03004c4184241c143c0c043d22041c0321400503800640684d920148507600248201c582082241c2100c0050321803464035407804945000d0a0300c070314048620a0300281c810a0b6184100032812900099014140310103034000e0141554641035001c0600141c8125414072415607081d0564481540c8800c0c00f14400a802890790050800700800f022001d01044025114029044114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 451185386 1250 451184136 451184147
    0x90315041a0a05101a120c04090b030d0c020d021807180503060106021e0f010207030509010e0a150e030a12230c1c0507021002010f0b0d020d02060309160e1006 70
    0x200f02c01003034000d1852600c80c0d40d03045c1031080d06814085980c21b0000e0038048540c0302a1600038616801d204c0d0f102c0d03060109a030204d5440b00b22240c840d0384442c1a152110b5041105e0940d1950100c4100074000c105001007040c07940c64404042c00210800208200141c01c0480003944040d869009440036480e8000c0c155506000c0c003d50025910080000f80d07160001d51a0108460b420019901140c04462b95542a604042e20403400b18001207101c15183d640301c2160b03080000103c503440c000764078141e000c080c02200c0442c00010805c10340e2601407a602d0800025501c540c3c0139944201600c0703009001010a05414080220040d40541c500010603400c0f003550000107600020700304041400000d6801d1034030140035041400024041c110144e5140d01c0346d0240305907250000f1551490341e0480c0b508590317407100c1052142613400b40d044050703161100c0166249a040d116170b07903a62030310f000741440e040e448003040480703210411021a9072080c2008450094980150403c0140c2d102c1c5d800361038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 451186636 1250 451185386 451185391
    0x191503050c0904090311030403031e030203061302030907170705010305010b07050c0d0227010611072106091e06050a021213150c03020711030105011a090315041a0a05 73
    0x5051814041d00080e480d25134095410140302c2c0c1004064010f800000d903040d504290b00030340c08502c00000d8144800c20442070728811002614045145103480c070700040d8070040000c441d1030a65030120000340d00350020003d4201030490075aa410034442c0a42000342c0c0c07400700c0d02503140000e00380000011005102e00541e8400c1d507201024080e0341007410140302442d01e03000c8007680d200d0b01044440c1ca00b102a2070f44408240b65009075100303a0340c109500603155540c80c8800988a074070010003000000c041c500040d414039407800e1004a2102d9034241702c0c01034816880c000e407a001c81c004a01448a624403043c20b0302e42c2c0708100030300c0160780b0003d002c4128011800072421040d24500041e8001114041e201c09140c4210880080344a4540883c81107030034102d41940460760002d0f2400a004000d5074401d4101401c40081c08a507051000c42c0c0000e4140030300314088001c011520980c80e44d03092224000070b011647c80c0001f54070b81800c2000f02c2c20511031102010100c034202054900515014451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 451187886 1250 451186636 451186651
    0x51e12061909020411070b09070b0a02032a01020a0c12090e010306020c0f0f070305060a0911130216030e040f0603020108061e040501060e01090602010605010c0213090219150305 78
    0x440030300703903641003030041c00044034200c1e0300030360301c4001c014082c504402605480d4000c006064030752615000c03c41c0740c01900d811030540c040c01440824500d60740041220030b0300c81440750044407140c4500107413007681c01000c066842940081280242658092240c0d4022402062002034414104038140e8420b9440d0140b00714000c4900010b1002c03c1c4150018410500c1c1d600864011140340e54001e1704000054091000d1a0003010f820414003008100f0345802c11900c071800c000764001550364036050804090010b000c1d00c40d06500c90001003159042d14420112040a81101c00880c5002002e0480300c0e800f0511a5150212080307040011f8810b0750b0071750b42d044c0c460007610b880702c0c0204100b404804c191030303501c0e020095803032025803201d000e03440c02011203483d0881140f441c0c40025200388800d13044a0110780c0b600d03200f08000d82e4442c041e003113450b4042e5141d0000504151104010744032503e4041d411421102a100345200391009400842d0385c8010241940f0800d140220300f594425280039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 451189136 1250 451187886 451187911
    0x506010e01061b02030a02120c18060d1e080a030b0103061502100b0604120f120c0f020d0609050313090b0301020a1710030c0b0d0c0c05030d0c09051e1206 68
    0xa082d103c4580d4070800741c074001000c840b00076201c0c0d4006003c180e441a40641c150b0460b03016890642041860390032400e0300407a5038903180c45d004000c030f202c031101064054442e1100c800701044030000c000c80088142c1d00142510350303541c10420040c01402c2e00c01142800a0f140000c0000c00140000c1e13003440c2c440354ae0780a045d4600079075100001810000350b46581c003502c1004000703904109190545e4100344034100300e00802c0201d0505010800b0682c40710814400ca525000001800d000030700740d4003550448507420001540e003006401021481d00c0140307030388070008141d080485070100c010704484086a05100101c0004245406c2c0d02640103000f000c0b0f000000d03440a49861883c0c8154001c8420070401c800c15500e84412604145c40d5110711503030302c0c001410f01010701640c00303501070700d1050303040c85101c0c00c4440d5112641d034400c0c11681704400d583c80d6019601103100d80c101800400b170007003440f040c118800783c000780a0030803066280c0c811104003051400140012840510420200202c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 451190386 1250 451189136 451189157
    0x10c030c0b0a0209060409060807050f06031801020d02031305100c120902041808070b0109091101050c010b0306010b0408010f06080a020118120b1501083c07020a0506010e0106 77
    0x207003402000050300c00b4034503c0d001d0111548540f40c03031014200820180f81c2c0130440f9445d16481c5801e10341a034011501481c00c00100441c1c0b074a5103000c40f9000b100c00c044401444440c501c68a009010b406201704402d0300010602150111400c0c0300c28410b0300070000d40d01d031456080115001c46040ca050600820300c59020344024080e1070f0b0002c1d9885002030004281c2c0c640d15026010850301000044540c28408501001440504040309014003100c400c1045501c0390340d01c03480749000404d050325040000004051110390f0081d006400c1d0010050100c2c0c2995840b0f410301c011603006402100c90640c40c0c1a001b8420341d00c14010a030803248280081c3c5010300c2140c004441164030855080804005900006222000b0511415000c0d0095115008074104000300c0c2030340807441c80007207040221010034000c40007070840c4600190841e41d400e20f00e400c0a20802100801455822070500e5000a002c206005401282d01100d0724441c0092303807440ea88031507146c1c6841400313004007000181705180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 451191636 1250 451190386 451190393
    0x12040b13031b11090723040b030103081c050c031f0f05012006010803090a12030906050306030109060212090706180302090c0f0a020715030603020904020f04140906070e010c030c 78
    0x202d200d0281c003e000c101221907903000412003010007914241c000850700c3c03c1c4281c04004000026052070308503000c4500e032610b800a00b030640d00043c00003504006000644083d40801c1101c0b100c4152045001030003107142c0101c1108040e04121080c001c80811420030050002031740c0c4d80b90040e620320b0358403650034034100401100e030f0706040040910b2030b150484110141c46820000f076802000c08100a680e608110014400e507203402d0b40c080c9000148060000000903000b1b4900d20581e41c203441e0050312981d880c0c0001e8054411403101600b06440058902040c40920100c1c0d40b254400788211800582d0b600d034203d5201d01a402d600c2ea40700600b410500c014544140311503003240702c00c07a10508017100907240c0c0c007040d880040204056403282d4410040d0442401c440700075824603080403c0942c0c80d40e00410300c2e20100900081c4200100317900c08800e070b80c031640100c091075a01280708910707217081c2464a6030781c101034031888081040310300e80504a40c401e0085512a0354103581c0c1e0312800b2041d64 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 451192886 1250 451191636 451191677
    0x521090d030b061c09140c1f1d0114040602151807090f0219050a09170a0f05010609050705130b091c030c02100201090605100b0702010c110612040b1303 67
    0x30340b4654840e49500c81c072401b152245140d15036400e20350014200700c0844000700491082005401c0d540c0c03564070050a04901c2d00074807804510202c488892521502c0b190041b039800a6103050720107025808200407422681c001408900040602441c00c1103458040040e0100900c41c0307030314102640100c8080c0101401c0d50002c0c0201c0401300f90241c2001d02011b02e0088580d40094075000003440410009095503100984c90001c00481c00200e0b1070203c1d0104640d141d6240103c0075060786005540036041010075400540200700c1c0f507004000c030b81807040c07009205511500d030502c405030020901050050362801192a40bc0c802004130030300c008184210590400e0005041d4240210301a00364096140c2044502c5d0b00d8107990f000007140c1d143c0e03103000c40c11074801130000f4040e00711116061207402c401c070049855058090034426482401d0380b504441850380d0a892640000010441c1040002e80e070f142d03103010b5440703805000b00554441c51600300794404d0200190016403079549010004220a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 451194136 1250 451192886 451192927
    0x4050a0b0a2c010603020a1d01020c151e040f0e09031215030f030d0e0a0807030513170a14030901080a1805030f0c0105070507080304060b010521090d030b06 69
    0x45103000d4010b0040c000006010003640204042600003c09040541e4808403003649000f03900b008000c500d2841d03000135503c030040c103a42c50140d201206884581d40707401d011784040703515854000f603840811441d0001c146c0c003d48910540c202540e400402c40020400341280b20310880b00085007400c0c42c59140d04840030010b030080003414100c6c1d4030f0710755a8509120320a106140e90b0000c6507030f0700740c10001e4030072900003040303510081d0054101100001e907107a088450b46500b5140160300c80c554611454804442c646c0003e01c510f40014484542c010b001c100d40b0348807800344800d89030900706511100d850384101460310b40000c226000050f00181e041d4060803c1000c00030310441061442e655035072075a404082005801000070518003000c032000d00500e81d00c918a403901500f810300f15515103806020142000382400d40354802c0b0f6215921800503034400000e1051a091501d03410040000070346425101244039000314a04c54901c01d000b40108070810102904091620030003080149144034207 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 451195386 1250 451194136 451194179
    0x60e090a09080724021c09020307080604030c0b070e0d170d020a0305040b01080d0c080306150a0302120a0501050a0501360e06010c020a060809070506030c0904050a0b0a 74
    0x7a900e00d28045900c0d4000350055600c511503180140d848110000c0820568946030618507004000803003600b01e0010b1a00d01c240b82c064000304100b00e0074400642014095001300c401803013640c0c100401d1661181440d2583c5000308001915a100c42c4001c423904081d90700030b02c1d00450034204540001b00001c0e90300103c141d418080c9401c0492810101e4282d038001302800780003d480b4000e01c42070041d00034030315005000070302c0101059110000050202440309001a0000344003000042d000c0e01c44800010b41e40301503100c0150b4034a21500d01900039001891100891310b401000207030113264502c245e90580320000c00354403403145018011540c58910940c41d080743c03c0c071151b400a200106001c441d202e018800300008901b07091480c00c1c06856001810241001b10305110039025171600b08a04003900d10500e850901e981d2070500940c40d151880e0720080c1c003c0c0d800020040c0d603969902c0a440c1c0454100c50034019501c503101200190342c100001e00340d2281068508202e01075413521312018030a80c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 451196636 1250 451195386 451195391
    0x80610030f181104020405180c090402040303110d08010f1509080303040f03020607030507080408090111060403050c193504080303010303030c170705090f0901120516060e090a 77
    0x45859141c1030301ca0400707940c80c0c41c0303580c180d40404220310010355901160003070710118280ba03d8400000e074601c99000030450040b14070000724809000d032034122950200d01030420f43d96a035a900e0008d0104030b4801100300180240d50176110500e00c6501464100c52a503015403508500f0549401c0d484000e0301800002c0c060303e42c500194080342800607500c41e07405840c010403107060b0b50a0290401c64020310340c2d400c0500d07000030040940c0c1c018240c1a00f090308080e003d034031171000c40d0045c0c6008101980c405d085215650402c07040550201c024002000d0000c181e0700d00b89c0844032604014036116200511038424602841d6040703400c0c103075410704c590941740400c05980c426101c664140e4425041103a094000000500c2415014010509414000d00d0204041c003005107900d00c841c50007a0001007080700004903940e056845a000074480c82005151000e20350355419000400c18a08500300e410f80110150500800f55010a41d1704451640d100c02c51030f1088001080141d10b00108480980b03039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 451197886 1250 451196636 451196651
    0x30207031718041b08070201230f0106020f0d0c060b0310090203010e0c031203150d030305071b150515060408101a09041103070911090a080d050702040b281409060108061003 76
    0xd5030314000080709c40d40000c1030051030401c40580410f241c0141c12900543d40500307690b010b0480c0016012000d0304d03503840c05421500492400001074110118060f038144200009074000c2d01d119800b903d90144205c0007080300d000038103030709526500740005c016410b411584080c0c09035450440150b5001d000441602c8005500c05c0005100720422241900003d83d03031000c0002083c3c1000000d48220f0010040002004039980d50015448405040d42d440c1d41c0c5520102302e2102c0c1c04d20341160301c0b410051aa80e11a41c459913825940d41548600068072410424030f00720306880e10b1012a0660800f0780b40c40110303030f07a6448044043c0300c0500c107039800d4450b010000400307512610452200c0420446015540c42c11102000200784a64000d400341d80c00901107440803c1d040402c0f84e05090781528003080c112261030001d54110b518146545101003070b00034003020524121801c0042d9481020722144041c0c1c405d00703104940000b1182d4902081d0300101091203480c0041c001c0f4404141454045400d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 451199136 1250 451197886 451197911
    0xe1e0108091e0607080f0411060c07081c081006080402090c09030d03020904050f09030301090b06090a08031306050408070501082203030b010207081203070804030207031718041b08070201 82
    0xa03060800c90000b0b0360040002e00440b590b0001180f5084810841c0b140c45504258603200300c01131b580741c041803140380d0000348030040301400d001400c000e2a860040d00c0c80070203400c0e00c0500c46145156100c0c00602100d00085190419440c1c1c2c5003514066502c81c0b9985e5119030921441100241c1405164941403100c40480e6408200e16130a00940c0c1c1d03400340c1c80f040d507a001c1c081980d0000c0d000045003030b900000c01169030300000503641100c1d030303024000c1908080701000c155148038800c1580d8001e2082c1d0344c0031509110000081400780e205a001d602c6542d40e40c1021201c03030280d4090400c480c1c00075101007002d0b46c40750301c3e51500a50048005030841418201081410b0800c2000b10301180d10754006020560f01480b410004107844c5014001230350072420300b908035200040400003444480c4d030105003410700c2000003002640d030060302e00d01c1c2c0d83d460007415452a00148003401c40d40c81142d900c152107003005e000d00032713022520300c1440000500c4101d06850f400001825202159640c28444080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 451200386 1250 451199136 451199173
    0x812091201060f09110325090e0c130b03240a1e080105060411030a090503040b0d1a04090812070311071103100605100503100e01090c0e1e010809 64
    0x51400c01d20003545145442a484d054800d448400741c2558800d008000c02040007038480e041078440c0c408821480540d114082e944146940c014540d00d4846008000c03e80c0c00010040c6010307180c07a000700c80400d80d40c0501410364403046031040220f040703a2000d44160200003051010f140d80084c121004544c44022007d1595940c0100d14029860940200402036003071040c660813100a0703800348403a41c040320365503000c0d20020700214070069840d00000c051041c14070039540580401030845548e903244242c0a03020300540c0400004008220000c1041407501d07101d43c050030780d03110400c24109207084104d0040703010b0040c000b0061507101c0c810040725212401c000c02c441c82c403e001c2d050121a031071042c546424964200000010702d447ca082c400fa503181110303076075080d500e842d00e160303240d64030030718203100e0f411035800602d035031040100105241c01c041e00410070142032655008142090f400411041c4014001c80c103052641000000d42c940d4480c0c00c80c03a6200501c0c03404c841e860f801c0076200c2c504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 451201636 1250 451200386 451200389
    0x2b0f020c1e0d112e0f2d020c1f050c090108010b030a0f06060201020d050f01081c0309081602030c190512010603080a05070c090507200a0f080919081209120106 70
    0x50030280840104d07803119007481411034512100108000080700c41050301c03444090b1100c403900c040e011002000c60003040d0f4040702d44414000e4103503581c40182c00803c0f501d88030490303149000c143c03c2c00005201903c4030070a903400303494169a080016481c080381c500d000d600240080c0e01083e1500c80d1405000034502401340100070a500040c2d80d0344000c800340c0103c0d40040c06002d45174111400421142100054100000d040c0030601d49030341400100a90040c000c041d001040c041001c45c04e07102d4520312140e4218040d0083d41614003507011041008000e00142c03a550340d070140c54000034884c50900c1001c1c00300d028942c8000058050f200e80361414180c100401620000f0000200c8508002e10a1062170040c600000e081c403003814442c501501207000308090289100c1459003000c20701004001e450261500035154544082040c20a40810b83c0100306090003000c110000d8000e941181d15090f044640c1040a8000340060035102d4150b0f603c131300d00055003d40700c040c0b0550b9150b030070320a04c0c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 451202886 1250 451201636 451201693
    0x11805071e050a140315010f091a010903030e03030904020c0105010501090f0e0705030717040f03020f0f070506030912030a09020307060c05032b0f020c1e0d11 70
    0x19005140010a032107800c04111199107044009404016039107031407001c8001d5443c010003019020003200082442d20301549071390040c00701d02500008216a6944412040e01d0040d401030204034824001e5055681e0601340090004040943c1000860302c0b800c01010b84641c010241ca00d07101610780000c0507a0051401d660041e507507000100200c4da0800c08040c0140000000c680307541303140903400141c3c08030040502003804030000024410740d100d0322404041c03d6003450a2030182c1880e04000040b061981400c40142c85034600c0c242c50580000340074407c00b031a9000500006040034140100d582000d40909050312445040c10740d1380941c08082c5120b01a07881e00014105401e00401d488c2203d00c3d84014103010720701003660040b0b078010040324551880107481d40c2059080907031b080300705035184c40c051084515120340c200385500240c0080040c035085d00111390120403010326900100507080700b283c80582c841018035030001d00448015045110322010380f81803010341a50000007040700b6a018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 451204136 1250 451202886 451202893
    0xf04020d0804052d182202040c020105100e241816020606011403070c0c0f1e0b040b03160309020a030b09210d0f180b0612010b010e0111011805 63
    0x1140080c246244070f18401504a4024040c20340c0910700c4070a410010b020042c050fa501b8490316864800e510506100c0c40d40900100016001c160009008002c240c480a0302441c541c100000c2080c0c01c080414020703a19a0050104946200d0090f69807142c1c62030499001100c0d8200842448400c840c524424060250507606403044060700070b0800c240104042d040c01000760f405000b0384010381c107a0f54000da0380d08242e0903400407424281e10781a03150f4000880641501404102803200003103440c444601c1d40c45581591f91107014260040c01a80521207281e04240b00203800711519810301c0e041150981400245140143c001caa50500e190704190340900f201e9040c020401e40810040d40c9030a02180110b11400c03110311307405214442e0142c0d0f080d080d910381a1a03045000c00750301520070f003c542418031380da461061800d03910783e0400302d07907952140608042038000c14406024104141d8016550001c42c511981e00542d581c106000510502e503685210003502c0780741c60b40c1c96884490051004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 451205386 1250 451204136 451204189
    0x50609060a0e0c150c0d021606140a2102042702131e090f0c0f050c06010b0f071406090115030201120f0b1f0806090f04020d080405 58
    0x10246080d4000d81401041071800d8007820500e5004511101c4038081101c032003071200b041c4c9000b6881405011521522030080b1040c03c4481500052501e0094003080091001c0e40d0b50703003100741c6145c0803607044451400341c1088a000d50503c6007080020074202056038100300044032034280c0072070b001600071003035005250041a28ce04481881102c442c2200e05066142c074801241d113190764990f0f841040c0b906501c01100c264909a00982000500300c1e403e0100501d0070100c1c081c41c060003d0b20040c03400f1403000014060302910917400c80b014450004001d0010343d180907240701c10380c0d0104c80000c40e000342c10b10180002130b0502d500307040030068160040205003080d40200f130841d2128441d060f55061807403400c00049c0d8200c682002400303030002000484082040c0b208020b0aa41d040c81d517030082004550050035a0350304100204041140d5a10f440c41c0c0d41c403800d0040c800001e4a1018144001000190051a102c1d000a006912540f19607040942c1c8202041c80480c42c40000003061010186 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 451206636 1250 451205386 451205401
    0x30510090c0b09030309010305090f03070506010e0c03070207060507080f0c0307110303041202060702040b1203040609150804020402160b011710020301030803060105210c252a030b040506 82
    0x4003602a29400000324902010100041d41e61b100d0420401c1c11325032920005407003642c0030f01200c501180c140c01600e90701c0010f4034159884078000d01810941051940216150703c0803241600d1080a4036001065400d062a0007603603203410000003203821300401c1049004200401019061200151006540741d640d1864020038121101010303e000b41d00c14070080200c1641003c081d03022680680b2016624035642c004600074251000080742c1256500603801d20138000000148219000b41e529481d003136498440c40300c0104420080200040c06900114026241075401010820032129400e28443c08a0717075090b00080003640141c81d07500303114005040006040c0646c4c6002c00601c10218610760441d80c5e100c241d4000a4070f8941080f070041142c0c0d9a800007805040a2058261455230f042c0c6003042c2e450340e03941c0c030180c41c05145064803031540c10b40d141c02c15400d81d4242e5015801e521040c501c034401c0035581d07045565a5104900c0104000040b81400c0c800328012401540a040980b03413500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 451207886 1250 451206636 451206653
    0x32c10050c0f0d08161106010b1b03030f0103081b010c050a0f020106050d0b04050304170318031c110c040504111018150504030209130201090b120a020306040603051009 74
    0x1040d4540c2504406090003850b54032803009075000e240302c403081d180035285402c202c0d0300c504155003c0b031940c41f9090000c200a0b4102026014070900b000340d550140016220a82c1c40e804282da80340c0c0080c2c003900040c80003500342c20140072b60340c0c4007024102c1681071684000f0700f0740d00244a00008a81d000440d200c0c0c06a0180c540e5402c49458002440035620700ba020a00c03040304d940002e89502d6074003020804001091045400409514000324046840f0301e003416125440b43d0b02c00311280000b038401c8089400c010070b020080c40c904041c90940c0c4200d150f81a030382c00c217111800640502651f0341100596a8034801d8901031405818141c220010150500407244030010744001030045280390a0081b110002e018400d96070762140705100f10b20b000c0c00684040c0619000203510201c00d008010b401c00504040c04035290003640e81040300ca03a00c00c200c05031840740610149440342c010002400030f081607001160800d2019000140e00c69694071218200041c21050901040d126000c0c00305014040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 451209136 1250 451207886 451207903
    0x80907050321160b04030806010e04050702100903030f0c020c130e03040605070510021b0111160818121b03010b0a0306090606030b0a0902010912032c10050c 69
    0x10350091200e0500944415406424aa41c1440e1200009a900856144088080c0e083c0f81c1c803102e44140e0b81094900074202e81b4040300c0b9140020b01c0c0d0700080000e0714290044500407801a0060107099840d00014400303400400d4064041c907450300a8442d8402c0d0512800403100c826501400484d00c0d41400c01001c0d141c800303491101c480c01c009410b02407146c040101c41c111170440c00d01382d07074130748640c60078604003144840780307400d81880031030228040808041090b100b01c010030000c006041134840c01c070a0070301880640044000f520301d94000001e0780040203180a0303202500d51700c1040d00c80c1000417694861048044920380025034500c0100380f00140700030800300e04500034004040c03070320007049145c2c0803444061310858841c039003242400003942c00315020716080103207150949041c151100281420700412070001d0000300002610845240500d0420343e850344c0c81e840d0503006220345d000d4018440500c000c182c43d585024000700c0d61050f03648114043d10340c03152a11351046034102410100c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 451210386 1250 451209136 451209139
    0x14040b03031602040b09220f0c0603020306041401030c0504090809030708010e0f2b031401030309050f0301061214070909051b030f15130c0909051207080304061a0d0308090705 77
    0x941b410b000c115003031500e449000c09003e01d0013040f0f01d945070034180d80300565a0b1018103242d4075128049080f0345d0580040d441400d0a850a0082c0c1070460a1846000c109120141284045900610403450b05800005002d8012000c8500308251840080d0a00c407a41c0d00600c1d541c0c1d50b40c000c178500128107004011601140001904080407900720460000741c1c0740b0745424000301003c5e104d2940328000c1c1c0c0605080010a02140803c0d80c507850083c0846500d0702401d4411800d14468200300c3c81c0c140038007000e03a68800350000c485401681e811494501d07001031403e05000711040421803404901c40c0149483c0038400804130705065085150444090042c19402a00500405040c861001070031002c00e4190b585650401d80c1d4032241000c408089001c000c0c032001a200c00000e010465800c201850f40c007820503a20407040c0c0d20390051081c802c040008140240500009000c10101d500c40c840311402c0b156048242c66a03800041d5030b00e0002074044010801d00340a00c02c003ca0100980c9014210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 451211636 1250 451210386 451210399
    0x40f150b0a0807031509140a060f0b070212030f210c0720040b03250801020301050a14030705040f0207030207060e0a0519030c060203040611070501080114040b03031602040b 76
    0x107031244010240c0c1c0c4010309000034940c680302e100c0e40e40340c0c820a901d4010900c0c00ba041041510310a0301002c880020b580034250f013402c200c404a016001c501201e003c50f0210b6840da0f02c1d00c8100c1c0c0c01d220440d131000b05020b50b980018481011040707400701c014155044080074442c440800102d00c0180c20030040c3c82c0342c100820510041001036040a0b050900344100740a040010400c2c20006010300b8400d02c82507014000d480c60080c2d801150300344144d418103044448a09503440f140018200d0100f4030a0b140c0c0041143c40400002110842c048070840014003030f102e801e80c03180b01140584c0c0000201d401c006034005804418550305215200181c070252401030042583c0b440040c00707030700e424068503101e41ca60544000d110b00301210048011680b20541d604001d41d11080a0b499402a12034030b00414074540710000b601c103001c2034101c02d4500c1610f0760348041c0d0038903100700c503049010090f4a80043d59200ba504969800f0005800c000c407640c084500030181c40e20511041d00c00c0d21202c13a02400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 451212886 1250 451211636 451211647
    0x90b03010e060a18020c0c040b100f030f0c0f02061f0504020c071823090a06020c190809010314040b040b06030a0602030106082e090b0609040f150b 65
    0x1451004480c115092450310280e10748880c400602d44410b07a40c40612a40d907200ea0216441d81c60b60003901c80301c0411419a246086600d06100036107010240c3c0c1580080d90b090740c4140c60b4019a409503002496203400101400c20104400c112100915600081021440c0c02c65035941d040012551010f415a404020a01e58501c955240612801a14807454021600b4520482d080207100c00802c60305210700300e0103440385c8445006207416810382524940c8000c002c0e0180d4201d079885402040840000c05100d112a150381009410180010140340141041c10840a07056104a5501c82c0500b00c4103544480e518009421130f140c0b071101086040898003040041079070300c43c440e80d1068100207040b03903c2c3d030307554002070800381a0340c1e00078051b42c03001c000401c2c05d50340661010300c01d5840b5003801d0303e11081200c0c003401e00710f41e00700c190a4101d0084e40620858120350040401070074080c00a50511014100040c19a44803005080903556036030800c5040150908055000784102100b0303900d4507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 451214136 1250 451212886 451212899
    0x2040501062309040b0613090c3b130606030b030f0304050d030311041e0501110a20040e01050f130f11011b050a1a1006081f060807030c09 61
    0xa0310080c0e040e008000c40443d002c403030364403181c00006506100419095132000d000d50843c070710161070301401c0d011501d0f100b82c0c1d0b0360300c1d40540e41c10703803207a120740c041f041d550707030780500707490750422010310410002c1a00c1402045c05496290701191410407088000c6506030078518000c046a0054a28038843d9000714101e155481001c81102c080e0380054483c0384003100c2030f00382130700a01014480c40704a030702d001600264540901021000085100200007450303555000110341c4002404412111340c1c0086240c04001415042c60005641d000e408000d00c07000c20704002022100d1900c0c1c01c0311640d4440041100c50003c5034259030340044117110502940036130342c0f103024a85034208002003850107d241080c03038981c0108501c541c141c4401e5010ba80b0015940b41c401d0700c031041c28504480200700036144c9460390304a10038607440f405201011004251410008841c02c6030090701e2102d039254500c44124a00c030341d03143c4c81c9001d410191034660507400c0035500141144c4003110100d0030814115002e0142 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 451215386 1250 451214136 451214177
    0xd020a030f150b030c041e06030605010203130e040606090507020a030215010b0a080702070306061d1510050f0d0203010603140a021218030c0a03081812030103030302160b0403020a0204050106 84
    0x39941c0f8054016129520368841222900c20784d000003824203410500344044c54071000030f900c02d680aa540034854241c1e9031005990340d00030600086550380c02d4070024400110b004051651041c09800c01090307003560b480769141103600550340100160440d00c20340051540403c44007804d0380040c00040300079807401c04000c0c2603000701c18121040140f014040b800c402e00c204401c1004d142c00a00811029030780d50644011201554114a03401d03200d40d0000b0304076000d617802e41c280508040c0104114080c10034044402e5800808003e681c1001804581c4004d2894405036001e0801030300c0020710040940e01c007c0c0240340040c00020543c0c01002040d000d03040000307409402c800828194201c0172190101c0270700310f00130302480c03a0340c40c40750344001c10525902c41c80c200d0180c0042d50006590303442f00d02446864070303c0882c2a8139800350030401000081d210341d0083c403001c24625800a1841450342d03a4018078942504c0540050380605012820f61501d4400d0600416003406d14030b0b01c0d40000e030f81c1c1180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 451216636 1250 451215386 451215389
    0xf100e190e040b0601092111060702030c0405060303130b04092703031104080d0905090108010b0102060c03060f0603010b091c0f1101021c08091c0503010b1602060d020a030f15 77
    0x208000030408109139074040d81e56003018102c0782d07070843d4a140079018590001c2c1011a07064620041d480300b03c50080c1429800c0321503454028001d420400369074000e10000e440c01404558040c0b00c1007002d046040ca18076814005001c5040c0c0059482c3d1600c02d28005071405922002500f521501c04428a48528648440788a503d400c0201e08011100180515400303217512202e91405900c9404601075070160050040d1401191081031907600d400c03c843c202c81001881e180960f22500206500030080000380d907020100400740d0300d00346c00001c00310b000c581003a0720410000303a0208161250740351195401d5411040340c90390064401d07050b1036040315440b07403810107440c144c0202d80990b9180d1003030001c5090144200341d1b40c1c1c803100032084020450030089942100d64040c560800c130b810136074058034150311a8190386040c10341c0d003045580c820941c032009800d13804400c441914001a00c50a0181483d002e8503500180c603506000b80142c15501f0358540403150a15044145c8084000e080002c170 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 451217886 1250 451216636 451216643
    0xb090411010e091608010f350a050a17070c06030b03010b09070e13091211030c0111041d0906010612150803032a04140f100e190e04 58
    0x500d89080300c01a03680d04001411150084520010400301101c00d00ca0480304440540e500901daa0740c4003045407810b5010f002e24000004840030701c4103a041c030340842150600d100412020603030180c1004910301042c021080361700c5c2c4c0005002e101403014400c026100007004815040ca001013a03a20b001e00807202e03010f40d0040c03541e41c841c649080d8400f54802c2d455040081d101c1140350910140241c400742e50ba80001c0c1c801c400d0201e81e6101d0001d607000e02da400c00c0c0d210005540e030004021090b0b841c6aa1030804410910041c4200d0f06801c0c3c0900650101c543e0440e0b0b0380c0d680780c1c10030304021510340314141540701029030030050181c942c0c0d0003e400e41c1100c0c1285407000303940c42010a04005411521400000c5003038030314020034400b00100c0190b00400c02c80300404031203200e0f031a944840c0049c00919040414060000b0045052003800c1c0c0312030510024090a2140c0010000408c0c03440080c5100c00041c00d140440465070a103100120300d1510018080c0041920308011007011030401031008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 451219136 1250 451217886 451217903
    0x2160617040f150f06050607081218060a1505060c0705061b061005030d0c03020c010e0411030a05040c0807050306040618141b09010302060307080403110f031902010b0904 75
    0x5000d0269061041d00401c0d0b201c00c10803200002c940e00f0300003030103d500076034410a2416030300103407500e02241110102a0700481c031500f42040700b00000c4140c00001c00c403c0600c9030a0498090580040c4101ca21a41c6001c80000e60344040c614105071094103508100c2c001c0c981000304c11180c02000804001f02c4204640140d95041c260070810252408124209410302c5050300303206010380e0300d80038441607400503002c940890034400e0381102c43c00358010780600036801400c00c0c5083e43d403041200e40d642d10300141001c0b44401c1c5d048501941a44101e52561320346a4400038801040300c00e111810041c50010000c203907403420031000903140c00b000f07032000b400c040d610042266400d0030401ea00180540141100d03085d030b591402400d407110303540c5081403079080101e0742d00c0d01d151500d540b00030305803900907280a08603664200244c2d481c10014009400703001d841c0003c0002e41000b00150000d10020202440e01c0c0c0304160800b1034496070000d00307181564140417821103035032142c0840c203504c41d4018071403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 451220386 1250 451219136 451219141
    0x61005060f220503070605120601090f030803040206190c0201020d03110d0213150906030f020a120b01030e070f17011404080a090302030304030309230102100c09170d02160617 77
    0xa100c00c80c43e500c100d80501030000b0010712642c01c00e000e0100d90800d00741981c000c2c0d407424011269081680940200c03086124428808181103001460344a440900201e1415032039040d0380005003219000f02000842070030700d010465a043c00307000d4815040c0c0c1010301c2925a01c3c10849418010141c11107800d0b58003003180340c003880401c2e01c80f02c01000d80880841101481140c0207002c88600e000b2800404c3c02d10621400d110914402c0b55181d02d061360344c110580c02c600031148003038000b4221007410141c5071043c00c2c108010920001c001005205000d1481614042040010000311301800e95540d2500070425204040610040e5110341c1c8207100595035a03035044243ea0b9500103801c00303034152101090110801d5007005030101554240403240f0103c040030304000b60310715690300007940140c00c080001c0c0c0c2c4070441d9801c80354071a10a414150500307503c484044c0e01800280c4070390b90555201504404180ba018803100100c00c040109140312141801c1014010b07030303c0298480c3c0c240040000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 451221636 1250 451220386 451220437
    0x302070618051201020405031b1f18170f010203010e01060806061b100612022103040302041806060501020f0322090e010b0f0f1507170309061005060f 66
    0x218407001e000010901000e01801c0001c0d00e000390080c2c00f606000f446a400b011208100c0c150300701000d040c004106c034080f121250010701c108000140201d05000814005c0343c203150b14440d00c84090040b0424591704983d45000c081d1800041c03005d11003071644100b00520441040441090640c0c1060238038966584504020450511a0079060100841440917240100c1000310301c020583c101050203105042d140d0301c80d50128560554025800151039250102600080130f00c01c0070700c3c4c5403000ba039090540e240c000c10140c40c11108a808d403184403d82c200200001d031701c079803809408284002e00fa000c4e0303a0304509980b8841c552401c0241042c2004c102c003c4880721603014041d00d04481c00780140584650014083c00c070360142036124180250b80e401c01b900b80385424241d4614000d000601b494402420008164880d2000361015003041a0520030000f124001754043c45286c8010304440c80c0c8050402402c1d64a60803803403085000300403030030a10b0840c60954600340307095040d080051581c0e11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 451222886 1250 451221636 451221677
    0x3060609030d210501150c060f06080309090907270b0a06020c10031509090507050319050601120206090609040b090c040603050906010303140c030d050a230403020706 73
    0x400340d0600c5000751604009a00004610b80465048080d0701500f010700c60010076160309004526246840c40303042c103d203c0c411081107580c68040c40f400211074955844000503112030340c001d450150f00000b04250541400f8180c1c580c004600b40250101a041805000f0354a8070401d82501034451308018010420503948000070402c1c0003000e29654640d42d98021f515200310ad41c449108810f0341d0014910280a80a4021009104d841e50345041e420001760340e00400074003009855038416948041110b8804000c2005d001115203004260394503d46400c5242c4101604890701080784500c80b24010b80740c0340c00b614401d9800b140d0480e11040d8100104004101c1c1420040d4440702034010b001040c40701030010001d03114143d409128580c4c901c0c0c0300a076108004e2000034001007480700c45c64691845040603000e003003003072801e072440e042d0740c0c05108054610030f0ba48001c400d99030f0070860b00d5070b4a4043e440031800c03d4070401c01d500c620b0643c40281d2034502501c180020b201181400035103092449 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 451224136 1250 451222886 451222897
    0x105031e0a0c020114061027091d0d0f050705150106050a1b0c060309150c0e131404080c120313020321040b090a05120f0d091802030606 60
    0x44140c4501441c1000003003000d02040480c200140d4130300740009a042020701145481030700042d00c0b034402c0300c441540440301c0d80c984c801c000742d4081a0781001d1061185500c6140c00a089039240032803201080204e005880800032006a050b503c40e80744a41000c1d00440301080c0c1e550141411502c4240c04c0c01d00300d0400072004d03202898842d114001040350754000740030700307900070055803400480c0c40c80c1d04184680300141c480c05031144040e1001004801d00c60303041402d015108001c42d004800d45100350005031540c0f1441d41e4007103400301d414614070782014100009110791b080340c1404511585501680c030010050005000e00000103840384810f5020000c001c0a00654898503985c4e240c84040711144031403031442288070307000f90501200c4c4e10b184002c8400700e250103280d0352440c0a16104406001740c0c4044800780e00804813540020307090355400c40b101c4050400c08068109034560b901094100003c52105000340580c0281c00c0c0020300e1000b0407450182003c150060307403500d52800040303245c043c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 451225386 1250 451224136 451224181
    0x6120e060906040b0603190b06040e0a0503070303050f13030c0c080d031b050a05030a0b0d140a0b0609070e012109120f02060415150503070b09150c060105010503 71
    0x31103050180c1a180000c2403031050340110070b18040ca803900020142c803031240101911030101010040d002280c0c10f00c1f01960020030003000020f51505240c507060038600704440540b00c42c2c002241003414507400d0300500e503010a51072a01c515500e01202e619801c0c81d0808405420082520001010060101c1c50300002d0f00d00d400895a0300c1d41d00010080140c1418070b4035810b4064503800c10b412550040341038492080c00380d1074040c1140d9420044070b004041040f00c0a6001c402c0e800309401180c7e846608403200c00510028000c0920341d0f05100080106c06480303540180c800c0c00c100114a07031b100c2d00b22030080400f440d01c866007600c0303a140c1c42d1091000440400c54541307010448000c102d05c2880408113054583c0342c1c4414910607400690720b4140885010f40700c614460305185510000d80d000101074507013461031005079a00caa000c0323883c2c4200b54105000303100c0c002440c0102840d200308004041350701c04c0d20340c41c5082118000c107600c07000184100e5050100c0400030604846601c462a83d00014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 451226636 1250 451225386 451225393
    0x30f03080406150b040317030c03010e0c0913021b0f070510030e060a0903170408041413050708010f1202130c120e0304090c03021602130e03042606010f06120e 70
    0x100c44c9401034103680a1b00c0101c403607842509a80d04008024800d50f03201303100d00d180150441c1e285c03840c61080f1000c005c0c2240c08100d010480bd0800f03a54032441d02c0c0b001e203081c0c0001030302c0f0814081c188045440c110000344d80e0f03900c103180201800c040080e00c076050300e20a5501851038a00c1810507800391000d200c1460079809440304108450b6143e500000442e030090345d5035107248841510381b6000744400c1d5001303050001301308020311034848000160304821034003500004402100e20008800c80d0b4003a00d5a80024694800401840500c404550054543c800001c204101a40d002070701000040f0b407540709440e190394080302240c0c0218114122032508000500030061880e0f14140c032540b00b4050944254608a03900503041d02c648207950428400200c140e000f42207a80800070182c200d40d10111282c1d8980320a0821541c041c00600001c240150010381c40070300401da400d814102c044c1c40304006500203801000034141410b260011504142400c11401e001d0785801c50241c005d440c140000c034030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 451227886 1250 451226636 451226639
    0xc190509190b0a030533060910030e0705030d0c0f020d1a01061416060531021e0901120807060504050c03070609060c0b0a020d0501080312070207030f0308040615 71
    0x800382001041220f903243e60412055541d100800402d0380415840410a4181803500e50a4030810112041d000e10041c04103080c424000d00143d03000f01401c9c3c2400c00681c5410b102007000d60f0802c8120b01400f0110701a2002c4205500000d106602a0b94003412681e03090312030300255210200700c46940f43c0c026443c694000003119154651036002c0c03151000090311000714491034680311040e12520401f002020749035813920384691001c0c01700505000c6024400b44074004100c400007501180880f0780c1e01c0c00402e0020640100400000c030790290940c9020092100c0a01d07594030a40a815603c4e084142403000d121414101d916005852004201c90b1410050000744000040c0000c0c041500300d04440d003154a40100719070501031481a0004640f0030b860b0840040c40b09441c156010200e69401070070901211b6000302078070003c0c2c0c000f4406401c0011030075101541c3e06a226401841400201500351443c1d66425006d05404005410441020042010882150071804140b0700b42e040229415 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 451229136 1250 451227886 451227899
    0x50a0c0614240f090103140c1002011e0c0e100201090609060608010c110d03020c0109080a0513061103040e04050c0a090c0908062a070602040b0703080c19050919 71
    0x640c2c0d1120040a021200034001810b10b4100749451a1410244c4000d0040c0d18550702c4500e0a550306100c01114003c00c0c1007542e05031201c40c2081064050359001182400240d001821052040c100200d5030380d00300025200080d4001a2284003203100740e503081d44002e00124101d004003a1000018102c070304103425103040c025250014019108d030311000b003049a040c02c40a84442640c90315114054102c510410500c5001e81d01403c5501c900c0f200204010f0f8540e5541841035101a9000001c900d0100b4039088030012505850302401082c1800c507000f11a1103c070669a0042c0c0c4030310310b442c24210001408202051003403800b07a20000d0700f000034a9490311580c40240580500c6540080c102e2000050030500000740f030340c00380c5461141c24588070800c0d14031880d40406100201010f2004000c0070300002c6407480140020440111410f847d00302c01e140081504001070305910104005000d80884e075400e800d0600081451400c0c0540c0e59000b58000c1080501100c90500041d031030b01e000001d5030b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 451230386 1250 451229136 451229161
    0x140d0b010b03190b150c07031b030b0105010804050a0b0709090f050601030c0c0b04021212040305010510122a09020a0815040912050d020d1b0f030c050a0c0614 70
    0x50480012911920341260301d85008540b50700c15020b40c81704910300303100e48000781d007001010041d002100b036406003510390b285e0310382d002030754400440099410081041031140003c011409007109207012040c80c200760301c500740d584a041d41d02034141071480010401d0306018844540051414030403e03c00394400004220040504540541c00f07c1e081400369014140b003075482c7c3c00081d60215038103016455540a00024800c950080406886100c80113081209014050002544500004036a0386003c00c0d2079941213005a1250070f804030030454400c0000c0e034500ba041d04020106c1d100c2511480c00c2e0b140e040000c189540081204c0c0c3c40004c41250340c4d44e02401721441400c2d8071000090100e2410248000c40d50303c00e80192900e942e5150500e06244100300030f1000e4114031401604051070304003504104e910602d8803540c0d001074441c131600180e411030403030040148031703040c1040144414a4054810310410002c1d5081003414441c10040001c2a80408186101002c00000520702031601605 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 451231636 1250 451230386 451230391
    0xd060e0607020d0c060f06091508010c020d0c0b090c150d05060d08030f04110319030f03060e0601051b072603032701090204110d0609021201140d0b010b03 68
    0x8080c0256000611128000649020584000da9805101d000f9645904005026002400f41c01e251900300001e900c0100b0b004200321481d00703207001d108851030900c08608450f8400f0002040d90464006100b2403600060600440c1d40c00c03c80384825a40c48407030003420000c4490700b150380203400e1500903003c0441f00c0702801000c48170355010081074132494200702001a42640042682004000040b95440039001d503e40041c40780806544200780d002c0001e05007601000703030171524800c41600d8000d0640c00b89030b110000001e401d007008201e05115a4004541000300620705103e00081e400c0101c202507102e08007111800e00a80e105d2640f240034181c0b11000030700c0e0b0001c070707070b143d00c13130304c0a90880c011003128000e010f06007642604950122002c3d8104107240c1071451195601c0c05031030056101d500580441c01769110306d0030307550580c3e219401c040755500d81000c2040c61041c040507882401c1c0400c40307815908c21200701800c02400900050340303440c44107401060f447c080d400018083d07070250003450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 451232886 1250 451231636 451231661
    0x20a0f050d02070905090a060c02100e010b09070f08150303121f051008041506090c031b02010902091506040b04061d060306011709190b091e0a080f04050d06 69
    0x201404d40c0c0fa0410010b440c000e070b9000300300741c01c0740c2c2d00b050002d1084d902caa01200c9040c0103445868107094a418200c40400304000b0031039450b4001e0000526040350010ba206c516800c00300000d4282401c000d21030803000300540f03884c920561260425903410000d07941c45440e100c4010307040380b0f0486001914030304c5c94402052480c030016808a07042c90440203a640c0a1036581e201c3c105a540e5803100c217280603101d284003862a54860000c2054846400703004d203c0300c2252000714005500c01e06403144540070400138411645002c100c0c60059944410194002c81c0c1100720302e9103020003000050b150705c525400000002d03000100099110303008490000d0310401a103a0508002410060100d1444110341250028591064003224100017500c01908151001c0c01c940400080d00784041c050091984c05440d1030761404100700980f4001c00603011350720b00f002440c00c0741c583c42403002e65a80d00c5d0000018003140f0085602c440109a500132b441c002c20008101b016460641d040c039500034140080380b03d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 451234136 1250 451232886 451232893
    0x2041a150910050c060c03190c03090b0105040b130f1b020a0c050603041a041506080304180605060405011b02100e03010e010c1d040902090a060807121a07020a0f050d02 74
    0xb40d078040e5040d9201c4030104130261100d6510301c811524983d10050602018001c0070b80410ba8044c2c0a1081c0c058031680b50b01c0010f85900c0c01c3c1000481e03884140e00880c841d9041000c40c25140c0c507910f071021042c1800740c4010a00451303c0743c08501600b0b1a444e4a2091082e581c003c1e181143d00140414215020300100801c0e035440f00c0c140440c3d40b100b181d01415125010419030510a007907428141d001d8080c2850301c0c540c0300c0080325001940c19a0388445032030303480898140840e02515001e0f120307800c600841040100e18140c04034100d8001c0f0320611307050101d007000803500c00140a030f1096521f40d0050644181042624000c0c2c07400c103207202658040c0d80b0706880d081d8010f01c1441080d004c0102521501c102a46042484030780009101440c1d810071388540c1c950005843d0004480d010300344184011610314240b28800f8a080416400074410b0b058120400022400480b951001c3d550000b103031501a540e0120309a1a001d000e84000f01003184004045003408000f00d40030040c2c01083d0300760b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 451235386 1250 451234136 451234159
    0x12010504031d060301060c150f0f060501030204030c1413140708060102160521010e010504020f0306100303030209041824060305340902040302100305040f02041a1509 73
    0x1020708040b60303100101e8110000b040113100480c06109820101480b442c0100782d5800f00d03003140b50035611800003010f601500e580030300500749294043c00c1d010f090203103011400c00b071940d12000356a00c43c0c0d20910a980e0916950048691a084565040b41010f0301c070a211a4502483c00100104102e85000000d0a11004100290310100321318148215012048040b00e080408022600c004106208401340c0709011103882c603d401e015882d441034491000150501d0680148141c141d010710206110750841010018004c00c40741b81e0358191b80e01843c0043c0c0f02d0707011030082801040550825100d103441081d12034100000a01d440b9410780b080e144003000720034418200c106442041c00700034090b81007840403103811614103010070700555260402003820469040f902d245c0f090140c00c4112000d400040500a5041c0703d070150f0a038066628007040f00f031400b5180c001041e82c804030000e20031078580b64804a14403400308a106640c0c0c0c0104051015000e000c0c00301c0c0c01c0c1c0e004201260142413440701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 451236636 1250 451235386 451235417
    0x1030e1c170105100f02030c0f0a0c1208030f040516030b070306090506030703030302090310050c0d1a100e01140f0c0709020909040212160902120a05160c08091201050403 75
    0x20301e03038121000900b180c10340b250603000030b070340c0b00414500140442c80140b02c480c0d8420010428640d04d81d0810000d090b1780d42c400d090507641303130865400401d2120400f00c3d101c000a00c4450032241c4c400c0a108501600751101d20300203041070b00c441000e0300b240001100c044207004503807a003240113190b287c500300310260380c3e12a0001501c0381280c41c6a03064101007000c10109009400508813108020240ca510780d540e11010000c864080d582502c002a02107807a54a684544c41191040c0b900802082401d882c3c400001e80c0083c925041603040142103485c011a9074040c041c107204c0d40300c200302202d84401038401c4c01995a0070106650b05075104490001605121501c201c5100c0d00c0c020b04100c519a9590b0240300760350039446103414252240a6001d1301510070380082c2405054401c070003613a2180410304904034040041c0021141c0740c680401c2c0001400c00b82c82d5141d40b8403450404c51a2061a401c0c9915140121580e00707401c95075500e410a032107141076003c0e070b04c26440794031048130305101c804 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 451237886 1250 451236636 451236677
    0x10b0114030c0f0702040c09170f1b1801080303100906080703080c07030b040303050f0609060112150513020d050f042a0b0a02060a1109030604080901030e1c 69
    0x806095100c0d4080000c5490700b55000d00810281d1030110300d091400049a02003070403164228002c2c400211080014081c10850303031551100c407275221005148400d100d0003016103451440300414542c100c4002c80d040e1684940a404451522803880d0b07888560b0365030368040e05c1c0c0e442100c007511185d0035a40081811207280c81a0300c2603a958100405440d0305550360480caa510860182c2c81c5441481400000124088621803241d0310a03980402d4074145642e940702c00310b00280215126502c00b808000d03580e6840f0744030351a2050007110108000c3c0d060082c0300307035081854101035000b0040d003000340400c0401da001031421004022080107282c0c2d4100584042590076100108160f2030010130003510406c680010214502898030380484507621600380302203134414150900036030000c0e010001c020155224a14a250842540610700b52105001a4603400010001480a9804a060001c99100b42d22041001055400b110b0300490194942e00c1d200c103a0b00e409600044100d0103081d004111072 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 451239136 1250 451237886 451237907
    0x120f0c0905060a0813020109050a06030c0305010909080d1a0a030c030b1b07030e040b060d0f05160e120a05120301170109110402070f2102010b0306040b01150909110c010b01 76
    0x5640f80d40181d00d60042e81c030170503003003100c00b47e042088521000c107103942d48072210710042155490004401002c1c110281c140d80c0140d2003081c103246804103000c046051601180d4201ca010725000030401e8620f040d00c100794580700c00c05e40c0c00020002003c0b0410140d03800010540380030310000350265564003c00c2038107502d044494100d0000c2881450002805842c0049211800520104440d488a8040b07045904108220440741c2e44545440c06d400e81c0d2441025006114000f14140f0004007400291003420704003580d0307000d040d04891104c1682c10510000c003403182e026042d04e010060528220000d50003c2c0117816504000d03103184801c803a0705100d982c03910307075100c1400e40c141851340b006c020003900714510070748410105146603400915000440803c12040e01c5c020100c05074161402401c481e080b0504601a80c800e005020201e000300407140e046411403c0d40f443c43c0000443c00b00c3d0140410380c4810303c100e04040c40c0303080080104024104000c00741000b00028500c0100440d21a08034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 451240386 1250 451239136 451239157
    0x102060c130e0a020c032a0703050607050d1b0f0f030516031a122104050604031410020a020102041d07091e051c03031d0c10120f0c090506 61
    0x411a00b00205164601480e0340b001101c103005007030402c4200e440e03065a002d403004160710b000c0d4100136858030001250f00455202407500a101d1141103a403102d98540010f407a01091000219000001c2c003041d0304803010a10540500200310310324840c000d480e00e601c0b40450350200e51034425150320a4440c1c40340c07a00c106103049158509a00400303041d40200244280c003404811021450350712501d410b4444d40c000900c10004182000c8a8070f441510020004080d10b002d500c10030040151f503407020191030580c0d0300240c144075150303109181c241c9495a6502d10004d01800403030301409860b010350107003044510303651014408101501c541250000216a92004520400c0c81407011081070280c01e59a4041c50b100115507507128000103c807400501c20b11114000c0407a90304041580c54011100c05102040013403c0952210440307988412580600750b002d03801840912030743d00c4c8141c00c1042003440e0399508100407040c2d01c03d0440540500e001d00d4010906d0b8001c0010141440022074080f50f10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 451241636 1250 451240386 451240417
    0xf060c010203011d042d05010e060603060916170c10090503010c050a0503070305060319050307110910030b09010b04020d0b0a1a12040f080c070905130c03110a030b01060e0102060c 79
    0xc1d803221b0070112158040c241d1112050a0ba1040000c000340306d8a441c000761040101700c0703071404008052070260000c010354041d4008080d080d00e1000c00300031090030740d00d00841403103104080d000c41e0742c03902e417542550329400612510a00c1407190401003800a50b10150b000740103081901c00142c51301d00c208014031000030710400c0040d00692090380450f4101100400760340c0c03100d290707009404010301c08030400d40301504005a803004004140782c00c0d4403465015600d080c402d2a200460b0f07a15404a0b20000d091900900002420101c0c01c1d48810605400240115245c88141d19000014980003c443c1e004840245010400001d0f901800e12100c0c80b0342c111070320b4034201d8030100521660140007115586442c7c0750000000c2c51a02c0608900e41190001b84662854603040c4030070344030f000c2c04080200494990b000003241d00c03440ca03c41070703d401030001c1045030070201c081824107045500c058512020140007082e003541c4241d041201c01d07000d90803243c20b034840d11942d0809100310300c82c0044014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 451242886 1250 451241636 451241663
    0x201020f0f090a05120d110c030a08030411100c051902091b07020d08030f010b09010c080f1b01051b03061f050f0d0c0801091a09060f060c010203011d04 67
    0x21490001045100070150a1512a1341c0d20000720301c1c50105042c020358190072801090032810390006803103840e481804001c10700c116030000800d440304802e01000d00403040c0000007030f041c40300c41140107031000c0c8081e144580388140050005c0862002c00c104a40c0c0c0d0062001c0c41e000510007582d54010382350010034007044c5440b0ac00c0707031280b07040300a9203194000b078080c0003ca01607580d05403030071055405012000e0342ea160101c14a07841c014143c0007041c00c14003c1c443d40e4035a036400341d40c00d12682d51001509540e040c6a4164000c3c40c0035002c2342c100030310300c2e00c19400300080c4103400c428020450b4482101100b07440303000600950004403802600040072510709402607900c4034400729000c1160510310324085800100c05044c0c1c2c080c10440303001d25201d2010102540e803140341540100002001006085401ca203d40041e0701c00712011403081d0b46100200b6480d944807503414005203002403280f40c1d5048854459030107034109200702400b2a40200d8007140f004200c044640c403c0358040070446164 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 451244136 1250 451242886 451242907
    0x81605040c050a200a0c0b130506031e04030c0510061406040803161a0c04140103050f041101090b0715151a0708040b0408031b070510082a1305010201020f 68
    0x81d2078000d03a502e40c40c818172000b44081030001145001424030110b4441c4c0e0790301c00c44c0d0303500004603180d80118050042001013003c802c0b07107282d54845150a4101421441c3ca50342012078401c4010180500940103464206c12a44803a80c0f054046406402d6944501c3e0b07003100401c03806004500c20300c980c45d0000c011220381101c140208980b15442030402c8c0c10007540c100b036001c0e10b00c0811500d04005580c0000c00f4451180d150a19014403003007442d042c0113514103140301002e031481c041d1000f4140d641f070740c401c036000e680540400e0300542000c1c7e20070382d0dc43e6002d00b480711942d01c80a1103482103616003007441800078030080099041c6c50400001220006022030100c0b41c5910120096543d41000e100200e000340d1b51000610081001c8001940c41d94409075a500e60380b0221054480c140d400810200160f1b01e13103c00340ea00c00c0d00b0a041011071562904a04015603041c1c281c540081c002c0040801c00e0455110040c0058000680341e13a8000781c0c81e207005908074842d8104160000d00300b0710004080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 451245386 1250 451244136 451244177
    0xb01090303030f0e01020703020706020f030301140904020a090e2505180a06050a030602091915030209030f030c010c020607030e0709020f0c15011418040602070c081605040c050a 78
    0x102e448800c00201a070610291328220382200074100c0040e080308a007004500c5e8100101000358200d600075529552410f060f103c0a0780d4041c002c00e0090100c600060103550b40c41c5803107401031070080c01c00d0010282c00c111094442c0302c0c010480420503034441c07000c070381c140c0c412407a982074030b202504403201101007069008d441c0c40000c2c280c440c05901e8103004989616840d06910013103204180150702c5031800b108000706d80418802070010301180410420102100b441300e4110070509040060343c0c1e00c0c03c01c000c2428020000b10000311341c44002034925408a056200006012060f800d4401c0342d107450340118251802c1c00c180c036820303501c0201d09100c03941c01540144844041c111240e40340040c0300500c1418100700d071082001c524101001000404109444e10403071030301c03c41e00400c80d00c0c86000c003220013500144c0702420071a030228041c42001801075925010b0010a03040742c4a6040252a0304411002401a0b81c0110302307040040703600303501900c1517070b6082c811600c8000090802c420b840c82d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 451246636 1250 451245386 451245401
    0x11508150906240a080105010804110108190504080d050106050a050403030f1b1112010e10020a030b030610211a1017071508071b050307080d0e0708010b0109030303 72
    0x7803120400c4100b007000c421082001a000c8402c0c4003e40d10b440c0c9406014000e81c90513030146051164410400001500c004161002480d003424483d58540b2140b5403500c0c4820080410944d092030321092005010394030000d070104100d1882c041c41283e07210841201d10740901d103000004908240820310000b4001d09141c460170040f440c0064140c810084050303417035403124006550300b48105014505504003680b41c0303448600310100030b001514150f45d0703540e07030f800c81c0b03140c0500d900f80d0118a003c0c81504c643c1100241d0a001801c40b005030402d100c1c030021074103a51203139424151010004481030903440c40440101904003404428051191600442c0c031440241407511010f500040840d4200c030b00d0a000b00d500050740001c0c150035017004100111281084401c80500034107808001a581d4091800d14041c443c0e0b51480c4841c0c0144d148c20341c550301404500602210001c030f511540300a40358018024882510100c80c0c8036980c40302860300700c0714510251030014000c001c0600209029400422 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 451247886 1250 451246636 451246639
    0x60303170402150d0b01090b031605130801110c060f13020d060e060703090c0f08060106050a05071e110f0306060d020a0305010509060619060c030e0301140708011508150906 76
    0x1140510f1480c964080d0360700140072000030700c3c3d403a51100d142e942d100d03032144050141e41201d1880d608010844da1035907958010400100030000030144144068481010001c001800003400802803812596000e038100e014481100d00c191000502019101c1402d54042c07000104100d482002c2c680a00100d01d00000d0309840540e211508681d011808100c0c2a105002c25035000580c2003403481c02c840128850761104410402003c4103001410000c14901d0440702a81006582ca140d0640152040d00076144058a401850080d01e4100015a40c1680308144141d0600c03154800030030820206486010311a50103034032140004071942011403860102d40e000604150a4650f04e6960a09580c0c0403204c60030250030000c24001c4605042e40045900984460701140c1d072410008020301031941000007904009d16003400d40c419031002e50111981945200d0b0211407460303e64005042c00e40c3c01e100f011041d41c0e20b1f42a20503481c0c400c2141e240078800c401d5400f504044100104540108082e1409 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 451249136 1250 451247886 451247899
    0x302100507020d1b08010b1509041d071512020c0d030c090801110901021207030c290f01080c030703080315150d050702150f07030f0e1f050a060303170402 68
    0x480214048500d5440328000c0d90031010b413942d0524003510700352030340c444005000b9a580c2c80c201d854505094191000d0341025500020b401b40451a10362070350910340b03610090f81c0606034000c19050f4840c095120b01c1c02c0103440c0c00302d0303081002035107104a100794542d0f1101a04402c0d620050341e8803c0e000750031a040a80f601c07900b21500ca6030ba25007101ea40003007600762920000b40b00350007540c045c0b04007201d41100e1803e9504161013034071301910103150b44100030a07000705941002103800d0f5021415503980c10740098100309181c900b410b82c040c10001e01030115030780301c0c031a20800d1501c2c000803c2000d4983c0a41d1150a58940c0c032071181d030406807464000d03404034642072581042e030515009410302101134000403d9a003011240682000e01414280c1c2c10355541004102001c408240219004412440d0000e04142c0c1422100e00410a8040400042c011480000c034400c07880a014a82801407030010050ba49503440f0308001c4500c64800200070a044461004110001c003c6041d807140c00a4540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 451250386 1250 451249136 451249159
    0x1020309060f041a0301240302121501080117030a0e04140702252d150c05010f1503030f0e1302270f06130503070609061701030210050702 61
    0x20842d800580948801000120701008131841c9500c1e040600c0100d0082c540ca954107011048030840000003000c0049060307003400c69915842a41102c20010600300d802050342450034210a1440c0c880f0141030001c0c031b07172030000705100000312032403850b021101004628065107001e068880d003203c4001140d0166440c02d02108100d07221100b240304081c079502070205190300d00790403030101e511a1040c503c5011a114140725116812604030f01551241407295522a541c00c81c288245100360407a0840940203000c4d50151500b0070050840544500024810b00340360140510449550311940301608060f03070420000709000d550704003410003180c500b1405850035100441c01110a20191880d640c0d40040c2400000c2d10f0710110300010105082400c102c01c600d000002c04250000307072018415040040c4403120b140007a03045900800c0041c040d0341f2020b64078840900b50440c0791080d00d0101da4081c500000966100813802d05a03940240780203c6c0d928a00411a0550805141244c200240c40c29 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 451251636 1250 451250386 451250389
    0x9150705160203100207061b030e0601060c06020d0e010b13020c07060c1b0e0712090203100f0207020307141f121109120a03020d030209010509040506040b120d0305070806030a060b01020309 83
    0x5c3c0301d418010318001c19051907a000d041039180344a99440c00301841d014ac0308150180218105044a14500d030159611100382800402803040d800030742e11031482c10103c58000c4c01c06400010310035000300d8944007108541032400e0180d2191083d0702c1d903103030808802805182d0207038011190842c003884402d8501d80c9172450283d042c1015030402a56001d03842c0402c0072030707a844020040c01183c554804d01210361640c0c0801d0399801060601c8a84544481580c808100703140c1c1500c0398150001c049508882d40c440d01c000d62940d11000d4203024143c00c0c07000401c142904840118040111340e2400740f029074610a60340101300420982854050030030124030180c0e18682c0b0304107603400c0407001e40b090360074a282c080d10f0041c1e410380403001d040c018450002c072a0f82110684a40c244241c4000c1070550361280018001c0000c1d0b43d01ca54000c080c04c844a2400300300261308844140140c80c10001c45e12011005d480d0140708450103645640211030b0f250014038030780c1080f00c04143c180112810140c0030710 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 451252886 1250 451251636 451251641
    0x2603090303031816060f0c03020f011521030917210a08100f0306021303060903080a0b03031606090c0f090e060c0a090303141e030915070516020310 65
    0x10b0303c03000c20000300c0c20742c0c1880c0c482c18008042c802d024809030010303c0d4078100018201e600c80c203d11b18180105013102c807007031600074082c030401d01d1440300080100d00b10100c2110aa000c090092150f900c100f0326039a402d401c1400b642c044001d401d62565140a448c00d41e0142c07803070001040d409141d01403400304440c6c0100340075269407a800403000e640d440305960400140b0003a030051048180e0240a5801c000401c0c8820b490340940e42c010a0240c0d0b45e40d42c0c28903110030800554002040545040c3c15407052581c01040b2502903010280305200040c02c1404042d41c13402180d00c661102041c07480c061000075013651001a130180b092619400c075941c0c4144400e007600380c039409034516030f44a060040d5101402d1200b281d0001c90045440d041c0a0300302002084c5041a010003810b1008104100140da640d007001c7ea000259088100c2c4405611b0702c01c00c0c007003500141d504289a00c11941c004c81c4420b6076030f0b01d542c403559403917841905041003039080f00e507452409031044c0c0c0c2500800c0c0404003101c080b030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 451254136 1250 451252886 451252891
    0x62904142407060906051003120c080403080409020a020f070302010815031504060e010609050f060621070504090b2706010c050318030c0d0c06031d0d1106060604260309030303 77
    0x41c3c02c0025880124100501907030750007441460282c002d18018000a502901d8021076040c03149010590380d0054540b03806184500d4202a044000100c2c00040301020364000740540303909503081e40c60745940740580703c1d551001400003e0200318424000341d0300403030240c5910302800000b02200c250400551030f64400300401e0351306403045910b03a280d202540109019031f00081200385820403003854442184080941c0c05002c0078071800000402003182a0900300d082c6118501440c044014201000e018104d980305104c5d140c207060804007404e9952811503001003960100031800080111500b80305680007000420181c1480120340404020503010405040344400c039002950740650b10008241c03402c004e0003c05441885070000344c2000550240c00c070411140070781000b15204c01403084240a00a1103100c00c030320303071141002640c1d0480e4071100e00d0761842e16403016112642c64000901c107192045014882000101c00c426030000d55035150100041004c40c41070301d060201c1e150000e0b0450707000303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 451255386 1250 451254136 451254143
    0x4030201050f2809050304031b03050105011401050a111606170109061d070c02090f100608071b0206160f03090603051005010819062904142407 63
    0x1103200300b02440080c5001c032500407030f80c545002c50003140300340302c040800540040c3c0d001c55034030341c964030701046810802c0d00c0103154019240080c80c0390349000300d0340c00e407454801941c541d8202400000c2c4080002c801d4244440181d462900d0617074446400d8410b241040301c130391a588210142c80c4c0750000e982c901c0700d01825455640c80b5003440c51111000c903900041e001001c91516040c000c028510803891034100410201b8030100b80c50340d4414041e034a50301e130800041d4028140c42c0400c560b010318404032600c56004401013410454840d02c040b506088101c5140020524450101c1001158500350001c2144020716a500c2c00c0c030011581e90b0961101d103401c03286480d40f10400f408158100344420042c25003460100001e20341481e0401c01d0100900c40c4506108616000c12442400a04180005500f200c0d080c01a075543e004003240051910880340b0600c403031164400410b014050480d1f0403a0401036405c074514420b4020072099040103840f216401c034030001c00e0902c004250380907060340ca00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 451256636 1250 451255386 451255391
    0x4030c051603020a15090302120709051305150106080a3306110316060b012318090c18030a0f030512060405090601062f1b062d0409020304030201 64
    0x10b1803040c0b010140994000725240d0500c105c88066155001c9900022241c04035040728403d2a4042e41504040042d08140a614100801c014186421008800c1114810003c0303030f4440700c01e03a4541d02039402c203015020000b400c050101e14003d001d42c000c02404074500b0040020080d260b1040e107043c01e0041c0801c20a506401e9040044a80080b11002c2819140c405503280c050b41d1406200410400130340100030a55030012a8100d922444c0c00c40c907882c00000c1005d02158840600940b607030001d240c3d008219210107041003d03410309182c50b90144240002c524100500b8610408145004c807403800c0d090b100e4a2020310200300d904001603605130081c0c80c1d055039001110300c150000c00c7c0c000c0403203000c0ca04100c1408000c420005525044543c0d41c50081401543d22032202c001c5010b01d0811015403071022052800c200340840c101c080e40400034103511504040006202c0702d07002c0d00c04107d0380800d20080c8801c4652680400100e86400d14014034601510349003c00101e800a0310180c0041c0e5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 451257886 1250 451256636 451256639
    0xa030204051f09171018080d09110301090308220b0106170c04050609090a060b0d0501050f030114070f090302040504060c030e1609091110080a0b10080c0304030c0516 73
    0x240c0240c128000b40410541500258007480307100c070f6940900d080d12080f8107a51b0401c03180e0814400a0707115056901c02180c543d1040d0040d8003c010305400d1009441e40540c10812500c4c9203014418010441c1d49500c1d00c1480d5550207040710b1146243e40945548181c070300944000003400c10b503680e4040c0c515038480039400310040e804007074a070000070301001b4050800c000c14800380c2d480e1810b540d80b03c00102c13000c45941e500e48074944040c1403640c0c00008a010042010750103001190049030503500181d4407440c070201000101405e89002142c520758042c21f080c086100f003441203407505002511800c00208040c0c2c2c0390b012408850088034191085940c402400038080d50501500c2d0221240d07500400030044076808001d00704d107682c425820016503a410050400061010351031420358000c0c110008030611003805403903040220b4482240f070380781400d408128581511a10302580041e540c041030b0755140c1c565454240c0c800381055040c8200905500001042081807010000600c0070000046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 451258992 1106 451257886 451257949
    0x7030305040e070216090b090a0c08011a07081303020f090c03180f0d020c031002030f04030f0e030a03031a0108090c0d0c1203030605120319050a03020405 68
    0x712a0050001b0700d0000c03d5201035000b20382a99048016070300c950b41c3e10200d404d008002c1c400310318990300621214070200150a181e82c1003555039403502d180d5440300c0360a030304101d074601d40c20580719000b80114145640d400c5005007044c1d54184280c10322030791a0070300d80001040d840381c201400c3e003800204002008000b26a0385941c0603100c1c91030f09010300a494100c0310382c109020f403080728141c40380050f552084a04c5a402810f0409041e202d540d0115030710044154000c0c1005450fa10080f1152340510504104a1081d1070006071440c240112202c1c005c060020541030040c8002080341518022403181e1840104540140e4845054613050031041841c4c1c20819469000c04920b904040e01a07100f0010b0390740c11a0f00d110501d182d0519587d59221f070b448500c85000200800070b103192b004401622440c2000d090241c2455124808100d0034442d0540a00f03400030000c0401642 = true := by decide +kernel

theorem cover : BRFrame.Cov 451079136 451258992 := by
  have h0 := BRFrame.cov_init 451079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 451079136 ≤ n) (h2 : n < 451258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
