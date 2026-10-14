-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0495
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:05:54.524042+00:00
-- url     : https://prove2.me/submissions/bd4c06a8-61df-48f9-9f07-c949b56346e9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 88848921 ≤ n < 89028777 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 88850171 1250 88848921 88848937
    0x121f0e070911190912080304030c020604090c03050a02031b0304060b0607060504150b0f040b0a0503010606020705010f0c0305091e180a1401081b0a080609060a1410030615031403 78
    0x1000f14070062484125030a004074002c1c000d22002d1a510840450700d0352001e554414800d141511840040c2d80c046181600160b000c040d8068550301e4961400d50035009450740010040e40071421403411170400e0b0501591031300c14421a440c000040380500050f50491051820040c1100369101403610300040141801c4030b094840b83c001509250100c03999010701000904018100c0115400702010007000304414040c0b10b0380a07050305070003c0d07140c5003801504020003080c0c010300302c2180703410009860100781002010400c1602c80000000039080020303180c4054050300d020200081c03c80308145003e90544940d0740c0050510101c0c0715004241c2007607481148142310070302c42e010a81c600c0b0031001c04203018004142d0800710200010f054071000f031441980c0000c10622000e035560700c605051041c16691490a500400c1c00c0040402e1940201d20610115044580b02d07440c0884924148413004d000c018a0140c80e400c0012410880c07030001406541c0016060a0380c1c580c0d20f0303c131581e035481003013 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 88851421 1250 88850171 88850197
    0x9091505010b0703121109030f0c0a0803070b010e18011410050114030a0e0319020d020c090114040509030906040b0304060f09050d03020a020106170a02121f0e070911 73
    0x40089042200e90058407400f5605480c1c010011601c0d01c100405001ca080303421299010510030050140d41c10000d0b00e06d0b40c184000944107000c007520600440d10000c2d0401c0d0010341c010000c05000130104404141181c1806090a80c0381e01c0c4d55250130f4150082d0b000803412036007000302440c0d105a5810030302c2d024000311072082900a0b9500c005682c40706180d00c1c0c20010050070310000719100b0701600f08028100c0d000003030720b00d0411a20340c0b07200400810707520003005a00c843d030709010042d010800d401c4900070844030380020b90300d084040006440707003000540c011615000800c1a400023002600d14802c00100001e494944405070301d075040c0c0080b1002e0b141681046010f90780f1002c1172040100c15904007014061040d032104058000e580982d4040d4115960382030300140301c1d0141580000c1000001001d800d10b4102ca004000390454100300c1684180c10102081003009600400540c0740c904400001c191040340c12015400c1403499441405440d040110031401d00144c1401007a085422030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 88852671 1250 88851421 88851431
    0x61808030c0a0806010905030a0602130b040b030702070b18040902030f061603050a0902030a081305030a060618050106080712020f03010905070f08060d020f06070609060b10140901050703020304090915 88
    0x800444071040d440c407c842c2c154100e0310380303600801d0031600101080c80c016200c00d01180c3d40c80c03844c0d4490350b115502c032112522010040c0100c0943c1485580000c20ba07200401d070805d09850b900c003010301044040548a26551802002113450911441481c045180c00341d0784070f8074115002e00c44040c0302074a0dc0002910b49800102a1301d8280718000b0741d5034000d03004183d10080c0355030307a001a5200d04110141082c182d00e0025042d50104801c8030094452030002c0783e01841c149001201c03030703900c10410b0f2010307003010014019141c0c80030b080e03640106540350140da6990f140c3c00c003600a1003014a000c940110000010072642c00507084980100190740d40d140729000061000c8501080a980701c0d42d2090807400402c0161511a220400c0424000e0146c0c0ca44141360350b42ca0200c440640044443c41d0f181d9102c98281c2c500600745c12004a088e007050800903c0c5031060b0406171081d106818140500464003d05041c4204182c40181254080410403c003990501e0003c04007504083c4000e94140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 88853921 1250 88852671 88852681
    0x240510080405071a040305010204030303090c060305060d1203140405010c0f080906010e04060605060703020d03110f030f0703090507030f02400b270a0902030307061808030c0a08 78
    0x1510840d1040b9008400b8050380d03404c24a0744800d0880c4103485400c40e4009100c0400811001e100420003540301c2c0e103001549100c503280190030280d00d68410f0040c18503000420806d80c03181003c801103542d201000216a055400003070f0b0023801c84002c2c0190101d04503041000f04281540700360207020041d11215008181c002007194503240841e00e04020740c101000402c4010f030078009c0c154000e445044040b9941da106c03404203000d170b01708d1039007075005a0102040e011b040da050f11908001500010800d880c1045290480d0210310001c3c1c12295920b0a181c0001d000a1190380840c051680c00025030b101940d8a003428401d00c0080310042e0705c40c662203514a400c03451441c010303a0070329a2030f6400183c14241202080b07906413240400406641d155850050150340303400714060181d00134002411040d4100384040d580b1500105254001441c00c00c3d03040140c0d03000810764000c1d55210f40c0124071a09070019900300b04040c481c0090180d400801030000764100c010240240e640345031f951405035524 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 88855171 1250 88853921 88853927
    0x51e0d0e0a08070308060105040b0a02010213080c0a14040b03030a020a06050901090b01050f0103090512040f0902030408160804030203150601080907181a0a08070e07090302010e13240510 82
    0x30401090031208004580001c3e0040128a42c0614141807843c00c2ca59503022414ad0742d4414000680144d500181c400514956075180303102a00b140300c000c026045840703002c69001c0e5114020303a4075100b20707034042010070b41d940e8000e1180c156018050ba515190b81034806595106400412038000b0304000026500fa0414030802080c144c01c4044542d041c1d113808103002441080d4900c8a04250b1280d1090b4003046040004052400d13003404c1082c1d5039458000104070340002500310000040c010000d1001246e9541c0c16543d8400c1c401080c50300714983d9141861180c8142d40c0000d4250042014181c0514002d402c01485a10280c0750394400d81d0f01d200b0800e03240c3e41c090250b6070100072100054189035495030300c09018040880c4048000e05660340000d1070802e070a6200c95426480b0401c148021444442c1c415044041410216a80e80c1582d0019001e260154080360051306143c401103000c100039084858038105104000e083c55082408041581d001405441c0c09900142c0402c051584 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 88856421 1250 88855171 88855183
    0x1082a0a09051512040b0c07020d0b01060e010503010308180118081501080606031b0307090e030a02010e060c0304080901030209040c09080727050a090206040905010e0105010e030d0807051e0d0e 85
    0x71500c000606140d1361a46c0b44054041d015001c1008070009000a000507124044083e1110340230b02c4c00035506625040d00180060342841c00107040081c24401000028617140c2030b2000301d0340d1003500f11841024000100c4043ca03140b0080c1d14070301c0c40c0420002c0c2030000031030044014815000100c0c403da0304c800b0f59a80e0307040c050350815015402540b03042d442102d87d1112a50001c001025510b039195200a0502656039043d00d4402c9a00001000c54150ba024401d1640c040403113805442140342c58101902d07503010003440a4040000040d4000045c3c2c4242e040302e0320070790002c100f0413610300300c0d0500604142441c06144141d10aa83d004070380c0c0740c2c40141380c055400c20180900c0c0070601c040e5103c4041d0602a0804808940ba0007a040059540002a0000c2c1564410003c2d25601d001400d0801c110182d001c0f6040c805c8074010020700d40c6022a1800031003c3c681400341964441d0132080710540306800702e490a80c450020f4919010b802440208141051100c05008a040040c0c5081d2a80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 88857671 1250 88856421 88856437
    0x9010b0f0901081b270d0201020613020303040e0106030f06060503011a09120102030708090706090b030103021207051201090302070b03010b1c110f0408150601082a0a090515 76
    0x1540c00e01c603010666101e098002c0d8029022508001c00f0f8242e001c050420743c0000c840d010742c040912150014850045403900409a0119505413a031080750b00081d45840c006080f0440710f86403024000155101041100c00402490780340d00625030b95104010700404c0502d003910315803800c06100041752440b07203003275074143e4000c0c0811010001485024514070340c009180c09030070810035484403042d41ca080c40610311034002a200c1108501c0e011114908120440d00101c0c280640713804140466108034043c0e82c1500ea06640c0007244030317803400e107441c42c1c0488d40c0e020b541c0c0080701c0310000c400f001d030641203490468880c0d001c5508058840070304c0140c5020902070710704441c8044c41542c0c4164161002e107015030700446800030741410a214280000d03404401c5007102140c000604020700700c4104581c200000050403180135606141d4002480b41d60040c04201821211689450305019942d0102048204040409581d0001c1d84030140880005101e054420f400f400801c200c2420f035030341111050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 88858921 1250 88857671 88857697
    0xf160c05060105010e0a09060b0405010809010207030e040c050c010603032303091002071a10031e11040b03010e0312010f0f081c0504180501050405160504120f12080609010b 76
    0x50f801c201c01150748144010600303500c041d051b400001d202c425449000c02801a80440c950341c0e6042500250003400c01400d511a04c0e88100309007400b203a4040b20b880743e8150100c0d40851000d0911000710388900807088404001d500c0d02c0c00010805070440071a9001103040c961144141590072001301550004540314076054119481e1012007030b000d5402801060f101380014800310000324180c500c80c1004550251880301407601c02c0c010300010700d0b15180c014405050407092407409035668a2150070b104165401191585036a9009030703800e40054204c650108210390310760809108440000c40280b02d01c031304032800c800c4045074040d00380c5201810348003100014010008442c46a0140b61000002d0604020083c480450381140302030920032664a0420040313007550620041204a484c013503d030040c50351007003c1c0c80d00099009802d54007110540c00d400018441c00f070500103401c102c5008000c0000c5030b0702c0b42c145401600449203c0c080d44041d00e5018046c0e032120580c145a100d02c03070410200c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 88860171 1250 88858921 88858933
    0x30f0f15040314030f07090e07020a030309080d0f0902090105030a350d0e0609071d0406060b1215010c0c0b16050111070b06041401170c06030f160c05 66
    0x20416110400c1900903200f880d04100f8050401c001e01e0007a0015070307404041680d03007070510100940c000340520103440c1c4a18117207071030308180c60003075030703802c081c3d40010309054640c500e00040c0314200040c1c8004400780301d01803082c07021101106004142c0300004912035610fa10000c5401e050018568204a600841540000c60003100100261404498000b404082000c07030307590001c44d1302c0140440c207100d040085132180c110100a800c011004000c00401e0b40900c0080101d5000d220002c0002c00817251200000c1d191824180b0150200d900048864500014002d5100c007040c030610b4429961450040710381d13207220004540707540e42800040d00c1101500418881d100b07160000707000c01c0b902000d0403031207029665030b020700303688240341c080282580c0450740e5820300600750419031344198111001c0007108a000b00c0c2000c0544103009001040300d00c100c40310a820820410300c00088002003400391245000d20700d580030a2403c55000c6510405c84681c2640e07203010740342c001c00c455403000107407170 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 88861421 1250 88860171 88860193
    0x131a06060708030903041a0403050616050901050a020106150801031b080309040f0e0a1b09060807150903200109120201320c030a02190b010b030a0b060307030b030f0f 73
    0x10b51034101030b2415900d80000c1000080c40d004803040c0224100c25640665150381c69401c02c5424030b0300040042103130042d82d203070540080c0c2e480021144106001d08040741c80350427034141280101410b4120070310810508000f2404240c0246c41903040761300c10041030840030303074925500072901c140388500c03034141d442400030b80718074581b540006600e8070345d0304c0000850441048409142c011101c000340d074082c41169201560040700c4010502a045428090124610b02a41d09030741e0782d072510440048605444029240a00c2108a0402103420455044641000710050502c25a69460346800b0130aa15030004081200c03090a204090301611014014400f4072101c40000140700e8441d403030300c1f0720044518598401c550180141c2d02030f007401142c403580454400f91400c0000704034849168a40e03c02c1c880080c848650050654583d0b603900c03600c03034031041e80b8040908100c42070561f00800c048104203105600d540041d4002c2402c504441c80403070302004043d02c0d0b44a00295002541105042c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 88862671 1250 88861421 88861433
    0x3040f02040b03030d1512020105030103020d0606080d0f0207050108040f060c021f0603050f07030f060b030c221104140d1127060103020f2203020405131a060607 71
    0xa10018006800400d0341c45110001034119881040d920700e2003962031141050a400a1403a0000750080f021010301070400c40e0000381c418041444020f1140b000240c1c020204040c41d08160014101c3d40c080320f050040001000e054444a1611035005228107540043e05601c100310903401103400c181700c0010200c3c0d940341c2c1c0b07010b0310100b50300c40c007503220310a009101d81c03600c07141040c100b4481800000301e0034190b00e015400d11041d6143c07444168030200040c4081f80280304081d02d8158002e0b0001142004d0801107400c00d40d2410410f80d001c0440c4800020b65000348841482e1780d40c8030340d0f040190080d9000e00078400d000c0c2e80102e4103180703461504041076040655040c20124095045100301092050006200040240074070816020b201445981d280c0d030a44c1c605c0e00038509007801d504040d02400001e02900030300c00b6904004007400003d9850203540d06a24010b9600a031040c0a00c0c585583c6c1114030102d6604212008035501c000094070300302d0f01304010300420000301591f240005503141c007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 88863921 1250 88862671 88862693
    0x50901111c0b03060c09030c060a1b031b030c050d02010e100f06050d050106050109090c0e0103092108070e06190e0604120b01180b030a0803190f0902030c03030a02030304 75
    0x420440e9641042c0496aa0030042c0c2803040c50201c014a6a03050341500f41070401410f140d120b13008000901c100c6a81a03041181c0d551150b28a091042d01c00302e240c18200c807410000c0c00a42c46008500c0030700c078145940f2018400034240554202d0b102905650001c0b4202d800c6546148102d4011034140300c80d848080d0010303a1540d020700008110f0707588800005108402c051000c880d02ea40d00c003c100015604100e440c00104140c02d03013000b080039181c0c0d000d003042c0444030240c1c0c10507a40d14050000c106003a50300025094100c01d071101001041500504111001d540c842c010402000c500100e5292281c101d44940e400c1d00d0242020f100400da090b10042d010603c090b600c481c0c03e001c0424088040e4041c005810b01404080c4007a51402c402c0020340803006255500b19828115031038810303140003c4c00c000c8258000f80c03680d82c83e604c0c502c0030090b90b0340c1203800d0160941004000c446d0704541d0b07000181c44038001c07030540780d43e03051107000c06507284038400d480800741e0014400140400c1c1d0300700389 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 88865171 1250 88863921 88863967
    0x90a0f080c030408060a0204030210090e1302130c091a090a14040e2b08010509040f080d0f0b090a0c02071403010b040606050a03050a0513081809070206070305090111 73
    0x3143c0c24240c46902050900d101101c0841c01b140e4080b6040095240400c00100640c48904018034003a003094190b400e48030313000f0005c6954080035609031045403110600481030501c0e807002004081090b50000f000800688603080004011155010000c9401411203c1220008101c114090310780340e0f41d052841010212280d01665803068948000000d00c607608143c810300f5074505100e6043c0704801d01000d1a1094001007010490041c4095118441c00320781154000c80c0c0455403080c10315002d640e5205000381154801e00b40b00550f0203041441d00201c1c0c00c84002c07107400400f076840441c2e1000311030061408100581c41003004002d03030a8072000401d0600405000800d01c01280c001013803c0d100c03203030f01c14000104005011211603074188038141e00014040000c3c005401c080d02c3e03200d882485400040c101c2440051001308c40800503031452035072072000d01005464500030781d010303450305412501080443d08000004a80850611681407044050034003582801d401c1c4241512040e15201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 88866421 1250 88865171 88865173
    0x14030a1b08030307020d02070e0606040b033313090b18030904090309050102010b0d03050f18040504050705030607111c03140a0e0f03040e0402190f08060f090a0f080c 73
    0x40200e25181d0a2000758403c01440d002003900c100e0604000785480c5d1640d00003526100210144801a83c03140200c0e400c0f900744030841034170b81e100d042607209000b48204500b19124142d1591a4100e40c4042490600d4541142c1d0242440455420002651511070004184074007034000155410b034240b0b40020000742c8801200e0130601c140b0045000c960801c0f40c207801007284a80704000c503681c2400780d4964000251030354051400342d0b80e4081e01a0042400c5030610305408114842c141007482e4200c0d0340717080300500900c41c43c201402c3c0b80c2d07214050380c003d182c02030040c08000345000340903003048406001144024401d501000b0003c8044130503919800082503142d0b141c0048000400742014000d24484000095a01d44064164034000c5080344e00150341d001484200300c2d481101d24040c0d0b00c96010340d0596100d42e000c9600c00c0b003203200c5801101a44206200101e00d5150001d059481445001c8010b00c0c1603c40d502c89664400346194010040801e03c40850f0000c0c0c0d01ca8090131800780750b28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 88867671 1250 88866421 88866473
    0x2060304140613061d06010e06060f12061005040e06011d030d08090708120d020702011809021201050405060306040204110d0c020f0601061b20040c0e090114030a 71
    0x7511504180b410b58509440c9000581d110050201500c00d4041d81a6003040881c0c00e40084040035807aa401480307200701038042480010b103151102c0c801c8035588010241000e0341c9440c02120380001c007a041c1e629500816052403449110740c091021a0300740c80701003c0d2541b09985180044412002c103986011159004039060001e0303440401c1840e800c02000c0e140c0c1304441c44c22900320340c90a00c041c1d01000440c0e0104420601c030f41c04000889281c541d48640c05a640e0b4070030300040c0e0f45206010748040103120f140380c0001d5501c1c0301d680608941081c030690244e0740c0e641e803c02c00003501c00c00d076800340c2e051b0401408103005151650222302c0c10b0448600407814401204038501c2296014100c000151f04801c0034803041580c24410301d80036000609003c0d030510012070580b1104480038100070805014990f640e28265000c00d0b151040d820300510901c01072412240040240d580c3d42c9465005d080c1460001c1000510300c0741916017100040c004016083d01910340c40e0100d844852103107545264a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 88868921 1250 88867671 88867703
    0x1e0302040e011a010807050a0c140604030f020c03010204030308011e03060f06141e090c0706110403030216050105030a02091801090209090a270501020d06061110021602060304 77
    0x602400784100310000000030780e41c1c26021003c00310b440d40c22681d810007110104003c6403540040c00d03114032251030328080650740080e140c800481c2c0181c125035612031145008020405034001c241c0030f44000c899007529000444042814247d000f10301005000c680400e0043c405419403d000e071064004140e00c4c0c0300b07203a950341c8412003101d807120032002903103850314402d01008420880e10b0000c0e00e02a981090003031002040d0581c0120341c1560103108154510205540d00d41d42825036103000d07084401001310083c0f6070701c0a8074690181c070045001d030140b00045500301c0d10007112003048a4040e1102d41c82c0d42d03035400b01c2074000d6205a10003030f0b121081d148240c80880384440c1070b501800100c0c0c001640c0d015414100f02e0300070b5000341481a803504015107501e40425104034100d0090817006c038215040301c0e62411a029008682c0003840c000d180c10350015181758401030581516600c2d00680e41411048400c80c0d00b6841019a00c40340b40c02101004e03001418440006c650003070060702112007480700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 88870171 1250 88868921 88868929
    0x1d010308040312021c05030621100e0a0c0807060f02030c0607080709080703060504060b09090a03050f040530010213151701060507050d050301270e030c010203040501060b03010506041e0302 83
    0x81e04105e0710002d14040300b0090541091007000b2a81d240354409100d00329150341481d650707000d0400305080b529440e040c4103064004100030050499a1000740d541d11184c4525106959103001d100c1c81001942810354010b41078000310031200c08170384550181000d0b0303075021003e640c0c4402c0a480c0c0020040c00040024840500380041c1d80a540b141c1c001140300d04090500c40152a010460184150850000d01241034400207000e801258542040c6841d038103111000c19444c0035962209410120951b001f50000c00c88445180503a40d2440881404080c201642d50803401007003920024200152402e000c1c00b0308400d8110030607031081c942401a803400c007841c0021984203a1001002c60000b003010820041c0500902000140038648141075600d0a074800314100c000c170340c002098400403822200c8540064104144002d0b1042c101c030303030381c1528021140c000d60046400741c41c079510b4504040f4400d1581001c807030407124002c3c0a141082e0a00c140d0786d2141040d400700179102c0c45601000130068907 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 88871421 1250 88870171 88870213
    0xc020a0f0315060603020c2515170702030a090e0606071704061706060409020706141503010b0f0303030f0a0f050a0c030b030105010513020705031b071d01030804031202 74
    0x200c903a440e00280040100040c0541d183c0d5084101410b0050040ca20100d0780018541d40200c01007100151110307000707009000591090b000305035544205203002110a4100c4050008100c0d00890224255a0000c0403a01c1e402103400c102c000414490041004c0500810165001440146141c0c54040e440d607071a600481e811804070800f9201017410042290006503020b18510b180070702c0549031034200001074a41c49140034103814654003240301000e0007015400005801480030400ca50350510341c0c00c4005107a00e400c0300301d11035070030b0515031074440c1005035030032650303c0700070380254255141d881c08101001c03001800d03401105e6481880744041003c60080e940689400400020a0302c4821030040540784901d004a00aa0400e0010440c1e40c5030224454081080310038016240d10151601d2400c2d480744240e0340c2d01c42d04000741581d440410200d0410202c501850125204070825941248545424440501102c81c18081007003c1034500e030700d451008c041c0744140c40208250b014041c41030383c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 88872671 1250 88871421 88871423
    0x40207020127051203030c0313030201020c160504060b0c07090e190f060c1e03270b010f05030d08161407120806010c020a0b1e120a050703020c0d0c020a0f03 69
    0x2034082c0010002070815110100c14125030402451071490400c0074000700348800307010040d03030103400014601458402e50585050701c03880000d407241c400c1810880c02c03040c0e8050203031a108602c2d00000145000e0f00c881103a0060b44028007401c0324a1401400030001c01c101218400180581d1540108052030307021140d00c0c1900c140a05200c00042d401e015049401d6060070030144100b080884076004041c102a00304000f01d0f10303001c52074101601240e081f0a0628054100311030320070300b280040009103034206050b1112812401c01050b074401c2016a22107245922030041200310b40400e0005441c0015180e054025092172944542c5000e0340da036080d80141c0d030a1750b070341180d40400c5008070707840204143c0040c800d281020b070130203154001558014291207501d43c00540001c65003031800440e14203400c0600c03c511036644031020424141c0c4130220440e401d400c05481c20740050402030092098914002072007004003040300c1001d006448030030320410243d0b8001e0904000085140c48a07401130051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 88873921 1250 88872671 88872737
    0x20a0512030a030c0507031d01090b0a0c0203190f03050c03072f0910090f0608071206051b18030c040f06050f0f01020a080307030b0d060606080f0906060402070201 72
    0x9100442c0010200d850307421807182008030410a0b0004243e0140b80302506c25079880004946070039100059500c00c416920540c400100810809945904210602500360003542520b401d98040d1320344292010b078030760000380700c000103120340e1000c244518041e082442400781202c1c6040780544511541c115003600060a450640d02070030950450310f900c4030b4404000b514590182d061142d0304600f140030f140298202c0c55075400c5031400c846500c7d0080d4000300f440700e0a80d80040c0c0c03110030303826458090003010b071092030510000c6250642c1c0d00d15466106003c20001038105101e030600c2c01c407200c90030352029900d4458805840038555592060210700385040800040342481e200a02142094900303005104034454000101d4503600840c0d08400c4d16030100007903542c2da840e03c04c00c1d00213001d820360054104012410030b40c00c102c0700d07501c40425901c1c152a0060565200302c100703190082c00310350704e40f03d54105002040050429401514100d1300c1410300c400b001c034400c079801c4c0005803000003d00b14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 88875171 1250 88873921 88873927
    0x150a18080d0b24090604120b1605090603060105071103071404060905130f1a0405030703090902070c171e060106080106050309032208010e011b02010b0d0807020a051203 74
    0x80050381d40300e0354030104426039070b00310b0303008071076001820402402840c040c1a540010f0700c9102907490b0350071100505039141071581411540d04100c8814013044941800c0000000400312165001e201503500515004140c1841d6564900c0112440c0d0030988080314200c24010802100e65010303c41d14019002c5200300c1822800141c040101781c030520b0b40312a003628542020301c045025070700c040304581900584040d1b20a40b0078a000140b00b05030b1140140a80186170501081210110041180b2800380c2ea924034420b40300e40d000412485510001071150648031000c06c140200c0c0303114180c1c0900c0000c144c6004914a625a8200b94408502801c803908000300601803075070400c42e2940034145914000d03041d8606070f040d0981d0307807040041c80d001d168156413200c0200e03064292040b000d0f21108000348000101c0202684c06400000c0005820300c0b21880c04210041c814071071641400c1c2c00078000e130421141c81d110f4444035480154141d0700808042c5000c246521480f0100440072080e1000b150303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 88876421 1250 88875171 88875187
    0x1050417161205060f09030c030703030903030f06060f03050c0c07090f0f0c1b080d090b041101020303091b1311030907060314040201030c031410050a090905150a1808 73
    0x8404007103600710301105100400c281c0003042001484c40d90000c04040e440711140ca4200503549107014840c081c82451100054417800c1681c1600b004c0740880c4030b034806101803480c00f80e044003510761038001c0e03000040052080c021001c2c400c3e086030703400190a4205038034150300030980038103000440d00440c5c1c00a071110018607005031584910000880c8109041001003181c21004284c84a001152004041052036400a1140c1c1710102c1c0d68000c030001040050107064605400000000c95054900d1807501644410319400402100c5c403403d0490041d040308240026501480130240d0025a04003600840e550307681d04281c812412400203100b2210b40300c3c900f8400f928074002203900800d080500745065068941190401550020f50900780401e0001c40c9810890003801d159449000d02c50301c00b01030200303401e6032003e01400c9e642c09580039402982c8402200007a111541d8005141b644020008a080e6440c102103030b80000ac9010007140d00c141c3c0e618400038103006041c09582c441400100c03d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 88877671 1250 88876421 88876453
    0x4030c080c0f1201020c01060603090605181903030603050607050c06010b0c070603020702030c090c09010f03050c04121e061e1401090b01090b1c05060102070f050f01050417 76
    0x41404100400c41c1d201c18002081c0d20194000c40580a41c11440042440caa400c1d0141c45c8094042802003141e66500c2800402034420584207940440c600b42c0407034150140e031a404843c942c240380050850a08401000c40d001480440540415941300d8000c000210203100030341c002da8050b694652945c2440110303500305101a80074101d1550100800011080c2c0462080200c400500f001070300c40003207001103820038400300d80e21a406414402008500d00c8109c2c0078105842c1c0c20390b1503044100411409800b201c9040e18406298201131008111465010f40d0440e0024071400c0100c4a02c0c80300100b840105001003c00c840a980302d014145c81c02c010090b20f0b10317800795189030900c01042070501c010390740c0d6018001c981e20552603408200340e690240060a0040c4001c0240355652482940101000035523004c2803000d071070512012480c158170014402c1c0030b954040c082140c1407417800041102c42d80e451100c8034140401400005010032214004103c10000e050140152184d2a1285 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 88878921 1250 88877671 88877693
    0x209030c09130204050a02040b16050709060302090123030f0304061407020907120605130e0c06070203120a0c02041a0a05010807021203090a0b0106050a082505070c0302150403 77
    0x481d0041c52000e04210720802e0310100b402049405540002d00c949401c0400c3c0f0207482aa0401b21b0303000c200140c0d141d03d1018241c9002c800501940070340d04500d48a280c14015105548000fa40c4941e03d40018817020700420034416007010511003001c504118000828145031001c1401c2c06103800114081001a030801c80482403115840340252514006a0011314003000250560041202c590907620441d4080d50045020344070052150502819512000c0007419126a42c01080c0c010380d04e040d1044c5c104102954007140d0b00402400911800c0c03c020002a00310711101400c0084404101c0050380b503e04c00c0901c4e18444c00721074a682c50b545020711226107401e034042ea0412000008001e24031f070340413501c0d26869aa00101c1541d03511041e650500e0300a0b44400a070210700094000214107412100600030741c2029200e5200036a18500b0744042c0701d850300c8100c011181d1001c2501e0f011031103000200302d400d104d0051f9130940c58880c0c0224203031080c034400c80c5468800009040c402e03c080b414070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 88880171 1250 88878921 88878943
    0x2102130e040506070206041e1112070603060e0403090b0c0c06030f0f13020108060415030501060801050105090a06030f020f060c0609100f090c0e09100f0b0f03030a0f120608060a020903 81
    0x11b06403814030b40d03243d0094001d1502c2100b0f51829842682080000b205550b604c1d8a1004141034030001c0c4424481d52241401d224000200b0324142c00020808004001da900c034a415450711030384645060f0f00ca03440c1d50b00c14114142607000c1d207000207045640c1da0740a140102d41c2030f03100000d14900744892210102028107280218540d02d400700c00140e9011010690000d030944010410304060707040141108150741000308a5403d095001c1045001584854106c4800300d500b9212511450010742c00c032041400054120700d4070000210240c20a0700043e440610041c200c54608158034440a082040c2a142542690000d5614110040041c01000703c0d074004010304112403400e50b0b4405411707190350312403460134412074800110a004148901094100c00001c24024480c1a03200d0f48000c0070540805ca00c42c0320300c981c941c1064200002510b58510403034403500c1c85000d0600054500c00f5004589085503a116035000c1752107442804014000c0071026009a141e40ca903000b010308180005034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 88881421 1250 88880171 88880173
    0x3030f0e0607020f060901020102070f0501051005010503040b0103081803012417030904090203010902090403080702070b03010305060a09150207240c0c0b06010315081006060e012102130e0405060702 87
    0x2c0c01e000da92400e030601c80619080301c140350b60303035207010042c0e02902613941d010b4094842c0c01f404d132041c414190005803040400d1401c000c40f45440e140159100d020549000e4142c040c030300018800134522000901c0c0303200c1c051400e0101501e2800c0042d003928552142c401803100707465801200c040c000d1000001902c0c1c0d10010b1600a0700d030850281e80c1c0e0054580d42403065032a2122001952000e40c89810000c0e000780c25540c0030300e01410064101503042d40e00b00c4c01441000000201501d4600a0301e05a0750302c43c0103040d50b138440201c140045d000c124003d03518039070109561280760700c40340b00801d030180c850700100c0c45881c0c1c4407042c0c180c038260b040d1039081207900303000034901c0c0b2650201c3d020b41410b501002c4924035482c2d903801200200500d26400000500c0a400403c0c40f4a000864090780013586405002040d290340f0200c0301000c01d41e4600780411400310802900b10010a2018a80300803d0030041c101000d1429048681031558021000840c01030244020b001060129580c4116180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 88882671 1250 88881421 88881427
    0x5060307051921110d0501030c0e0f040b0a0c0e06030109060e010f050a0b03040c030203010203010b0301090c0c020f0d0303110a030b010f020a030212070206090904051b0306090706210603030f0e06 86
    0x11000014000700b910210201d0703594402c511041044c07001c3d5009040000c078100300c0c80d03841740341c100c02c2d6034540d000d1070f840e603081100012450344c9001d145c2d511542d4040b81c079038541e4880010080150040074a4a414044000e000f50030548030304001c0c5009103400000410020300d8034070141803009040e002800c00202100003481a07840380a40c42c0c0841e80ba03400c890340d890b5071f01e080c003e41030a219003000b581035000000000b8880140000345059540c031349420000011401030590ba18402c001000f50040c03202c0302e4003007452400c409440c612500906000c03071070300d2410f030b0040100e6100640c0440071a642e00030714045075a010305000c001c0b040700d000500f00000241c4010350790782c01e494010351000b58001008001c646030034064505002010b0654040d50a103454426182c0d440300d0451a81d00b8070b08d40f520411843c0005489009051440c081c0c29420308025003182c07801141015442280c05003850103001043c030788250b00065009036200a01d0a8800a00602280030500c903d4403843c0d0034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 88883921 1250 88882671 88882697
    0x10090501091406030403050c0304080d0513051906120b18071803030212031302091501030b060405010e040b0303040f031101030f052202011b030905030d030e1203040507050603070519 80
    0x20f200b100d4001c2d4040c1030098440c00340380c1c50181366101d00d4201d480103000b545103c11074a038000300501004000e00300000c95990321074003807000451480c0003044502110b00c2c010091140200c540e140b0708902000c0210740380c0481004a41c41c4032514010009040c069000c00150550203e103615416401e540751100751461034800a5a42c05258001940b1050000100e90580102850401100d9004d4025902407411018030004100c003441d607a070209080c10004d920a260001c01c690960b00140c4504941902920a110050544420b03883d00341c0300801c0049441c0040340c00c128021071103030b4880d10010756400001401da90703000c1e8001019500b044107110320903c14420361120400c2e03038000200070b602a40012155201d10440c00407a0610b050f01b03020525a00c116502c003950801d900716404000014400c030100c0c3c0f81c1030036a078560f13000b0440c4801015103040043d9045401102284e00c840c2e140d20018465a10980d1924041103001800ba0042e24107100741452580882c24010081c0c000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 88885171 1250 88883921 88883929
    0xc01020307051c02030403120806120309030a110406030204020f04031704150c0213020a09080106050d080301180b040c050307170103020a06050a02010e07060c0201080c250201020c100905010914 85
    0x382c52108031026583d40c009106030341c82003003900d00845e040440045524030b03d08001c2c1c42020156829400355000c8003080c00701d00400001c44580000c0070b0001c010703014003a214082112803000e2282d40c425261500000941d40398000340c812400d208518513078907490b502c1d0507540740c1202c07500000514000d0100300023a43c100e0000fa204403071103042c002500310075440080c0707881c0e82240c80310340f410b13201040750303003616501440580a94080c42c00800c449a02d802c10044850071070700c4010880541000103003e14500400f1610102021480100b00b0121210001742986e40e8003a0b0344001401c0441013100d00342d440900e040719117107044030603141765043d41c010401d40b4010780a480c1c1480000245c0c11421407003507112074028600c21b0b05403400b1548a0100a100060940080c0d00144507540800c0140b050a41241e005043d01d0096001035200d036203c011040f0340104050341540503030a4040a1511408005841c81c01169141c10350329003014000340c03001107190080f84121040b22008103d6880f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 88886421 1250 88885171 88885183
    0x110301230603010b0c0102090907020f0f01110f1308030408060403090909120e0a0306050f0618012d09090c05130606140c070302030d0809060a1a100516050f0c0102030705 75
    0x24800d40690785d803001c001d4603400783c4180c06889400c8460002003001866000c19406903d9030341c0f03016207a4440005200509942015218098881007000f2070701040f020540201742400f210200c204a41342c3d90b0607400d0071900950700c54480741d00128100020154040218000351020207000c101202803911103180309840b94014a007489200d010740a483d64481c180c00000351303400703001440545003074400310002e5a401d580d0940505410112410340b400c4d50783c4028140c803c3d520040603005086000340e160501c0d05110020b080f10020000704103c09a40030342c90310207004440c0e443c096071900c014401d03901c08a4104c658120315280044c42090f6011409208203001c0b001c0341500e580c1e80180c600e00300080c51348004c2d0701d80b0074000035680f055000031005110380403481c182d501a6a5011000c000d5034800324010740b21024802d185036492500e2691190794291a1410074140f01c01040117171005d504810f030944195001d025110703800e5004011005110900388007541c1403a980e9504c0d280e40351 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 88887671 1250 88886421 88886429
    0x90f010f0804061109031603021507021804030909050a020703020f010c1718011404050610120303051812040806100506070f08090310020703020d09290c0111030123060301 75
    0x703848400382070352082410245c9103001401003e0b03405c54511112030600b55002480200d008407408040750088010070401c1c0da41e00c030b0700030b004110720002c2c4105901e81d02710024422000e0026001c00070070311001c81d00c101c52240d0108140160390750380604001c0e00d031555840d00852141c1c101010a12040c0d4040f6240700d01d11510f140300c2e8200d41342c0c41265254148403401c0341c1190340c81e214000c02d440e00540e001c5805540504192552070302d0390b80c64030328860b0150090385c401c5424100c9010000b0300c0f0b5480726900ca400c400c2004904601c0401013800c00b001e43c000701c0e210302000f040520018606101c1c0039044202d00044410151400010400500a84d00040d1010400f102c102c000d102104084603070b24400203059490328001c40402000a402441c802c0e40107201749480241c60724051802c21040da690300181c4820030000f0100c030000c004980c1030031040c02006000e1711034400003d020b03100e002034191500e692258106808162554030080107203080c0540440c8000741900c2e144212030540e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 88888921 1250 88887671 88887683
    0xe09150d02040902060c0105071707050a1b0c030b07180503060c070212031c0e01090308061905031501060219260f03040606030302061803220506040902090f010f0804 73
    0x20031a600002d402040f41c10780c041e41041c2c0008075030042800c103610007031144e501501d5000703210320f0202e004092810101e5052000c21b400300501140e0034042c0103501100182d1090031020180c0541da0350100f0071550b1b1085405081002c18084003d4100c801c04100c2100d0119000c03110b4034100009503143d01c05407503000d480400081e03240641d140c0038801c1d46030252500c102c0340e0350300820210307000d041401d080142e0458a052040c0c00d01b120306002d11484660113594103100c9407144020401e944245c440203c00c1062400e00c00070382e40e02c041c05102c81400000c55207490640c54804003a090021000070000740c28210505213000400b500701c00345580112031007840f002c1d040440b2000d0300d4401c0e05c3c1c480328140301c044104070400800340c001c0c80507203100b507003510190b0f295050400805080c0078041c51290b00140890b01c040840c61980e01e204400c01c002d03d04190740c2d22404948154001e40000c44540c3e00003c1c60381e0306003825001081d0a10082c03070104040c81c00300074000d0032104064401040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 88890171 1250 88888921 88888939
    0xa0f0203100e070b0c160b090112060305032209060902030a0b03070e0403050a14070f020f041104180b0d050a050d0503070c080c0f252102100c0501050112030e0915 72
    0x3044804000481108145402000049840300100308068200d208c1407400105900e003031201039202e500680c01166400b50080d824141601084c901350000101d02d44101c8910020014183c8424001d0100410210707a005035281804541113050340d6450700031500075484004d0402c00d160400100c564099010701e01151141d031020030458000c1118202a003c03c840410b102051105090300860f03003500c01c540c1040300300300c0a000d110666044214094400a0900c03041044505034182202e040b0304040e80020b4540c4090002965140da418042c1c0e02da600000c220800c00c0030070030000301c06510504105082d45861440100f4801c1101c400502c1d9800c0441c8051154000704001400c0140318000d4860007810300b6110503060480300d80c00d200e241103450340041c0846003450013002000d082c03204003105030a00d030207110200700450110803c0140b000400b80c0415804e129040c081c0404140305001402c5900b0005c000a4000222500c55107149050001e490b0540d400802051000d9880352070f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 88891421 1250 88890171 88890187
    0x807050607060e060c041503060803160c03021e0a06050306151b060703021309021309090206220e0606030f01030b07051b0c0a080304060e01050d0b030a0f0203100e070b 74
    0x80544000303090400070384908418000178944101c003810a44072001d000c224034644d006412410f481d0180f25100454108100c0481c04041c0c0e02c1207840d04900401d44200d5840d903a80c00f02c0e40c0040340442540c010100c03040b207400280342410202005250070300d890707811030502100050840300c55604552050340000740450100c216069050003803441c1c4405c1d42c44c10300d00b000018002e9030091383c007404e11290b52031010550240504c244d03103400260500c490340c0b2504041011000f010015800d0740c1c401740c240f0100d1112400105d42c104a44040c070480c02c02caa103052024884840c014082611410043c4200036058549004980c1102d800c01c4007821152070350034041d0380d40c1c462100c4640c90400c941444419007480000e902c1740854041d01c40c030020070780e030741c2520361207020f907000f4440090170003c5518050b40c441d401801104003094800166805103070006032a00c032851400300c900187d49042c0d02c05503c2c0901503498400124a41800780402c40880507495402a00030100c14200210b100701d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 88892671 1250 88891421 88891433
    0x3090b03130b090a020405130b042a08011e0b010e13020409020a080f06010e0918100207060b010305010506040807030f06150806010f1d0106030c0c02100903020405010f0807050607 79
    0x7403111500490921014180580c1a54a459034481d09134021800c00012400c0c400c54405180c240c25003003900d0a9264455a940f0000061040103801c030880710301601090640c601c004030b100070b25031940009808803030180703a0400a48000d40352045c407490811071a2441e6044021120792000403607109a40502030380c9000c0c024011608461182e500c0464041038070794214586a0080700465880456035441d07500440e400241586050b0f0403650100108034001304031003000d801d600780701c000d642c0342c464402c81ca6800ca0300846400e4440d1900c8034059201540c052090501520054400618207418100308558810f0340d884002c0658a951014900340b101d10b6118805101c08500d0304800155248801a43d40d4400c0c050305115030034500000558211070254140000341090031045141e01e8114158000d003182e902413014488103021510040c0d403a0901040e007408161215a9050b04500600044072416085203441049045003809914000a0f03c582254002c0790341c540c0da004145091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 88893921 1250 88892671 88892701
    0xc02010c060c050c0705060c0c01050714160e1305030405060d06030b01080604150903020d0f0c05010c0f090f03080d021b0105010b07020f101e020109080d0b0102120703090b03 77
    0x10309034030710380044444503690160013000082058411200203544030003c004561040a8041c50180c2c4602070031540395008501410000b402502031815500004401c1d508006004401c803002e60345441040c49041403041c1925045589000c1004064850380e4419071b41c0c0c41140a0340c2e1254001080f9065480c03081c0d01300320302456012659240380c3d65182511595400300703032170480f0310312052007410900c559140303c2d282c401ca405a006020114540006a82030001c4151410400c5042d5044101060b4240a4641100e019a49444003501c032200002c0034412103802c090b1390342e4001c4904001103610b040503190019a807071001030799842c81da42c5c00c80f00b90300103040b54111035080400014075450300300090450f25000740c1e007c41140b031010040004130f800003003c000100344892001001d2018034200d90003901c9560000040c101c1e4141c03240d692503080086100216501d0b441d888845507414070a0148100c503000140381443c2c3c4580e4054200f104c54010461050004400120141002c03021 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 88895171 1250 88893921 88893923
    0x7020f1e100906020c0601270b0d020301050403091401051c0f0b030a06060306050106110d0806030c0a14100503011d0a0b090708060103050c04050a0e1302040c050a08091504030c02010c 81
    0x8002e2500d07549002c3c0c019411201003030030030740034071130000820046001c1076490003090902080341c070f00340f14264132340188100384000703410502c00c9031402d0068034244291800f0781d00030f0f100c02030245e10341072291450040c11440320b030400c44144201820207980e0312002c9030039210400040384213203e07007102d0f000820303e074030440c0e904d4882c0c0e08900d4144449507102d070003920300420051000e0ba807038500c183c40321000304c8440d0070160700c01c5052680c3d0a11402c0c146821000040a4603001180007000850740d8007103420502009080300e202003035a00c0c004010b060f08207080e0a001d406d540c500900007099511a8001c040f000840b2000200d04100940c0103d403100705c010319001d80c5041c4070380c3c0104211001c0310610f000c6854000469100914501510201c3e440141118446800c01d01040d4549074007034034030f030704501c40c5031281c0c0010398031401015806251550764940341c034000c942c004c10010014141c6d11082e00409220f1031000103c60007564451f802d81015903042c422403004981d000d6034010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 88896421 1250 88895171 88895203
    0x5130503070b0106020105150a060507020a0506040b09010e030f060f151f02010e07050f041116081207030b010f05070201110105010807053c1305010e0f07020f1e 71
    0x907034008229500b40b03000c1c180c0302560700030031003540c60a96240c40071001034400ea5110f240c0c0002000514440d0004100840c4044d0810315803640e00c0c008615070f80c1282c5c00818000102148481d0139581c000c44841b0002412801000b102504900c0c59072140ba001d80360400e45410180007481c680d070f0b2000001c0b400107000e0b1a2502818502c049603a600304940c9402c801035091000b90200b060700000d044003540d8008000702c907030703044600403c4001c06048240c1c1c030443e54148001d05040030b00b0100e420020317010701c0410360395a0302e07921551005d09008121800b8946080418199070760f0051040880000360309040e0390314182e40c00140e4010300e19480c0b940d229820440081155032011a050003152010360f04040f40c8034503070f41c0c0380c595805102240c1503018148020036510790350099443c0c11071003014002107400106c0c03441c1d11095034801d0704026401000401031202090098120643c40816440604000c6184030b544c0e5460394105004440200e02154004180300d00c10301c9503000da404030307107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 88897671 1250 88896421 88896427
    0x9041406070503010e090303060a0e0a0b040f0c0807050301080c0103021813200f0d020306040207120903020a0b040b0a0f090801141e010b0304060c020a0b07080402240d05130503 78
    0x900611581c0709021740408008500085105c40c2c000100313480c0601d4006040074060307410301c0d40c07074440b56800501c074411440d201c250100d69a1200c0c45100e0780358040c9000840c4801030b102d00501440d6000d858801040802c1004200c030740000f140c5102040400d00c1c0149e641d07070f90021506009032102c84510340c80030401000d05103110480e407040c07000d4418081840443c010b0751189100ca030190601a80a60104000740c5413881d009500855200d88018001401c0c00c00b15165440d41030104800302001c101d03102414000d600d0803400d40f40c000c1c1003814000d8079140c204944001c050080340c041000788051800d200d10142e0040d61030201621024000300b082c0102d5a0401a01c5107054401c40074605007900d030403a00090301300015058401d8084907924580f0345540c0c0d140141004502c00085006000400c2e00289100d88031901401d4182d943c100b050a2170300400c491405c22010740d00000481d1070b02c84a44140443c10350300c2c0341c441c18000003200e031fa40c00d541c5031003c8c22006e00141180400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 88898921 1250 88897671 88897681
    0x40207020901090c0801050102160306050910020c0d03050907030809040c0e0603090d0e03060108070e09010603051f0c0305090c040b0301061a0a02070e06010215040302030d09060605030d051201030209041406 91
    0x1561141c2813991403603a034100240da0311001644c407810342d80090084c20003034542c248045541c0350400fa030411040001c45001c1c05c0b80103001012608440100e01c500d42101c1c4400104941c140515a044590346000d802060b243d41c1d24920300340f01d43d40c4158025034903444800c50850007000e0060248502030310540e560f00d42850303041c3c1c0780c100c000010004641900e10b101c04a080004805041c4c84e0814020310803981002484004076000628103025907403111300c00300c00200244640f15005025103060700d18032180014040a80c0d4442d01c1140c10545481d00300200008009200c1240c4c51041d140003030900100008079014054a812041c0a5084e00207400c10b40e015520083c011801c00c0e07420b1314085606c6012100c101c0c8000d640e80340c0140d1261100d03c0b1401d52015056400a1103030040300c0c90702d8000600142a10306003081647c801d5a80c410412041c00c0600640c2d81c800c01c107291151804004514104042c0410301000e400340001400203010020003c9051070003081c242c089485a241c9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 88900171 1250 88898921 88898939
    0x31e0f010c030626030a031d010e070501090803030403020601060e012312010e0907151101090b0106140c0303010b0d0b03070e0a060f03110d23060a140c0d0902040207020901 76
    0x20f68820496056016a00d4a088a844024112407001c606002d54504059048200c0c0540210070861155001085981c030000000f40305481414044d0350240c0301440c80c010015001c0f000c075600184090f0003c2040200003a80484c166054030b4460800b82d6a40c1505801200d480100d84040e14040c1c450450b6525071807024400350401108551450301c260ba25446035510720707030068803444a1070744003080500c102103401c012008104102e1400c80221006021503500351030403400c2c2602c07040703103200041c0a95981721280c848003942c2c20782450303c0c091310b2a103195034901c0140706500c0c0e40b685c0810b02c00b00441d09070304003548032000101200e0a00c1e0700c03941868490328041e15621817152501000240f00c4921a60710b1040720340090164942c07900c58020b1103800401c0d014210791040040c071a4807c0d401c400c07502da0751b05a0008000f01041d00e005850b074411211207014a07100d07032201104000340c0c0b04561003160841d0003410740105102ea20362012601900400340000d41c0600100c002194802c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 88901421 1250 88900171 88900181
    0x409060f0c0906020a06020d020d05010e04030305090d0f0e030a0c170c01090b040b0c15070e03150c0306061e0412060506040908030604021e0a1e020c031e0f010c03 72
    0x180d000070030000c8604002030b200304032548212009a04034107502008110940e000d0480040c03c01d4026140200e5028072400300e03002600a507410401d06002c0c0400c1c55032610803268480000801056580c0c11061301504c0c48030f140548400b00038840c00b01d55040d86080c08003015003035001242c0e07c07550342c60341000384843c0b480031071411480c840c055030048203600c242422030884122021040c0303041c0c14085041070542c485168018a44160460b56018801100b0914032a1401e581c84410800c0c2c00c504060600a00c15603c1a0388406003050000b642601411203800402c1107800c03d9550110b000325000c0480a058040e80d141c4010400080c5a200e0812012030313a480340004002503542c00d410001120840c4001400f6030b0401d00001d002c40c140703a80200750142c080d070420407003e0740116100307815510041101d00005c03803840012608284040c64081e00c01c1090000d441c2d03000705900440c5da00c0e52441d0503020b60080c501d4490344441130a00402851501400007401800000d56001d80944 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 88902671 1250 88901421 88901441
    0x705010914011109010c050307120801090f06080319170c030402120312190b03061503070e011a0a0912030804031101020a0c020f01032715110702040e0c040906 70
    0x4003492000200e003070041c842d040032410114889030411101ca03004480345625602e08907550700c0100300707c0d000b01c0c90b1039039604900c0400303580e8043c0942c1400d900c5c90540f01c04a01d85d50200341405800e00040d0070100c150752516444801c079504144d0a6602204d440d09218884e4420164200500c03640b10b0113a801103200343d00070fa80300a1580318481c01386580c2c1c41205801c404040800300030680569000300017a4030004d014601145185034840001d0404405840c6400700080d080246ca01030b080602560f0000c0c600580c0e001e0496141400c1a071401205900c0300340e40350800500001c00c640649001d10143c20306c1d010441110301c0500c0e011301041001d48058010404824802081042c14000c442440c1004d5551200d04081070f801e00941030040388105050689960880040f012020020f00342d040d0542c0c0410003c00250500148403030302d1203641d0085604104100b0f59503a01c8501f11032007035505840002c0d50b0000134001605210078602520390060621464a09101054210304059 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 88903921 1250 88902671 88902683
    0x50f0c0303041109040b1504020d02040609030c0501050a0c11060d110a02010f05011a0d060e090d0f090308042102040f02090102010e07150516080a091805010b030604090f0807050109 80
    0x1075581e03c00c01400c0c040884006180c1d80401c1c000581020508011801050000e440942011101000c21007a078126800001c0010901d900c02c000380b11903007003000001e100a0074458986050718100500e00750254002502c00750813021180d0b0551038480c11100d0114030440e00b003152200b505844036040d8010f88603280150701346540004054220b209481c100c85200d0080e800d0030342d000b884041c00c1e41292690713110407030399a000042c140e044031800500c5141d032880030788030001005001030058850750314440e0800c53b00c640700303100180c9440101c40c16130b0800c804401081e0102e404040002001042c025046428170213010700792104c60f0064030b0b252034240c00910a080c8988004e0b0799840a07840b440706156a07143d252407006005000a102030b4040048950b8414030325190054950b01402889000a903821020404541c1200391000c03000b0b0140d0003403015500d0401c8459a500018110f03034840c036030340c17440c003000c019000c0c10242400b5400b01036161104503504115008180c036090a50324 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 88905171 1250 88903921 88903943
    0x6060e070e030f1f18080306010f0e13020c0a0204090605091b06030610020f030c1006080a0c03110a03060608010c1e0207030b061c140d05070305030c030601050f0c030304 75
    0xc1890b001c289822a42d42d40c1d4001c025031083c8503541c00d80e606101d000032040341e64403403224600500001c1e8881085010f0f076041c590b241449400148420045113280081006100d161002c43d41c500b4144c3c5d40e01c9003a03100258458081404c03071800c260200d00700950103440c001c055410818141c1101e8818000302041c0c0c0c020b194848214403a5584440f00e85604c0a41000007844074070740603155103002c2040348100d648a030184d04903070340307560b104c030640e241130341e001100c040380c1603131580a075001400c1c803100906640d00050ba00c14052101d02e0000822070780c1400100c1c1c04a84034152110002c54016805003c51540c4008050007400800f140400040d181c01c001214112441410002455558002c00300545192186c140030030300505096885858088500000c1001d10100c4806500910484c645a05e1441805140c498200e865400b409400c4c020080480e40142c22f0b43d5211801b60300d029943c1d40c6020048941d407180401ea80c1c503044d0701003900c8907204030000c05188158480c1c059408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 88906421 1250 88905171 88905197
    0x1505070f09080109050c0d0c1d162d0201110a05040e01050a121103030720010314010b120c04030503040303051207030605060a0f020109080307030e060f0f0708070c06060e07 76
    0xf0907a849450040c0180e8085410507501c1d05008000614680c09844010000b40e114121101c0701b200c0c1d4040ca10f10340d142e400501c0b4800e03071074000c3d07249150081d0a0440b116607408c1c0706160320400d00170080203030070300078216400413500030b41041d01d40180085500350b842d44465805441504940650b012100c0c00100101c1d0030b0800030b039034a0a0720210a894640b400e0141c2d50b0f8450443c0d1440704641500090000c0c138001005100e031410034000120081c1800f1219100041c2120403404010410509501c01040f102a1120441da00d00d4071446d10707844243c0e070740594003940b4481d5034401011071000050000038564410040e10300303225501c001106a403140752045040e40d03040d018140d4041d1017004482000d5005988840d024038143c000822552256290160107400c1103d1103800f1944900c1c40d184411001d2050b194480e04001000149042200c0f61105601005022405012001d008545114020f052a0740340f80d5001109000194036000911100002695403001080210511304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 88907671 1250 88906421 88906423
    0x9020f04110a02061821160309051305040209060f0d0507080106030b01090c02070b090f04050910200414031c020d0e041e020f0403390f050d1505070f0908 68
    0x5c1000d80001c0c001c2040882c030742d4981c3c555000700010114030349010450082d2224643e802e900c0300342d02948604203410701e01820b1088108030008080003280c506010080140d45000380e16412a00130703070311a88082800004650f1100c0700c01e4020f4614803850000040f00801500040181c0c1d1040380c3c5030b8050399039001003c0690b03618007021030168014880070300c08480050b003e4036040500410034642c40c01c40e071001c6021600103031040a0503822804035405030f0b410a004140c0d074818900c01014030f54450f050039035454040c50054a02c501e5080c0b84000d150f58040107030740e4012200340c10500c110b01f4078a0001e9511001d41002c038002c00c01e42d1019084503c0c191240c0303818208001c28022911031584046030003903012404050001c4424070020000c160302c0c441c00750040d40e103201c0d100c101364580c80600c481e8500454101c00340d04619035041c020b15280207812001c40702c0a40b01d00107115601d241c580d4400c0a00721078060030900e001c0402901a5001c408001607032900e45468050a031140788003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 88908921 1250 88907671 88907701
    0x2070501170601050a1b06090c06050a0c080a1403071d0f01021e031309020309070b031b0a020a06090f030e0a0f140303090301111e1204020409020f04110a0206 70
    0x20391030801c401c1c8001800c550058000f401c0c500090b01d07041011440840d032983c11120840400d407401c9a6511000e42084846c3da1900040c09586c02d049080c241c1040d03000b0628401400000c02c408000300d0388241c4140030f55102400d00410300b410070746030724000a00500400b08400c41503008155042d4100e00b504003c407007e0a01001079028013281412142c2c0e040408021008508083c8010492030712440c0c0c0d080d10140140c01d0442c6e0240c2d47c0c1c103052078460324000c03164200d440113020800c2405541d83c2416060382e45905001e4035581c0360518488282d040046a09014083e02c0c1465110380400c105402c4c02d4804134400d4481d00c00450b000310038003002c00e200d405410303611a00401c0a05c02c0761881d80c0c0165a001008049a02d44062000801e003540c9d5921080002c01d034021601040c12220003903000610100071900908041130303406100441c0c040038101a005940c2c5a900000f552036011780d501801002600c1489024503032401030415501c1455086c00501a0b00041400e0403111540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 88910171 1250 88908921 88908947
    0x3041101080105060a030c0e10090f050306250201020f1809090f0304052211040e090c0a0905060d0209040b07020c0102191704090e010603060b09060d030302030a18050c0102070501 79
    0x892800d21000c103500f0f07402487c104010a00b40000520955a1940c0f40c24800072a604260340d501d03600761030b20000d076414601a8000383d200c0d4004004000c1d40b00b5607114211a00c01c07900c1c041c90503e4200300782c1640203204020301c130b180480c03001030554a0006c110096280100081c2d411103030540e5030001264a800650a00d4030242d00200300c100b0513403818028603248484d0319020418a00162000302044a1001c2e021003007a10000c03404000008075401c491768003500c03100c09440d1040d01800095607016650050b0984a40d0b2080441c031031307032204115010619409410315800d0309107400c040aa600044034408014410f40315607150030351020421410328642103a0021092015683e42d298401d28554044503250081c000054006880e000c0e003210041032400008545085080070b2007903500310741440d4041c03070210b024004561514a41c0c40c3d2025014500140c40342c450b04504809410140301d05040030303074540340b450184070011582c0100c800098088032459070380c44005582890300115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 88911421 1250 88910171 88910179
    0xa0f050702151c0203090a0308070207060f080a06120b0f01090923030f12040203060a06030b0601080903090d0501020d050a060501090608061c0312050108011a0d1406070503041101080105 82
    0x200e00100e1000c0101411600c007100406010801000fa510300403038100315012442c640c4854504414107400060182e0001d2040c4080c0408030b0800300080e2000301c0083d00b11081040c22000650621388641c0008050140d108910403c18100d0a10000350201603c45035100601680009404080c0c0e108680b24240c2c0401080000660b14445a288003220341c080d041e01d010030459035400c4004000200002c40701c0e900c3e0380e4404d05040c01890b16244008141d138a42614054042c4003103a5000b00303082c0e01c03020920304a00c142e61010305440c11070242c00b01080e00940d441b01400204841900644600d43c100441004203070b440554010a44059210301c81c00316484080911840c0e110300300b0b0980c0b00d4006061090750510a0043c11000d2594000c142c00041d01c14040d40d4110503940070341401000d0820007402644030301405103c03006c071400071079881288004210000c11011810f050f07903041800e800c0d245a860800700280060f030003103c04441002c0030302c0040312658040c01000381aa1070240c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 88912671 1250 88911421 88911439
    0x6010306050a0e0606160b09060109020702011e020a0503040f081c1b06060b030103060f0c08010510050702120607020601030515010308070206091915111506010503180a0501020a0f050702 82
    0x20003d942c1401810140d0403850400000e4100b00400c036409a540b846801c102e4018070341003040a0400c01d06030410704449c0d0041102002507070340001e100004111090003036000492603501a0718015000c003000348035020100e4002040c0072201803010494030078070b041d19548401c0441452042004420110105101040811005504500b80c42006108400c009000768941c41c40409940090340200c0f00641c6485402005002e51b01410440041e1401e00c092694140380c00901d4008103003101030200705001c2422001d540d204040c0c1c00c100407404080c2c0b90383d0b00b091b4000035181d038401d010030f84407441024084c00050302c102c8020703030489806c51041820444c15508101041e0f020070f01e901d40c0a0740740030040c0c0f41c0c03055900030301c0001d0940f482d6543c4176214030b403005803000c6282d84001e001134104c810b00700a07504400c40c0c3e15a020f442482e00fa41c0c9c90b0343d500380380c554010304581242e44038401e00740b212041000546c0206040400c41d02c4100c0d41880b407080440d0716118900d00290042504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 88913921 1250 88912671 88912679
    0x1050702010c170c1303150501210b061005070204150305120c0309090c040306021603140a0c060902010207031a01230303160c0503030f0403140606030319090e070309030806010306050a 81
    0x840c000c0e0105030003005c3c03e0213003190b0300e443d00d00c0180061102c242c202982c2d400100034140c2000a020f13955284694140c051907215110011008030040c09203020b0a003150120b5181c6104004680c500c2e0340c000c2040000c06e009821000c0703425400d010468280c45041691410300011200796262103810301c00451038540b0110910540800162600154141c180b0010002a590303001034654640c450909040604030350400408051801003465001601008a816081d50109829803060f420200c0450081410b1004070714081d4540d0010302500f00d00d012303089036142c000f89054100e410043c0150820b40b64503079401150b8400040d01c1d0342c554010004e15042201080b4031500160040030382040321f82da10004242945e000d00c49140c05480c0000d0b0a00803c404502908a94410311009055a19103403011964031712403032801080c0e2428841200c3e0384036100c4c0020b040031b0190841203603120b0400440c040c0103814034100841c0800c15000016207075511901c00c81045940042c03c08628505d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 88915171 1250 88913921 88913941
    0x25060c0201090302090c0309060c0a050901031e050c0a110102090f09060409080a180806070504060c050c062b0e060106030e0f030c03090108010b030408030c090315070201050702010c17 81
    0x2110004a051045205000016a4626281912401142c10f03c241d0724500404007501b0135034001d00c6402034079424003010500550200c1921080c04084c00c000801305602000d036000c0300c4da1020202066414501000481e420342c1014100d09030103912280460b1303c183c10001c1c01d078016500c4d80d0f0307003003803041c2910a100c3c0b8003002541c0e08584081c1000601150640b43d000c0c0d01d82c0006450300c04110740d200c13114405541031400c41700400401000d840c15085c00c41c1c004040380301c1e900c00c00081045c2118280107002c01440090709268008280c03580d20304104400e0035000d5075094482c07540d01c1c0988410030000c95280142c1c1c6c0c00c0764900000d02926070070104254003c001c0d00828031071f24481d5121820342e80f034041000300f0410401c2002035032101140b0000400000c8141c1201240c0c000610a1100280e2203009076a00600c51080494850840f840880e2074000d0314604da2200350804010312004540650190740116101d90081c0700200c078a00d42590000582c944240010b552200040c0c01b82038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 88916421 1250 88915171 88915187
    0xb010611100b0415060e0f0619080702070810090c08010203041203020c1005182a010e1507030306031101020c01140304020111120d060f06121505040614032506 70
    0x1000b003001504000700c2c4c40c1e0790400000d6411943c046400c2a00880c40c1c0d1826540c14000160101d40d030501e80001d00c03140040301041d203521082881424804075440038024007585c409001c1460441d010361041d2664007000d040301200545402d00007a20200f0a0304040c000c44c0d01c10f035040112003411008480c800c030002e42c0a504002558003400c0888200b584540c0585809044000145880b400410108600340303003480c440d401404800c05032542c40f904009580401486090070300d060a1b2400801003890784411400000b824600014090205905070b482142500e0040c290403070180107050059030703100d1114101d41e01241045d41d9801001c0c05500095501ca40b041c507045020001180e0128034210390112030354100030001c03400c084900d8191040170001c1c862590901091407605c54050150580703003a50404403611004540700003009584864010301019100b000310075a81c15004028007a400c10951003030190074040813903610701c4841503050141030381c9840400ca103002c3c0203036000c036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 88917671 1250 88916421 88916441
    0x50c030a0f090b0a02060910020918060402040b0c060a0e01020a0e090406060905010303050318060c090d05120f04090608060105062b0c0908061305030a030c0210180b01061110 77
    0x220b1022404110401410003070700402d0060f800030201c90a1140401e4201010111187c0d0064414041003249640300300c00104040e41d0000c4600890701e40c50040b90103840b69402101580000140d02145d410002942e24841e9840304130400c410701c0c540e402d1500f42c0c8140c0700c200340003c0e080f03407074851903107000f28100d82c1140c41000002401541c8508c0401562401d0703009502056000c010010180e8203d440001102e02090281299203804c103000280350140324401401100108400c6080050030000016071940101603140c40c1c0e403c10081e0b40c0254843d00034034016900b00030b0002404200090520b0507648000c0103039003095810034140594004401c0107042d0a102444007102d800702600c200c1c10703840c400d55034158003035080200d1a4506980941142d410013444400140800c902006440140f00c0524020995130740142007285860941c9010821840c07070802c51040c1100d013105584640d5100b540d09030044d07030f65600255031110150401d00c8040e007041c4041e8002480c0c0e03500c020072007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 88918921 1250 88917671 88917677
    0x20a020102040317041805040804030b060d020904080d11030105060a0c02310b030a1211010e030c031801080103110108060103020403061508010501210b070509062107050c030a0f 78
    0x642c2d240c444d00418051a00c900c00007910020b0244400c004d84c044013100c6070304c0c100d01030045003025900c0c1241c0d8407075884081c100c03c0c11000070030380f641c0e1490425890031b40c0040c492026402c160030200b40d0341d404a9941524030307280410f40c141c1c100798041901d040703a6000744800e08180c0104400d461204103150b00320b0b0b11900340300940000740f120012030450899031a01d40b40740b4035800d001c01c80031100030150f020b110f0350003440040c0005114110317100d0001e4651410f8195441014101d0340540b848034054010b0340030200c5c401c003101e100003005d04140003000c0082034bc118410801500c0c402401e00004e0403407009442c402070300754059200c580c0c00900c10725005280031b40c1d98841c202240e01101201c02e400c034501c00d00300400c210074010140036080c02e00e003400d41144220501101800c2c0342030b0060410502d80c0001e92a04d0042d000e4440042014000c01c0e0758160011910142c043d0104d449402d66003c803003c50040f51080d81519041c8020f0790003149403d102c46010307541c3c0c00c0034042c00010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 88920171 1250 88918921 88918927
    0x7140f01090e070c060b0105070506180c21010624030c17011806050616150e0a030909060803040501050d0e0f070902090f1207170307050105041202100c080a020a020102 74
    0x1415810300d42e852041c1c5043c3d075900b0040103149000000e5841d413020507410400d0610102c00411000b04110350800180c100d041ea50101c02e41d6020301b050402e080f80b542c851812035545c428000d501640f00b4110000c41e0081100c103883e0306401c0840170320701c038502109148042644031141d000340d0001401c0c0300903081c4058a4268081c4e07440d1204001d03003007984003c110340011000004c0c2c90240801406003115000c4c10101d41c401e4170499032411620180241c0c9504852141600703042e80701144820003201510b0f0000c0c204d0070041d007815914451401c00c030780f90250001707008002000f95015124169075036490002c400ca0a14050701ca036680200d6a03001c5c0c001d5880d154a000c01600000700114400941c0b20703a804000c00400ea84045074250245080c4c401020f945a40481c1c05400c2e01c00351a03400108101680081c1c0c07547c050510000c1442d0300e418140000c3c0088100c028900300c840c1c0e82114078080e48211010143c50b00214110b002c9410100400d0402103550040c060700e480600c00182 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 88921421 1250 88920171 88920179
    0x19030b090103110102060a110a0f030905070b030907080303130609030e09071e02010b0307061112120411011d01080c070b0f070e1206010510050408030d050f0907140f0109 75
    0x400c044003a031003110031080300b51a8080558050120384e43c00b22504004000051161a0308142c512861984104004800314002b01c243d010f54070a0280c0c5030840c0444a03000d807108a10903107030b401541c6181080c494401c000815100020450f48190001d4007841a03a10342540c03802c001e03100f0060218207000310384454001d01c0d01e58400c0c02d4410a4a41d8036401002480d95922500c011034219400c21641000c00c0c5400940340012040c0444141d0300e48085400341c101c21143c200880c2c4e0540c100140c0f00003c02007601da581d848240d006600481902d61424003200041d10340c410f16100c2c0104680301e0f54110382c290341c001d03046103611200c0d042d0711503d096040d0b56090511501200c8400e25030034014148008294002c034034850b484029108120781c3d6034000c2e03030780b9541d240512905100e0680d200c400d0341c010344280e0541d40204280001c0381c0e1111b40310301c0204c0142000302c0f40050003040c0c50000510101000075a20102c903078071100281c018850b081440044070740050f007607050215001c4005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 88922671 1250 88921421 88921429
    0xc010516050f0c09060d021c05010e0d02010207060b09011410021e06010806101206020c07090e0a0302012007080d0207140f0609060f060f0109030215070c090207050319030b 76
    0x40c508840b100080e00a10100000300518240050700340c80c020142c519a03d001616204c040030800240c02031056904846490f090340500103101c01203070203000382625185840e40540241000c54032481c0180b103840048400d01c01d10000034800c41d045c21005200c03d401c0750138143c207072414032551071059941c0380403054030380f191100590070010b6482d4002d0004000c248030038099207400540b070110000c8801d15050382e24503c448c04000c042e0020742e0010b1004040c03181002200000c150101041c4088841c10041e1500c91240040c00d1f4003550a0034180b00070080f540307001040c842070805429081c03803183e492308841c0d50842d80441340301c0c40d07003080b040000c83c843d418224400c170b42e045c1c01801421b12448104c2c1c01c2c9107010b840700085901081c207104514000103d460340c01002520381c3c0c0036199500004a9941c11240c0c0069040b408000803088002230310070042c00510701500500352202d0f9207a103140103d10601c200601150428030030745904003c042c91038086400c65182c045060130070a0001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 88923921 1250 88922671 88922683
    0x15140c0f03030c040807090b0d121b03051b01050c0a1b06090501020a020d020c030d0804080702130b0f061903090c0e0a0207020103050c07120e04020408060109052203020c01051605 79
    0xf450448000c6420400884200700a82c09019500c0c07083c40f845c505400816448070000d00c005048503292490318210038031038070441d42040800100c0d07855421550502402c0740d40030071aa2011000844080f59068405000b850700070781e0100c1c210b500c1c245901400315107260800c101e10030502c00f521060404241d00d0700400000314000c070001699410740e064040d281203100c60500040d90045000403817a41d402080071001030495003048046603a441c0b415540314410207200070b61003445441664030001c0164004104170a00341c1e88040249100420850140605820f07540a584104007501c1914401d410602d003091091380c40b0602107848680b2102102e03000ca0f036050650f03501095990956a2500038141c226482543c0d5030300e020002c1d11a80c0e041c51203440e039501032043d644900f80d05a00da40d4112001040110290b643e50750311030341030b1405081c0644403004d404402e10405e0800044040b0000340d215415001004c400e5440c4005540a80044102c48102d50100c032a50300858018026 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 88925171 1250 88923921 88923931
    0x304080a051005070801030305030103020f06070b070305060411120c160512070203011103010302030309040c12020a201513050a0c0e070908030412080702030115030c030c15140c0f0303 81
    0x41d2040c0c1c40b024035044200c03000144114100b03c50000100040ba8116003107906607601520740004105844001c9981031084001c0141840001802c11000d44c0e41940240d010b684222020f2100520740c4e900350155009000b41c1e0444211000f0101d41101c80c0d0318020b003440c500000c00704101101e503484182c1010341240f005070005400040f1407007103240038801e4803119001003a00070704550554021980d80d0091000d00c074040c40e6281c5901501c40e0140103070343c1c1445031444042d9601c2008110040c40100700c0004820202c2100304105000540458640c603109010020b099890340e0300b50240d20f02918110b03040d43c0500400350b4240100302d0b224100d801038404001040b40d0790901a02c001c000080c3e561120701039030424032060254410344018649110380058060780c90326203e0000134010b2481c14110180840c040b90b0001c1001607118003101100c0c012024410803d07a944034031503111044103501c000007007402c0d101740c10390f41c0b02602408161501204072400d400d0076140203031542d40280c074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 88926421 1250 88925171 88925173
    0xf030a0207090e06070c0303022209090b06030c06030f04030c02030d09060e0307150e060d0501060c0201021501030309030b09010212010e060f010306080705010311070501020301091b08040c170304080a05 89
    0x805002c0d03144940075103519440f014000f0002032a02d4500182051000d00f0020704041d00019032074680210446034101480f9421062410166a100c04400030402000304076080c43c914030018841e848d01150003a413522000e812240b842d900c2120a810300c40f0028030440c1440700c0c070303103540016840400102e4507084541d152001035a00340300c070103041d4902d1404054403d82c440b02c03051140480620381c0f408490040e041a0400944240000e0042e02483d00b440960314600380000034181d80c080a00c1c0191070007a02650b80700b403c858a601900b4100340000350101d02c002101b00006805429150f921640ba20001410200c0020038211100020380c018110500450140a820f1800d20340c0c0620b10390b000d007020840399142c00c4100761903c995120b0103041c9640c5100708051000e800d0111000164894000c5543c1d68589482600500b54104540807a0084601c80d51806001d0764000b40500d401103200d00d01c041c5000c001c0302003c403540406013900d0006101c0010311050410940103200d20680c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 88927671 1250 88926421 88926433
    0xe070e040c03020a0503030a0903110604030204021204030917030315040209040e0d0801060903050606040203060d02120a03030605060405010c1209150207030506090d1b080426010b12100e0f030a02 86
    0x1c01041109211350300014801d410400041484a41080c2000112079220395011084920500003544074051540041d410a00011703204810f507107540c404a00c1a03203c0d4503004280c0e52121002c60580c03158581c000581c1d80200301003200c1e000c814101c10480302004001600e014044400b0406540301d00c102c40c07000340d00440182011070b0700032940901500052400480140c034540712240e8503a0045c2c045801150700001013580743d1134841c1c0200c10320750040e055090820040104175030f15030314810160000b07803400d0404942480e00404a40c1107490581d10b40b0f006102c540c40d500c00d405038016101080c42541640003c19120706182809040201d401420100d0324509103035040000050040800e504100500c1400030b41128140292440c0c03181c9411184a281c50440060320030341d040356600a1701c0c22401c0d80e5040e007080c480c1c44520f103960002c0c4070780045e20303050291043c0300003036213000d58003c2c40300344000001580c00056035110800484400c8a040c4c40d156080d030384001c0107440141c1181d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 88928921 1250 88927671 88927673
    0x207060203100602060601050703030b13020c030301230114090103090501051501020f0708190c0b0f030a0c0f02070b16020a0b03040c08060103020102030d0203041a070e01020f0106030b04060e070e040c03 89
    0xc01d400014180f6002070700307840c82c22900003040c92050b508000c00707140e92601050300d5070301d03103180403241c54140a408654600ca01034040c0e03544d820034844c118420846070b03000e488000c0d010007030400000040e12200c107944d070160250314060300003002c0541010740d241d4000000c00c40c00d024160141007150b003105102d94020000908145042c807404001c3d41c88007000b00452040091031002200203034040f100054001e01e8038a06401850713002c01014000858032a06000c2810021402075006a104000700150300105032049200320501002580084074108a04424031008208000080384101e0b110011640040c1104205800c184941c0c14040704101c200406c640303074040504000c4000b88065071456000135503e00c0344240c840c51031900400403e00301304814174035801211160888010614015000078115070003140c0442c018410b55031001c140ca44107108000c00e890b00701c00c103c01c81c8c2e666034071500c01800414003000751f1480348020018031540340300c070410b0149200300380442c5917503e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 88930171 1250 88928921 88928941
    0x30203220c1802030c040b0901140307020105011d0f0a0506030c04050412080c16030f030603050f06040c0f12021c0b0a140c041202040b03240f010807080717030d0207060203 76
    0xa80c0e08500c542c60701c1002030010003488001079808031120749000c207540f5030490700121400714010300703201c4034400e01100307100c1150f4040d0840b034180c80346003441e023440100900074600284000e4079146441d051240100b038044405800c2140d2085000c3d08852040140d40c01080444508490503921070320000c070304559072548404076603001200e92149504154400311100290441c02000030309000300c0d285000c144074000c4d0411002150030501391104400505000f0ba21680300f12001c5541c041c0c010000300b005d0345540141010740703001e82600d0703054070501d03801d2250b03510703030300b0102c000d0707004003c0c406800160600d5000c1e11403601c00c0c0c4046a14140e80010640201006e0800c0d036500740c0078002072210003880f981899000d07030100d80c081841820340c40480e01b4203500d5500b0030180c590203001d60100c4040359800d103000d0312400000710318903a80c4584241d11448180580495900603010030007440c07158820095507801403006072443c2c1a86444d4140c01c07a801032004a031056004400c100904038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 88931421 1250 88930171 88930199
    0x905040509030f0f1c0f02031f0f0605071b180b0402030f1306090204020c0d0806090907051908030403030309050607080f0a0e0f06091c02030a0f030203220c 69
    0x5884000d50504815010142490141103c80040c03810081107172040144000c045100c0170054602c200580e5081900d807401175031080f00c0c07100d8002c0f9080c207035011070828000320404940302480e07410b00140c10584211402d9100b4801610102c12300c1904040d9040506e1069005003012100e64503084030402d06032003610907000d0402d03c0f0b9803060003040028a0220b113280d0344491203800941d080e1910b49402401042e0280003e5081480851011b0000900290010000c4000e44810141b0790780e0504211160004603103084003030704230000402c43c0c1d040005943c03c221079140031612941d07854502491031a0429803040c5c000a84641d03d0b941030043c00c0c04469040841e07860100c199207000d0740018401d80004d0700d08150181d0f100700c1c88085003000d10900c9a01554201685c850b07040540c0400d0360f99895002e00640b807405c0482c0483350314000001c55034072021640728107c050f03902e004250000d400042c01b0601c00c1a075000700000c107402e03440c01c03550813500c6040c011085a080c1500180150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 88932671 1250 88931421 88931431
    0xf07090204030b01050427050c0a0e04020609120a06110d0615020c010509011b110301060f0e070f0e0303120f090c03030f07020420030411040b060904090c080d09050405 74
    0x40d104000a2011030301c880704042c15150141e40110380c12104021119000f1000c103150070f02c100d828180c81e41003140109040107110000c40341011000d071a20b281c3c0a4150050720300a501403001c101540307090614200004005c0b41075015503003a0365080e2100e00c00e0326900b03c0d0784507800d4400103078100c030301000e4071900c0301410100103a0088030b0032180c0080c1d40c4421701e00015040c000f0125a40c0e01c168405c800d80420028101c0d100784000450785083d1080300031100340e251195003404030111314140700e84414011201c40c14000210703601ca181e002d42c0e0f00c140d20002c2c403081007800c030045002d580b030030002015103001e2001c4a40891074005204183d40c48054032045107a013284045212a5030300009031213000c20320080c1c0684c0c4500900c002001002080400c0700080c0c850203100041100d020061840789009a4005642c03c41c0724082000720f40030159a164011001e103c44106410264000290f1a11607114107000c4c0d40c0700c418440c85c0a04c2a0043d0001580c10001401241445e003d859042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 88933921 1250 88932671 88932689
    0x3010b06031506220608220b040203030d1109040f0e0d08100506070b0603070f050d141e0706020c0405060d1101020109140a03020f06070203070305030c130609060e09010503060105010509210f07 85
    0x12520802c0c203044142840c01c0023130710a103040c0000c5400d56505104841c02150341c1101081a107001c4400280b06030030a0000c0b500c0f072494161003081510a90085182e50f5003c00043c144404a0803070035101d51402400700d40c101c209412011515403a280018900d05002c0d0003240518a4030400701440d05415401681ea00007088404010a8941c3c4085880e401d40c0980518018080c141c1c03000e180554010380700c24135400030641092780c1000840e801e1f007070320000c2c0e095a404002c860b041c003041c0c4c1c03001d49240b50020b2000010401188000d4015200100c0500c004034050119072180d0030413580701c2c81114219007020680b14105038041003d000003100d10350140074a4600001c01a450b4020b501c4080e06015000001941424202c0c046441259110b4a035510640c0c5502000b0541812802103c02042e0b011070003004606d4400d01e154100c900c001c0041c1916802c050044805810110817250481c1d4a078046403406240180020402000b000c020314030310280c1103001b840d164065101c0046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 88935171 1250 88933921 88933951
    0x41505071a06120d020304181404081c02040b070807020d0c0b03060a050915121204060f0306241115090c100c050607201608060603010b06031506220608 67
    0x1240d8020042d20100c90400d48e400c0d0f52a0034071110b06018112244601e84192803100400003080f12403006002000100d414590600c404d0700f108038102e00c510700880035104c5080c0411000079480c04003d140291018140e80d612100300d030f8404e089044a5000244242800700c05c22206051900007040289400ca80808050411004d03142c0d800e02c40382401c902075003d808101544010801c409800129000c60040c8d482e56144002043c2880c10f00c00540003e0512030001041c54005120100c04d00300710034404011540c12405a407645201d0202c821170303000d50a123640e2002c122130b503414407070806c05001c0e200100c41c01041250b00c907405910f21092002c80c1c2a580d010510000b1425030219807030818038462085109010401e00c44070b00d04c100a031144e83c8000b052402e00740341070002c81d24120110f07078040d1581410503090380c01041807a6004042800000c110305601ca002d031814a402624146c504464208800112100c05901036060060031400b0080e4a40c00507000394045000c60749208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 88936421 1250 88935171 88935193
    0x25020718050405120406050310050a060e0405070306090c05070b06030d081b07020d03020312010e01080d120204050406061701140a030f170a020109020a0812041505071a0612 76
    0x25804103004845002a58800000b01089000c200c45020b500885241c07580b00c943e2004020f180e40d0088035040000e004114000446041c201c04200c1580d249490303440c40514004148001032000415040c10513868003000a00c0d0f030181c0c8950045401203503141941c5200e00d007080700745040081c18080c041d5111040c07200c6602c0d84000119009411403040e41d00802c00303d286528107010ba4100654043c3e01060303a0010982c00000030a0880c000c0c1c560030140307a99503041a60405024070444d03a43c1d8010146c03501c00749101e20710400300c07180201001400c140e200c1003c2004c95409410140118105018251204040281985c01480c152400080c02400e070404120f002c011448000d05001c1c1003800390041041605d9040340030b583d40d03483d0580721941d000c0002e003c0c24503028164051541a04046107044002c1031b50400d00c0301c2d0a4240d8540740c540703180d02940c0c01008080000b0080e052101c100002c0440900c0041115400e0007103080c1c0c01c1040c2084111550a00417003910761024030254 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88937671 1250 88936421 88936439
    0x314030c0a0f030e091005030105070c020102031b0111031608090a0f0303090809090c04091404020901060c021801081b03010c12021308010e101d06060d0317250207 72
    0x3000e115400a03148581d20003c0c501507070948004654540e01094140400146040c9180403104030f4404a00130301180d11055400c1d608090385d1440603006030004c010750340d14075a41204807120200d00e04000920545c0494101c0201e4009850050419030080d61001d41a60700c22005504078a80c1d002401d080c04865070751301d084510106008091584850045051000c81c81c1990081c21000d4440001c52030203410b0800c031a4003034001c401d4040d14250103524500740320043c0c28402c50f40500410103a0f42005016110114030380f038100e0740036618501c041680080074035094020710701d50700181007018180c0300c0c03c0c101390858100c0030b00980c50100c008104550101e42144110405080107035100030703c481400300b42800f41c01c5031a00d58285525034081c07100001c1ca8251030390307496800304510f002e01c04005001752910703503503180180d100c00007040d45490a0025a2001031007402d1240070490491000310720350380d0869070311600500c0c90814186407407800d003481241308400d10143c02c0c3c060809401d9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 88938921 1250 88937671 88937683
    0x5010c0f0519090e040c030c0909020f0603090307050a05030702030c010c0803070e040f0608060402130e1f150e040c050111030a0e030705092403070b031f090c02070314030c 76
    0xb1240900d4101c03001d59860301890900000d400e00a00281c2c05140a052900d05009148030844548001410006d0107500c02d118400c1031a90040600c9030007440901040400c0d00041c010b403146000c10010140054810400795107454403030006583c942c200e90040504050b40c01661905110225402100046002d8200ca038401014200301101d078002401207001004440300702840540f8040e80031901140001e00b09100b1482125481c0111203038cc01031030142c40840042c0c501a5104a450340500c2c00101070300b03091a4100a000100100120200341c61260194051080c2041c0e08081c0001c2c0560a038608000d0311007030030701300c102051501d0404d82d2441404070550402203808085842951f05010007001408024181c000030f0500140d0100c28180300c050705c0301c1407083c14950907c5801c0110745103080305c0c80002d0541c1143c3e6003034040050300b40300c04d0149007980d103000c1c400301d407207600c500c13480d062040180c0c000d0805a05615002e005c40c00039020128540e0b0061100d8004504001b641c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 88940171 1250 88938921 88938937
    0x1e060e1303030e0f0610081603020303070b042405090f0c09071404080708010606020f150403030b01030906050c090301110316050a020f2506050c071e0f0e0405010c0f05 74
    0x55200344510f00f94280040111624181c0c0640014824001180980401658180c00c1901d50003882c840c650183c803400c5100c0203405400501c1600041901122481d0340680640b042c5500c0c8580545101c21254000d2002c1030180d603201c092240c850b008000c602104600d9400400d00b007400c402c009895054010316100410001d1100031900006150990b03005002c86800c8510316622103030114041d000b14029000144110704044084810004240a074200d440348040400d40700c6031422400380844001103410303d6151101600024490303c1058030900d0401c043c1034a803e5601c0801d030a40305d649400200c0310f841441802514424108500455625800d0003684c1c7c01001e0350a03424121800c5000c5114002e040418101c4501c0d18400a000c1a5040ca43c0c114940c503643c080c0d90074004c1203020f150315445040c050008046102d4030140c00c00080740901c400310380e00c0704005500c241c1d81d0404c401c00490001800b08002d024001e4020040301418006c180c14070148004109000b4041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 88941421 1250 88940171 88940177
    0x240919050901020706180203010c1403010b0a050405030d0306060206060d05030d0507180906061709030d1509020a0513050a1a09011e020a05100204060516080405041e060e1303 77
    0x3001c10001c00096044414042c1d20410902c003480900f480d00104c0540000d0a034029401d0190505216104150340a41e000d80141c03000c0c21a401c5c41c162940303c1d040690101b05200c000c110200f00c9603401c11095042081554020401790f00f0004000d05284000e0000341c001d282082c0c0c1d410010b003000c4140c8441c41c0090b4000074650380c40302e20807110440403c02070800d0080e80b150220315584103400120a1303908070f86400c1c3c1102c05004c41954150001c035944c040a4206004181e5419002c0d04071720110386515203220307000c903240c0008500320f9000690042c0440c0c0700013641684000c0f413104040040404a562003480c500d006620b0429486220300800c0c540030001704031800e42e00071101c1e10301145410011880a40d030300c003406566045000f4060ba454451600380101c0480c450088038247c580c03e5031290300b8040312144e038032410111300c00125082007050001007201d868521942d119171a0510545ca100c519800c0c980084a03103a0b0400000044140108106906000144104d00f94145 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 88942671 1250 88941421 88941431
    0x14070204090609080a0f0c031b140601140a0b19050f0c070f030b0a05090d0e03070e0a020702100305010b090f030309090115030b010201090c05090403050c0105240919 73
    0x22000900811041c203006001c0c038501041d540a0000203c060000e01d100703911202c0805072180341c25600b01d640c002000b00002c00290180c440b0ba40c1d0490303489450f0780320701a00250f0f0070000b800d15003880400d8010021102c1814040c904a1a050b2a00c100030900360742c0351413810301282e1420006107100803075981403090000e40d00c030700900c520b030845034001400d07030950315410380310708210300d030b070f02d4035100685803130360007001140320a103103403003030318000e03026400140300d00c2e2813581c0d058a4440103c8141c030362500402c0d0000400704028655184103609a0b074006a448466104114625031150020b40401d4a0308006100c1a8055000c543c07060a0840340110b0200c1c0f802e0010340785110340e0f4a080e400602800c0009108070a00c6080d00c4a00740546083c80403403501001242200e9416502924007030f075100c2c00300010700380200b580d40c00c54087d1600502d4201c820716803070709542d0300341d0301c1c50040313803001a00c050598951954098070a6044400408a00300860004a154011140d02201942d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 88943921 1250 88942671 88942673
    0x60d0c020a0f050105010302010327062408060702120a0906030203040204020f07060903110a030509040506010201020c06040f031806020318040f0606080901180b0a05060301090206030a02130e071407 87
    0x30030890030074a521a1001c1202c110900d0820b0182c80b0a11040f4086421700142030a407000408012408818103045d5045500a544881005c2e114032384500c6492502c3c0280c4101084540a00c0c0000d002c49800610f418248104003c0ca441200280501d100100748010f50740b10780c1c400c188200319102840c0168613a1200e00000d4028414010207816a0900003000000c0044503002030b885d640c001e031203404021044544a54440f82000c1001740002c00402007400545000d510030342d002001880010b06207100180c5240c68904280c0701074810b02003054110701010782c4056019814500710640c200010b240081c06581e80c05110a550b03140d4055286041d480c0d111030340312190303c984080f0b06101e095580d65000c0c00c2d41400380c511248035400c0c22180d05201d0310703074805540b502c4d80c41154100726907510124000244805081590b041d5255013040001da0ba804d40954001c5103201c0005958402c412801c01c0d1059a0798464101120311a0401004a0300705800384992545803555940d01c07a15 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 88945171 1250 88943921 88943923
    0x603031806090d051b0307080d05030c04030b0403020f010e01060f0b070609240f020703020a150f06030b070f02010902010917010b0a0906150507020a030206070f0501050c090a1202060d0c02 83
    0x1650340515040f5090401c4902403000008107501c0c00ca985200b00031a5010355800d1580300e4840707001e0394665920884220300468410b01c01554025040c03100f0311300305910381e600c40c9820f071400d8030b00b40e0060b0f204031008200c0040a10507200398410300c8000704005440c01c07820403c00711841c40303582545400814140f06100054100c5001294048040700d0040d084da0b65601016840c403107038101585c030703088442540008a2003141e00c2c0d04e400d0740050960036041d6a5441c0030403103131070030074104540356651401c2422160007220080c52049213a0303100ca00e4020001000b0060400c521002c40e2305107082c0740c0151b40c1007803c1d94203803252800100300468207100d1950241103130010f000c1e08514410000504030380d0301e030300100c15510b00e040c002c0c01000c58004200d4603400b4001020f50311604881c400c02c01898950028603005210f041458506611902e4a82c2181c004031001495a1800100d40c0b4051800b0300304d0310050410031141c0341c1c880010b50041502405482d40e030400c0f07950748a02c1c10b400140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 88946421 1250 88945171 88945177
    0xf070507050105071e03150b0a020a1e0303050c07020d0b151f0306080d0203030a090f0602030708040605010807081906060506040b13050618010f2120030603031806 72
    0x40c02030024031a5041000001700303004030004800c02c00e1081490043c004a100703004070300e4000030090900d5003040c1000341c01038280d1300c08400b82040d482019000400940804610349503d000b40841086070071203400d01400b9140c0050405c00c032000100450030041e50f03140300100400d500421408440e0340d803098a4030041c02c1120f0016030007015610320750b00012449115000784141a80c0610507a6a00c8002c20307502c10008400f4005a0010300000341d2a40b613503808020110301510403099101019281c4030101c2e40207503260000034422504001c01e0006500030140101110f600400849240c00201500c40c20450302510303075100090500c400380520f40d000314002c1c0c803005284956440d600c10707110380d0b9070b071005c00020b0701c170007208200046500e03052058480c107101d2003000e006603030040001124000345c0c0748041d206000c400e045104407861240941115458051800900701601003010900c08141103c005059030b820410080c0c140c402000350f80c001403640c00b0442c03090b9000b4000540b140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 88947671 1250 88946421 88946423
    0x30906161b14010e0303090c03060f010e04020a0b040e070f1d0103050603210d0b0d020109091e0f0207030e0301060f03080d060b0d061e151b0204090c03020306070302030108060f070507 81
    0x58201395040c0361050010000314060300c108402c0f40d00c081602014152941d0088804489131600e1000401860030701c0500386074018030007051604030640320540d881c030a400542140800341220010400f0a42e008800102502440d00f846581c00640c610741391800c9450343c040504042c1c88401007502030311300b0031404000a006100c0f40c520302c1102c0d00000e0540c2c1101012004d482d04180d6401c0d151304100321076440450701a07444030740050070555840c0140602409200e01d91141d410100c8028000388a00342c3c5071180740c50096230752605410006d04010381004260300c80d0345051010004d02a00d0320340a400c4036401a000d0391074203010309645001b03007450703480140d5202002402d807028002c10ba1041081e0344603000000c01003c201107002c0c60002450003a403810301c581e0208080051f0007a02c0c004103a01e121282842c3c070464590100d010380714118012100540709500900c1145400c0c003005500124900e400c600310b40c58071580555845001c0e14404e80ea41d01e1402040040d8410401c07620ba903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 88948921 1250 88947671 88947673
    0x90409080d0915020909040f0f0506150315270a061e0606030209010c081e120a050603160303080a0b0d0c031101020102090105070605060a0e090102030906161b14 71
    0x45480404801c003420510b4011140302011810031190341e012842694a00c48014001c12400e44e920b5651044100400c0020ba600c400b00000e1480050400c04c4100e1140c1380d1031440c03542c3d144031007090516106001c1c014840b9911800300304840c100402c0c480466940c40700d56076402600a185106003400790220010700140e08042c0d061030f080c1e00190040c0b00d44840007034100a640e5549108404034014080c0b4140042c0c849031440e404900754201811900c0c020f0b40a0000c81100306140c000580d2010750101d035528650303010410803181034407030580d1002081c0c014150042441d013000b8003408460000905214030f0300e02144046c0e00c0d0b41e1207444005000340842c410300d01c0504081d040310440e8401210420380e003504070300c90b40d4410f0081d10b43c000d0060b15414200070b116696a005030000811468101c1c00c5014005000d0b400b00241034003509410000503600d060000c040ca05141c0010901a18000e81921040c00725600c0304502413884862521907052031004e1611100c22401d00d5400449 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 88950171 1250 88948921 88948927
    0x1c0309080607081006080103050a0224041701060f08030307050d0b06030103030e030d3f181202120409180533150607060e01150303180312030209040908 67
    0x2403241c202c0845802218203010035104c0e03668540d41100c1e00102400000c1254120714044001410200c0c503001203c10584680030041d01000f50700111508181d02041d00d0054551409450b114284a0b04020302000c094011000f810040344507941d10010b440c10041000018020726401031560000400721001800103541c2c0d40d4034280180030382d66960781e4501c00d02800a4099030540070b800b10a0800d1710411043c40c003044243c41608030201580100c040e104480c480102c03000070144070b0000c000301494501102d01d100c03801c00d1200b08501c4030280055512101204100310714820a55080340c0d000c0c000864054640c2e01d0b0103c00f2400494020300c03030300c41c0030700e03807005048012821220400c0491640d4240c4d140d151090030710003426141d07205a03014100c0040d845007401401401c0d418001c00000c20360421240705035084840340d101c41d0454513401c140a104143e030021340001c08482c003001b13182c043c03421a01c482600080007840032092650001e008001600c8680003a412541c1025103d03403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 88951421 1250 88950171 88950181
    0x105131a07021e09010504020904020715140c090105030c030601030923010c1d0409030504030c0801020702090603010203074a0406050a06080f07110f1b01030603021c03090806 77
    0x1400c0e0010301d0100d01c95410407410100c00c003c11001012542c5006240703000d030b6480c02d02803000070740c4071084c680c0d0816000c00c040c60105034020800702c50540c54244c0012080f0000850b05908080030745440b003010007c210910035680d01c0800d89030010600c00c07070300c0d83e6611a40300503001001041ca000304811003130120603000d0f802c044001d0f1003000204000780455081c0407000c0b0b44e03021407200441c0038111920b6420706282003d0b88840305991003803c10b6441e140e01ca40740d1903c07108055200c040542c0d00024030108600b801051660404003d070000d6080d4200003801030240d00401c0d20b030402604a6403016480758400e0000000303004a180c400e41555090006810300400310b8200c268040c034200500003805060078501d060485116940c3d608142e100e08078506a421405403440c0100b0100ca000018206800e120f4010312040c214020021103041648080000480d1a0620b0525181000800158030392032600300014101d07c2d005482d6607410314040d41e01041036041501c0c14821001001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 88952671 1250 88951421 88951469
    0x1081302030f0c0a05100804060e1509030d1406011209030201020f0a0201020c010b09090d0e0f220606030203010f0603110705073312090201030b04020307031d0a02060702010513 78
    0x81083c510030341c1d840c01c4160700c0303200b0f005046090004180008107104000380100300f042c2d0103045100e490105131074160500d1b4001502040781039801000903080025500c48288040c070fd1906800301c1c001d40c51103140342010020b0303d00c800c0b440303201000540b00c41054040510030350440d041582034035905611400103a078003d000790002c619844441d03203051405c1255151120805110310725100051100141d0f0050890300d020f1382c080200e4014220b144840710a68a0a5000c0d0070580d50800ca107950360081000345081c0d9a0302da0049061510403c0103001c43d403001800c4105507a81800d001c5994044090404100c1c0f04502c800b40003809181c2c0b0103d4914141c2084200103400c040c034858400255406076004098104444030200300340c603a07013803410700245d00407502441c014140096500c0d03440003c01c00380c1e03100322080c0001954581c1e50000315440142c69880d000380301e9000302440c08807580490301c1031080240c06414040b022803000e001c2d442c540783c02006400d621414902a0b45c1c10306040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 88953921 1250 88952671 88952683
    0x50d0618020403050601120f020d05070b04030303142505070203100221010816060807020f06012403020c06010e04170d050403140307020d0f030905030c0703021002030c0c01081302030f 81
    0x868040c0900000043c1c1c1500041c2c9005100c1e8004c0c0b210122900d030b2350700b08500c01ca49070202f20b03a0b0340600040003900f201c3c2c1901400095000e80c40c003007000107070400d404451b18401402211900244054a40209013004903d51024040d0406d540d840581d0300000741380158804540588a00001d056060325500c5101541503150324550188580d881e0f4014544940c0050200400d00c1c000c4502000130620510650390001614010360f43c0c071144c02c007a402d0404a090b082034441da4a10740d11512280044809025022a82c1c9011403d00821a9800703444c0c210600c0780c000d220211070007080600980007080e004418180706c855035070711010160f01020380003c03542a400704000726400440008524222032242d12241e02030400000c901c8425030300240d160300340c00e0405503200c11000001d081040180380c43d508040040401c945035104000c0c900542401d8941107400601808100c140009440d0300c0b80142428141e081e0340c0c40d4040760010b82407841000c2e5051241291411062a011401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 88955171 1250 88953921 88953923
    0x4050a0903020f0a1505040317070e030606060a0903080901051308070f240c110a03031d0109230105070f060f1401080706111903050d05150f01050d0618020403 70
    0x39902ea40e060440c2e07030f0303440b01c28a61020b81000d907103941000602c280c40d0310075035001e842070070002d0300d0481584226041e0541101c0c0003003c2440c4006610302d034030b0f0070490b455120354200c446903d00b000c0800024412049440700a201e10400f1465500f00c0c1c0c00354080d07491030b0038614a100032581c0d03610512569040b80348101582c01c01030750300105415000c0070507190682c1e030000b003003500912000382c1114440c00061050306d140c80185c00aa621381d03501c0c002d420046001e0f558003481c0000d4524040d8907240c00c0000b9a05204000c0c10810a03010840404841c600c03507100003020180c3d1000041c0c40c40d21500360010922070030844004100010380e40f0034110490601420081c00000c811059401d844c01e00580e40ca60780214801c000c0d052084042c02c00341d040b990107443c09200c2e51188036440e185402c030220081000850f6010441041e44542680440113000200c40c60141c1804034800800004035207042010004141c1c020f0301312a00f01d94018092061020110100401503400035045800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 88956421 1250 88955171 88955173
    0x21060e190c090b16020a090218040509010c0806150705010606030c0f02010b060412020114070308060316050f0127080d02012f03041e03080703050a0e060a02130504050a090302 77
    0x60410700ca01d2160300b000040d10540e07440a46446140304013060f04590795501244d1010740c001d00400c8200d42c900190504003440081c00000260700707403c00c0300740da1000b00700c6400350385802a400d21a0342d2010315990070000a403600c84000c400a240e01985202d000c2001d0110b6080450001e03415500da48003035a41c202d01c0e030b115050068140022803d8407c04488168004d0f000d210034040034103601c1e85201100d1050400916900004c0102e0031290440b10090b40894141c1041214078101404a80e540c2c145a0035103c0100e4100000981c1c810314031585207041200c480e91186a0a400c074210000b4841d0204809101d10341e01e0080a5a034101f001503040107500300401040300c1c140303085965a105605a1000c3da0030310711940095903d4000910954500680007540b100c180c10047c60382e54003501a40d21013a0600c1c1c04031000d000c0e140043d0414850b0783c0f500f4445a641c000c08a43c990700481d0380c803400340e524013140c0484040002a5005a0342c0b2600d0311051085c118459403103140800c2c400c0e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 88957671 1250 88956421 88956431
    0x603120f03070f170c030a0204170f07211e050a0605040203120a08011a070206131d060d02090405010623150f041206141503010b0a050121060e19 64
    0x85086400140c0560941c008601c10130103e024002100044c0d68080e40380a001400c0558a610580740440d4884541d0301c140c001c0c03c0b440c222040c00b44044800340000302c60703c50a07100021107100664a0700a8041d000e1000a5000c01840d041003100003030705034220003102c2c114280d41c2408402898140c804922034803524001000e190106810f44490011b20303140c000399a8a014107200c1050000d86241ca103e2070b00304646070050352080050034200e8174403c1941e40ca142001240048080d01d040d02e00b0407491144d08021043c2e85184d02c844011b13605039520034081c0c6445c85c1140c0544000e40103071a1543d558810580d900700703002002c6500c48030864030050003a201902c240b010f03128402101c032400d8410001484503100000c2c080c001c0c03c2c131170500020070548603202c5030840c1e035054035400c0c0c900b20468007070a1145400d00510030318017801c0700c0c01c1701010310b00b0001070004040c2d404041c100d1050f032022100711006a1b403041c1c00604e05107659020030729285600e41c4419510204203098a4948 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 88958921 1250 88957671 88957697
    0x80d0305070f05040608060d0b01030308090c03011802010309020f0402031602011d060403110f0102040909020f040b01051c020705070303020a0210080c070b18070f210206030c030603120f0307 84
    0x5444164001c0c102d503120300b0300d02420030b07008175646000100300f50f0b04800e4a0080800145591210b0790081d8001e95540381c1900b8010301c000d05010081024034800d030706100c41c0f2141247c5002040504550900300041c00d1141440459100c010704c2d00364a50080c030100c01c000007440c6d810241e04100c4255802000820411801c00200300d02c13048450210f90b11650002e03001070b00404060000d03002c0141203848030a504030003d070130390344140c00030600952aa0045811401d0910a001d00b6034002c4606008202042000030820f028410811b80032007030340d0391421230780c8840d64116080320350444241c4490310346078280030b595801501c40403805080749240781d1003444e128980c01d40c02001841c40325032514903d9107a817550701d080508a002c69500e80710724100c0303841080001c20001c082e88403050240501d0070340c9a00704d6550800c0318000080490722844010381c0c0c0c403012254410100ca154944949900700403e181c01281c1d903070105114400a400812101c8102c081d610401c10381c0c1d078056050711a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 88960171 1250 88958921 88958927
    0x5160504061a160b101403010e060a150b0403061a06070803150604090e0a0b070509030303040f0606050603280e030318010e070906140303130e0709050901080d030507 73
    0x10901c1440c010849000ca11050300100c1c00042c00e0150f06010302c0d00c0d48050380e88400607211016101c28007665102c220404c0354405400c3c0040090720b00b01e00230030246508000f2240c803144018420390a00e9076940d0156600c00040c400140a400c40c55943d41c2c0f1107440349052002454049100d9441c145540354003025858a00101d82c4981d034031011960030340e1a0640e0031004a83c0d04d01c20f141c0c1c0400207104c040740341400d070320854006050b4072000313151044281c10301040205020b022541042002c0120402c0303502e0000c11690065400a000080d00c03025090080041900743c100d26031008001092003800901031240400608694000c10b29142d001403100003218001c0584442942050000a4100440030710200300b2001c0c0c04004101c003d20f1965080c10500315400043c2d02c2c1c0d0365410207000e003071040082c0d040f81c94420740082d07242211003110300b004803440d0300c15100040d00c401d00040340d2034400c11055006100180002109584440c07919403034070340c0c5a0715540080d18110028001c80c2c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 88961421 1250 88960171 88960181
    0x1e01060504110403020d290a090219141302040e0c03010609050d0b06041d06010611071508010506030702070b0307090503100908030c0d1103040506070206010e1b09010e040905160504 80
    0xf0b801840081004d5031070f0381300c155840c000c7d80031700d00c0402540300d40c0450402c002c944600c03d035442d41000800ca0042c0c41003255a203483c0e039813030080304130391002480840d52800f0041c1c0640d801b128052801903816804102034860380e0401c0b6170400302401808001200480030b0341c1aa1b840d0384503204d41c65141d1090000e04158108041c02c07003004c4401241441c00c00e40d104040348420401c1310b030051540036480d24a000020780c0b05400140b00c030700c04540060014441400503010400c1403001c0c038036400c58000c194580600609100c1c00f400800719980b90f008018050051542902003034803880c4c020b0028094400c1c5100d000c1c00303409134005210b0850f16030301c61283c0260788014000c0c299214651007a001e034005002d0000c0c1540c1c0d40007003400c05d0030001c003d144294450b00041280d480d00b01d800904200c0188c0c86107514000304410320000b03a0070f842c1a2032500003503580c40d40c3c8a6102000403101060540c10b4560040d20300003401c1c003800000300320078110002080d03145040075606c90074041156 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 88962671 1250 88961421 88961423
    0xc08090d380a0213060809160602160909020a031101110d0504060906020309010915260615180d020f10030905010b0f010e0f030c060c06010509060d0317040201021e01060504110403 79
    0x4096500140012405174000603000442c03c8211000c0d546820321823010758502d60000301c0980e00c076010b13018108002c1e03951030024214600702440b0703008265000c00d645110718000240341004241080718140d106080e1070184860442c102d5880740105c4202405d1640f250040000049102c3e2001c5001c5000100b01da500c00f0f410b13583c9061440c43e150714810250354224190301081400301c544021914004043e071943c3c4020100c07045c1900700f50b07007002646443c1c5060840400014080044041d0000f01908240c1200ba1031402d001512440024590010042c00c0c44c0e119568201400ca181e47c1a8020420140f0030002005104ca0020401510190b01c40c4198001202c1561040c0c550030500d203a00030b0032402504486250510000058842c0c0101c0d856a9080d0700101c0100100d14008042c641c0111003564040c5040c0350a840040202d840d0072640300101d40e4500c08102164800c104a501d002e2031a00c0900010040703580d554041e146c544689031140e0f040000d05684a2024000ca404032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 88963921 1250 88962671 88962697
    0x30c04090f11150406030519140106030f0f38060a12020c030c0d08010e040c150c1502071b05280312030207050105070c08090d380a02 59
    0x60710281e490078502c600107503806402c00c4104010040c0903420b07501400160080703840c0442c19241081095000054640009085504041400d05900c3c41d20b10400c2c15a170440c41c000c44c00800b4681004050030000004103100c81c0f40071850406078106042041483c0040200d00100d0990500008080101103038402e03400b0000b00520740d0258000d041d00701c1c088490388405801c0100d040b80081c1141c100c0036166000d500b14410f10500e0316880200036001d0500700c008601c6070300307185d11203181501b818049e00d1400d5000607140e0981c07500941b1108000c540c84841e0781c001203118100c1d14081e400101d02101c25403025210000341040382d48400d000d030703680035210340c9003403001002c0310788a901031489140a1009510000c80032800f00301210400650640b800f59942e440e51410341d084440013400710702003103144116800050005e13004c03150b06950844490841c40e0703003030070091041c4556440760702200b1500d05100d8104e0a00c8182c0450464000c4920010b81d80c460f00c1840aa00c14aa071402340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 88965171 1250 88963921 88963943
    0x100f0603020a09050301050405030304030f0503010b0904090f060911030c0301020408030711120f1b0d0201120209060d05010f050a06080403090302041107021002010b04110a021207020d0b15030c0409 87
    0x61248240c0c082c240503451440c046503503640d02c0e00031030708485013541d05840742e0304000b042000340368010000100a82541c40c1c20383c13544d850010f50028030f029046241d4403841c0c680c0c0c030320020b01440d4201031071001d03006a0200a003083d5494a14608020116494024012070000b9072241c6418400d0ba41101c10a802842c0351050070744d100c803d1046140e044680c4142000b8240042d001c04020144440c0d28640040c0014984044450354030200079540503ca800c1071819800141d0742304592a144160301c40e03005d45c98030380c0000096002d01581e059102100d10306000001d640b00c03031901c010100c0b40281c500c2d03c0c031103440750b0045490076001c0781c0260100e66401c00c1000103003400d40c42202141e52000c452403c1c18042c0c3e0010300800001e00030400141c7d15010300355200d00e42803145032190080c0120580c545115110060345503150070b850070b0703c038080101d1034000303640385c00c0102c446856214850b1503c1b0300d4090950201030015450b554040d10a80c1d01c09006410948550704000d0340050081032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 88966421 1250 88965171 88965179
    0xc0c03090816050f03120711040510060c030c1e0c030c050621040809090c13060813080d0f060b070302010513240e01020406020c13230c040b0a09030209100f 69
    0x1c4135040305910b44d900740c42140c1e80c40381c2081d003200c05030900d6803048554034060b001e000104000ea0300f0142560101d420060000c01074943c100c0001c00d0026407501384104140d403a0708051008208803a2a035075050441034000c81000030340c0b00c0384002d0b280b09010b0b05640645071018420390f07000740d121010000700441582804a42000029a4007901c50320030310385000151070201e0300c001e005a559240307000c4c0104419400c00308407011000504190314220a039407410b040c000711700a001243c0544441400103092400b40300c7d94110405083d82a0000d204840c0c1e07075401c2007401d600501e002d0b0010f51802c5c0c081307090100c00b41c04c072840d1181c0010301e460401400c10304062802901904140b902a95098500300c044030078009000106406d4020b0a02142000c080c0700070f80f00c1c254901c00d1100d00c0c16144400e10700001c01100d061551409800c103203552000c0c440000361103a5003001040e880b000ca100c841c12a07201280790144c034404c0e030342c1540b80c0d200c2041552503c4014015064006080c41c0700340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 88967671 1250 88966421 88966429
    0xc01020601180b03100f0f050405030906090d020603040b011503020301050102070603020c150f0702010e030705030d0c09030c0e070912020a05010e0a0302060f0304120809070323010c0c0309081605 86
    0x402c12000420000985860b0702c0700107450f11410410700710b03000d07450b018002c15002c050b10414203550403c070030510803450b2640d1455103034403484000f1482084003040d44c44658a0754031084007880da0150200365070b8107050800341c0d400344003442900941a070744240000760300d10078000d42e41203902c1a0000c12025090500030740c044d40003042408901e01c030322000d4a00710910854003c1c000c103003041e007030030141c10140002829109041010032559004000d040c002036000400c4958041c4030150004104050000403584002154005880258074442c01328840c11039417076450040300d964591100d00e96807108000007034000c504010358032410600d000c00907940142d02101c200d04006207003040094a030303030025135203806c4860199014131020040000700010320004034083c4065040ca01c03075903c1c00d00358042e601d5000740802040110154015041242d605031034440104904000340300901500c0d074000d110b0480c00c9001d5000403078110000460b01008240d0001450385803244511250905e4248 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 88968921 1250 88967671 88967699
    0xf06151504090207060b0409030c020a0803180d0c08150f1602030703030b190605090901050105040305060115200f0606100f03110c03030c07060b100f0809070302040501060e040e0c01020601 83
    0x1034407203e0b25101e41b0600b503030342e40c4034100b5000d01ca0b469030350804005005200b100b26440d0815011503004002c40554807401d40b04d070721314400c070855440311422850b00e042d102034465903108034094410186031070345140ca0020f00e0b03031091940340c0048800e03a0b6640c504c0c4d607401100b501c034240035802c100320190109210b41c00c82d92018074003034507111340030b4460441244401c15503448040003c10104555480b440c001000c01d0040c4000d00c1c1039070507c0c0c02c6440301703600c0c0d09042c03040303920440310180300c651042d00a41600e60600d0550350b0076440c02c0d0a24003019100d4240b456665528094000002c090b0f103805450000a20304503030b1980319000f0380361420740040040801107090f186007802400010351040000b1803144601c030b50311544038a014540201610200c903099845001c603800801a919031140e1101c07030403851407925009540364a006c86083c4062a0400794016082100114070260411038101072101300799000c000c03464038602d001c3d4541e50074034882030044e001480100321689880300340c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 88970171 1250 88968921 88968923
    0x6050f0d0321060e0c04150c0501060317040806060102010509030a0c0305040312021e1b01081f0e060f010309020307141516020f030c130203090109050f06151504090207 74
    0x846a80c42c0180403200348644415110641e0381601c49000740075490b6101600b40e0403900c403420031070405040803042d040e01c044800c00e6400700f0008003850000d12509400c0540210703008004400c4252408052115030760103030040f042148540c1d4041043c070752052260510030320a080165050910109045030f958007a1482a0100a414000840815070045401d40c0321031194008003600410a45400d442080403484480d11303401a0260040910b00041c40d080516024078229011343d540b0b00410502e03018803a40851651092000441c102e015100d0440c02000120f40d0603500d03541c5140114180c0e004140020740607002850104450440c80c0024501424010114a015520781020031082e41041d41c4080020b10620403c80c150b05000c03580ca8858201a406400c00882d0280070480c9091030440c0001030650010014560300802c0d807003d03148642c042e040d5106442074101c0280c0c1d982040e41d800030707125122501d180b281d00e807800c0c46400c40052851181d08140c070f040c000100079001004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 88971421 1250 88970171 88970177
    0x40b100c060c11030c0114100605180411070b0901060b0708090402030703020c06070e0a09022d04150203070b01050f010206040303020d020d061e060e010c1401021e0d05090106050f0d03 81
    0x3600f003d02c80a1000d04018800c0c0000040d11003080404008001e40c09889480b120140328402d204443d071020840f0405512055507006003081d4402140050141e110020309030a0003054090402019031143c038002c03d1880300a001280e142c841c2c101d228440c0e010011300c080010000100c250810b82c0280d50710920a090041c2016102e0711910300300001114107500284a0140f0340034546002200301d030103854808021801d000c5541c00c14070080300794140c0c000d614269200b01300c0c54a4038503c2207034040c04c031022040103a0150000c001e1350307a812001d01254001d40e414008551801e002d500956138040c141c0c002c103100c0c0c480ea03c00381c009510185d041035845808000001900405014010081020074410443c814698040d4920104280c000d0001c21200c070403002d159070b0744100d50003c5036800003c2c80e442c420360aa4450300901c41c4902c0e12900d48041e0302e140a440f170070400584410207040b107040c0010741c0c581c0e11441c22605580200b60b84401c18080703e803400e041116800e4510342c03080c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 88972671 1250 88971421 88971437
    0x270f0402030c0a0201062114120406050a02070b0c19080403061a09070201090309061b120804051204050105030a021606090b061311090607030504120f02040b100c060c 73
    0x14045800c0e07a0003203690401c007180004074076880c42da0910450005000b211942200040004401c81d042d41e21a03001614040a810b84107074820f4080c0b00003040702d0310a00809540b560b54840113400d0f60084105000540102c0100085540a8400300e4804c0c08042010300782ca5012a43e960130300e0000800180c401c0c0b8010320001c00002e4840c0300e80ea0f203094010988101220910081000c0001c0080c030305405c6905007602d03180042d801c2500c180c1520700318282601d0010301e100798103040c82140384019150b403581d40c000c165003d40004004c1d010310300a2040d1881310401d450003140a01c11032082c0c0380002c1c0304000091480115501504211001801d4a080841c080d00d506040c0c1d07461000c20780c0c0e032a0039142400080e14104800c00c9401c82070010138048400c44d000b03440d00380c0c0200708d9038030302a060010703c1070109481441124054189a007595036407941ea0700380a91303110501c050403405245014602507640c070b490500f603010320740c16645401c6c040c98140d803184040e18005040a0a1010300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 88973921 1250 88972671 88972699
    0x30708030d1e020a0203040f091a010e030102071b050a051e06070c150201140a060b0414010905030607020a030210050622020903030d05100e06010f0309020109050604030302030d0b010527 82
    0x280003c0400e05078644c004e51f1106d003072450442c845401e960003104030914100009500044030110004014401d003050740d666085e101c00b207406842052801002c283e0304818000c0d05440380e07045001555000e039008082e00e43c0340d00a008058000342000041c145400c0c440c18464603005008050082c89100d200b02d80541d2030040d544c416003030492000250b5140c6084100c6c0d1180c0c094031a620282d1143c040c04107070714018180406204500a80c800c048030394090b241d09902400b48040202005401c0358014a068140251100d0040c01e0450040c010089a100001001d014040c060710005126052440004404416020030610101841502440303a90495542480500060b55525030049510718150140c0741001d03040750440c040e021300ca6828440d07a40d0f4400249240345905085c005181807040c001650302615546c8055405000014003204140d40800600320001241c84140000200b14005465030b0041003540c3c40d002d90f490b0489140d8401c903a074402005903001e84459180c00710 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 88975171 1250 88973921 88973981
    0x2060906010909110904051c090609050108151002030c101407080a060f081b1002120f0702030604030c0201020d020604150c051210060809011109062520030708030d 72
    0x4a03010390341d6030440729101d100090256800765884400307151007027829042c1075020700b01c0320309801030504000d20140040d03500201c0c921704502c07000e001014079404442140d402980ca9024036101c005601075101107254040f4240210050150100e80c11811907540f0340040340c11000007800e00e03840c90780391040001c0d1100d5081030000500710319005046541c0300c04c00d280c0025510a05002d00404000700c14005607940030412000302c04642000c16a52110035120300014000c1c001d000e58980902c81c02d100426800c0414511664400e8080d22003440c0750800581c1c54900494029040e000c0e2100c8441d40401540e01101c04098942825414021002144d07856008110754040356800813202c01e00006030041529075105503080002d00c8035464910800300140181099540580e01c0400e80d00c2c40c0000c002140016602403254036007400030b840c00c004050061400481200d8464444003003100c2c1400700b1404103845883c40190b1910400c1d04441c1d0007041c41803906c00d1291500300d25100d000c41 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 88976421 1250 88975171 88975189
    0x3160b0106110610150c0507060f120506210304031a010602072907080705060f0117010c2015090a03030b011b0209071803080c0601060206090601090911 67
    0x20080102142640c1000405030982a0600d01142a43e0140d410405107185500545003965a40005030002d07030382128090b20008a010002002402511404031344540c2c032445040040c00b43d6920012519010b0b8046001c60300c1c207407003190b000a105808295410741040705000c001a07000308407460071b5641e42b03802d00c0d620f9001581040403200c01c0010000185d0401c0064081d0100203000f040d05100700b0001c030140c41c0c145d074492840c0d02c2d011450f1070a101da03003000d80c0c40cbd0f150040142d88030b51915030781c03400c02036a0034001c0b58141605000c0c030f00e451810502c107000613010300351100110403101450141104a0409100d2141c2c4078050705840300b181c100031200d00034820000101001815417074081d0603500714010361030410903030990b1428001c0121101d5241030350107a440d07a243c1e48840000301c8241d154020080304840b19240000100100030f4002c0c1402d100c40015150540d803220707030407620340c0340c1039914181390340c0560014000d45040342d000c0c0c819103100e00421a0f0002102c404519842 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 88977671 1250 88976421 88976423
    0x80d05062206150206010608010611070f09021b01050105010504050f0301090618110d0209040609170406090e0c0a090e0903041508181501140f0409061506050c0a03030207050316 78
    0x1540301c0c0b0081240707401120302d6080c0a81940041e181c2d40d8109900241800c00521843c42000302000d0120203c2c88184091801f500d520324403548036686a0856070302035401183d007040d181070440d0003100560010f00c641030503035005079584d40c40c01e403402003000f4444010000003903043d581d810440b80001d800d03124050010322901d00c0702501441502782080d5211700c00b22594081c80b28000a04012b07950a08890350141d44000001415411401c150381605030418000440c0c0c1070000e00801c0c1640c209480408540d114800d22a2a41d0745991424450017050303142004a000e038a42403007400c0b40300800707652020241c2c04072424559075103082d411412200500d480414070030b80a0094012001c42d0a03005444c1040c028220f22407881e0040c001d94005108000640d00c226501a41a0342c6010f000e4403503480c0244203005656450625000801001120031181c900510001600501982c02d558440885a014081e1460300e500c05a000c1d41c40b031082118280030820268071f6030384c11103604501e09 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 88978921 1250 88977671 88977739
    0xd14090a021306030c031e02030609032703030405040b120105040614090c1f020a0804180b01080c070210030204050904050a02030c010c020901121a250309080d0506 72
    0x500a6006012108210580d50b40c256403c020b014004507003031803c084d0403a50300c010502045040138400c4201240000d50096250103450305200f21040000003800b00304e2201103070802448000b0249000030074462a00c01d8041d0004c0c003041100b440c155014101c2c0c84030143c51260360000c00713080c2600b11003003210701702e500d10b03030722420103000d58810b4246583c0a82c1070001403a1540c01c0e04002050481851040d040c02d10602240340d40091003445100c00080d801103e4030384564071551444051300b00c06540e0001c6034600407007040c1c00d40c8105d02840c020902100118500003c680910810a0880c142d51003807640800000840361502c90480e48940d018001030808050a03104050500c01020095810840341c03c0054000d60b81d021a4141104e0080c18240d59a0b0b00c2d170f1500781c003034080c4241071040140194003001001200301d607020040c00c01741a04550346002e910b00a40840307028410103003502c1c1040c00841c62804403680400d401010040c110b0440d0604001500c1c03640740160010380300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 88980171 1250 88978921 88978933
    0x5090c040b0d020406030b040506180405011e27030f0c031e050d050c0301050a05120111070302030408010b06190810180209031002181507020d1406130b0105060d1409 73
    0x24451b03040c03003007007550901200c09201340d003001c00000b080700c03c03010081c2c4103a401c0b410110b01009002d5100c1c12082e0285c0390040240c007648085900100140c00204400107207042088980010200159011561644540c8444203426000302c0740126a042c040b000c1c4440d405c241c0900b100510b99420822040340c3e151a61601c0306402c0106450300605005a0040c0a02c0140032a0703840205e014160b40d010f5400da02c01c80b26a070455070140590b90884171459400180040074103902100a1050724480002800812000310038040903114203011848481070a13202d00342075601c81c01c005500211036010101c2070540300c004441040e03581c0102c4403a415030006007107040d070a09003d480701c0340000007411820199443c40c04500440a410003904c02c00020a07403101d4248108203130343c0080e40113424050710130301c5480c0039170404040000052140c480c020004241010a0001c039105941c000360011080c0d2a01d0700788401500071414030103050392500c0440c03010480414030548075441c003e0042203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 88981421 1250 88980171 88980179
    0x30228060c021f02132309090312040f06090b09010c030e16032612240d030f0c0602220f0e1303050f0a020705010e0102010c020705090c040b0d0204 65
    0x1100d4600d1907031415034100458074114640461400305600800e4100942d484441e1425007480f8641504a448041c5105d41454a400b640c0800c1c950018025501070103185c6511031201c2c1d403401440301205800984400150019130303809900c202c0c40d40b0a0f6800310f501d1041d03680d04240d6000890b00010541e66405500090f9507140c0510550200520060714040081d04280c2100e00c01600024095001440d249100b4031408440301701500754441c1700355142c00ba00803504480b01e40c00d43d0032a8141d20028200c0041824030380700c16605030802001c45514040340d0b50151008095241018180410b80031105c000c070b54140001e041440d4002140c1241c1000ea0782402c098104503044a1241402035505100418a0366281500000d10440c5071030011b1852504540e070780720340c881d40061a40082141c0a00540028070708003528400d0700d9204004540d840124201e821240f0722200503030020004001c00e0034007022142d04201e807038098514241c0c94503100115540000603140c0060b40c0010100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 88982671 1250 88981421 88981433
    0x60908030a14150d02191206020702090a06061b020111030a080103020a0e010b030a0218060c011506030e0309010c020d05030a08070e03070303080a020d15060c020f040e030a0c030228 80
    0x5030344107840040071103240080d0340c04074409585181009000e486d200030b4080c3d40e240440c0b01d4070024414050780d0440981c0600d8214003039040725100f2030240c51504007003000b00c1d12900a042c19600156129040c4600703e40c4040f841005416003603040c81030440884c034103104244000c006121290300c40d102c503549148140255110300350f0086201d061420014003c80c0408001c490b0003180550780540c8800c034000d4081d5200e0a8000c0d0340d6030108002611980c10301c03064004a40c100c11503082d0303001242c1d48190590031388028500d015459003080100c2d10340380d80186850f0b1403450002c0d0000d2a00305071030b034610703155600c80d5160300c0c0862011020800c1c03065001d00300440c00b05069000d401c0a526517a80a401203001404501c9a1600403030b185007401503e5010f114102c00f000741c040300c1d255076510013500e800b10111044c1e0203050003505076801820700d40140b142181182004503c0c109000714100c54075407170100d0850850103100300408004450b0801d500442101c070540710081001071400b4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 88983921 1250 88982671 88982711
    0xa0605090a0203040b1609050303130e090c03030405011101061206090209010b0705100504150606050c010e0a020a151107080c040e0a0b070f0203071505040201020f030f0d09060908030a 81
    0x200840780d00400070440019080b8029581000b04a940381c902801c0072001504d400380c0c076401954142c840800c0465000084151400c04c03644500c01110490700e50300c45050f00d40301c1380744d10190581d104200411142d4801d642c0211990414030002400707a07140c4990902c1d882e40f040c030030b4800b141c4540d005015450a0a0800d00410b81d401301b840c80c00c800d51381d80b607844861030040c0f88195076607800003401348810180120b240c0420342000b000131075143d29018105800c0306140c580c040d0f1030100005580343c0c0005c1c440c552a0340040c41403017013620700b080307040070a20b03004000e40030030800b2040c060100c081004104094003250b00502802d000c29000e000c21100c101c03d0001d01d5070300c813110400209070303100d60716600440540b07006c1c03648030011030040c1d1851060b82001801801801c52203482e28031240d1000c1c0c081d600c03da0941d11b0789410782010607900d000c1c44410b0303005071004010351034458840f42c1c401001e440c4a50781c08140d4a000b1788842c20a6002118480800e5490b10380e01a41003500383c0e21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 88985171 1250 88983921 88983931
    0x50604090b040c05030f0c03070504030b04050604050105100303050708030705040305030c011e0b0603060120030a090e010b040308192d090506130302040b06090d0309180c0f0302090f090a060509 85
    0x10250640c81d00070300032501071b20041c18050700d020000000c10086c0b4491400c68002d981c100180c1c00303040c1814901180c0e50301c8226000d56a5520704008500780c420200402c00c00c40360940d80342c90030706160751100300c001d07407018080c24144503081200000149041c000b4125003000300000081c442d200307588880c1308688058240754094501070094107290f861005480d0880c0003840c6c6094100301d0760b10b42139440003448101072281c0c03101140014200d81e102e03d013001529800c01c1215082d0741d0720080199680194040103041441c10b1014080c0c000002091301800306c04c03490410310341e0f1a030200076021016050000030424183c3c11152098681040b611002044281c44003490f261080240711000085404000e1003240c0b1418002c3c0c06607545010307107450900c000c03c61321020840c0e00e8050b04c540c409218045407002c2e95074071700141052070701c0382045280d000c2d2039070f203040305200750200d0007507002040d12a031200c1040c01c0404281c81b01c1c0c103503e01c5682220700000307116050000300102d40c10003c00b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 88986421 1250 88985171 88985177
    0x11010501051008130b0108010b120a1101111207030302030114010e060301090c050408070b070210170408030405030d0c020102043318031a041401051005060d06050604090b040c 77
    0x1004192902c0c904400000420f1400883c191544c4064140404003000c0141c200d00501001003465801036000070000d410413201820610010202d09031200b0781e4510142404c1460f500890b02940190b42061141d0b84104c20350706d050b0f80340241c0500301e400070202075000903030100040c811082c85080c0a0090308017401c10a0412a2150015607980704c1405500e5100707845100240000c1d00070810740f0060301c3d10b54140c0380b00640369181808140c01020040c1d2040403c0780d0003460b50f5010350b210360b1145d146a4119103069482c1e840345040ca60019008030380c03510003004a40c1e262403542c461886e40d500713107a00150350340d440c0004548009a840c8002c0f940b040307448243d0b400721141c0710000c5400c90240c4c142008100ca9039240440100216800940038000140c2c0404c06441215113040c4581c1c0b05241400c075841000f542603080310401ca842c203802d00050031080c0043e00e4080301a00301060f07001004200b1581b03c5000c035041d5000380d4081018103407034000c00100791030305002c1d00c001100985 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 88987671 1250 88986421 88986431
    0xa0f0b03030c061503160e160c080d05071e090303120c0203040e040303020f0301030506041b060e0103050a02090d0503030603070815070309050a08040b07022b060203091504050d1101 80
    0x9542c443e121000a804800400058611800a9201404001c2c100c03c1c407506005505607541000611360700c000c454612151815040c4d0010302400303441c040591913045100c2e00c1c10320444089020082901034600014085032081400b1340001d5a2810809906113613103e0b20704902c0e40c40d014090400795146600050304020142d140a640041590101c80e5400310201640e161828142c00034403456a035210303548800400401400400101107001e988258148030b600000b2020741e6620181c40e01400000818006000385958403d030032070707a00000307407040c01864251010000303111898205c3d401c882c00e4201004200c800d01c0d0501c0f03640000c044c3c82015103801410164041001c11000f4110400e05a50b900c0d488117000041240c0483d05510124850303560b42c49074282145a040544101c1c4110074411800b8000328101180890a648860300340b0107906250307403500c0203500014041d40c25440b138140000a110107084109000b030303000c5c03005040c5c0500c1d1000001d00b200d84207003c20013168140303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 88988921 1250 88987671 88987687
    0x150a11030a02100902060c0f160614030705030a1d0d0e0d02030a1e05030315040b030a08041703091008070206010e0103020102071a161203060807210507030b0a0f0b0303 74
    0x101e18600065500c40f400106028140300007102802980010b01c403900c00d003096100302e00310000b01c00c0704031080740681070320301030b60740700229500040c002040152180a00c0400c03801e9008d800559086a00220045210300b051100300050030302380c2ea10078500c0c0c0d0103450f449040310380103000d07100035141c1a5501c12110400d9000b180c2e40d0b09414070020701800085014403c002a0760b0301142d181d0368003009599607400c03d48407940300c46a040d5402c03841940f030710902207100e180005145107215840000c19040514085a00e031414004215440e240d002c02c2180d18090b07685c0e04d5621440c29034a0715801c4003401c000400926000050308000c412103800001480540e800003510700854a030600946005594089609001d00071117030180421034036414200c003080210741524080340920340c1c040280d90b0303540083c5680c0d002c15203d03030007a04104144124413668207111100c1254002c400f102c814a41c1c03942c0380080c0310012030340e00700815964000a0100c40003800340c4414224110002d5041c8118 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 88990171 1250 88988921 88988923
    0x11b090902130509180a050c18040c0e090304091407200a1704240221040b07030c05060c0403060b06070201270506040303020717010203040302070b030a0b150a11030a02 74
    0x50083d140b080304402c1c00180d20003908000b02104040b9007064412a1110f450480d64418820b0300083c401c4003c2107002d80c0308034160003400d1003a9041100038602518180c509540300c03002420300d0001340020007011580880d10300441b6020798101a50b040585001c401c010041d03000d241d02e400c81000039000c52010072100003201c0e0341140c2c0100710340c46051002240c84e80c842c03145030b002031b58401c0403078031400601d0786a0b40c034100c941205800341c0d400c0c0320b0b0b02d03141203d0700c0c150306075030140c0e07110300340001e21080041030040c05010b40b20b82058490080151111850441c0c1206d8001c0301040004080c0100701290151500088054072254103000c1141d001901c06c0d0346041c140610001114002c111148804040b071004140240c500c60382ca68517400d000b91034040500a02001800c041039a40300039005100300da01c1203406a01a008950800c401c040b1320b9030000e0014840d058540c640e103100741e60317407200720100d160102041e140c0e2070b014003c000e031941c1c2ca8041407614503002070142e40a0310750 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 88991421 1250 88990171 88990207
    0x405030c030c0604031707240c0e0109030308041b08060108390d0c06110106080601050a0e0a020d02030c09010e010806090c090d06020c070618030c0e0a0e011b090902 73
    0x5884040c52417074600b03000c6c004c0d41d0b40c011554041d04915200c1402d040360000d28040b40303440c10050800f441a103200510a58001004041003400035241d4002040428450300400390010310810362040c00140d00071704074509010346e401c4003440760807010042204040c104003800c400f041d05d02e40c0801012251005c100c002810700c1000d448080c2c3d80044504541e80e010502d181154012011b29600d40c450714024010000103076004015840c0003008600544002070307241c12150020520042c0c1400c1448000341c00b18064480e071402a02440783c40300e460240d0001d140305038003102100303171259611000181451904180740d81404052018019540c8072480c249070302c080b00c03000c0c490303444800d50081020b0101c0e1201c0601002e102203440700c10108042942000c69040355215407456841c1c912005588045110003058114075020400206071650300707481c2c0c03010340c40100080c550440c0c6402400c0da035401c20b41104041202d110030040641014404021300b080650850038540c03003a20300b82100d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 88992671 1250 88991421 88991423
    0x190b060f0f19240207120303180303020306042906071505090c10050c0c150408010911041d06040b04110d1a010b09150f070c080708060c0a0e040e0c0301020c030405030c030c060403 79
    0x946c3d044082c000e05000380c1108407070400595032101c2d54042810000c00135081990307418401c5040c2548605980421207880705481000041944007030800000c10201e5400f0010880e40c8200d01511120340040fa489424404d900c52070107000d41015100c02c10420340c60f54041d801c140403060200022102000450504420040d200440810036200880c030484c016503001690543c00d202c1800f04000040c141c0103000311003030b41e0a002d24080001d041555544a1a2035500390f40280c0c0024045030008460981082c020310300c020300305240c1c1e070114821802180d03007500d01d03d840c4560088088455a407460050040038940c504103d400000a003a00e0896200880d2a03d408251406440100d10803210060b51081c00101090359400c10180c484404d48220a0300c1c0c000e0307100040890700c0100480d44040466640c480031007201c101084009c080c6c20360301c110284150100d00c002c544092004100c1c24224000a40c3c48030301d480109890215103d069034020f802003c0410002c3e03c2d00c00655081ea = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 88993921 1250 88992671 88992689
    0x140f0f04031101020a030902040c02010c050703080c07060606020109050d0915050c03040b0301030f05060901021303060f0905010e2506020601061202090409030c05190b060f0f19240207 81
    0x1a45450504a850b40030312941100a5440041c1d0080029010703401a2038251080e07405001001c0004800c3c0c1c2202d8000c014036021070300070884103000910038000c41c1d40c8402e0f040c0700c603424080a40c0301e9070704a9420303400410145c7e42d1500303074505012080168003821061032a02d052042d050885845031840300d144480c00f44440440c000c0310380b680c14416540508060140562251f035241000d401685c2002d0341510a8091100030620310340040c004c40d0850031201d01c05100711072946d41c9100c001c1c00b01d06015890113588444107000a2005c0c082d200c818507076040241004044104032190700c0c05942c601b034400f0000c44804100f495004a50b450440300c042c00c0107480950203000801c00f03842072547c5c480d40245044001010150048030011360302c0d020300c00b102d41032000010316000106198601030540032451000070620f107000340c58152028409040e402c110508039005c900c452aa42d01c40d140c51801c8a02d0910400016036054201d01240814029800d5107018003c2d440b00b20600681e022 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 88995171 1250 88993921 88993951
    0xd0509070f050f0d06140f01060e0319020f0a090f0b0a1203081e010905040c0501030905120d0f02030a0c0e0303030c070308250e010f09051507060b03100609140f 71
    0xf05a503640001020a90000418090400c000c85006248003040b01c00c004006142c1e0008524181f03d140346802482002d0000d00301e442d0f02c81d1700c4030400a810b800890740070b4583c440031500c40d00c50002c8200202a1507002042020a81c0e500c6816124020111805441e204c801080a80340c04c1c01150070094141c10f21000035100c926680400e0328002c40f0035009640680000544020319a01191150b4001e007045000c41c1e880d08011016100300e480058403aa1185d03014444c2a80d001000704807072552964000352010340f500c40030050340c2003151210403155030740002490694100042880d4200300b00e02640c03542c13030000901d82c4035000d201350103020461680c00240b4040210600141c1e4000130000744405000107002c018401042d107107410380001c1a203200912a03030300540c21a4107480c4010500c0040b0424049142110b800480c4107564154131410031260523141403080c81e00800ba040000302c3c01071b05182d0204103a6910240c0c000804020100700006000d020201c075410024503003020030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 88996421 1250 88995171 88995199
    0x7150c02030304090f06121101180605032404090503130602060105010c08030705120c0a020f0706120e1c020303010f050607020d0f15020409090b0c0c06060d0804030b0a020d0509070f05 81
    0xb40f06e25080900024001101c800c188000c400e04115540002d03680c440310072942c40c990802900315481507030040b4409102080f0000000118114000c02c003003a51440b18512400140540d00b50030401e6a15030000901c5509000c4034204000203092540028496549010002001318001c07410213024048044041146130f4402d004440d0071423526008402d880c01c0c003c12115207940a22640030140c0304001d0241e110b10320109900c400c589854607450000c8601002c40c501410550703c00b401140107144500111080b40f11403030200c0200c0d6402140c40e0340c10403208211842d010381110f44220402c0c401341c4010b03a1550302401215601410405400c40145820240c000c040001014841e0010130086010440b82e8441c0d10914001d1203ca2806e80310101c00c02c0c041d100c0c03060700b9001500a90b00007506403d00305891500c0500c10003e01c2e1130580d0700e407036603542d1010954400514540028595414024900405800c0b82030100904403447c90403540d2550f002030740c42428003501d50805110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 88997671 1250 88996421 88996451
    0xf050706020d020403030815030d05090d060b0d050102040f1205070303050c160e1b031302010810090507020d11030a08010e061201020309010501150206130b04020a03060c0207150c0203030409 84
    0x4010b145254001e64580741ca900c0d000d0b00060080f6003251564000140c44202440d00081510308440103456092808000c5004d000510408020a541f10f50322800c1c140e002e503d4000320041041d0007040016121401c00700c82400c0f111481d40000c22b005407000d07216001c24004507003c0101c0e98103041a43e65043c240c2c01d07403818032104500706403882e00038103000182c0302200300701148250416100d41948010201c00c090490005848010091481300c140b24010350041114a070400200e152201c603d99940309450140c802c00ca070000010303007041a22401c416082502401c1000c0c040300990704024180300010708004c0140714005c00020f803100418040e8403480c80c400d1183c0300344002995240b801d1400d05001c0c00d0203108500a841002003000d0016102058460141a01c04200c400c4032080340c41d41c140800f0080c0c0241e074003a07620080003001074054400c261103507400c1d40241200c1071801c0703042100d50030718252038014040007080400050b503001c0202e405a41d0820350001c0c800304214180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 88998921 1250 88997671 88997677
    0x6020d020d0315180c0305060d030512060a080f010c0905120a1515060207030b101212021f0902010e010305100e0c071205040e0a02090a030201080402030120040320010f05070602 78
    0x20190904104c0000c0e00c2c80603142e000107594072030301d841c00c0c05503403500024804880c00304600900007074801d00c00e0000f8038048540250f084034004282c42403054490b02e44070300b010010a4034100a03990340b80010b2107150403514050092508849251090400482c80d5440b00141c480003802aa012010b07984801d143d80e01605080d81a629400c1c165525014041d40d584103030b00060f25480445800100c0d105030200350761058071481d440241d010700c05030790f5496202480301424801e6000d001241c003007580c800c0c2c00314071884402c190b021404c2c20007400050441c00d2520021410141800c3c20812090700302c414036422200c01030840c54a036070f2a1402800503005504c0c0060403015034160580101b58444040c1080e5a074140c101c07400c94545d844414100d08c81c01d0706c030b5504085520b01c00c00c05507010320700060b40640007500200d402400c403400c01e071400080d11401c0750081c1d008a02481440303490350b40501c0318104041c616502c0005070300007a084002c14119401048000210082000565015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 89000171 1250 88998921 88998929
    0xf0608030a030e0106241803060207150c080702071710060611070f080606060d1e0606110c0a1214030a02030319020a0c0215070b0406020703080106020d020d0315 71
    0x50300e44800303085000801070240d9050706402c035030070310300c0c0414502c8014090304030900c2e9003965a0402c424150041d07511320a6085032104a0300c042c1000000315465000514955224a4903203d5203ca00c2e200c540c11035007009002c104210114003004400740c0c0010707640d403d0310403e8186007440c1050010162501d1420340c1d0f0840c515090210000b2040e4003d800b15400301109019100c545440d42203c2803003569512848905174081c1000c500c0c0e030f0601200030402d0350703204600842d021213008009810f141c4804071200945a454200300100399004112050900b0b5620141148004d003200080d2140020b020350b518206040b81c0440422a60001440080e400c0509489e21403954a0010f0745070b4004a80c84405910035040d01a032100882c03003180c1150080d5222100c540e40a6000e221703101036a4891a1030a100030044200880c0e115040107110381d00c220809a9079102501e40101050410790005040d544000715040f51540c001c503100d0103a10607071600040a8101e540031066008060348 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 89001421 1250 89000171 89000173
    0x280f1d010b1e180301180b06010809070330080a0f090215090d0213090b0609010b03150a051804020415060503131a0408030601081012060209030f0d1e090b0304060f0608 74
    0x8a0700c11089130b48010030345000c4c002d0703000031f0040d616240195929502143c0c2d20281c1d0700215810b2002401b1a840d8010101c4442c01190502c8081c03071210100c80e21000382000420051000c0240c014036902818200321094042800104002c2c1c0c0461180800386121403c0303000e01040c400c50a884403441b90b40069002003d901c003c54041d4520001080346100c00c0d151b00500000103529402c2429050381228204900d040c075640da141542c0024100c20014140d200010a200198130b50344c81d2000c02e804800e0003030740c1b50b09040c5032040004560351070a0208100208410030003080741c018094a40c0308170021080b0f07001c3c8001c1c0c0391001500a404103280d19100002041c802800000d201031445440b080c3c888c0003480e03c03805403043e4503030b280d44516003040c52202c41d54000a400b503006804403007800360407036804090b6540140c0c02d041e20f04644400144881032400c90f000d0b20b0340401c2c000d0314510304003034404a00706011000320348001000604156103580301c00010501c642e2044008141e008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 89002671 1250 89001421 89001431
    0x10f05090f0a0b0a0f0305040312091505010f0f050d02100804030302070510020417060105090615040e01120201120b03030a030b03030c0d030b01030c020c280f1d010b1e180301 77
    0x50700f84501034101840d00c100294400c002e0f5448140030344102030090b03405849511112103410641c40140080410032a410010b1000d440320044250013414082c0540000342107840e0704251008207070381500c1d40034922400032240d0f01c0d00580c4400540c40c20714102840c044419079070301d040c150040e00c22403100a00904c0380a20b4542a0722150f4040c2054648144000c10601da912400399076440c001c0c041d40b9400b02d0098040303032440c90030300b24040701619500c14a50074a9522903200300c07224404d130b00c405800118102d08504660740b20b8141c42001d02c03a14001c00c420030070103000c00e03603c0c0200000017091598035906500c40c1ea40800c00d03a054842114200d90902207501d0009010340000380090f4042070074911001c0c0a580045155002d100014140c2000340003e82400740380c80100c0350030050174140030100428400c43c101b0081d0054075a040e0702103e13292407030110b0210b80703505034044580000e00340174071410640d003884150f002540500340710342c1740c3e070582a0b20b222a28042d40340590540c602 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 89003921 1250 89002671 89002679
    0x9180c04080a06020301211205031b040f03022806030b0f04050405010b0901080c0306040b040c15050304120908030d0b1201020409090c08031c020c011b20030405010f05090f0a 77
    0x70343c00960580740c1f0751351040000c1030304105080140d401110000c0450700003004d50b085072071007900130b141c1c442400210100c000c2d15074052071240d58895002580b0302c0025041c14406e5062110100b00c0c0461200c40100c50084a040083c41400650140004064641880a42507a2115a0802c99000042040245081c1031506034024240640d40c140900480780c00003940f0750b000b1519441803c0003030003800d80ea581d250303156000c188000f0030032201c2c00382101c0041007205e13010001520340c3c0e043c0c0d100e00ba96400e245c20031811091241f09090100841d40005004c0e5010100c150346500c0d0051a0110b00029054005407094142c20035410083d840820005100c0004ea00504038040c0aa6902610992100c4510b9200d02c603540740e00c620040c200b07800125083c1a0b038010811090000c0000840e80340000c9010301c00c1221f2400e0100041e0788840f00c0443d030a4252940e00440034480c0150b160501d03000010340a0031561a08109110021581c2c1c0780d1601c0301010742c002d5400c0201407911054507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 89005171 1250 89003921 89003933
    0x51b0a08090703120807030c050a02030f0310080303070906030b0904020f0d03020a060507020106060e0f0603010b030a0b03030a050901021006060e041e060303021e0601030c0b03060607022d010509180c04080a 91
    0x4100c1c6c0c40c2c0002818075000d180500d001e101121a12031007580a14508400801d40600c03591000d440d09005050440c40000c82041c240040c1d401225030741e441c200c200d40b4160008041d5004841d01e1446110004107210060f034804180c0d086c1d8050035901c1d034024116a007400c0e42000402c0c000035100604020070031420980c10f44c010390640341c2c40d455803000d0800358402d1111400515128a41010341000188466000e8102a5034464008800410483c000001207411508400889004505e0214204c00d140d80c0503c41015040881c0004020081c6801001080e5003014040d550040d5504e901d8a03603080c80d00303122204040318449081c04115a6450020366846400004500002d1012200168160007042c1c0d103040761340200b078022510381402c18658a551002e4040c03540100100207010040e02c4800070f032208400220080c40c2e034921002038003400c81c0d80076044141080750070007469655a07100f05100f444c50b660944070920750b64030009815036610517074204104a110705682d040c10002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 89006421 1250 89005171 89005187
    0x709052206090c06110706090b0904090f060207080315060a14181809060f15101e030e2e09030215180c04050c0a08060105040b070b0a051b0a0809070312 67
    0x10105c070444d0f11107565500100c96841c07450281120b4200c0c20800a0b449207816040b01c920075004880b000e10385182c50395000126803040c401152600000f100b000722648882c424050131500984445241407240381c0d00521251008024408112000c5000c03070424405621218000f9800f50202c1880c01c00c80300c0c0003881002c200d401507154882c220014080710340202a0034001c0c0e02d5460083c1000b2a600104410840e4110702441001120f040c042c3e481842903803079000c501082d4038000f50100414076450b00f4856803081318021480b100c41500000c2e034690410910550b050000014040114541241801068800c1500150910041c0403a844c40300c18811480a0342200325810300409405010a9a8048820001030082800308003052401050b500c0c0d4000c20500d019850b003030b241c9122031000e8200c00010344548a0038004c00a00070424403030103801c000000071070740c00e04031404215040e030b12a0586080c1044041000306089036010000c0710051540075115100c001513000006003410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 89007671 1250 89006421 89006447
    0x1f050409080c01050903090a060e190e060a06030510091802060a05030901050f040201140a030b061308010f060b16110405040809011d09161103040e090709052206090c06 74
    0x5460807001c1400b00c44c00001f10b46050f100174290002d401d140003000c1c0d400540580381c8a8020070540c510009144a031349240c40500010003a540c49400c02000703109507614550000414140751005000040070b62080312400c0b6000031174007280c00c1c80c00e401d18070144501c0100c001c2d04034201185003407219402c0b40c0558420fa5013100200100d80e0f444801050f5190b050b40d0280c04180c0352044245100c003498014500303219141030126140e1070840204500c4d40c400c042524030f4220021042c8440402801990b804140c0c020301807110f1400d0402003030722071080c0a084407214a40640410400c45d5551560741e64050081080085143c503060008056200401c0240000c04400741c0301c005184016a030101c02c80060000342c0c071651a61100041c0d0448458803100f07200d034141c80d00c411407204000600141180285560542c1005d40c02207192460540007124500e050030100058180d00114880003410303910581c4c83d810700c1900b020300040a00c880040e102c3e20804102150264008038402126 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 89008921 1250 89007671 89007673
    0x5060301080717060f0f0402032d0706030b0a3303090b2202090702010e03041203171b1818010f05010215010504270303060801150b031f050409080c 65
    0x1c3e4000508140c039520200e8460505030f8001021880200a241600b540544050105c0381c4441031080031404440030010440c12000c0350301f401d026080710a1098038001c3c5294141441030b01d40550018805030040c0c010944c40b0382c10304040c0c440342d846991204212a0610110301041604002c004011b0503034500d042e528000e00a0204a0304c0382118041c480f00003215980514241d0b9a50030468807281c0500751034210740d29076010305080302e070500062004100c03203050303281d14100d585009080d01080c81111203c0c504100f003003000070810600c013601ca10045400290b49c1c0d00070386505008602451581a07004020103032002001c0000e407841c54141c504080c2820421590b44004a81e070f0070001c683e01044044a03401080181000c2e0040c6220341481d452143e4904400b002a1200504005007075000035103c20040260701d00038400c1c4804440301c1c040a024140c1022080c01080c40064079000c0d0403c001003c82084000880e070321005060b000703000348000d5030b46080580b103035046100f1002c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 89010171 1250 89008921 89008949
    0xc12022d04110403030f12060f060c0213090510020307031409010b0f0312070807020a150909050105030601031a180d050903010b041803081509010f061112030a020d0204050603010807 80
    0x1402c0c0000140ea048a625590300c0428580c0c000e4102e5040c502d882d0005040c42d1126008204070031800c0540d4090546956a88105040c80c010011007445c410032220045141070107140104a010510443c0e282d5901d0703015075244c4800c4000c038020050340c22440d401103d520203001a054040d0003403541088111a0b00d5124810748007010f0f115490010085800581006000000381c4150040e00079503000625079000140c0d206c00382070006654041e0000011080401480320300311074812180548000d500400306581160b8444011031052404d0110b14034102c4005080d110600742c000b4148000da86c10394042100c003000240c5141c1200c1d6060b8800d508003103885016040c05d108201121403258bd294007162040e0310286e6500101410b5a06101000081042291034600c01b281c000c100845a100100b8078080000302074041d83e0488c01a0343c0c00c00d40c072480500e2407010a490304800144001aa1405d140c440d6000070300c05c0760302054100401100000f150349020910800b21440415040c41c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 89011421 1250 89010171 89010191
    0x1b011a030d02120a0e0409060c110d02030702010815120a0803010f080c0619180b0306040f02030f0f0613090809100903030504030f060b03010f270c12022d04 69
    0x43c4031601218401c0080c00c0510200554a22840002d01c02001c09000007541c5031040d240d0304180c401d02ea8045020940088400c0328402c81080b1b0949402c5651001e1404c02c03a0310350000704041c1c8090308000c282c3c89000040712003a640c00d60841c00da0441e54003214451010780ca009403854009100303126955582c0c20740029502e002181400c80b410008080740d14105000a4080c0300010b528000e03410007200440e1401865402d00b00b100261152095a40e228500413080006179007061410f03115650041c810301000400c0c090020350000d403540a00c16183e0751b00404a115207103200c2905207801c1c203054a0a050001e071030002c2c410300009464480360300d0004081910b0301d644522005000070420401000030a41485198a0742841050082004c043d90b000090a50384010080c1c0c120720b0381d07800c204141f041c2c1c285654014001c1072b8010071621520b600c0343d49aa0300307540300320202003503c1600d64085588000f9402041124002c60011413130703011050300c00141c2440d0001d0f000705c1c50065046 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 89012671 1250 89011421 89011423
    0x20c120c01080406020c01060b180a1202011719090803061002060613020a0201020405060a030e15060a0303050306060d02071202071208041e0306020f130f14061b011a030d02 76
    0x40c200106071103058081d203840d51818003d612548200e03400c0d541e100404140f20310b000000303099800580c000c0b44c0c07540310300000308920301005921203c04500c0d034101d5100140d03000703d40381c00001c1c40c0c109880d0803503031107032902c80340489101d40001d0594a003506000421801d0b4000d18029a000e541440c110659600240d950310019035020b54001890550f0481032000358000303210f40f221a20001d82442e036200080361103508001e24010110b511440c0704503134510100100200589034030f01c90b20380350138020f02188010308140006410858004005000e9496620480c0d1184e486035a04540c0ca401508203075800692100d4a4001802900c0300010b50001d044192034a00390001c1c891071510f8581200710b5005200380c0a4480c6a00c100c61001003c202c240c800b0b02043c007403641c20596a03a6504200c7c50340c40c045508020207425105405200c10307003031000080e61800d0b0076141199110252141d450301c805200c600c801186d13080110300c03003205210b203600c1d000301a82078086a00e48070b407a41d001d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 89013921 1250 89012671 89012683
    0x41e051213081506131b050307020c0a0501050a0302070305090d08091206160f110105010b033106020901050f04060201061a09031b0402070501110403120908030d0902040608030307020c12 82
    0x101c4003d810030b8001c5111803420701d0b8044402c41c0c0d81100042c082901d40481c50015074040c000e4400300d13002104020304260144800f0500279021514480c1540c1088006007250040300c01c0d030000c041e404aa01d800301030203001140d04040000301004019030b03803803500890b20b0784005085801030000c10088240ba0307034000f450340c0c01401d450048540d02c00141804030b0751f84580d601c2070820061280c0b01d000b503040c800e00c81d050107040c0e1014481c0c2d6034034108520501118004140d403480c01d510980b4150090582035021007410303400346000d603440f41030800488a40c01090200302203810f000030f0004a40303030150307c00001c44000d04010034240c02c8031030b500380141c0640303481c0c1074054101440448407240b103460080d52441e0010001030801800b03440742030841d62504030300e80c61441c001800703005011403c2142044601e00303182004081c2e00381202c041c1c49010f885038110780e55440307100340021540d070ba8015002800680084075282d242c601d0703000f03569504684549000e444c50f41d00c0c1e001398071008101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 89015171 1250 89013921 89013943
    0x4240201140f0408030c12040501090302010b010504030302280218040303150b19021015080601050a030c0905041115091e060405010c05010b0907050301091103010509041e05121308 79
    0x2401440c3d03840c2d440d42c841c594001030402e0182c080800c030b0726844040159000e07010314010781c0005400c1e900383c50080d08603120740d44801d050203020b110400000c1d0340021107103404009201241d07424582512240036807038640e0300081d80101420310302260000c03001003061265000740e605012034200741a0f22201584540910300c0074100070400c16041020004c00200407689601c1102c18411610404104443d441a103401d25010709030030421520508000740c6015210444440806926540e1145241c111520801c0c1605403940005402d08c010f11101050b44403010349081400c5008080f030560707560010b004c4030301c110a45442c1c40c000304455a001038142c00f010382090300d054200703001500c5203c502001118550b4807501d031050302d900c600d1001806001643c582584a504000d00d40055038141c00f00301d032406400b8001001035a6a800c2c1c010380060300300340003210601a400740000141d9110101500030301c41e00d10548050384200300241281103443c00c601b203001d03031207102454a510032852 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 89016421 1250 89015171 89015191
    0x120313140f0906030703080c0a0c0504050601082202100806040f0e1b0d020406030b0601140901021b1f0203030a0b0303120406110d05090307020a051c03140424020114 73
    0x1880410b03041104400760050b10007400c860103166a940c5561480d0322000c040031868020b140e00e80100841580381d080502000c44080c4020f1802000007030400000818400c03808809810f0380c0907840303100306486890394019007036044030410390340c02900300361068030341a01580c54140404640000307441540000f88201d005410a090300960120310203582c00d03040c551001707c0140510040c0e03180d215000045101d0500380b081403804100240c00780098100310b0f004032104101d130360410f82c1c2c086100c40c41d6848101c60301e6000301640c1d02107800c0c01ca6900700c8010b0190402c50756200b09400002540c46030040d80c500380300f0301a10308107040e1a070056441405001c044580030500103000d03500442080507400740e406007480c41c0120748c4400e0707d20644003185950000034000b420750501050800240030240ca00103001001030309802c8a421030340e9006004c00035441c104140400000c02114010a40407c032426038a04401044e99042e0b2a8013a29000d0740c80c11070030a2110000213101071103005406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 89017671 1250 89016421 89016439
    0x90a170d050901030b1c020103180f020d030309060203040b09070605071104050717160e0d0f0209180a050717070b0f0a0e060406080a0b040209130b040b12031314 71
    0xd0400d5500e5007104504074140f6031640c0c034200082d01ca0010207001988208600244020940005001c881880d035094130800805030540001c1021030540d071030410342c1500e4105820083e801c080f002000300f04001001c840c000028401404803140c2c1c0c0c14000e800c00303c03c1d10425030340c0e020165403074400ca24000303114014a0450882034541503100ca079101d00c0320709010b910803510050b19a511502244d04030f10380c04e52078030340500071948240c030140e1180050301d05d0071100e84203450310311080b002070314000e00c00c071407140001e240c008644651010007540704046600300c00091070308588403201c4c2c0c0035002c0161161209080b080400045e22000c0303c4041c0021854901c0543d20207555034880f4020405000040400030060f440b84c00041000704003030341e99640103040541c11402541c2200d10020311481c01401194015683c44100109104050b90006180032200b4086005002010b061550281d414541000e0100001c8000c1000400d4240c0072215144c0754008080156020a46c00390030850003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 89018921 1250 89017671 89017693
    0x1020c1213090915110a020f010207080d090212010e0102090f0f01080601111c050a0e0d030f260702060403090f06080112030e0d1b05040605090a1d0d05090a17 70
    0x741c3d1082d040345020f5952480001c4040c0c1c005816101c08640e540744d2900e0010301d00090517810700020f940491804000c2d4640070168a07140010301a559814108175038961002e401c40d5030b8100c610465a5691000307100d4183ca820620703000b500300081d4a0701801c90302e114820709141c54103a1000b20601612144541e0300c9500c0115a1582400c071446807500c2410311101056041001c54890110695101036a940d00e5800040c0804103544020780900c2c3c121240c2e40c00079400c000c044039044581c0c03031321301d0106414004543c2d44c040060034445002c001042400200c9030b0100301a44914020f0321004d50166a61300c2c501060069440307408000780d543c40c010701200041c5001420018040e24140d60fa80c0c8550000070780319441007c044942071200c203100e083c6d000448811000814040741e00f04142c0b4902400310b03c038a01c3c0140100141a41e0700154038602080382d0107840c00390164011113028040e03500021381268485403e01d44186241e030130006680301050400c001c001110800b61a4013401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 89020171 1250 89018921 89018939
    0x3020d06110d1407090b1c05060109051c0c0512120a09170a0510020c0303040807051f090b010b0f0d0f180627020102281401020c1213 59
    0x6902450103140c0d020042003036000418050b2075001c002c2010100080d040192000c5c0010010381d000c1d243e800001d2120101c503c103600b22400240c2c80e882408143c0307a4a034801210b4001c026000141d014510074441e21400c03a40f81810031000b413203603103200c40060b1034404004406003190503905595002d002c407844a012154080c01910849040c0000080c0c1c50b8450050101d802400c0c0b0b000c00d0703024072070241c00d0101c1003000124590811504601d840b01c41d248450712480004c0018108420004040b4100320040081282011040212100445114584030003400f0303c1601602c40c0720390940081000c0c9214002c441410007000c0711186072141940101c0c0180100b6107030701e130302c43d50b0300c1e1401840e21240c03800500480307114050009020305188803d4142205090040e030591281d41500740c0182d0700028580c050180b4210600c3d010801007040d494003440c1c60000500b007080e0701a0b030b0710400c0c5054000d0a01064840d065403002500e02c079845c103444c041c414502406d00082c003000c01c19049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 89021421 1250 89020171 89020181
    0x1203050906070f060203090124050910030812161b0b04060b1f090e0702060f0a060503070f050f030d120902010228031407021302090105130e090705040603020d06 71
    0xe0080e242904044454840300741000d110001680d00303580000400440103028401c500c524251001c074642d03003c9404003da5058050350044c0781c020000c80010860103c00c0c0400c6000566026803600d664604500d070140c2040c4003542e145100c10f114005141203030f03001c0c0c165400780b201c400044061028582e01c0d5401d5107000034006645859403050401082e8031086201c00001407540ea40c0b1b500d0035000f6100401c941001e5100500c02d240103804e0145150f8045041070300940303200040616034490120701ca0050505c2e0380029818441c150000071494185418142150300846007500405410030a140c0c552500d0043c07600040e9169244845545681d800005094010320448007034560380179510100128035482e817110150703030141d82d604042d44041a02c50448014102c1814401e0640c045107a42904042d400920758020072040600c1e48200c2c00d0b2003403a401303100b100100a40d204c03070fa1f000001e0142c480c0c0e2940e001e122004241800e1034002c11045a9010b44840140030b070320b07229200141 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 89022671 1250 89021421 89021437
    0x327150b010509041b1803020f0d02120708070e070807020703060e150c1207050c030904020313081201060201050109020c0309060a020304030804090b0f0d03020a03030905030d020408031909120305 86
    0x410f1181c0c82064031203202c2c0c1c1d80d203125140212040d22507492405801c40031071099441c00c0c0610350701c0a00040c0c0350183d96000c0381206a481c050203490a1001466281d0160302c0c0070258820300390000b5031103200103440300840307903071003a280c01a80315031808a5012000702c0b00c1e500583d128660800c0003d401d948552041d01400c016035034690b08a010f2012544000d454682d4501000320b00b2030b281c8002000c0040d005110360410038541104024070799200d01900700011302c900e90220001e800710a05001810102c0e0340000c859a4580c02c0a6080004d0002800b6031001903103804004101c552803803007214000013a06000394105200302c420002c01da8003030b06103802140810312002001481d0f0201070000b40c14000d80c08108200590180010050106a52486803415a030f03100046900814101c030b40c5609460b02041140803400d04034a10b2054850340555a8400074000600117004400b802c40030b5241d40480c01703102c00203502121951207900a040c1082ca600c40160300081c01100100650 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 89023921 1250 89022671 89022677
    0xf05031c0204120f050f0d030905010605040204051827030c0c041a120c03060403230a0c0f020111060a0e010e0a0201092d0306140a1a040b010513060327150b01 70
    0x442d59910b001b03810441010805000710341c8031030504040003828040c500c05408150740c11400e203450b040004125071581c44201070404840d40c00300c0c4299214442c442a80c02440030654a010154004540d5a41c02404c1c1c48d00203004020741c03005a49490300800042c4503d5452500c680c1881a04010143d90150761103415445071044800c6252810b2003400d104074001d80712584078503454282100a07020078520450101c004010004045401c4081c1642e084d80050655000300d18500c01030310000b04e0010340c0d180d284111400c0000c0d500c1c4a41049442108020003030003501c413a034850304d80c0c0700c82c0c502000740403541340241484038820070b2004101f81c4000b6440456044000300c40d4200c02074032504207503191a142c0b0b41c6271074090b40200d40c06400455464003040904000300780c42c45003144a503500d03407040d910b907804400141c2c410b106988110002d2205080c0180c2c0d00c41c2e0140c001d10899011400c00503040101c5004103400400782e41503142c029030002881d10361141300f01700034103000320b400d414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 89025171 1250 89023921 89023933
    0x910020a05010504050f06070504120303090218040b3114070b0301060203180603130209070306050913030915020d14040b03090d03060b0a0203180d0f05031c0204120f05 74
    0xc01d009008007801680928003906100000f85c20b4031342042001001a028480100000c10003041444600050a80c140c42d00040e2130050f0720002c0d034100c0c004c02a40c0383c1c21f00d50505200c18810702103400c030700a1172840d640008500040c010154000000260b05521540380780c08000403c280000a070395491080080d2000e40b030303c920150702c4603042030300400300503400818514050308040c081d0340100541200c6080c19440c081d80201440302001d03c5c020301800c00b080100715a1406500041d025007001000031803c0d20740070355a6614518010400e500045000c800010807800070306041e80b06e106284d015007030b0a0700d04c0000741c6004001204069100c01c0c1048000358050200d0042c50203442020040c2c03901c0502e1a600400b52050b5400004030f04000b000f50405450300007003180c03c0302c800240703000084440c410005440469483c00038108040d800e034074008006011000708603154024031480603004851603004100e02450103060b90109000c404c3c000450307455401c1c0c00c0014411022a0301d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 89026421 1250 89025171 89025173
    0x50d05030f04080c03060f0f060d060b03031615061a03040c030f080306010306050102160e090309040c050c10050408090d02030a0c06090f0504020f09060a02010906060617060d0302030910020a 84
    0x420703544964440b200365040f00c1e4280105180900000350003c2c4001401c80e041e00708115058528200582618410080720310440c00f0040c2e00d0700140d644040003408d070780d11841812a010520000c1c8901161000ca4542c83c1300080316051103040156040700d02e8002e21617170140e006114a5002510907610071403c002c001002400d0a5144071115100c1c0d100e46449080c61400501a0740052b000641550040402030840d12044a240c0d42160150010608d40380c07206801a0305500c242d07201150400e0602282911558102c1c009210744030385901103a84000401c02c400088078010f4900038030218041001c1144c43c86e0000442e003215000509642c01d80c0036550711192610203983c818030204140d075504000b0440718041c01001808240d400750301d040c80400000c0414410f84001d54031640010501e0181c02d8401d600c8030901a42c4100104100ca44811000d042c2c0b40c440280b001c45190f030b40c1d00090203410f00c1c05070b400000c2e6140e0011810710b46824108030848811181480c210701c0380c0c4a00d94 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 89027671 1250 89026421 89026447
    0xa0e06031311040e030f090a0b03010b03010303020706020610060807170f01050a080a0b06040e0a06050a020d060801020c071814131703041e02040207200111010b0109050d0503 77
    0x14000d40c181400d4800d8080701d0310b007041c10500704005a43c82189807a0700307582400b0b008002c5455404880740d00554507605d0500240c8018159001003003090408800030485610860055040c5d0380030fa000c43c2c045c10740d04d40c402c9a80d00d50032256005d81d225021401c010050140d040c40b500542d8606041d0b046000c160802400070404580c00c4602d02c03c0e1100422031820002d900c44042e00400002d03202c0f03c440c58441082030b11002d4801ca0280c4c1d502d0740d011903481d02c01c1c000c111410f1341c0400300744454103042c80b20700081c0d0044074203814028501540094002c00510032200b407400e00130003600c840c1e1b00d084501c000845039103800d1a1320f16269408040c0580c21080881d01c60846496810b440301c0040c01d25003030311400d0040000e8640300400c20300012990600d030580700d6816000c01d10f03040a4851000c01e010303019104000f8105030038060f40704410000d03458418107582c000c0e80c2d6050400130008003e426124a03201d01400700c1c0008406100c0c2d401c00c00c0554513a13500030801c8034075103c000c000f01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 89028777 1106 89027671 89027677
    0x16030e0a12080a0c1a010807060f0c030f02010e0a0503120a0b0307030f1a01081b0405010612050604060f080d0905062b060305010615020708030406140a0e06 69
    0x3d00c4464864005000626480450f42c02d45511041c14075100407020f00610100c1d0203120800314034503200b21544110f203e565554030103951942e86060b250031a4101042c011035499245040d00080304005000b05584203600035a0b880c4041341070064807103400340112107814104500d0034043e9a000800b001929001000d05481ca01e840c6070804403a0103801c15070354061941400010004800704110a050844100e10291040803504200899034240500c02c04a81219140b20002c034195010b00e500c09005000010681e8a807201c3c440540c54a90007500035a2050840c0596a6440381402004010030703114541130802010700c030f010081c0800d20004003040701d4128154034074140d4210701c1c000c0d504003000b0042180c8500500c04400c650038030100241c0319088000170304d03a000104840440d101c0e0340e41c04480350189500c4400300e9202103000070030002103900c40a0142d17550307001 = true := by decide +kernel

theorem cover : BRFrame.Cov 88848921 89028777 := by
  have h0 := BRFrame.cov_init 88848921
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88848921 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 88848921 ≤ n) (h2 : n < 89028777) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
