-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2712
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:29.190043+00:00
-- url     : https://prove2.me/submissions/35737476-6a98-4488-a9b7-b37e2dce14b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 487589928 ≤ n < 487769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 487591178 1250 487589928 487589941
    0x60e06010803160c1502030d0f02041203080c070614011401020c010c0210090504020a050c010b040e0a031d060a08010e070306051513180c1b020603190905060703020d14 74
    0x8903ca440340c031058079801c5480160400c41103110b443c2c0289482c8400d030340d0f0300307541a20080d100d500101c2c40d416000c1c103015140d07140800a1017114115041c5c1c0364200041d032055030701a038410400030404510020140311580c081070349805140080590100141072642c10400f103200414074450305581194041a050411640c00510b40000c4580454071000c91a40c242002c13208800550840e5422500101d00142c8898110010389080c110a030001c1c0410182c4c136040c03001325451480d90100b154440d0180e003001c64000c0e540f09007262406040020000700d40c60100304a03610200c0ca080c0018850001003124007240310071584c02509610341404003901e403000207241c0d1407520394445803a004c0007135811004101c020240004182204401003841040b860305001062070a0000c0045040e0300b0032500c00018002012a9466000f0511410768841035a01d0054440310345141e0800f6554110341c0d00410400c0003c5482503c03036030740260f914024145e038142914081d11110a054a045e07061081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 487592428 1250 487591178 487591183
    0x703090209150913290109060b0906030a0c3006050105071502030a0f0e0c03070b120109180b150a0b040311040e0a0c0f1517060f03030c12030103060e060108 69
    0x10030010b081d600c0d902c0c504480c184810390408044a4038000103038402c0326140c51348680417840c100d40e1888401c04c030745540c4d030341d8441a601c1103101941c0c1c040010000a440501c069005000196051a24906030f40b4581c40d00d26150003041c000c1080c4035004400d101030038080b4059040940000e1030a030342441c40c142d4480308031000c1d0214460007582c01000094960b130300d603480078000c052100301c00d000d46010f1a01c62600c500460b0f0f00780c0e01a0040850200d0076401038000c44560342446c03801c1d0315480e841d003550b000042600503031080c41c00d041344503000046036205d4107040c00742081c07014543c618203141c0704010309003000e035100080c608028841000401e0400302841c900c400180e03804100300406401e4035041a02d4181c00401202074142c001c1490185507000d00103a0380591803903034290001a0054034040c03039940d010444000140e00181690612040440020a02038100c0342408502c08400d401d18ac20042c1c040d90b041404001003080c881c846c054800311110880140c115941090b607101d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 487593678 1250 487592428 487592431
    0xa02091f03051f232a030103050106050103020a0906031104030b160e1512060a0f0b030106030c080112030c060f051810050c04120f0503030c0901120b0307150201020903010507030902091509 83
    0x14445454400045c0100030125510800750794404062101c0402400c0840b007039410a0209a44039840c2c2080441c80354024402c4850300d0320f6030b480b40055285070140440141c6590750240d000e581d4107000c00400500700402c030602038240200060311900c111003004008403501000603203c0e2650a00c0c16810b81c540008903440c020030724903003e1240e5609004186040c940340e008088010801c42d000504103804000340d0f068881c603a40501524584a404441d809403e002d0480c5000c80110064006400751802d0016544210000303d042106031000d10212a4100c400210a201899044403030440500200e060010864020480b40c10716105a4006001d2402440881d40e0b1144402c0180482e0465000046500008030703503480c90322007003115036608010421130200c0c024a41034290494940224406940d0207001041480d10385844c5c43c0b0070400444580b803c3d55402c00c45950b0f25142809000d11458070703500d01191401951040c0030000c20010002258405808a207859542d10000c01c4bd = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 487594928 1250 487593678 487593731
    0x1306170616050a21060e07031a040b0f090412090503010e0309010e0607050a1b050f1e01050403021207031a07021c030e34080a02091f03051f 62
    0x71521146200801d0b5012480c44c1043d415040035074054551900072500a82d081d180d040c1350314503a0f42c58440068041d685804991706400900458400301e6041c2903000b0103002ca0b0040215884290310710206011020941d0181c941075825002007010075044a030300401004160000c10440c1411180d440e1a801481502810071035a1601c0b800c04d0b0381d400c002e0744c0a05400106031140f001091a102080c4501c040030b03505080d40f510700c0050f00740342000f9205c070710010180100d003d540d0301204c400c1c4900d5502c04200d040c0a0180720110160721481e003501e8203120f10800801c2181d08608100200c141141021010b001031340e001c03c41c1c402d42c0813451311040b001d140e4010f580580c000c0c00c00e030f018144001d809071445c81265070100e00805500100e059119858180d02c0b1444d50740079444d500b07403503d4042d03000580d0002d4084401403d200c402607030701c092480c0c2110807040c180d600c128451101035109458950101820402c440b085035100c0324841c017041c4041040f064076000002c2010a01303002c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 487596178 1250 487594928 487594937
    0x90f0403050705240c090315060105211506090a06051c0f022205030a020105090a080118050c0a12020409061d030a080a1404120c021306170616 63
    0x418100350203003054800301c56101c802d031200c1030ba112000150031400d0110001d000c0b80150007040c0c01c81001402c8868191020307014043c0203962003456140c140d0054021410032408000d10100e03084500c80c8481329100495694459041c8091000c20020810103114881c240401c03d07488150380f0b0318803000490300e01d8108141c17104000070780402c01d084200891045182440598030041005034000c041d003038400c084c0c042900082d44504410b6170b00e07902078a601f6610800e2204050f60040000d4929010014201d801143d2504810345c00e50700914100907800c3e2031a4116010400c05100d651000b10042c0e900703112082c9804516024070020400c080c0c040d6030b0301c502030018084541c010b90096010002451a5020070600c042d42d01d602641ea0130000031480c0300459030195080c000d510b403407044110200300c80e0b1226110311840504402603000ad005900448400507250024242414001d4030000201d4905d0481e600200c6003542a0761190341d0032040402c03190f030001c0c903180c104901c003600e007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 487597428 1250 487596178 487596181
    0x503030304150e190506090607050d02130302191a0a140715050106080a060806011a0a020a050129040e0a0311010e0f0d0f02030a021906140a050f01060509090f 70
    0x440500403d0b0030324088003a030103041c400c540a450900b00000c1d4a40c03040301101d1869036191383d09516000250b921000158042080c0b1400c102a42c0280c45040c16124070407402a0780e81e1b00280002c00505015545000610f03010414105d0f02e8014800b400da451a0701440c1031001c50005005060341c6801c80c1c1018000705000c41407000320300380810a003070380d081e0400695840c2c000c090040c140445052a000b41001404260b41030302164842c1242d0180c244100000c0700443c004080d900040780f01030443c400c000d09180030900c00d0044035148401c0c1c006102003000c1120354400c00d0000c1c4620740380504d0400742104604000000c100403942d0300743c9004040b80040150860142c810001c2104191080078408400e000020501c184120801d0b140c80c0c0c400021044241d84a0140216460158001d003180521480c40c0360074042c0100d02c034020000b01103d4900314003132480403d0300c1d04104c0725030742e501b002030305a820140e00e4003400440c02d10500700314548002501d040d40040081c19911003100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 487598678 1250 487597428 487597463
    0x3080a050310090c020616020102040609030b130c0f05031207050a020111070902041d0601020705060a23030106030221010b1b0705041d21030f06030a17120f010503030304 75
    0x702d0941c0503143c1600c0921071060f00c0c5100a60340d04d025680c1c08509074a900d64002400d00510844d01211807035110780c810540781da103c0704c100074401004c194644c1d51881e40d840024120300c2c490360103090110f1603803e80c2410070042c50b00c2c2c20076408040e005100104654400b242000800c40440d980c2440c0c20400c0411401c0118148002e951044035082e0011902281c030711115594400180502008030305035544220049a90300801c0c40303801d40041081018101480c41229042a001804440041074058401d43c3d420958401d0b40b0000020f5404121130100d0503c041103501c60000c000c0002c421541095002e05d2240325001303429810809c61400c1c1c942020f0b040c0b01c001e0081ca801081001040f50083c2c0e890f05102a001f0f5110090107168034621449218078005003c9540741c008090842c1d8401100913000c16016003000d030325101d02c00002000400c181c104001c5c0c0c4106503402c40c2c4610281e00610410f0754080c05203602d00e41e541c0c00620041d1000410b07242d1094026080035008251903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 487599928 1250 487598678 487598701
    0xd0e040905210a0e060f03130302070e16020d0801150513080a0311120304081818010b1c061203081b160308060904121d0402041d1003080a0503 63
    0x10041070000c034079080940c20410160702c05408441102d4036801d01c0c500d21442009214418801c0d41145803030107201051010746001e101c900a28840e004071b074202d544a010095130a9801c03038060707801e030520071054400c090381800900e00790f040c82e003000206541408000060148070281f0a810040085115400d618400710800018140a03080c0c50001116041c000c1c48000102242c4040d4410440d05512654441d000c8a00c5a03420000c01410101104205403010754080034203580040581c01c070072141c9200c250a94000c2c40040e1a69a42c2c01880010800540d40b828181c1103051034060100700703005075881c441c0140c0b5410300c0d02e4001e60341d50030102014002406221819007802040341102c11036011214405140203440c5c695259440c8800c00104401c01c54004180c84446100140c59a0094550061429055404600136192400842d00300d03001039020081a00c40e202c0c0d038007464100c0c5980c0307503080890414080703c00c2d03045840d5600c040c800d00f402041084000000102404080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 487601178 1250 487599928 487599943
    0x30c08100b0f010e2418010f0804050c06030a0905150415090510050c1e1305060901120f06051008010f080303041709061b03070308071b03030f0e010e07060807020d0e040905 76
    0x28606210748070584a4a042140d8406c10b12850100300844128400c3c00c0c0078410240c40741e0303031010041606c1ca13201004c2c01040e80020b0300c0c008046403503002404c0026001e0111409068600c1011661031030207090028400f90f035200f40440d01490544490089503000c580d2180340c8104580101c3c071510b40011018441c4960140351001c0d15005000c484603003541c1c0018030101d070986602902240e26841005114071400d00d101d404190a029800b8138981150032200d0b8a404220002440b80d6407400480c204055035070325000040d40642c0107001d4482c1841861002c2c00b0320340002d60030f52070326076180d040f081410900c85041c4580810ba1014036659401201c8200c008c1d1641c01c4540d90700c40200980c1c076088a042107010415001c002200303188660444030048aa1541074400b182e21703601c041d0001c0515484042515486e40c6242000020034018800c1c0000244000c10700945041c00044c1140c20140000303045402100c001d0289643c0b2125070200d041c0204c5001802c0ca54514226183c6502c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 487602428 1250 487601178 487601239
    0x10e190608040f0b071214010b0a0f030915060806090303130b13050a060207050d1805010302130b19020d051201060e011e08091006030507140604030c08100b0f010e 72
    0x4004126145170310400840359151b8200d0180146801215426100d030030902413241d074840e0502c51160002d1246508010905103800e00180c101c1950311800000720810300c9140d0390648406042028081c20840c06501801c038501450a50600e001038801d4089603080144c030101c1510003041007403002c105001d41055002c82292204002898410069048940240d0380790240344000071841780a102e125640b00c00c41c6000905040c01c000040d00290850541e080c0314402c425408140c46128000420045101442c120400c3c0c024400091a043d0400c84040400509000000c801c082100388581590356a040c400d2042d5107540040b690740800d05041c641240c0040705c20f485a540201d00c00c0c0c0071300040b0040d9500c1d03100742d41d91001580d0b801d1100400d140d2102b0810000140340ca03d0ba0551144e00070101440c00d41c0e00d880784105005c2e560408019034104d40d512100c115820b01c41c2c000910000e032402c09480c0381050000e0502d40c0d80f211041d000b41c0545540d5809034404500c249440c80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 487603678 1250 487602428 487602443
    0x40b0f19020a0b060d0c090e0f010f0b0f010c0b040f03050d021c150506030c030705090d05010e060a05160807050903100510080f100902011715010e190608040f 70
    0x50038184000e41d10038400d90162030004050b00400c020b41400503516624035080041c0d403d170320389010500d200071311200101058078000d24820004515080c010307007146150144004c91400168002c101140003405002818041ca2010b8840020400d00c01075070310a800884d1440d07250b8540c1019542c0c4d215074040130038401e1000554941034841c61035018610355100b001040442810a00c0501d030441038007840d5404581400010b1250000030001c591100c0245016414104520086038900400c4c80707007110300d80d440d01a145000202044865481010700b20284441d0611507600c5101020130715109007000b440310002200c0038010300840e44109030143c00c03201c200304022080c0d001402d00341e0b100e030b440c82040840080d40700000160003040d4035585010303216404140c10300800400b040041203040c0008143c00300502d1101a4085100b0110035030341180884800c4001401e070720300340301c0d0f140c41807016088100307035014240301352410344415041c00421a100c5080003800002008802411107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 487604928 1250 487603678 487603717
    0x6090e0a020f0d022d09130b030c06030c0307020f0715051812011d0a02012c060406030204080d110619020408010e070515040311010c0f0c080d09050102060c040b0f 72
    0x280c1c91a48166803001d02c168442c0d40c66000300300e0300300c0188101c100d82c950107c0d00390f030351011001c46a40510700746d01004044a41c02d540c418082412900101c5403124041000700130041807a8040c415850b04080e100041d1154905004c414009505100001c07010002c000c01c0000d6400c01c0721388000746842000b002c240f110107000c103c0d913020300712052103000c038440780000724002008001690642c469058445410010010a90304c09945502d0740d50380b4840044403104440762213030760040024002076a030150b600d50410340c0072450641d803c44a03d0400981c3c0b82403000640b0081039481c0c11814260708a074251668a100502a0140d50840c49003540380000030080520b000a007401155001d403130f203c0a1160000170340d41030b4025403101030094040b10403501811f42c4200103131403100307200d6800c1c0d030f90703d00d2503495008401e40790342c02c081040c0d40071581010305150845000030041200340300810076403030b0a014103070b143c4c041c07032046080c41c80d03001c40c0003c11014401c00703885040e42201202040c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 487606178 1250 487604928 487604947
    0xf0907090e031b0d0e0d0c03020603040206162d021e03010b04021201090b06030c040e18010c02010b13091703040507030803071805040b030604020f1306060206060a06090e0a020f0d02 80
    0x5424a44c024940801d0700c1c040060124103084100c800c0c0150800b40d1904914915001e2280ca603000074412039211504000c403c002e401004a0400d4090103580781d070340130301c405041201d440215000c42d0303602d0b0aa030481a800503500d014038034072034018212031024550304201c0401c0c0905042140d996100f1f00200310030421200102d42c16049a5001800780099440d107001d0046900c01940c04030b030701240c00c00080c8818038995022a030845040c1000c94070710820030341c20600b100c240510050040c1d441c0c44243e82130303141c41110244040c002a000f04000d491f1640d4521903c0c2c80d44506094952002c000074040c0107003031051000464215808642c1d9141c035a100800b6030302445494000340e10300e0341000c109410039205c1c1001c08880a00103042a44540d020480c44040442406e50300034034082810200400a005200083c51039400030f0103c1d00b0039504110100c0c00c02e422150800030900710400c03030650b1a8110380d403c01c0e422080140d0307a800c031001d5200c480c4203201b41880040d0000030f07080300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 487607428 1250 487606178 487606183
    0x806090a0b0406360e1b030a140109120305060a210b0f011701060509060f0a03120530070507051c080403030b090c03010b0912010914060f0907090e031b 67
    0x44080c0140c050750081001001003400305c500404c98000c082e0303c122180000d05106035082c81c2c190a00a0840b415114203a4800048442e1a0740115417651141c0050040151784450410035800a06050004d86003030b4001c02d090701650320900000c200c800350101c0c031685106840c1c208442d003008800b031552403c0c80780000981828451410101c1c9001d5990307060141c1807041006540300282120402d449100400c039110340c854160302d078401c0c1203480000018241c0c016100004501361a416264001d074002c4968080000320100c8040c0300408104010b0301164600c0f5038050405c0c20125140e09007800d00c607240648022845d100381c40b916512507072068004003903d1240b0311a5605109200c41e02d4184840c028054403260688013082c0b0050000140007005003202d034501401648000019580035401e403518000c090340c00e1400e43d00c200c000000140829a44030303840c1c1c1034108107801e00c484001d903100161320562048aa5400300d05211003000c0c012a00c12405468843d000100c15000300c94 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 487608678 1250 487607428 487607489
    0x70905010908070312050c0319020601141f03050c070b010905060a06180605090102101803141e0703120e0606030f1209040e0c06040308070c05010806090a0b0406 71
    0x50101e10261000542d030200000d0140c141c80e400031510100c490318a2054a040d046070040e034a90740014030550b181c07050000c0800028040c19401003960754585250346030200f01d1030301c4650140b50035000e040c4920350006c42c4502c40a8480c0780c0021540d03103651035a0f11750300035814020308000703a10000140102054000e5406640c08880c5800780c0d030b50b5850b06032120786d41529a401039444502c0b040001074024005040e0740401801958150014807818034102c90604421482800002185e803081c5940300390660307105400348241c20b15180d540d44451180381c0c0d500d4400941c00e000091801e00301441070580e419642c082c404148040300310a111540c0b03d800480b0418000d1003042e8903100c03200c5001940c10b02a030700060409107003108035424840604040e00000302240b00d192141c0307005480c0c1c0c0b40284000c6008200154942e08985408400911a940a14100a107000c1030204907500c0d2a0540d070400201140013030384005801c0417030f018100c4c950000ca0300700c400c08205441e0303a10100051 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 487609928 1250 487608678 487608689
    0x204080c06030702100504050c0409061b020f1507030b12060405010f02190e210d020c04060f0e1302040606020d030b12070b0f040e16030c02120d0b06040801050709 72
    0x54940040d05414890540011582c1d100180c1c08040091001d030344030f42c0700c650442e000d041aa203400071100046030598400b20411540c40e66201d10685860780d4a240d921131b41d0300ba5201070700c0400d2600032034039950340200c41101166200e020100f59000e0096100131301c4100081e00c85075400100204154541e8001c070ba0a0b6100c0d4201451844a91940d100f11002d001410f1110011502d1084044800c03542c03207007516400c4415800b00c05c40303c80c80040b041d0140103512004042030518410000d09003440070803c68000d908140c0c06100741c16582c05013000759144030399480c00b143e4821050004254504a021750458940031022540e60b50104038a400500207031070900540b0614410b00c1076108000000e1103154020300020310603016048000c040e800e026038800350410f138843c401340c500c0714029944000f0102d6004060001c140e00b5004460440100b400505041e800d103201d6000c0030300c10f0420744c00d8601e6076988902501e542e0070003680d02408041008000034941790b14054000b20060145 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 487611178 1250 487609928 487609933
    0x509090604110d110c10150806010b030630010c110609100b0a1505120f090a08160803180f121210030807211d0613030213020408 57
    0x25806040c90300030b03080d01121840303546241800210902d0024450040c2502100508212000b00804200035288030100f01a0000594501e0008180b8006c94140d00200c0c950b001500108603400d0101e042d01c2d4000780641d00c0d195400c4680382d03c80002140d881c0c8075500b07006078152a2248101c15484100703101440d0315000c0d1024041200207991b403408441c44030b05903000301182400e00c1d0032038010108084c805841a0049903d444d000315900e2912020000050400700d4109a403514640c19960402c2401d40840f4040c10004080d50319044100805403c1c0c4100042c56241b01d40c0c1038047d18003c1c5d400c616080d44074105a0f0030001c1e200d03080c1c00b0502841c0302e1038100410841c80812608504040c4240c013030f290070200076081d695284002d01c0840c5c040449000080841d25130001894454410788100380c1c1418446c00c208804000e90b81075608001d00381850520701002e00380d0701c1c40084001c9807800d45070326052140600d005805d420081d00300d0485200e0016100141c0c0141c410f90300e10900307 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 487612428 1250 487611178 487611181
    0x31b11040c0e0306070311041401031107050309190e04030e01110304170d030e1905010f0501090203091b28080a05150703050402011407020f10020c010e0603071e12060303050909 78
    0x801b2800c0d1145000410800c900401c401c01020f155103070345a000f044181404250041103450088e85a0440e00040e81c464100140c044050f14084420150300901110b480301660b0400d007070546c0b40400108000e003400444c00400f03136a03071b0041b01040c0c80902c03140b040302d03a20303901c5e2511011807007104c50042034588112905030058901a001d520400f00342e11001b13060880003022013007000704580ca82a100d039581c500010003040300c140030340b9010701504040503a1340c2c20071410701c9140c000d45000d480c0212010701e201d02255a1203182c040301e880c244000b02188420f01824400c0d40c01d000798007441140c4102d246000c10404041400d10402842240120706581e81d45801d900361201124024001901c9c854150081d08419010303100c1e1718005825568041491004520658543c000c005e002d80d0009102c09010740e80500b5000303e0710815142e544c1981001d80340076046401031149803001eaa0f0094030840ca03944070701c0407c1100fa640c0907007407000603540d06015200c1c0d840180001d00981d43c070b00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 487613678 1250 487612428 487612441
    0xc090503061e040303271b0b04090902010315030308090d05090319210806040e0c09060f030a080a030f0605030109050a030e0319050303060418031b11040c0e0306 71
    0x70414840d036078000400110158a49504111500052040342415600e00301d010031494002c80700c042908501e00c070b41c08024828148100741481e1610030192410110b002440482e4100c0c09039001c80f01c1000c000720356080707240b006a0141048801c0d202a507403110000005143e40058014011b4414a064840d14a060b0740121994483c210001e0341507070103401c0440d843c1d80000e4100d183c46014005010800035040c0054206801303042d00e90b4002424072051002c070b403400e4802c0c40c1c00c004103034004090701480e0341e020840da0540241010b11820201c0310003200c1c2d8a0603c268405c2b030784e0082c10036541b0102c140340540100002d10070203a0f96840c0010200f03003820144a200ad24079008001400c2c040300725a81160350300b0416507034030f4050180d01a480e8070843c03010710780020769209001850f1a4074200c03041c0002c50b0f4110940060708071038001c5030b001290300b000d5442c015604858104480c0700d6a8280603001d00401030101c2e421a24010803001100e9200e012a040348004030165455603d0b0f45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 487614928 1250 487613678 487613683
    0x2031902010e0d170d0906021c0e0c0306060d0804170607031409060414030c101d010b0a09050709180b010206090f1b0d0501020403080c0724030216050607030c090503 73
    0x18810601c03107404c0792050355078201403e11488041000304111056a940e9000e82e000002000c181d080d4025080e201d4800c0c031b0248003426003080d001000c44001d00c10020f903480c8000b5240034013510381d0140b030174284a1540d046501501d405001c4c220040d1103a000556200710032989540024581142c0401c0c1c0303c1062502801344146400604860f26140c80700d11000c10040e4a1012a01c000c00490000c3c0109204010140c0c503443c10000312203410081e040b0190140710207507a01c0b40d2409001d11b007190340b454191019204400c8001030351742d55100c400d94840c43ca640207080314001613030346881c159110342c001005440080c3d003030b50a240c4807035007180d540e41841c0001440940081281c03c410720507034080400b1100b40103040300c401898940302d6030300f260700a07041900c0c00790700050078180309002002544014488402003281e22643c003e400c4400301a035151803010142c0000c0c0d0107404d9014107c44003159030f084004d0301c619041500006c2c001b0020840310b81d000c00e190203000120751501 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 487616178 1250 487614928 487614949
    0x1e0503120a1a12070f0b07030305010b130611010e0604060902120703021c0f020a080106031a010821220f080f06012603040e060108060609010e060d020702031902010e 73
    0xc103100c10401e1440c030020802c0c3c00180d862501000e204003200080ea00d000722001000400304031020983e1446241401400c0c0c400580180710b11070f1042007105600c5007254041030440707030f0514041e20955002c4031a103000d840300090010083c0b20314003d010500c20a544440071880c4200d40704d044013412100c260352a404c0354803000e98004506140d80000c081d4010044100d144200404404481e255000499415041d080418181c2d558001402040003030030307188182240c0141c0c1078a00f513242c441d815a4810078018106a008050355000a03418640e0099031030000c1c20b10f010304820748030417503c640d8030f22241c81001c0c14009103a000040c0001c001c42e44000e6541c0b40c0d800350a080e803e160014040310342444a024010b40170590811000300180060000b0380040c0c445209241801310004040c0c1202400651081a04011491881c1c0e040b002a10600030203031605510756280c02c80701402401000e001a405004901107400030201d075440b04507000341301341c84111041c00074500f8070a42c3e82d40d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 487617428 1250 487616178 487616201
    0x18010924030f02070c080c03071208041203090b0d0f0c0e010914011103030703060305060c0406021b0316030f020310050f0103060b040b060a0f020f160504091e0503120a 74
    0x914030485403400c0c07080d0005144801d40c1100585408200c1e600c400801907254050b03032003904202c103c0d05080c941880954001c000d24404200c01d00090303101c5100600c2980302d22007980c403442c9016007c040c0103e1360f100092041e800d850340c071030520030301c000094503911003684032a91411074078004c05c034024400036000f0b01042e541c114407241003d072180c015405208150f4140020f1b240c580c018208200021032103403407182d40100d080ca16501e0014034264010745200c3c4ea0510511041c0a940d5002400704400009411400e40c0b90304600040b90030711000707440315950b0700c075122030103c00d014407489480895407080e011114881e600100754011504240c0d501d00168200e00010004150740da08100c1c4100c0009000040503ca09000550710760302c25850f9401080b40c2d005255002a01806240840c0f555400907148140c1c1c2045d1000301d0450714000e0501c01e5a407090400c09125100882440c1d1644c03410b03401c120044d1506100742c1d42c1e08a804a001030308440000100021080d0003035009080d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 487618678 1250 487617428 487617479
    0x60a06080c181918110f032205060108030408190f030f0311040e061809030405010c030c060e03040806071d01080a020d111b0120030714180109 63
    0x2210403110415181010070783c0401c0d80070452003d14021000c000041104220046020400288280658041c05000252500d0078001c004c0c4031144201100d07130112600050029491041160380d07a408400340010744184503c10002c102c0000c004024000c2c0c807100400c03a82c0f09a070051115002203a00c00b402440b1002c210a0300b80003d00172209800c25102c2410041179859659840c540c00f80c101c0c0d400342031104c91000502c00ca904065445101d041c0711010102c4462814030b000310b42d00c0c0306620615042000851018040c18441c025070040d0640c001824050304080c0d51103d542ea404c07034024002c2601442011401c09030040215403030400504205001d43d542c503800549003010014401070300b441e02000040102c0c920f501c1003e5900b4265000350ba160b850510702d42425002120403002513070314002d000000c540e1144480301d1094060703c03805030b43e0358984030b0860703504003901e0404454110114506810041454940300c2100080ea144400d10707940d41d884038040c0640403803010f01030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 487619928 1250 487618678 487618687
    0x219050304060503281b05210a11031302030d020f0d0509060712020a031206030507030b1e090c09060103230a0b0607081215060a050304020a15020303060a06080c 71
    0x4078000c1002d1030344240c000810070b80d81c2c5103a18000b440b207008030301009400c66a4445102104c043d01c40031b06094015031801c42d0030031030b45074a444c54050003a07803890819090100042c13507550311078000700b402d03002180e049a100d00348043c20030524960316008070310901072905141c60480c4000b600708140c01006006140703000f020711098610360700090705d960300018100202404180c01100809100c0c5065004001d14013060800034414042194210992802c0c00c8080020079800102ca87c1503d801100220040d1280880d66448681d0400c186507011803100c1008444400429640741058055400740695038900c0c004400f01d501b0f0f1035209000e403c0104449014018081d05031b9400103503841d00007668210407000031b505030450081118220b000264050003005100c4850303802c40002e8041e0b08680448000050040c0039003c0c0c00c000b08200440020155a150000c00c0d00418000c4c0e10034103440000f020003903c80d8012036805008841080001600c5446103440b580300d11494170b86c1e00e041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 487621178 1250 487619928 487619939
    0x6030c060f0d0504030c080a0f020f030408150a0902180405010f0510030b070c06060f17070f124706010e0d031101021801090f05010905011b0c090b010219050304 71
    0x8100c0680f0a801b00008508107100059500c4000c00f01c0e0340300c51301c0d4071524088134a00207207400d60020901c10b050b08144400c00901c0c03070000e1100805881002803030000d54412030544011304964801a61150490503d003182500b0035030320340d00490103400280a9051000c0001060307820550b5064081c10490004002003040300e55800d421070010316116000c108161079810a541260700001d802101003101045103244118041c0e41d500e00c81c030b000d041d400b0300e802481410180103102d40070381c951f440d150307200c20031a44c0f513081e40381c103042c01c185801c0701c00f010244c4076024010003d0002510041000c480606402c001105106640503503408181110003018080a4045900120240301c0d2032646100711070710a001a120741b02d514403400044901d20380004101ca081c690003a0409103030850184a9a68000c42d498181c98082c00d000c1000388000350428441456000e0262a01c03120060100d280d0055402030380782c0d89026030854108865182c4419145600080018203660041104020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 487622428 1250 487621178 487621181
    0x1209061e040f050d02010203060a050d051506130f0605040c03050405120c0a050a12021219180e0f01050406050a0e0a0b0d02030f031c0606210615050306030c060f0d 72
    0x140103106403081e414182140c0c0c3d42074a0641da04030741c1030160f5004002c001050038080c5400c030040c813089480307400740d0071a900d620317441c0e914201c2c1e08026520301e1070020708035840e200f040092a0340580c0c000c001c102c244044030002003905001d0544100d04029411010324401e0080600643d08003014055010002c01da0700c0b01540941c049100500a44001c00c0103c1c02c2400100582e5010b080910306901e80d900001b420069a00203004400c0e03410b0000300ca00905180c484444800740e030800d00f0a00c0d0364070f50100b41010040c0d21050001c181c2c50f04003c4201e039283d0b80141210300990381032020b680c5403c1003018100081c084c44003141680313400a40b410030940c0000d0203484020b0501c3e0b6518182d500840c0c10055080032042c8594000030700e0340007448100f841038010078034800341044501e0420800401c03400714841e10500180b031500b145400b12480e0740c01140106001d02c0710100b80505280f015040d50070850f01940300b401080058074590078484100d42d62a101c0940f41e6180900c803108840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 487623678 1250 487622428 487622431
    0x81501330e040906020316050705030315061308150901020412030804060209040212250f08070201110c07060e030f031b0304091a09060d03020309040f150306021209061e 74
    0xc081011400710a0242c1d1900d100f0464564014100982e4030301e0440752500d1b03d0200544c038217007008810050440420004002c0e86e801494403034601508035042030009416020b00710001c0002c840c03d0400148500c0300040000040716138a08280d103d0350b036614458200d00507403140e500f030305110300b1210340041c0c443c01c00d9a81c418403a00340182414400c0e80450304980084150396403140e141010310079110b00e01c03c0c0d04078006001200c0e2407100765143c0390003130004017902e210030148000f59000c0b03000039000390820400d400c182108582c54401407200d0503560344031403260070040340b0710000d490090b05000c2015a041030f0701320002e40c500340d002d5880c440c1032030310700e110380d200c5010921022039100d085001e1429101d0b1001c1e16031117022102d0003000103840e130281285109070780c0742080c81d000980100949441241c01c44001841030881d6018801900300b640044140d1100c81d0001700821500758007510500d011640f881e403841c4c0d1040c10312503541c2000c2d40c0e40c105222806800594403005020f002d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 487624928 1250 487623678 487623779
    0x1b05061f030f03030c02060f09030f03041e06150515030c1317060f0108010903020c0415081501030c06050c0c0f0f030a0b0a0528050601110601081501 66
    0x41020555940b03400b034075001160400c900003038692541180f00d1b81c2c10804150440e1501d4020011400c00034802d95807442040700b000f031842c10100014081c4000d201b032803054242c608060801c12442850000010078001e481580c1c210140300010446080010440e130040302c80b01d880701d2440d100c0d040039103203035005410306100750781a0070000b050303046800c12404208800b0070010000340c00c20241100d455041600510100c2e850100c031640803990000c0e90b41e00b40300040d1070015013100805900100140075410400c00c40c0302f44401407000d103000300a0503040341e0140d216004243c2e141c010480b85489101280f0b01517500c40c2000c1111440d104100202d406002413101f8030341190b00010038286040326100355045145001003007607854541c02003a80c0900002180e09083d4541012000584040940000d442d03684e01c000407100d0b405000301c0c24060654804480381903940f5800259600040030400303c80c0d0040c40300015002880c040c000b198115201c4070241c07000100c04210040d001e274030320b46 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 487626178 1250 487624928 487624981
    0x61b0209090c1e01020d0c02010203031315021611030a170f0d050901020d0e0105010b04260307080315010f14030406060f080706080f010e0c070f120f1b0506 69
    0x1c0b18265121122611412040e20704950058481000a42002c0104a55400740045d100f42840140e07030120450317500c1071504070031410001c1c031070522112290030b030002d41c50214030018424852a8402501081561213400090004035402040c141c81d0550f0580040810885002c00105082c114001d4048400d030700207518241403980d0312a40507280c0507141c824003a5070005984412030700602410845480d460001e00c101e503d084050712035446107100340250140d10403813003100f05041603403c902e51100c0c1000c40780c49186604202e41c56a000743d400384800c2802846500e0594080c1d0408101c0740456103c000c1440d0f0307520b00302100303640010001c480d019600c64001c034082c840c550f5024043c0000400034802141400c1c00949848c401901085100550740d0041054240541c00290300c4a070710410692141c00c0c5242400403420b001d03600505503146280ba255003a039203c01d921140f85101e0360b42c1d903041c000e101c0600d0030030440d0380790141558001030001003d2145040d4030880c1242449103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 487627428 1250 487626178 487626193
    0x70c060e03191803030f0f0c060905061801090506040602071a040b06040e0318190f060302120105040b031e07031704260705010c060b0d0b04020307061b020909 70
    0x1022800c0d944400d000c0d8151000034000c0c0c2c00350590110030f10004480e450000c140190843d10003811076000c03900060100808a0300c51114240b00d00005001a03601000610100f12145402c9441d660111a1062500c0b4841280d6468150500078400c01076000703005400319490b40d44030340c00650f104040540ba405101840304014240d41e403030301881a40600301110341810650100801d6900182140302564420700001c81c3c0c0c000103080c04480e04a049540140003050180100041d41256201c0d1550100c0d00c100011b9017500342e00285a600003800079611241e13210000c0004940c0c011a1054055102c460303074080c4013a07000c10944041c40344004039401581d0300c0d61801142c400e0950301244001012404010f4001c981c10181890315001072040210f11921101c15900c07034042c03065030b04018000345118280950b036400103c0210010741040c0c4000003605004c0460201a20124080c0c80f41c00d50000340d0610503510b41c100b6544e224031070b0642410070340802810f164041c040c500580076561 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 487628678 1250 487627428 487627451
    0x1c0b01090b0f1206040b0618011404110a0201020705100519110409020d0b04060f0605030703020a1b0f11010e130509010b0405190501060507020112020a120608010204030c1d070c06 79
    0x3100d070b200020b400300c0109071300d180a10301101c03000405840c490003040f802588c082000211111213066944054109482801d0f020005000e08105000e05107003120004040044540c19002020181e00480460310b0307160f80c230380c0c0044c1101d01c11a1040e403415908034032148070b6001d5130801008a4500c0c0021801c003519085c08504984c04000e103804060368903203d01c0001e0902c0e0158000a058042d85115000e26004000d055440010241c0341010750001d15603003010b001c1d069245400109540b45055001030b847e08254015000c0015118440e80311100700a540c0701d51040d04c00210082c0c810008000d8448101001d0107014001ca0142e5480b14100d0b0144e0322107109140c41750394640281c9440042c010403d07401c54006030491800c202040000380c001d80d0700b11113a81c5400300c2003140141e0310341c14013108440c0b41600248103060325050205c000349032281500607005030f0380160500c1c10305d9517882d81e090800e001c40741400d52a85800d00300107980940a42c035980c92240c0942e03004900481d061 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 487629928 1250 487628678 487628689
    0x10e04060918061b0503040803040503070f0c060210060b04060c0c03022806080601050708070f0b0103150e0102040810050c041d22020f0f06090303040e01051c0b01090b0f 75
    0x841c90b0282a140300710004040c0456030183c02e02c400c04038082102d200e280340307000521501c0010406081280c0002c042001c0000070011141581c1c0c1100a0000908191500e8902c0641a11420740107101da02502c0502102c1d5205031401c5403002c0c1c02c1240340034a0718605640c022480b04040d81c4041c81c0000000142e220213898241d81409070031002c10100368000c0c0c2910030200c0c1d0704280100402c0c44204800b590704071048032105a00062065201d07412032901140030403402c08001c100300c0d9200000410049101c40c000196402090180f0150031070b103024500300d0045105041c101d5016810360072001003140d0240d6041181980c0c460316150321502e000440461244c803107115400e040c0200648101981640e014001072380303071901e554901540000b241340d4007442c0349170f105403641112201907960303503011101074000182c140c07500d8583c2c8030180b044184007442140d00941c03800d40754590814100107035010040d840f0401f150541d02300406a030042c0319181d82c07141c106580400440c000e0346e91 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 487631178 1250 487629928 487629941
    0x1d060f1201020c06190c0215010e040816030809190b242101050601080c0711010e040906020c3c01020d0e030c1e120d0f0c08150a060e010e040609 64
    0x9050301c0c03145c000f2589612000300c030811904441190003002d2002d1303441100403c424119001102c0b41c6846440e03d0030a040c140c450803182d01400100300e800c100c10140c00455080c416801030742516111202c0b0300c0041c40c02250081c0084c00c4c05c041e5800690380194941c404054a84101682c051000c07410700840c1002061480700e800303807015102c00d088038540900a4952040c0207103010780e414144484454500e008041c80107284100c030240c00306080e4410a140c0e08217100040090140b411141440780080d440038412600ea0301804c4034040156285c0c8016002059041810030200c003100c0d00320881c8190a111410ba5554082000289250340d600842d03490a40c100041e564844003201240c0c54160500b4034030124400c586101c40120a000c148505c0041452400c0f40e581c00408003200d004060800d100b413012844c041c0b0040704141d1041800d8031407120040d021052003902400c002c042181c45c41600300041917051200e481754410000c04119400c05800400c41d0780c0c5400304581a80e64 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 487632428 1250 487631178 487631191
    0xc05041404060c02031303030c1a010f0806090d021e0c0d0c0e2a0904020d0e030c1018111804030e21030d0b060c01020706061d060f1201020c06 63
    0x41850510052261521540e95240b143d400258681028000e044080121521015083c4100d1950100034402040040740207009012034110140d80c640d80b17481208025030041c00458494000000c404c4400002c0c906c81c0000641c000b0800000c03000302c440402110040100054000d209480303100752180e0031501180c9204010f4850041c0c00c1a05080c0c408200038500c40618060140d220001c01c20601140c4450703042045455442030700c5030200c0c0c0a0300c00c1c8031000004030300e00807485410380408006002c0480c00c8401b80d402458000d50040160b513804117100b84d565208002c2080050b007000c044c0b00101d2000b03003c11a0320650741d0759a410211044400307401007100c9101c85407141c0303010403c41d003621011051010910640c003169035624000c01d601004002d42e81c1e0b0070385070599181030940380006d0748030009554031322a51030680041e0040f0302c1a0811455544160031440b601909a584a500701a00640c03044951a0400801d242040002070043d5420010449090010f2080d60311454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 487633678 1250 487632428 487632461
    0x6050f060111160b130e0a0204290d1e0504031815140a03090203030406030f0b06090916030b0402070c030c0504060f0b07050c04090f061104050f0402070c0504 70
    0x303015000501504070300703040d4031025008006030b102041c0810000c0300584080c0c0c1e00b21074550351021500b4100003038075000744007010b0000c000c0004042071600140180c8922407c5140702c0803985030000d0304200c0b600003100c050070040c441102080710303079800400c0703452580e00f840b80500541008001192400d550a50000d502c480400d030400b03a0b0003007200020070110125511000c0d0807840204103c0706c00010420b04200008c56500061285d00200079858006058a507126968003024000700303005031107805102d0504e0f0154140d85089010303216a244050031207010303651030154520084c49512022803d0603a240c01a4030151954030150047d41c1c803541780102518154200440c0c0c101c2150301007446507041880c28400c9100b0711041e00304454500701c14940301d41a5260440c24070610132140368100d85000300190034083c80307600340f069131401428104950326000c501071203580714070b001c4e00d41c00400c5400c0000395802c2550003454405d024060030038516488000080640b140c40d000030502c0e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 487634928 1250 487633678 487633681
    0x31505060a0518010207080c010c060b0a060503040506010602190b07020114090a060b03032d0f0a031b020106030c05011d090106031d0c0d08090402130905090c06040509010306150306050f 82
    0x81c0d02c040d140c0c0341c083e09000410510307241030b0100fa650448640c042d4104102c00c00d10f1420440b944e00b0464200c1c100070581c0c0000c94848500401d15002140d081e81c452207883c00000c0d0050020488030309125000b030785606480d055461b004564100609200c003150340c2c40052089591589103001e000c2c980801c00780904c2401414920f05480a500c840d80c0b10750010406801d25032030301c40481d0b1714039086514804920303074100f2102400d802070700c04003a241180014040e02440d407550054000400300b0178510841c40c0b089204030300300c5180c0c3c0401011811094414800c41d03000c0d01380a51041124a40e0030006680b002c0400c0c2c081c1d20a13403241021070b80362804001d81e0030841d0610b126400783e120040c0400496000003135200c0d90116006440c0690004059016032903c0c0c0489440c14104102c0313240d1107588003400001464211501d00c6c00c1c1c06404d22111140c5442c81c201c90850f42c0c01880000c3daa421a01c40f0720050401416500303d00c3d2401c400000000c03403d0180724800d10300300c0790403c0345 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 487636178 1250 487634928 487634947
    0x13003050a020d0206150f01050408011103010e0136020c011107060606080c04090f1107050706020c0621150a03080403030810050105120405012715020309030307031505060a05 77
    0x1e00240c50034075015904000e04000c4403c5001072500c0070034a08980d800c1d2171201d031400627144d41c400ea8202c007090b03509060300c00ba014020f010040d0b04032020302060b80d4440c2e90300d4820013084820380441070180f10066800c03480408000031001010980f2500040c40e0a00c3c0050050071104561881005038601141e003006124452080c80020449400c1a42007460800321303444a82c46240180700344242c7d075005005050500d0303801212100700702c0f09625510041428450b40c2c6075114480c00e00107204003105d55606044c18410b4603400c1c2140d07181890241c0c21481d4405034014010f06012841401d1000c4035551b6490b007017048000c1d0b010780c841700e503118207504000384103007801810380b5060004950300f08443c1c2d0b4072004031004a04036440c01100e0381c403146400c0d0b0161440d0031a658040300c85001d0103425849080210074814400d00403900f807502132028141c1603010441d98403055820034000079903842d000750800c8041c1440b041d012485140c81d1000990240c003c01e0512000600c081908080e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 487637428 1250 487636178 487636183
    0x9060605190915060903030311070f08130626060d020324070c0201120b010c0210051c0c02060c1b0d120e070807090209040216110102100b0306013003050a02 69
    0x103c08200c2d0503010341079043c0324000d031011041d0321000341056030b90f4a42d90700340925541a18106540041c601140005600307003074003190050105440802c0e03141000040550182d941e070400540400b0700300c45010101308c20616501030003044207820500c0141d03908010f03030742031007030007074880a0000d8041c070b42102c444503400131040245194180230b1220314800140c0c0c0c00c10201d1845162105c00440c1e000c403000d004860f1501d940500a40066a0558420032943c010020301124034180000c06105070180c2e80b00d4042d62003080140c1c016800100216003591000c3c0300a00300f05071600443c0c1080042818810700c1e15004244035000120425003a50400b140e0b0f01499040c07004240007403140c2030a0070a0b498443d80d40d4411840b480364001100c2c6410b403103d80684e070705010b410b64443c15440c800d0030124164520760300d040d0b005010304441012102c0013031090740032040001d002415030340c1c01c1040000050407031095101c0020041070b4090400c20081d0000000e461096881c2511210660800ba1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 487638678 1250 487637428 487637441
    0x7091d0403020a2004060b0d0b1903030807021c02010603021c030212090d020a1805091f0209040615020a1b08100207030912030e13020301140103090606051909 70
    0x8501080a0060001090340003071025603481c0c1000020259051040303036600c0302504081d00d941c10506007900003402003460380162801c501e55000c24080160500d0070046500444500c64070603034480b44041c40400c1c49001e006a124400d40101c5502c03901e8001d09416140190020300b0050391155014802c504040101030070b0056401a90959070702280e0700a500e41c0341a81c000c100202010842d49141c0e0f0710320000c90300e6140c014025600d603544426030f0b1104000c192401c0340d0410b081201007800c2d0390001402800128a440302c20000c00c400001c140040d502140c0d000c0d6201d5140e0070049450412442032100640b441d400a0441881030326016001059900261000704076018040100800102c0c0c0b40c0340041020b100181e807091b0314542a0b9040701e954001a03034003112014440c04054011581144424003254003040e000340241408050b131109028500500e00d942d071142c113295029802c100782c800c1c41440c0200320251588081000c0c00d44210390300341d4644072030100b0000081140703d6607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 487639928 1250 487638678 487638719
    0x9130204030201021903080a15050a03080c01150e1506040b040e06090a02030907031403071b0f0e041e02150307030902040f0b0d15020f0f0403030807171314060709 72
    0x5c0c40049040c0c0c07009000c86100516840c000390300d0340c5410719216081400d81c2c000e00030082c0003089103a00c07401c0044050300302d400b281105c5e40c038086c0311603554002680340908540b04046044855600c2522007002502488281c0b40c04c024107100102e070a40780c00c0d020f4405414204c18070301a0345410010014510f1002e0181c42400e8410000d1220b1110041008410341e41c120f012134084284c4000700d1482e610030705001801c7c9200b43c0c2e9410b141c004030b014901c0d048a4002082c40f0b071050b201c0b401102c0850080d10b00601d41ea603003c0c075680350492a40c52044080d800240740c4050710100a519091a500840d030700c0e0002541c6d1a081011480c00b031240b480804c1c01180108048900500400d40d029807a00014280c00c551503181c28aa8029404a401440d034008515854100c24210012643c00502040b4003003201140000c1085114502c0c1c0c0400c2c81c01d69100d0101e03138032800c0c00d00c1490340b581320090b6400348601c2d460520325681003001d98022212950355010080c40c000c90a1001007154155 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 487641178 1250 487639928 487639963
    0x1203030c09080309040e0a060f05070f03020a0207210c031b1a0f160c0605030a050f070207060f020705031209030d0f0503040818030f100e0c03120d020913020403020102 74
    0xd00010720b000090798000b09042e10001654822050003500c1c10720800b20080805050041d00180c96101d6004540541c00301d0f219424280c00c022003e0b0142d008a44040005a011000030003443d0200039030514021104e00e00402c0709151616400d03d50101d90700203441c40d601d81c1d030301c10b1140c2042c01080c60042c5202c41402c02c103014a1840d004452160405240c100340000c00c01b801c41c900001810b40f083e03a13004d444c0080c82070f580c3c0d001034800d030011a1b140c903a0a00c2c100c00980c445c050300300c82601c50385150f40982040c030304103402034428406112508046104404001c1290340301081aa01c0c400801c811980d00e825062041600d8426154000001c0007036180300d070359101d41c101081c0c0f504154003404003510760814554011760401c080c52003660512402c0900c000381d05000c140c0004640980f0380030b100c840c1d030345042c442e17407030307035a5941e003a09513011018802c04512400c0c0070f44070020711840d000d4617101034900000c40c80080003245a10882e400a010000c568040204081c9030a44820 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 487642428 1250 487641178 487641197
    0x7061b02070623030714070c1a0c0c2116081605180402030102090a090e07050a06171504020a0f0e0a14090a0618200c03031b0c071203030c 61
    0x21481003d03004070a100ca007403801101090815018610f0a08102c100403043ca4484a1505003006810441d204410304660f14021040c400c142076021541c0101c0320000500d28000340c03005024040070300c2e00d461800038010305482c40d8004024000409d2144200f10084841c0b0f0801b036140c0c3c101001000c0841c000f0440318800c0015807034201034244880c0c91200050481e80d43c40c0080b80c003a00c5007074461603208029a2000c02c4084890344440035285440702160031098645d01444020b40301806500040351003807201080082081da130482d80302e02c0c0c040c01070407501140e90215060382c100c49646c40100b054854416120781d44043c49e100d90020031282c841c11145005040340040c1c1c041c40526003c0d0f0100c02c0040d45621040e0402d80003440610038255101300955a800000e1001c06114000352400a100140300c200c0344081e00ca10f000b032280a5403554850380d000090300c110084140e92801000d008009500800344041001403000d02c804000c5680e0900e00201121004003040d818040c100300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 487643678 1250 487642428 487642457
    0x90b030c042f090405040602210103020604050415030c1d09060105011b050a0b0f0118060506031f030503120a18050a0210050d1806050702060f040201080402010507061b020706 77
    0x9030b104124180c0700c5400c280098180320074000352064002558020f41058188401c002c400da0040201d0111122006c2c035900e80115440c820880a110284d03120f50148014011442c15601205600c0c240c00340d00494035030b480d965019814000d85c0039107941c0d1403054201400c445c0709856030740c4c45070303200c400762100350b060000180c044803202c0310348070349000c2200450081180402c02d48003116004180751810349401844161150710900505440000520011004903801d01076081660801042982165245080000340c6c0319a209030512480c0310501c00004620207000402050704405000e10241c50407491140c103440f00c8880140720f50341c98080e4400407a0b400300c0c0007107280d68102c803610301d66400454100d4140c06100c200c00046840c3c55025003003010079651a8191300e11400e020301207583c50342d0080e610748070115039400300801e40310b00050040d84501081ca40c41881410220308150307040d1145022104950704200007062042480000d00f6010040c0100030441c91415140866021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 487644928 1250 487643678 487643711
    0x60118060c030512100302040b0103180f050a0209041b120f061d0f0715080402240d02072907050f03220b011a09090f04031206090b030c04 61
    0xa110301810400541480d108152098080740c540003241e200310300507801c01e481004404071503840304a104034070b4600460300c40c1d40079004280c02091919517110b0b490400d516620341088628008131392901421500340010b940d1090118000c0303000301d4503200c542c240e903071580604072140d4101824806e0b48901600004452513042000540c0c4660080386c0c40c0c0b440c1e80201c007403c080f0300c40007802d07014041240d12040000241003080b186c070f6003030460980d900c11000351600c40040d42c0282d0401786041040d5810500308004010855101a03010f1a00e55200d0000003240c200c410100e522040148106510390303009503403810300b03640003c100d85040c1000d02015005220302000c044908001000060a107180c0d0108003000c2140383d0002040c0012520f0f03c03032004c100c2401000c6108415003002c00000410205681c10140003415403002500c411040804c0c0100060084003008010f02502e004100113011703c40003030a0038000840c060301281c040508109601001501891900e0b01ca80d500403000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 487646178 1250 487644928 487644977
    0xf1b010524030703050f2b050a050a050909010914090c091f030f1b0f050a0927050102030106020d0507021e0315090c012601140604030f0c06080601 65
    0x22014078828207410701d80440e081c06035030350000d48680248120a0450703900441c45c00c10b05400c500c00080340d802d5800180116410070482c01c40022018060068442d000d400101600d00d21400c01d2402c000d038440c006600803800f60403000141e5259101100445003441000d90007501440142150301d070290003182512000400c00111660024407035070403646402c1e5198040d5820038003082c0070340d695050005001042c2c03004008030803480000010300d03125100d4800142c40008105200141c41c1c004d085c006007044d450b00c0400c0a103400d11041c48040d0280810f00b41d240b24000140c2ca80d85005006824441c250a100d000d00c03c007003010400581e99590b14240c00300800402262941800001c40e00c1d0201c004c14010881c07185a0922101c01c40020b6240c0c5440401d9850620fa540342540151442640c604400c58046030200140300e107603000010b403031442078050205420207a49440c0d101c5102c0c002501551500000ca8050050560008103903038400c10a0070301818a1500341c0f000c20b0076000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 487647428 1250 487646178 487646221
    0x30512040f06030b010c2004020d020c06060a14040c030b03101b0207050a0b0a020705060c03030a1104030f030e03030f040905060427060e01090803070305090708010c0203120414030f1b0105 83
    0x1003a15000810310071802e02c7c00480018100315200c2c0d025490700d000940c008d180c1c1c810680b0480001468518081030258142c0d0121026510082c8200303052201401035400060103040d00c84800c4140d585042142c14401111000081030b02c05a0180c0c4144040c080103040046400001051046884100e0201c04541000109940e2040e8012040f07062031456000300d54802000a60258104800006580250400c200800003000c5616041c0d01e40c0c0b0980c400103050640d008401c5000c24050304100541500c084c064a140c14648200c0246c290f01c59040841c03a20380e01c42c20301c070050410f8031800c5000702e0404045200f5010030302c404a82d4104c51400201441d480d040d1a6150101c29008034454070f5000e81006d4032800c05d00c0c00074020700701c01c680d10b0b0031349d20a0040014500105000321028100c60b500518a04441010941310402005100381c800c0e500511649200400820081c04041e0035081000d840300f0800302051082d41e40c05120005580c141002d1055008141415154209 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 487648678 1250 487647428 487647443
    0x81606140405030703030503220b130c0f0f0303030506030f03040e0c0f040906030203061608061002330106110d0309020f0306070305090d0824010207030512040f06030b010c 76
    0x40c5080101503501ca181c1025400d409044000410960810013660207150440240320102c000f03460748842103c240103001c0d101c200444007146520030f428035905aa14080c41c002e04280b602c584010500d80980e91001110200d640020001c0c5541072040d03d400c088100c01400303451740b05644559aa000b580610110144404041200c14085000f00c07011b010420200c0c1c0d4a50f0340c0d40c15600010402ca01c411380c000d00406002540074080412140c07040031300c588036281d064440f00140203078150556540300a61168890780100015904d00341c03921319038400d00245640034203842c00c031500081a4058402c0c0510881c000c012181d01044642c4c001c0d40d5443e00044481c1640002401c0081500320540c150107081c040c420313290f900d0707003180340300e061030f00f044481d91584244100c64030401100c0c18502c9040000f032542d4281c10040b088442500c051044802c026142d071034442c100502030696040315680003800700040c01003000d21400412290070704001104101c400600780c0420311200400381c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 487649928 1250 487648678 487648697
    0x12021207090c03060306050f130605072703020406050312031f05180105041116170708120402010e09090c0f040f15090e0622060f050c0307030501081606 67
    0x500030003100e0028200204140900c411412000d00180810300054600038103000010344c07400c0807520164043c070a003c514400d885025201d4400900c406031000041100c0b81e141e29458072054003000e00000c03c10400d6403001c0346144100000c440c11540010700076040f4554020304d100011003602e41c0847c400740c607101c0a0310590b030100d42800540d0802680710111344282280b111403640703003506860050743c04104144642200c0b034a18042d804144a03011007220700350000484009042c00310400c4a414541041d20607615100035410101180300c16040301d200304802c5d5170780039909040c80e11056840c18602c1c00c010442136200c00050200c41d00170000c6055450381b94903282e1210b8a5210001c1c0c1c00c00a20b6171500035000d0000f05481440c52840c100754807846ca510000c61107501030143d074228180340e4086200d940c043da240101095030f90b1591101d40c0031440c1e24034000c261180203100d062960720b02c1c0040c0042c08444041e001821036500803509441c8042542d01301d0303000e5400c24144802c80c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 487651178 1250 487649928 487649959
    0xf0f14010512041704060f03060801020309191b03080310050d4101020d0e0c010f0c0c05091003021305070f0e0d0c0e061003050402030c040209030a1202061f1202 71
    0x2000e500038134089104000190005400d0b91000324110014490f03581400840d0340c2e548440e0a03800b09684006042e0441c1c00700c01c400105907440401c41c2c5201c1e040b2600303000007410340c240c01000954010b450312803000007008010010101c000000c0c00d07044a245c0400203c1da1198a0b40e254a18558070000b0a0704041c2e000d42c203c002e4056800b80e180c80255200440707900c1002d070203034011401e6000002e06004812a04150210740c82c4440303101039589105a02d03c02d2001c803a004100c8000366008282c1640104450710b030401d045100d030145581c0904040d2540c414000c1d60b8411144004007103180500388012039034000c3c01d200d2005118542038180441c0440041d280070154280100b298100502c000740c40400f61440500c1a001215020b1225200d968160306843d8100c0d170081d415000f010580ca41c0340b07840e03405000401805411646c80204580d10a0214429002c4400169001d2801c0081e1590280070717a07803d441c2868449840a46000358556081881c604000d2094001214a004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 487652428 1250 487651178 487651193
    0x109122303091003020414030a0f0b22080405011205090607050921060414160614041d100b070b06060c0f0a030906020d0305160c02040f060f0f1401051204 68
    0x4290301e000f000d00711000340800c2d014000b944030307200c2c2c5010925101c0c5140e24500c2c010602c000002c1e00004440d03200805a550350400000017050350030302c001150030054042c0c0b1002d140442a9100d40340b8160340764180030001d0400342c004010114100c3c03c060801603200004101540c2219690800580b030f1803040c00000e208d100351411580c038980780150b0a0700303407000c0060700b20b02860282e040d03545d0100103030070a56205c18400000300c440034a11b040c01c0003842e110381881000110203240303a50800742c90340d40303020001a881001c1c01d04410110305000c000501480e442c0300510780000360b103140c2590b035500c3d80d00c6504001c0161707202c0c807800310341c0301c81103141130100c042c0410800c02581e1006c03180c1d1401802e0342202d402050018405c030025049a18040e100b05c50044820703607455400c2c0d0101e982d04440c4815018400c90700143c0b40c000c0b040c40451603005900150100f09035484ca4242010f034810032540443d846400920007054010344e150b6001400c82d0755080c0000c015840c980d80d1818080b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 487653678 1250 487652428 487652437
    0x40b0103021b1c0503060109030b1015020c042406030b0d050d021b0108100b0a020f0313171506010809160306020309010b040c0f0507032106050109122303 68
    0x20801c242c0c2420011040840c5499140380d0000c0400c2c500c00300803008903114001103420034042a0071546c00d1010445441199501074100f480c840e1505465101c0d00b103104003c54120303000350307000d0411026a40740a010700c1c04252040001101e10100050340c50804039004e00c05d5105055881200300403903150401442906c42c0c000d0110313650740d107029100a5072891013021801080003180e901d240f00b584698071850068004003082440e89d414400b65504030f510034904282503101c0d0322107050003408107102401211084160907207140740340407224a0445030700c250302e6556400c10900c00010b030480160403a003180c4c00786445503007607480150041c6003014034005400007016618000042101c0343e0010361141d400c0d01c009204402c2c0321301c103000a983c400701c01d400119a211441d10000d0303105202030100940a0b02d4202180400c080301c1c2c072030f400086981d151113182c84e64030920103560001c002d000108003900c66503800c2d41550b2921010200612445c050341301d646c059402c0461000c03c2640c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 487654928 1250 487653678 487653697
    0x10206092104080328030603150c1205090c01021603170c1002040306021b161802090406030b0a1409030a03020d1410051e1309030201090b0112110f0d02040b010302 72
    0x881c0d03130700c81410800e4004600d060945c1d140310710741c038660300d40036100303018000840358400c0d42000c44110031560030f00600f9070100c9007020881e4910780c03690301d5609802154010310b40d0102908003482c0139000282415211240a036400d25005030800020f00c0784001c0032130341428851130640b5610b180918506003c852078903200034500218011042c040540c0c014500c050701721200c49022100c03410040e40f2a0341c1e1940e44045c3d203064140400c8001da060904500110307070340303500520f07040105001500b11030458100342c440c00da00d50100700a0308400d00c43c0c56016001c151417607a4500d4100c1e0159900e10841d0000c20825401090407190146640c118403c40c2c0c514404c10003203441c1c00385095001244501c41d142c45400744056401c03907401403840505200c81c001d40255000d000c8242903e004c2d055071507007202199605c00e0b03620f020078540280c0034040c0c9411309840c2c1580040c4c3c180250f20700d03003405030703980300c2c1c18900d0a0b0603403651004190f906096050300d000c00c40f00703030032001a8024007404010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 487656178 1250 487654928 487654933
    0x1020c0c0907091a04060305010f050f010c140f010504020301050a0207120f030618020c012409021b0a03051c06060503181608010209040f09020a260a110f01020609210408 75
    0x2c400b04c014a40c0150003a0740841c1d90400c12603136119295243c00305940b1845401402082c48618a544138001c0c005003a0f014503030008801840c1c0b040d680c9021032405e50745809942d142c00744030843c0390078048c1c150032400c0340c01b0540c1001c4140c0c540c010b1002c44014540280448401400c1d0030900a0704441d000709019448030b100901c805203008081d51040d29610015440c02404040c41d00954100050b102d1a520014007128104001c3c14000d50202c10804400340c03010940500c000340c10002c142c42e8070720913551142c90f078004886031840207005130610f0b1019030400406002c0d00d584082583c4c1e1001801a254aa03113800c003011a0904010100d17000c0101581c40020401600c150000d180c05042500d040202c404064000011111100d1000f54410070b11841084407040402d0364410403e11314148040e080090b00040f4a800e6070070320100c44203600040a5462031500c41842000e018082c001b034a903500e80074801d1912210018040e550356004c0c0c020407550808040300361000361180e0000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 487657428 1250 487656178 487656209
    0xb1509060c0c13060e160203040501050901140c03130e0f0a09060e1b0111012a02030408010f0f050105040b0d0b1b0412050606030a030f030c05090d060905060901020c0c090709 77
    0x22020040c09070750003103410b052081400f24002c5580c101d0034120346c6810754040d505140c1403100440d00c030f9000c0013126040083c100e20340c540e0380f8100401005818621401103640c0c1216450041c1c21712919440742c0d00160051040002c01490a00c0e0b859110181c000002001201482e001c0020980d001c15041a440703030a6101c1000d00c031242d145000407802f6202d1854612054004500f0780da0b05862000045600a0280c0d8055210419a80041c4041d0040e603040c1a2143c05090850300070a5180c10700f25200c2401400c1e002c007078070070030340035040664007802061078900204070700315031148009044503e4500001c002d10180780039445903040c14400aa503655a50980e41800800c2440c1541e4074001c000101d507003480d00252154456905480b06000f582940c001031b001001c01c8002d950911a00700a0007100340ea40b41c5070608624815100026212800d041c204d1800c0c2c8020650503036684108509402c1050008052142410403200c030032065035144001c40f4400020783c412140000300c0711 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 487658678 1250 487657428 487657459
    0xd061509030506090721020438150304030c020a050301060b03060307060305090703080310050409050d140310030b060f04050709170303010b0307030c020708030a02030705010b1509060c0c 82
    0x10380303080c00c03603004100300c45441d2075001c006500d640700c5114002c4101d04541400d0046800f0300c0d00e03a240c040c0010800030795400708081c2050f8241440841e03400740000380c01c858030044202440c070700700c2c4a0240d829240480c180c5200310072520010304054284240d03040c0725030031903607543c086001414000e0000c0c8400b6540302c00030b140c2c581068484500c00d0007100c1020803041c5c80f80c82443d03c210008402003258030724503141c0c11103a41c07010340300303614140c801e103008a90b9407600e00880018a102e0300040504040c21003004000201c0341c40c104000000c200180008078001c3c480c00b1094a81011400b810340c0c8400e030010309280840c0d2410341d0001d0400d810001d01d543c02c000200100c803a40f042403502c0c006c032401900c0d1284400d018501d40500d003880031030b121b40c0c0300f940401058901c60040711100c913114a889842e6801c43d65a22006910000d002001c00400380182d07000c0d88403e03501d00102416000180009014055026008500109002e69844820001800143e40191507a00340e0751880 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 487659928 1250 487658678 487658687
    0x131104060902070201121109190905130302250b09041b09211203090f0c080d030c021207030f0c150204061d0d1407050a0e06090106020712080d0615 65
    0x2000c3c164041003500d003150b68041854046c55501c50900e04005142840510400c02c1304e0301d076aa0345e540c8520740503401040030002489124040c4240540704c0035503004070f14000b46000390854003a43ca40c803c02400301000c140540c1c140e01503944480c442515550300c08041401011600440f5604034403102c17856002e00c2d0420b0f4800252002d0350061000800c2070546511100c0f248800100094545180e1a404510aa02160b5558801c0c1e000e800c82c00e8058507202d03410580c2d5040004545c00c00588e035101c0c2d6801d0306c00c0820052590004c0c10040c41c0b5041c08111500070100c0240900560000d0750040f00d119405400040b64041f0803040d07011040002d18000713400c5070060b200401c1514030f003c01e402c0c43da0030403a62000001007550062a0390f039035611105100090102c0c1852180d102c0109281e512500c0000c0a806a0091008146810b03002c010000130180d0241080d07401504050040d81c0a044000042c6500840e0080e0789101540e503520041c01d07954040a00b0300c4900d00000340c0d89500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 487661178 1250 487659928 487659937
    0x10f052d04032121020d0f0c090906030b01030602071109070c050c0105030c030a09050f0d0315120206030a0e0304050607060207020901061b150b061303210503131104060902 76
    0x550302c040710210314055505080f40c0e0450140302142c842c41000c044a000804440c41c0742108082c05400c1c015400411011380b00c0c158202d000302e649070360f0009456580020410024040104180321041c6582c80e00c120701c5506000c0900503d40000e00041400001185801e112a001d002da070003c0c903207424000c144043c2100116039500070403403880f80541c4510203803406500d00c81c00692075500c0315440c0f0001055001e00c00c0341c1034019603d25160610090007c244541c949440c08245180782c2c001941001325590850110070544d4036281000d603c1d240b0940c0d500c8482d03030600107481441002510701c3c0d40103c1e40004d9004600107141e000f001120780140400324801d803600402a40c0301c140540344140c144028141000110044001103010310050440c0c601000c20300040242103030340461010392110309644500100074600300100110780031801e442e004051301c200101e08213404002c20510019003100301c2003e00c040307000d060043c0104210103505005108011050340c500f1403401a411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 487662428 1250 487661178 487661183
    0xd020409020303040e040c03060606030c050318010e100b030f010c02030702280f08100b060a050d060f0e07020601150e010e0121051617062b06050412050702010f052d0403 75
    0x8288000bc3c05030300901a07001b13a59069210141076a860612185040e40c04100c4c010080d92161200b07001114140100160150448030100326500078200b03051074072005900401c11a850400301400030b0f6400701c26680150750445025138100c40100c040d01504204200551100a81e1480010b201003080e8441d405c580c1310006490020511809a0b0708842560004030303004402000400c004030b11607001090030300044940095001d464207190644415503400400c00c108858080c042c4d0300f5010001280141002002070a1141c04190010559181400c1c00b9060292481001078203070f0041d2140c461b60118244403500f007541c2410300c2d00141c00d068464061240b05540e13020150b80c819001404699028407014104d62940000e02412110ac9407c00843c1421010542103071000001036503001809404085079501342800c000e82e43e410440d2280341400400c0060b100141d070071441407080d045035400d0180d1138500410351903441070344a0a0b04101d204241e6a614241031006014109032070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 487663678 1250 487662428 487662431
    0x1b0f0d02160509040201140f0d0203151f0c0b0408090405090715260901020715090309091b08071b030215130c0905040f1a04060b040b0d020409020303040e040c0306 72
    0x80d81c030b90510900305000c4e500070f0700180c2840701c90340d41d03440c05a0042c94250754000615161642c0351a00c0c10498205403210008a090f03072241644d146000900020900c44d00000011201004031000e0141100c030700008200c26019070000b01404a120252001408041c20600c039034034081c40140e8480d580c80c01030003169805080010a2240b250240107102c07803015040400101824510f80381c1604000c1480c082da640800c405800150a03508000b02000004408205643c0e0340c50050413100e001e41240d15401e10308138a0644981c142d0141c00348200300d0741806c0c0c0294450b40c0003111565441911700030080c00601030300013096800100e40318100030358030340e00c03074651540500c0c12104100c210003d4030807804040e0500440c1c45680c0550341103031140302030f00c0551820b80d4498020065290007131044c20038145c1044240705503401048840e000485003084417548000000d400320b44070a07400390056690381507100131501e08204441c042d000c1c01d59201e5107031500346001020032025000846259 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 487664928 1250 487663678 487663723
    0x303150b0a1709010e030f04150c1709030a0209011814060d12020c0306010603050a0507020a0b0703090606050409050106050120070e0402130f0b040c050f1b0f0d02 72
    0x4400041640d1681205950704624280c40414403034200c1c02c080c0100c0c0311550303580c8010844050402c0248201941403100395100e5107440220605007401c00850701c24082100b52510020701180f02d441da099582001305074542c1124004079180584919000f074109038000c2c0041070701a44600c20b08000500c40c502405011040c0014500424055407116040f1301c4040456000a00311164054507010510486070301d001c410001901d040020790042010a58507401d101060404c3c3c001e1035444102c0f40005e01c0e50308c803107688100000c0c9009100c4400c166840001c9410441c16411205c01004007c0c4103104001ca030341481070003801103218480c0820061f10380042543c400c820381c050407c0b1404051310151785403c5800900c400010001c03a40300303071076000103181c40b00b5a00c030750348401340d0007000018042c0420080c401102c8814140800b440414080f1f4011009000c0c220b0712036904510300d421401a0b44000a480c02c00c046480c08074500510760700011a45c1d001a90003d026102c540306442c9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 487666178 1250 487664928 487664939
    0x1200f010225260f0a09061b0f081303050f0607090e091504020111031b070b0f030a090204060b07080901231605160311030610050d060c05070609030315 67
    0x700c551030000814600364051901c0102c031840ca5410090841c520443c2e00c0c01ea092040e1800b254800d00540c80440e40c4258248074042d48002001844c0f01040c94030081d180841e1135100c007550010300002d02c201f40001c1e084d80030800c1000303440011079101003264603142d403c13a51341d03032100c0c000c5032060001040d03030100050f08030509840074010740f41000580344039050001c818501400040c016070500002e00003200600342d0802c014108403060a10051001d6071100c0028100360840d03100305c101d468240642e010003030304541180d401132998140042c038000d0394404617015202079481329200c0d003c0070a605007413100c400f0040420401c00d03030301e4080e000a55901c0181c0d07051902600d18140380c00f840100703103644113402d0000c0f075607020310121003400251079a8511024982d800c00c940240c00700400801e03d0604001d215001004c21200550281c10302c0d001c2012030460343c1c0c015107029251201540481d005804840190303811a105204080b041c0c1000340c00f8001640344c01003016660a40041d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 487667428 1250 487666178 487666237
    0x40e0304060309200a06030b0d020a03110f03030f1b0f0a120909090f0209041106030115020c060403260d020406030c0e09010501050315190905180d08040201200f0102 73
    0x1884c8100030310900c1301d141030480803401003801800144d002071801180700003607030341e954003d001540b2803805030408546a000740302822103100b800c18080c5d8001d101401c1141c19540c01d0760200658134104111948106d1113152900d0420001034020f0301500040100340100b15078400070b140e00540310000500e688003110021194101030241407040380303440306001841e0030710700c0c281c0180c0039a0f90f08042030744080018070075502c03e900110360203401d4011084056014420a00008012108182440e06e191113541d0500a11103408002c0d5485403000306600601d1b5068405110307010318215112515920043c000705904940540424103510a000ca189000300545040c0e81041c1d40d158115101da804910207a9001841035601200d00c2c03040d2814088500b940e40700500003d1004500343c18040200001044404c0010490342c10052020040d03075001052075806c1a8280b030000940a003007020184040b0518124480d14000c210a20800300015009030200603081d0310020310b1105148078125 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 487668678 1250 487667428 487667483
    0x4020711090708070206160c05011d160b03010504020c10020403242a03020702130c03050f071d010903060e0d1e0918020702030607170a0623040e0304060309 69
    0x213006a00000c0010603001c0e20200340e80364240306050106500c8000c0e83c40728203641072000300380c2c0c0c44c003800054207240140400c0210740c1e10341610842c0300140e0600308042400e100500030f40707010b0341d00040d028858900400c0040044140750700115216078a0b441d084242010001c0311400460314071201d07960180c00341c0b01d42241503459049007107007a06904881402a00c6121b580f8080c550709210020168840301d2600d18081c03000400050100c40d1424003900f11840680b954903403013025801c0003803050700000030902842a0003004041500d070768004840740c4c0f640e40c000920f0103080c82e41101c41c4100000307064090f08420345035050003049440c0b18009100601d07215000103601d080c020014480d00500d201e00c0c05440d075202614201484e00401e160003c02d94000c0005404500f030441d0342e040001030a500200c0c6035009001d00745c41c101c6072075002e2800c461400c580a80200b01c4a401e50340755888115060000c1060701e03182c1e41e5441c0c029004020251059601240308007105501401000300315 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 487669928 1250 487668678 487668691
    0x804170c06032e120309080f03040503030d05040609060204090e0f010b0a05010809010908160312111b072c0a0c02070b0309030f04090f18030e0d06060504020711090708 74
    0xc10f400400c0c80c00c11030000c00b072010100c200400d02c030340800c0c000c580d0840c2104482c001e0315056181c914003031106290403214260030820740c1090005011590740482211001c030328407600400c1c01d407203a080001c01880b82000040645200080010702e0f1041c81e00541014080300b01900c42e6650141465030036114250310165221901d00d40503c000c1d07001d0130026400040c034600010358043d0310f90f648000d41d8400750040000b0030921500d0000c05034404182882c0700411780381401703915180380b02e07a4a40c0c0030341c4601c15000c100c4911240c0440740c0400039203005218101f10200b00300603414901b40b94007404914010740280c1500000c1103030354903003d40d0403030f400039034011305030340389808101c4440b900090800207079030004100907025140352401500140c40c1540300000d4098200d50300c081140c58000105420312801e94880d80826040f402d154513041d001c0d071f0068000681854200e006014541105078054404a0204c042c450708600f0303c0350082c000d8030b00c96283e0310f8040c0d040da41d140040f50b05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 487671178 1250 487669928 487669951
    0x9030203061810091509030306030b101a0a020319090609050f030a020f190b04050a14031b030c0910080f03460309051011180105070804170c0603 64
    0xf0428404059115807207450043c0e001445d502e050300308000030b0b40e503c0d420079000a5241e4a060050282c1a00c903d0b4018406072821a061403074045034500d4008a441c00350188440425400901d600038000c40d0f002d02840740e032910400003420f001510384260303402801d00260301b5010205650030204081190304000070018000f020701a800c0102e00e40446088035040341320b11603901d1615103100848005020130680194441c1e00f00030600800f034a1990100541c00d03060703501501c0c5074034081351701044040c2846010aa044503000400d261810a0408982100b031807410450800c180702c10a0301912540301c00c0c0c480031012004540da1364007400c0c50003141244000e103581c0411318001811b001c2c2104d0101038514100030340e2500890090005032000200f03498074040410010103012800340014190340800040c449842d11a6507405001c080e8011f4540120a000081c0c2c0982c00341c6402960002249079200c0d251418600c8400d941c0300065040d00c03d48113680e80e1442d010301600d1148031007404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 487672428 1250 487671178 487671193
    0x9110909060d020a0b0304030f02100216020f04020c0717070b04031a09072303060106021c0305100f2403060303050304150605061306140301062f030703090302030618 73
    0x700b1040e80700d0040100e031301034246540003400c112524042c610840c02900c6110004034901006070426824103035540c18588100301c08a8001c1803400d0b900b10558060b141e00914001e41e401240c024030503054100803034032903610300041c0404044910414800d5101c280c4035920340d110451461401180001070080c1122016411822000b0701e50355404644101181c0c145995610307281d0506801e925424510080e441f00c0c140c01d410200506401000da903c01000681346402c1d10001111a044143d010107403640c02050010081341a030034098060303810710341c9505a4072503a0030320a00040010708000184010b441c0c05481c000c1c03080c00700712505512040e1440c1d41c0d9075240d50104c0e407180c0d184504196200b1022500e5191800034100b0b0800c03080c0c511003400d0420f0790290000b0703500c20b40d400481d14200010f118032507102811808200d16462000d5032405120060031003e21500759030099480080360310404c1c103601800103c1124001e80a0310460385800900d50305800300b0450b6213045a00405 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 487673678 1250 487672428 487672441
    0x10f1d0f01050108040609020d08031f14010f11010c050903060a020c030307030b040f15090e0304120b07020f0a0b0f13020a0302060313061806060608040f0314091909110909 76
    0x31403143e100e841154002111f01103035001580505a00406440101c004820000720820307080c100400b01210798039009101d85802444048061314100c2581044030804401411a0088806001541130303c002031002241c0f100c4020419040240224401e100e8440071881c0c40e001403080304d542a1000c0d02441c0303140e50702030060380a0304442c801942c1155071440116801ca0043c403490394038918a803441c010652401c194001500d03880411205a5001004104503880621a5081d5400ea021038440620f6680b1031040e405d00c48441b0462041e4003801000100308000c031204a03100b603054013202c46154032514094404680100c800139003001144200f4000340c03400b103000d10340c001e240078840310300091250380d0a01919203030b445103062071510a1035681040403d020740c3c1c02074003452030001c059280503203850314035502c0280d015091003c48449075000c201111b0403140f41d198007a01501a00c06408903c0c035034400c880c810015003502e400400658005124110350395840001c08200c05034a910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 487674928 1250 487673678 487673687
    0x60109121209030b180c011403040605090312150a060e03150903040f060201090620040e07050403020607081b0705060a03110421050118020a06030b0d0b010f1d0f010501 74
    0x201403509016030182e002001804a0800c20721030340c0c0c1425103007248040200458070f00030300c040844e4140801d080e08030741483c0407001a207a00640244010416858100c03041c1e003103108a60b954100480040c040103c2c8500b60000441000003e4800385850b56030b6190032107400c5074942c222541030b0001d01e906030030342a08543c11a040f10f850000d40f840c0c1540c4000d0f444102e0116400400541d459901440030f1052a21440000d01d011200b00c403504601c04206107406c1c801c81c012080c0d401203a10109110510407400c1d50b001c0d6a003d40250340ea46568209210f03940c00001281e4080d07403413600c2c40b03210440081020022110003410003030400c0e4481c4401c4d00907240302503110b42405424000096540c3d03c801c100703d02e0708001d00c84030b60392143e5410964295000d2041609060603020f005074010b0b183c40126004451443c40c000404c11070b5a80020034081c0340d41c001400741105c620000c110789060305003210841d209042d10003042e007851a0150040e0300e0464010341d981618000420155014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 487676178 1250 487674928 487674953
    0x405070f051903110f0406081f0c0906111005042103060501020c0f040e0703061d030711060705030d14071d0d0314041206020d0507020f0c040f0f06150806010912 71
    0x1045c01d00b084201501080845a150b8043d852540c084001c00c090b80c407038801c02140303058440d0814000c4040b440030203000703040ca6100301010000010b1040305411424080307100d00110390401402a4101030138645450740e080e02000711004c118091900c140e6000f4403c1004550f41a00a070030056021801c1080c80b0f0380841034540c005031940b103900c407510020720038640994420380000840384444484031800e4480d02c42d00c0d00c1d6950041109001103610038403040c1c00302d0000c80b0303120b55035000ca103803150450040002c9200118104000740e01c0c41d041546816204800e00c2c0d903a1041115009850342d02200380e00345180d042107001107400d0100b0700c9005021840c08009017014501a070302c03441c18641a92402d410344070543e020440c1e10400c0d103140692508602c0c40e2008080c40400c16005a031602da6104415100d1503981d8003d40d09040a0f03004060030b44481e040820689a585a1035030000c001a800d41001810001c00185190301510081060311560b500400c10401ca658440c43c03107518 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 487677428 1250 487676178 487676213
    0x709140d0b04080c0105100b0301030219080a140c0103020a0e0603040222020a1b02180613020d02070b0a1107030302030619060c0308010e16120e03030405070f051903 73
    0x1021803980e01107407a8100321400785104014403999031841381c14080c2101c01c060a081000f22841000f005490061030589055980454a41d0301c100400200204d041000794400d5655010725200c44090003090034114584414200c00d5804058441004404030303c10341c41d40501196040070070000303900b1721030090755001c0d1001d810790035840303d05007800c0b00800040c0141c07140960009100781030544d20202000700350102040189000599500107001e0a0310070140c0000b40c1d5100d000100540d45507491010071270302c3d5400c21959433042c1203402010b54820740741921000c00500100b100303040c4900c1101042103055074a5030078400661b03800c4010f9480174021541c441074040301c00410f00c0500c1c10200041007180c54056140320a450f01610250050b4042140ca000d900b04200050302002c0c600441e07414be519002d8501640e680208004003085001c0d2541c1c0e120110030401000070006000b820b40b4030954002c07210320b548070100864422981d51910211214400820000302800c441c0c420444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 487678678 1250 487677428 487677439
    0xd090b0f180604030c1e0503010516030c140a05040f0b1810020115091d010507091a0f0c0105071103130b0f1216110316030c05120c1014070914 63
    0x166241c0317816480d09816080110001c085007000c0f507442d540c00d400b440c002d010581c0284010329001c041001402c0100004000380340c0c850200d010000d100e11140022001814145910369514450051040e0020b02845c40d003294031140c0450300030b481c001604d0030001404071910f1010483c400b40401e9900d000c4101c0159900d44d051012813600034020080a0041d010340021200d50088032020030300a0000030200030307450041440172581d4000318100941c6c1c01e584920340e103d05155121031451041d007480c40b98455010404000400c8103420403030192050740e0b070340e900701404400001e86034851101c0f01c0a055024100800102c101400901039442300455054142910885841c140000c21112a4014180304252030380c9190040350401c01030055200550400c40c2c0d0380701210741c0c0c642c5907202409201042c0301d801d007081020848030480c038100c10326154a540e1741c0e20030942d66a42551202d4203507810110b8a15210b410b10ba16948184a10f644985039149001c0c04041c05440109185070000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 487679928 1250 487678678 487678687
    0xc0a0f090803043201080604021b01050c0309161d060a0b0a0e030d1704110d080705070503071710110c010603030203030a0b04020a080c0f12090d090b0f1806 69
    0x4401c00c0c0040c0004008a0b01c0c41c0700c1000a2000f13a0134545610065601d403401034800000351a6030210700982d21080c15200182d545042c121b503064040020814444c0c19824a0f040000d4859620059030146150b802241e0b50385040d8208659100018000c032a503504c9420200013191800398462504101c02905c091700144c1c9540e2000d116501803c2041d0112304042c0381f05a0601342040690110601d40c41c180c40c035a0141d642c1001d80304000b074000b408107205039801040660341d1a204000700b030303400803140b550349001d8a0b24540361130740752161601c44d00402c40c001802050045242e5052100304014210f544400041c0c04014004000450b070056014002c1c41c040074802d101d0034010390300a400542d22840c3c0030105009603800720b103000d030155005206001034190040c4500d038000004444860300c3c0c40200102c06a00d00a103c0040c2a01609030113000c00102c1c08110003401e98440e41c0c0e8948115216044000944282120110700ba2020000d440707660030b183d054844110707001008540361 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 487681178 1250 487679928 487679939
    0x501140a1214180d0f0905060903030d1d010f09030c060c0e0301061403070f03030801120f050a0609050f07050312130e0708090d0c020a06030b0d14030c0d080c0a0f09 73
    0x2203076012201620070f40b03032641d840c0d00c0402e0100080a54150f00d441c100c10a0811180000c140c200d80d0b01c907081c05240080351102c031569050007580c01c0e81c001c2c0d007800c00c0350741407102c10848070b5802c0c085845055480c0c001d0001e000300d011301034001416015210105104400d64130034000f03006140c0c1000810400c41254451658207010300c0d0001d007042c02c0d80310004050b0804060504d10f9035882030340c503d500c01c2801c2000039044045c89046582500f1040d0615400f420078004240c540b8100070204e020b207200640820a00c0e46c05500300c076010f90112107222a8840c0165030b200070501900d41d2642c00802d0429940541000801e4200302c500c0085403410350312510881241002d6a058002c00c0200041088008081100824800c501c1c5800c0e0603094854012858042281c05503a040540340c42000b0266280c4e205c403140c179503500c004071120707951820741410b8603500200414002c40c0201c4000710001031086011034041e0b035800c0c4100c1e00c4c09113000e0082d10390322150501e40090080c0034100089 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 487682428 1250 487681178 487681211
    0x5091c02090a020919121103101e0506061611270402011103040e06040903112d0705011b1a010e0714030c09040c2a020a0501140a12 58
    0x8800144003d44c940f001c11041040e0300700b00b80482e81d519060000c040007140c50701c3c040040c0881e000380501c00c04014110100b070806190143c40070141d401d084419103d1448803044140d440c40c000d804000d680c0344c2e0002c00801c0d00c42c0b0501d190002283c00308c03040c0400e020700d01d480102d0740d004124618072a2101c51a0111085214646c0680a441010002075580007401d40f000160b181f40a5481c0c54104010294501d07009003000d4041d40d520304030582058000e005807001d2500510448213409028015a04012011083d0500840310040c82d454030550018150f025984140c41e203507000a0a1102c840c1d045010390402d5526800c03d546d482d41c0180021902c034040c0281c0c030b0b600c0c20a40340810b4043c1c072040c040c034403108000d130040042000c0c460b607400030798000000880300400c140f121904d041315903009150100c01c184107854216001c008030f00d4a0784848603c00c0e41c0e0320002c41d03501d000541d41c00e403e1440c070b802d10700c10410484107861302c0f5065903c50514007840006050704010b82104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 487683678 1250 487682428 487682431
    0x506030106090f140601140d0504030905061b0c0a0f0b130e18010e03130e07030906180c0504060506040509250c0203150411040e0f0f07030308130305091c0209 70
    0x106040e80d02e441c58000f020343c131260107502990a090920301ca541e02564100705108105600c4565a6075a0104041600c201c40400c0144401458162610b142c5624130180301900d60300e4201d9441201c00000041c2000c04280c01110a5210410320380f42c82c00543e0200c80e8442d429116058130300c0140440c180b179031a010030340a6154020b9581c40c00500c44411400c40c0e002200038501d0764018414046150700201c481000c2da5003413a01d406854039101401c1d805405088001800c0e01c0c240030400440391401005c4901543c082c0f0300780322500755a0f07018001112010b0050a4128004000501071341c10810080740d0011210404e030403200503249401011920015062800200b201c1080e00540c07a080020a81c81091104850701900341940c1d002041140e0404c520700a6454081c003403080e581c10f002c06c102d800ea121301030f111215051880a600c4503d6404200d0215401101082008070500400c0e8007442d03058550f54900940a010131420320a05401d4000d1092030405c0c100060310b4100201e03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 487684928 1250 487683678 487683701
    0xb0c0c06070c0806010b090a03080a0215040323040e0a02160615060306080114150102070815010f1a03040f020a0503011802040c0e01050f0c120c06220213050603010609 74
    0x7a04843c1c18400300c5810b0480680c0541441d04050080702c100da55944a001c00700c0b540b00c90410350360310901406a0900000b14500081e00c0100000c100c14560000039441402c000c050144404407000c05840510340114042c1d81403010100d0002481d03814254003c10401c0d0115003501062a003c0c3c0d21201074034030b41040294200340c2c0110800c42c0a415004040180804070002c0c020555900c14102c400103008152039003c00c200d1013100ca06034000e100f400094141507041d00c0060000c8030035420190130a119900301c404803c00c0010f40c0b45241700424519011061700c1d2032035601c2d60b032500700028420500c140c4c1d011a00c8400000c04c0c0d603003407060b5a010000f0345800c0d2000241401080100c9510a02c14014442c3c025000d004982c0d01900b180d09c105420720b81d5548a86c4c0b000c0745545080c010001c030f90241080007031a0603007803100094552148061132649001c2207819105a541c00140d43d030000d41128061081248001c1a0b4105541c418400b40c000140c0f1a84e90b04110151800f15040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 487686178 1250 487684928 487684943
    0xe0d09150509060c0309030d031112100f080a15151e21110f0a050d05070b0720041e0c0e100302090f04051b0304140d1205060d08040b0c0c0607 63
    0x21520f1810103201110362552310381810400910113240680e40f910542403030707480c80c405040004007801c404d0380c00607007e080c400d440d2465031a21880110b55460f00302c107003070b6942ea040c03640c0c0d0143c0c1e00c024080e9030215003000440340c1d03078142b078034000701514442201d080800c0b20f51804040340307081c580010304850036510142d0040600250038040000c800380c9070000d00900b02e401c0c145206803102d403411002c40d0340c02e0319001c1d1a1180c50030840e0400d1040c0e0040b81d41d61314001005020b000c036010f504501d00100c003a01c850401d000104120465501c0401c0c10501380d0080003d180c02d02040d070104201414905190a101401400207600d0841100c034175804030b40e0108590001c0d041600e06942c07100f0042d00c0c2080641001c002c81c1c40c1c041201104010640d1000000508000c58100104641072582003101c0b4001050040a03207000200300500c00701901e840e002034400e02e0724004d003100154102d54a185460704100341146940e028425120761445100300d440d5184d141c803c0241021400b5110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 487687428 1250 487686178 487686187
    0xb0c01140708151207050609060714030901110a050c010e04140138091c0c030803012c1807030b01091407020d0e04150b0309100e0d09150509060c03 65
    0x100d00d010000c0403d00d10300410240c45a00004000050032100b651021a03420f610307400c0b0b0400040046c42009030082009003007060700311030640c1c00005403100e0a0240c868980b030010207a08146c0e198101c201c007070b1075a8030403400740d2280d50040c0d40c50000d1000107440071a4040040c0c082c405010000e07800b00b151002c14092024208031191112101c2e42490007000020003588143c0c044c02e4003402d54518400c0c000d201ca903140c5a1300000b120303075906902283c030703005441d628100300c40300390802d214004070500d09800d940547c80308a03d249215502d018294206c41d03c0d40f6004a2111881d480150700d5480703003010201c041160380a900780213240c02130300804c0309400400141240000a0030402c01d561011400c5442d454100d003009202160941c0c00040e002000a40d550480340d80f98072a020030b100000074819815400300324070503844c4146205000489640c1c0d459942e60403a141240c000520440301802503280b01010501c0d000b10500c0c21504044403003000a203640c1c0000c1c2001c070540e20009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 487688678 1250 487687428 487687441
    0xc04120c05100302070b0c09180106030606030f05041203111b010506040b0306040506010306020a1e0f03110315090a0e2a06190f0207210303050a02130b0c01140708 72
    0x5548820b50650b070715095042c094541d0301d0038415003020b800c0c0c0907034107404620429140c41d0521100011280c07040d07070b0842075a49103000f40050045008140009040008556024038103000745401280d1000c08000b9500d4104400c030014102d0901130003000c0c20401a40441d522008500150241f0b40e000014060400b03030304000483d68034202a50090704044c007044040740010501c18116900700f8409a034860003043c04440100703001d03800c1c03071b0b40035000803060541941c400c285040c0540b05441c1080402828514007105020844460104054841c0e40100078208001e9071500051a00c2c00446c1140283da4010f00704180006a048000a0261601c180061400242035044400d4508901c0c03c00c90145008a00d4070f00841402403050b1819a0820f15108018600042c07101c2c20780c020820000340d492888501c1c2908041d80002e0070700c00400c1c0811300d40c0c03080364010082c021105442d90f103480507401298008140d10506c0b550385110307820711030109001581c45007280c1d40d40c0c00389a140c00d5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 487689928 1250 487688678 487688689
    0x1b0d0c0e09090c010e04090c12030306150c0b070806090601030b0409020a1217030106020a0f050c0316081e0705330304020108090f060402041109030a0809030708160e0c04120c05 78
    0x2a01001d10540c00c0010385004903c0002e094070596042e1001ca0030809d1031030405a010384440d030311450f56010a141101501c40d070180d0b0302805940300340101c40450321445002c0b104102c099030b00f140d2003081070004c244a50700981c060302000a0180001c80c00781c40c5500084d980030200c0d030084010201400f0b84004019600d0041180415880c45090540d414028025a9211060340c02025020300d00c2003081480010800301c0c508050050494048040d04800300c4d100020300e100e402854800c1c0603452402099a40003110f0302280380c1c0c000c01c0d042c0e01c0c02080102030141158200c1d1300a042006008152260043c2c050328103a00c0d001c5541c0d00d0a10344001032500038001d0402d8050b400190301c204420001003140d5401940486012900c4425034154012620a1100c0380d645031040b41e03841001c00110001500d00d07400d01b1020b850711140c6d205035081c0c8942d9007042090f4001c0703d07054280b00510055103c0d60b00311600207602410192111450000d21440c0c1c401036a480340c85000403c0286800d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 487691178 1250 487689928 487689947
    0x1e070602010c0807022a0402030a090b090c03061b0c070306060e06040612172106032103041202030904020703170a360501090f0b1b0d0c0e09090c01 65
    0x182c640000c141ca402c0304d00a49503011807048854403030340c400c0100350040d204480c0d03039054038008008540d00d09080051800400c08074408461103070451000440c08600890751803240b58015002c1d0407035030794208903a40c41190a400b0940b1502c814000c115140e04104012005184100c40020b0381e207040151810fa490002000d0130300c100c3c01c010081c80b1501c1c03074001240d100f5034000a811303001c250039280500140103403103000f81202400105111a071100d40079860080e401641901c100d006000340d0311112510184101c00c5d18007040020030b00040c0301240e000e889503003901c103881c100200740c400141a0b82c8501340680003e260402403810407681a0350580d00085000c0c01000540400211102c21038800840300055625041d100f004484900f00000300d0260b100008001d0382d102440c0c00041c00035500d800760754020304074001824044042600c2c9000000803005103060800c004410b5002d460085440020403503400d44a2000352101d449090042c0006d03406000d8400c11500018400c806 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 487692428 1250 487691178 487691201
    0x20d030f1806020702150d0b090105090f04020603100503030a031d0601031106090301020d06080d110c031009021906030c030f02130b0721020309010f0203031e06031e07060201 77
    0x1600580e8820010310501a00403030340c0c410b40c09a201e404600000d03984076015840c68100d0400001d00742c2c3c42c40c00d0380c2d2090f101000111813125013641c0ba0810710081c064111650300105011102040151404601440d80406411404280703e9140c00109007035401190f0340f5008030340c5400440700b0302e1503032422a01c400a242c20082003070f9031643e100c100011000380c590501800b0300090b44419514290110740d03803c403801605018095071210a580da0340380d410f04510016035080c040324a881404104200800e2000b801072191003a02840c140051422600890703000c0700000701d20502e04e0522648100802041d10002648000400e02800359050001032608240c4100111140d203482c204404060769524002c50f61a01c049151184151b40350318055000c05540e483e0031028580d0000c02000c0d992070a0f0394106403a991a84240d13034a0005607076640354144242d071929808503a0307003011f83d80310000030112186001049a0102e515107130b1103200300c0640088100303110168090054891106 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 487693678 1250 487692428 487692431
    0x7120906022419090f05070b030c0919050d0f05011503240204030f080d0f0b06031302032415061c05042f15040807060e061603020d030f 60
    0x48000e8035450503142d800400003214500d10003040e03a481d83d03881d000c01100c0411008026110203030401610351303141e1860843e828840c050001c2041c0a2040949020394041507285081c0409941000300740801c1e4142440e0000710080c0c0050310f581e9000904d44494041c00a184500389a800c2403030940e1080555404c0d0f00710529010000100084a0701c00c00010005080c02c5852600074910003a112741d50000d4140c00c401882d4009110014000b0080510340d03680411400c0035410384101501c21080d80658000390a1002900c0451203108042c2c58510080030f039500501000070710380801502070b00b040c66114540c0200701c4e04410008516680301c07400c440b160705001050742010707141d100c1c01c4111101c2d503071240003003820403100d55541c40c5403075031001c440400c00c08840d42036580a0f4403110740070b02c01c3c800890394145c480e0051003260242e9070280060f0080034102070302512154030245941e0342000d4200813010b003059217400c0006100b48a80c0c05805a1911200c008080d02e10f0811081c1c94503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 487694928 1250 487693678 487693693
    0x5030c0919031719030b06040513090b090309041a030a0311030d1a090a0606140a05040e0c1903061211010201020c011407020d02070f03020f0a0b0712090602 69
    0x20108419225010303012240c103401000d0700d045040100300030381d200803c1030452500700500c03406104050300b01464010041c410701036400c84200d040d00d5440b580b2513044841000188038074100402805108a0380f904007090709940b036039400e0680c1d007084580d0090390b000890b14203404d181c140140703a001c609040481c0605215903000a0300c400a002d4003c1c1401010490480c000c60140f0a40700c902828072410400d60a404400b0306210342d00ca801c5c10311034051040061405d503401d120b20402c0d10b00d0340d91502418007444066042d10351100815805220301488000390380c0101d403030443d100e2100c0400c000d482c2d040c02440f040d03108080c0000d04041c10b0814505110440c0070000d184101500007002c084205c49480044c0d00910400c00d48104030350030090b2540042d01a4865280205110741c00c8800003110b02070202c3e07c2c4c040500810031607501300700040002d031800f044400500b0078010070600404c1d989280100c426400180308981245001014660240d00202c004005110500150005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 487696178 1250 487694928 487694941
    0x304080d14030f040c080102070f0606320109030507180c051908040201030b030d0e09070c110f0102250e13050604060e0f010c05040e090102040510031109060a0c02100503 75
    0x40d0000911440e500d03c507083c001401e002c4071000c020028619100215900c215900f4942444200071606035111400c2920014000c00c0c00e0b0003030381c0fa040c6c190101a228030346c2c40d0054003d00180b00100741c10008100c40c080f001c03c2c02400003000034404040015a0f145090042c1d000f03031500d8403118400d1200a20030900e00818000c2c424030043c13118a408055980c0320720044c4c00405980c44000d81500c1448101ca800c00c0c0c01c0380c216200200c0440d041c3c40e0300d42c0e6080003111000c44102000f0b10b5a605070356011010f0030a049000304003a8140190388400c0403034811200301c11440c2c105092110640d95042103810050054036800100ca859016030b21180c41d210540d444402400c01804a0703558002c00b400d4110a008a240d80c0300b9100c0203010a00041e58010300d141c210740191000c40400c400070860484052084a00302d40001c0c04a802448144409500a06000c810004200307030420400c003103551b41a0040c80040840e4550142c445114010b02005089240007642480707420024890f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 487697428 1250 487696178 487696217
    0x41d070c030806032103190507050409091a0702100b0105071718120c011103040e180304030506131104150909050703060501080609060907150c0302011d0304080d 71
    0x16425014141942c0e02c0d00d03504042803410f02d83c401c0d580103000742c0045c02c40c0f080220301c004501480d00c407401c03014000c0d2070320116030880d0b8060718254042082004104452880c0750090300800b401034031680c141031800c12041c020702100b00c42c42c000681200d00e0101e009001c41c4920b10742080286400c504000c01c0303548414100c8143c00204580b118080344207050810725050b4203000540203850640307941502071440c2c1c0c4c0c810032800c41a0114130000ca521001d1030001050354210740149800200340d40310440d0300c0040d4510301c591480d039030000f00030100c00b15008101c1c85018000080e0078111100440c1000d0b0302006101035100d00c124142084c07504113042e0b4010034400e84902e035400040146140c94418070303114066000519850800000240c601400b003401d500c2280d410342030700c2c4540c1e1039080150322200c0d240600d1000300da82c248445c0b0030601c07443e000343d00c5d24441e00002513412004c0b0700c880592128003980110a034030024080c0306220046c07000c00c80c148040c0c1800c1441c101490505403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 487698678 1250 487697428 487697447
    0x90f0e01170a050111030601230a050306030a1e030809061509130f050a170708070b1905100519081f09020a0902071109070503040f060b10020102041d07 67
    0x111128100e403241d60a011062105504070b41d03002008000b265212070000d80d1a41003182d403140455071010000a420a201c80801031000034882c48a00d04481d4100c2a43c02d504050501d40e014400d04120b03038000303030f40c01845800c482508801c6c0107064803140340041007802d00030882081500041c0c18001d046000080d4005a448219042800340d50380f80640826041d1400005d0400c41032009102c0c28060007040000308103004d0460f001c0304c55a5011700c01d225104039103004240c0351041001e440880e4251020320703006120501c180c1c10543d01034400310240d840554120340e800000010030806490020340d030719220f00401160304000742c58400000d03107030210b8000011401e02c0c00c5407041c001280a0b4040f5100f264001d24800515072146e070107100940044a044030039040d4040380000901d40307143c0940c462811961498039554540d6107481044480740c804584054407850702c1103245c3d60701d400c0140901260341c00180c80c0d915084450426005400b4003817203da480e4404e200000360b000240d83c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 487699928 1250 487698678 487698689
    0x90b180402060f1201080c0d17030a090b07030e010b0f010912020303210403020d0302120109020c01150b070606050a0b0712021f0b0f030c0a150c12030c090f0e01 71
    0x22002569507001240315441000929140e507038001030100040214400c1c4141030701c4a0504488220a02406100082411900180c07000903031501400c040b200313000007554001000c80001c81c0815040d512031032070140a0345c018000c00d403030300400c6007560804d209007045083d048030030594500046002230941c1e00d00e230150205040384c4442540540d01e04008840081c0c40d15102e40348204880c040302401420f003130320110014081c912034030344094030900036070304401c0712a01c09503410f03482c000b00d0384004c1d8440550404c081d5290001d46051500710310080300288205010b550381c409003840e0a0b02101d81c980c21551052049280030b0180d400500140c0d400c0c140e01240002d40c254080500368a0400c0340014015200084c180c440591a1160044000b60720161450480100203000b01511805107480654001100c1c61381005814440c0c12042011202401d10203e004819140c0c44100780e030103420180401d4481c07285114081d1300ca0748460041803468022480c1c3c908040d0b40406007070062144 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 487701178 1250 487699928 487699969
    0x1b03020f010e0312070507060f0f20010b030708030a03060906030b01030b060a03050a0804091b020d05160f0803010512031804090c12060507030b040207020102030904020f1309090606090b 82
    0x1490510b440070450030480c030300365100d0136403101002d2609582d00c0401c1e00444000405195403611180c0c001c1150714600543d40d1101004803440e04405c0c005da0340304d0b443e214125921505032984a880a0182d80701a0260801440d81d507944043c0240603100c2075071001a01d98588503080021801c036510240c10340b40c0c0030303041c2403d035181c00000548400c0e080d000030b030081c02a0450f41c4200418030f4024801c1780c0c84824180205821311200741c1d10440007084d2403000d608501e100903055131003140202800c0d17000300701e01d6000001d261940302c00b0300c038035410444901030004010b20007440d005c0e1060391402c50306801507103002c031880c1740d07080501010000c5a0140d80c44e582004104040783d042d41000d407000070184458200309041200c0a00390959401300842d10f0200b0007a034a0400b030086585840d01a00107600c0d20f803141d401c0c00000d40c060b00714071440303040c03d00c1041c4062160b003040a0007042c40c1c074400b145516180c00c0c41c608440b565400142d24038a40903001d040c07506d41422441050400807138 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 487702428 1250 487701178 487701197
    0x6092c0402010c140f062202010c170c01060f0e0403050a112407181224020a0207030605092a0145080601171c0801031b03020f01 57
    0x181c0c0e0320440da01d40245400354080d030100c204000021003007485030f45d400450381c841e2101c400500344a13080c42000c1c1c4464800403050405940207110341419580b20302c3d0107000c404d045020419194010641c080b11594481c142000b820342402c0242c8041c04501c0c840d900c0b030b130030a51b401810070b11a83c1c04650910841841d4044410001e1041c000340c607104010702da000c01d4103400104202d00013140ea0704081011080a03808541184031000142c40262600303c0e22540700f80c9a1503102c1c80d58220024030303410401030f44650344601c0e00290280c451190014181d450a40c50200c055680040c1041920360020212140c8107220908120504240c0d200b058038846c020710048580030702002c0d05003808100d0402042018000c44000d0110780c0c0c020309145203031920014120041c503c188158150340e4401c0f0010f004c6608038181840e1018802e104848070f02038180110000e112299451602140c446001001403040d5803e024000f151000701c0d01583d01c1c20365001031100544000c4050404c5401030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 487703678 1250 487702428 487702433
    0x1090b092d031c0507030f050412120605041503170f030103021c060606051905030c030a05090f0a050d0306080d0f0f021203010315060b2805040509090706092c04 71
    0x211083c0d180f0040341c00481e122150440000750070b003a03849170002454003c4d00604036103688102405981d112000c4501c0304000001110400c80b049051a43c0903694100010613540340d11a060114011f40030b006e0300b0602d14103260400b003004a01c00c0c0e07890b1804002c0b6101c01d40f48001260b05580c0d040319220402c21003000030200c0d2003000000100010f14102340429000c1e00440504110304080036426401c0d020520111440d0209603180c55201d003040c4081116070195401c001e07400110f040440b425440075046280c584141d40505582540102001c8080749502d8003c6c8001f500d20036004101184007640024a200c0302c0d040d04004009a43c10b40611840c800e000c0d18915020424425843e540c40e030030071124140c2110503111035145040000207040c0b0740d00007a5519032290310100788032a58111481582c02c280e2642540801c00204404100c590311000c0c1117009800d210010303d00207003400302c05040245550496800c03603240d4070045500c00c080ba40034120300d00c1c005480202d940c40e6403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 487704928 1250 487703678 487703683
    0x1051c050a020d06110c0601140a0f0b07020f0619030f06030f120909020417070e193c0c020f071a07021002060f01091109011d1201090b092d 62
    0x45e0102d8445070300040c8244c030340400080250503101064050f0030503152010030012100f03164406ca032551050300804100340100c1034013410485001901c102140c400712400208158080a6048500b1400382802c2c4150f0340d0510900c100100050704c10481241107440314100c00003d4500180105143c0e00190842d51003a41c0881c001d118a031030a5440301d460700101e510008007414800e419100d40d22000646c032240d150020b010b0100710781c041060300a070b0040380c8c4c090006180054010b078850b5015046803a070720b2084011018040c3c4043d0080102d050300c00045e500c2a141200c215807003481d403151001c0c4081041000c43d0003041c000c45452450101400c120b01840c40082c0d4088075070f9406401598001c18618482c0c0030650f9030b25070340e07030b01c4002c540304513540c00c200680071107030074040b4035841d500403000a003032403502501550790b82c8260f100007400070b514030b010764042d41d445030100b038100040088010340103a4010040c18405200881c2c1141c07000c000c00254492199a0940ca603508205 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 487706178 1250 487704928 487704941
    0x30c0809040e06130203062a0a05070c060c02040b15030c1614030c0613050d030e2a011103120a1e02130609060c02130518010203010e01051c050a020d06 67
    0x10b6000c1d68158a040909264043c1c0030440980c06801080001100b001022a03864014611702012940c01c81002010984c00e8205081c4a01031103001c11508000c1540c402c41403000308a680e588060090043c410b00c0240c83c9922496401511028a4100a07886860917654040100c40a141e1140d92444908000c5040d4030400341100b0409054003016000100017054501c80c18000c4405a8030b600c0c10300b91403003002000c050030a8000e5540130700e90520a40021030b06254080c2290b00507543c1d44442441c5000c404e900102a00311420300c1206540c001d2800202505c24002550820041c1c0c83c0360310850400806090701140e032022400158403c0c02c00741142d00840c62011501c0d03880303928210110741d40384c1c01000040344010f400080e9940c81011030203901c65019042c1c400d0361414110310005000e028141d048007918918090f0b00140c1c00744003850003051205403443d001e501d01420301240540911508e103007001d81000201c045000040d44801c0558155024ac96089840c10503a004041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 487707428 1250 487706178 487706201
    0x31302010813080c1501060f0e01030207061b090e010b040f1802160c050406050f0607060f0605100306030c0b03100e0705091206191b0806030a1a1012030c080904 71
    0x2008103c00403080000204020b02c454407841c100b00603600c41c1e2081d84ca56111688c9000010701d041034402a5501ca90040d10903030b0712445001c40c106685121040d991012280c1e08130000303017000340400c4501d00c0000078500400c00a800c0516090405040028160041c0a40c06140105540c45088001d4660454010f40b40c04a02900003130043d01c2c1c600040e203000d1081620441c24440302107801d103001c1419108a1400a119600d020340a903943c0303010300382c507001070311071a03aa84900040c04c0c0c42c3d03904001380d40706d020389d07000444606604d48030ba0f60040a411503842c0c0f200902c104041680700e1407000090700c0c0d0b4540c0c89803441e80c0389641201d1078410b07402c4c01c50704141c107100c3e41492400001803503409264072071000041980d032580004211040c40e034942c113403008504290f021650007601400d40204001c0c060f07580e0141ca544650705100c03c50b103038040049182038100300094600c031441d0340150000ca80c61140601840c1c4008240700000740025004d81800500188940c2d55507210b0a4a070b00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 487708678 1250 487707428 487707443
    0x51006020d032003010b1801090e0a0c020a0b0108031309020310120c120605010e0f160e1c0321020406020303040206030a0905010f0506011b120c1a1f0605031302010813 74
    0x107854401c5170b4201c1e048111f01c01c11070988550034000c0ca40c00741e03111409940902c070b004926541c891741000080d00c41d4032080c2080d4015110108007084d40c140001c0e000e00120002940d036040550803404c115030b2150b2000c0001c0d441070090241c21804103160400316011444030721440e04060819201c1c00c401c5502540c0c03162110b240e90001c2003615000181229210003c4032195076451011a0038544100c03120341d40600d070b070441b903040d8a0180200e00d6010701e0280010000b000c03030003810141c07101a000300f6404030720a61000301c00c000d210441c62104144000003907007002c1c84e02c4000f0b0366902010340024465400400007405401096010404458004009124881000d1400310080600b40c030004c0c0019210180d00c9040007901c0c2c03030010825445404054079400b0707400c0844402030a074104480304d100400004403204240501c0c030b40998a81602c402c83c15003222130050710402c80307a2080c0240700045c420007188030484243c0108068081c00c04240b40c0d0313610042d6804000b00804000c2025 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 487709928 1250 487708678 487708681
    0x60103150507050a0c17040b0d06090e0d091802090303070c0501030f0b1c03110d09140901180b1c030503010915080a060e010b1203030604051006020d032003 69
    0x8191641400d00c5045040100309a840700d08044802d4414a030310070002c10070650707088000501c040b403103c011842e841200d40c02c0030340300c6840040300d51008807424030046c0c4504d07040c80401c2d00703803040840c51200100141040081700c0c0d0040c0107107a0601c0f0304500700e2845030520a1440c40e40e0111755407480e005060743d554202914000c58504e040f4020940000e15210351614003505600c2003c1c0c00744002401c00c071402d40b00300c03809040074400590440810001814410031454100035071000651715407103102c0d81c9400c1030306a801031641522010b01c03c1c090000100101500d0ba07001c0d050300001e02001081c2c040710000444c0b9035084070300b0100154454107462000b071660140145050700c00c640c4060008054100310007000320264003c0081c1500303c481d1010006105a000404010680f0004992003007080c00040c0c00311184030518583d901b0001c01c001b500e251610403aa80709050f1103132000883e0605100a56400596031194140b65a483d070305c422110754204070450404c51007508076a02e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 487711178 1250 487709928 487709933
    0x1e0203040c1a0c070f08030702040e03070804150e0102030f07060c0c0c090204090b0f030705010f110303070f1205090c010c1b0603060315050c070807021207060e0f190501140408060103 81
    0x440d40003183c500c460303001e40f11000c40d40c014041c0d4a0780c1200c2c01000118102000e0741c0802c401006102da03901c040340300800080d00043c14410150004045014031241e292039540d0029240b48610007085046405c200047c1e00d0380c0d0017010a580c6015005500021000c0000000740c0d8151031002024152047c90500000c03010881c0e0024016505200001d101160011050110040010145c41d0341a00049400e2200b54881c0b50455507068082c0b5011400c190325410090845d482510008001941400148102e80d08044204400c0314021420441c1d03145c400b004503203600c940410641005170020100b024010500c01e13888515900d5801d1000f00e07030ba41c40014005050030303c4100da902508015450450030184259842070607500c0e5080d1920120303035280002c44e404500d04070f91100300603600c0e194015041003072002a104e01d848040368a80381508100003041310714402ea10441c00c20042000c000030410300780007102c000b0300b40601e5520500c41400c113a401180c000070072034400c80d03000006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 487712428 1250 487711178 487711229
    0x201092102040905011d0f0601140105130e0618091b010513090501030c0609030c1a0c0a0b01090f23040204061d0403180e1b09060f03010312031e0203040c 68
    0x15400c6c01c0e4881750402031002c12a143c5c0701c0032002c00c030000780d0700441d0040100128018422101150524001d850800e012071500d643c2202c40d045052911001020001581049611780c3c5070300111172849213070351901512482e65843c01324400311540b0b80b0030209400030b074060000d54100c1207605226000807600c503180c0300c00405091105030b40d00c4004010005200b40155504402d907a000000311482508100702c03d20703a0040d6484480441d40704108441c0441c1c402d10a0780c06091061034003660725454030074100141c0d200c90069400d01c6140004030400002e01100c24078015091803000441942d842c00028010b00c0540d204048600f5003505503000110002442440b46129403120351100003240441c910000c2e19001c0d80000015400100e48114100c10b0b041280072000340d031951030000102c3c0801c00300e8010345441030348020040b0042c000c004460302c0d00c1001c1030301440d007085558690706010005245045041b036440d940040070900344414040100054152102c040060b00844c002800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 487713678 1250 487712428 487712441
    0x903270a09090c0e0f040f051011030702100608100f110c0a030215010f140d050106180b090f040f0f0606170c0d051e03040801110a0f0c020109210204090501 69
    0x4810b6005040d000c6100d105600f0400e005441d0717051a10756035039a9540701104114400703001e580038030900450440c404158040c41c55014800c2840315100c1c02c2003178002c1e1911b04e01d4820007224a040c80005c1c00103140c0069207140442e0042c40100c3c82c502001aa51b000b059080c0e1782ca0618030340002c0802803e40006a0001075600c039500712440c030b080c0c2e074844040301402801412002a60084208280740c0851404c10300b0400040c2403400210641d551a82140c919522068540c41014020b410901c82403260907a10a81664200c0d5286085600380754000380007030000b0401c0d800c00b030100051003200c54144800c1035112500b08512034407941c034001e040d02031603641d140f944070342500840c50303080c44c451092850340e001e401804d2402e1506200031000314a654a04e006100070300c00003811403030134015170401d1405110159590940030030001c1c160070107a04a1024054401c0c41880180d80c000d4210301124600c2907400c0905540d022842c5c00e4420544000e0743c80b03810019240f040c04810340c03005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 487714928 1250 487713678 487713683
    0x506010302180402130e03090901061d180c0f04030b0a060302130c120c0e0a1502060708070f0e0a18050a0507030902030a02090702070b070c09140903270a0909 70
    0x104004600440c5031040008120b800a40010351400201250551078210350104040901501e082140c050082040c503840bd070b00010000f1042160703100030014209581c45c200e5403d540380d011245460321012001d640113070400c810110300207100030160f1030003406e40740519800040b80444d8207000c23611901420080c002030f48940843d001d03100004005d84070740c54030b0703910701d480e00c24a100c02140b030300d8010440081c3c1d03c000e020003c1c1c00000707103a45910381340020b800701e541504400e00c0c030400c0084c07811200400e20400e008581d0700f8030818a070030003040100030b8010b250988840031800041400522103611194101e5641c03a0f464030303c10544c0c1c00051280d81048810050356403280011400c0d03030700040d806034044c1c004012440142c1850301e01309a0050050044404540c4d40325000307045548100c41c0ad5a0300b03444a2400d100c1002d45000d0340d484030161003e00016403d01c500025140e12a058014201c10301c1815101100201201401040200149800001780c4d90300da80f00c001e802804800c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 487716178 1250 487714928 487714939
    0x1504061a180a0506040f02040f2301090b0a0215010806040510291c080705060f0103020105030a0903020724110a03090e090f1b03011406011d0402070507030506010302 73
    0x10000d0a0400031035646404210329089140d944482048100800b4003800858100b1303180c84c0890030307115060008000034400f64082264141c41c044000c1ca5030444000b0701079582804107011207103681d200c0980d005540d0440800340da1a001400c0a07860010a642e0030040d0111a07000002c00c030700c02184d070780d03c214064410340f1090b8506a0b0444101c621822000c4010aa449202e907260407440805c4031103054094096102506400c0d850030032403015280c111242000062100c04029050054982200400d40061640e5042d0f40c0060010300004103040181951101002d040c944200480f80007405021109640d00c0c1e00e01b6840d00103125103495840104102e6440100b143c040082d00b880581d80682c0d83c048503d00f007154258513103002030034104252048210100c5010f17828094650320011030003150341e00340f018400381429a01c80b12008078406001d00208011641c0000c4a1602050500742449001203002d000074001c1c000d43c00b01808501c00c0000110812000182203412789008884 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 487717428 1250 487716178 487716221
    0xe0a030c1d01180c0918060302180402060301090c2304050406081f09080c030a0806091303020a0305091801090501090501050a0f060c030509180f0a0c08040f05150406 73
    0x9500c800440a128045000140704100c030f4000c00c00b903100c95110405442c000c4001075481d003051501c4843d100b40114141da5541e41081145061206004600c01d5803e9103c02c0c2e00c0c01e0f8000402c240014480c00c0c5002e070701c1d504031501d81445a1071100c4c9500c1d200380d00340c80d1640000c14440c0c0e0f541241c002c99000c0e0345000f4010490842c0041c42c41c5020030b0040d400c0421031000d0254001034a40d000e0210b03250740c8203008083c80d01d8400d201030300e43c00c2081d555401040c0361410412881240123850034620820010300540800c0e07001c1a80b2540c00d4050400703a40d9140700d03501241d80318101c01d80200c1405440000441c2041041e00214121071001900f400030380d894a0420021507598480e4a4600508440c100542401103444e42c0c2020300038104203003407190303040119625a000ca0016881c0c0c03050380c810404141d110006198111100c6801001301c95030380c81029041001c0580040c0c21510041d400d4020080200030032071101c8000441545181442d140034006401550442a550b034028074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 487718678 1250 487717428 487717469
    0x1d0d051614150702030705071809121101140402010e1e060a0e03010506010314040b090304050a0311191214010603050f07091b0503010e0604090204020f0d110403050a0b070e0a030c 79
    0x1b07840d100c54108015010203454040b468107501c09a21003440351a8880a11401242c1841d070404141d81c500d85503040880381011002c4d003101c0d042460170b100c1e18100028000582d03030242401c0298076054885007050203d501c03e1130100e14140f5459544000009080c41350294000020030010905500034401c030380f00c41c80103500b501d00301c00041500300300280025002c510020b400c00e420114490a6920700780d168004a603c0e48510b400070307161550302224260150515002020f5000007400700c2c10b02d1541841c10005003581c402c1c07805001a4044400421401c00c01e50102c00150740c4001141d460440e11001c842d02c5014920444060600d01107070000074400e021400c0301c3c8401e80740d0303641d40346a08206113258401c001034130300740c3c0141d580c0003103000507100e91008003900c51040713010a0f12046008500d0040d601c51660020002c0d030300f4441000001e6001034081340f103560019009495582c0d0720780403a460481d48c40103a42c01420318030000b013481451104601520500c07458500880f0641 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 487719928 1250 487718678 487718683
    0x21f0c06110a02120f121003150c120b27160c08030601050c19080c0c0d020303040909020315040f020f04020a0c0b070c0f151d0d051614150702 63
    0x1402040050f13002114514100e609030030007480603000800c00282411044000c0000c90f40017200c0b245983d21511005200b40708003071058401d90b0300704c01014000040028001480c024100d4014001d603911040484029650300303034500e43c10040f42899a4511260a030385138290f50302035078001c4e035a505001c00c18000c01d12885800c440242c001002e1490340c1c54000c01100c059002c00741c181c1c0b07640150309118000341c40c0d414038403a019001c1c501060321284100481804c04140c2c43c803031813003a0310071012030006031004426101121011040015284400e0000ca0709185421162102c912004c3c2c081004000102c244890322038001d403508088480c0400030310040f48141e50820b004219089244000941c00f803104a500000c82d261000c44400c0c1a6940d220380322250300d0071905542c602044202241440c4501d007000c02e260b1010900c45540d80c034a26856020710707014582081400207070040c07125038644c101d1030100d42c401c5102c4c1d421f030624922103031a41d070141346004c28401c81c6404a05100e200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 487721178 1250 487719928 487719937
    0x6180103050d12020c06070c03020d020d09090c09050a090e15070c060905071802030906090303100306020f090604080309010212091c112d1008060d021f0c0611 70
    0x1801014845500c04041e2092070b800016000303516004c00170001e24020501c002030042d10706840d20f0440307103c98900a4103040541d0b41d11700856208456011441d584410b100302160700c203680000d03a4580d075400480313010202d074110707a812011800000415002c2e070360000c99201008404d89070060710700c0200341c2015400341c0b003200006035100a2080816400e13484445c0003031089085503200703541d856a402d0410951298441c42e19404000c0203030700d52060041a511004180140d4950703d000c8440080c416040e000c050112540854250b4801d8811422182d0308040203000035116036855110507030342e90001c0c0e03400b4010b01603840b965010003051380641e5080200101018080403100440c40030300000040242d81c80c06104420380303010f4a501684c400404100684031511a968918001d00020710030142c0f4007641c1c811042c480e01e1940100d9240d00100102e9400c0300c0e2003424000999040403403100100403401007000c00c44055041569031040c0c51040c0b4046c88042480084280b45014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 487722428 1250 487721178 487721183
    0x519020706080c1c0c0507150221041703100305010f1a040c0513080601030b0f1e15030105090304210c0302040b120102040603020403060f02031005310506180103 71
    0x3500003045100c0c0511010f404034007041030041504994104d601029602c4c401400400b1030b100041d05001d0000d4101c2017029652130001c254900040048036040381066070a5120f5041500b00219040201c2c040c40c00c0d00000130200600c0d05e904000000000207850780c80704841039842d121850039010020300411200c0008502c10741d10700030b420b1061002601c030028501003041420881c0200d007001480084025003c9031006099660452619100008000d0302c64554828404100400040342901e840c010001c0504801c099454160180002c2024034071095850750910042101c8900e002002d00200d070703401c0480030404904215209048040104040c100c441070510030710144c10184c01514024001805885081082812450882e00141c20000000380c001900b00180000c0b400b4002a00d643e1040071803441c1055403a428461740c1c10710072a070050444c2460401684007071184241c410058184070f100c00c1c20803902c5a4000c05048610510410700f80384013a010070a5080003e043c0e0b035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 487723678 1250 487722428 487722437
    0x60515040c080612190602070b070c1502091c0303090b06060705060a0b0a0b07050a021003060b0304020906130e01060314120a030213180f060e060a03200a060519020706 74
    0x21182014001184800404c0400b9407041c2c1c0f1411303508040c070b40c58483c0b07454020f400040c2c50b030045241c06c1e4400100500070344100800c04540c0e40110300268108010360110400c0141e46040300c40208a070580081c2c1034640030701d061070500044c540c05030800300e082441080c801c002d50b52410304100f89070003546c4015245503c0100002ea40045950220484c02002000240c3e029910344600f003150b40000401c94181d00240c803002c04604008001802c05030550405008030350401c0d400041c3c44c0002000a44140e00f1940440c407180c56120070318032280071000042c41000e001c0981c05003e04600c1c0302c210b070500a40c6034424000d2201251102e460710201440030714201000e03030b00724040c0d04002da0500400d81605000103114804a64506481e9038030b020108003000c030700c10308100300d560503032100051000c0388082043c0d0b55185e200243c10340340c0c003454042c4904000c071501e66060f400008d03c02c0d00000c944c100890311540141c0644030701380580d14898510000008100e0f160407240c4108000300c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 487724928 1250 487723678 487723681
    0xa050108010221090a02030a0507091401120f0204140c13050306071b140303100503010e0c01141c0207060531030f180e010f0605090901090e1207060515040c08 70
    0x1590080c110b6403c005520300312617030b4450903000130f428401480c100f11f0300c59112280402c5250410f01031004400c84010b00420300c0e6141c85c54104c09000e1403c0d005201c43c1c03011001004560325944244c200c4440d00003100401e10f4502c2d002d81095111855000a0600d40480050b181c43c00103040d034401d5110346d44941c00310400b0045119948106801203800076a00a40e40c00c00080c200701540c07007110410609421145000103060031902c40c0070701d220070354000100c07000c0d1a07604100d15556040141d04801d90300d10001201402540f001800c80358417600001c3d080083c030106030815409400c0d4190082001d45c4001021044814540c1d2130780304035000e281040000c039006030140b4051608604001d03621014221103421141440d8014843c5440301c0001031220030000003500024103514207000e440e0440718000503140000c1485070006003515807022b23080e114000e1020101812802403081e84030031a0745040b00180000b02c880440500d200b5a04000b0307850701b4007a000301801030b92122a0b06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 487726178 1250 487724928 487724977
    0xb0a0504060b180109080a060617031306080714040e0405010c0504080703062309070303110d02030909090309060a0c1505070e09270c0a060f080a0b040f11030a0501080102 75
    0x5620b1014054140142c0000004c6c1c00e001c00c1c858a0f072064460800025110304041e01c3c3c49268000308000601644180071090300c40c40009201c0c03091b40e4090400280e0365881001c01c94a0004420f50207080110205d800681c1e440095003080c0114862002480f103058800b030708861502507803040110310b034081031041000c103201d548082c4d00f09842e42202d24501c0c0c81401e81c010103202c01d070b4404d032095018201c10014168402c07405070f144004c200180c5100200070f08020350b41d0041d0811644503a1244000c211844020030882e0410714010707003415207178400340f100a0211b00194405484400d40b415281032002d005125491190300b0b0758589203580c503004d01c1400841c41d0001c0034010201a400c2c1c5030b44802041e0b075440030201d02c0c01c0b0000c1c28440c030a6000c0c0144040315510101c280210710342910036090704081c00315403180c0100b1002401512140010f4050500041c00444161802803040406804600114402d811071841409039990300c40c1c40341d00302e11a40592031803120522001112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 487727428 1250 487726178 487726207
    0x715031409030324061b0a151109090c0d090507150921030c0b011214030a08040209091609060303030e0703020907030b18071107090b01020604080307021903030b0a0504060b 76
    0x4e205601401d41400c14003040e0030a40384131003a440d81c44460b40a42c401c181040190b02001d082083d1540c0280030200e40e1a042c8612801000030300780c4181101000a0440020402074803250008014280300b180c00c90305046448403640e0082c416031441d1402c4203142341d030280d100b17030040380c00c0b660303184042038844011400310700342c054802c40c10842c0036000c1c9030114a43c0382486010348001459450801442c1c034041e41b100380f41e0400710025800501040ea0740c6070300100c42961150701551090000c4d920000d03e02c0c10320b5000b41000007200c0300c948000c208041a94481000c3d0b0307220362030401c404101c04480c156908000d04c030007984581210001061103210b900003002204000d42190804181079001040883c41143e0440001d41d0551221001d00401c0110790004d14a2000c00c1000705040340c0000c1d100d040050010744100400800b244055208200708507401400b0103404414902a10303000340a41044240248030742ca0f401e0001c2414501032140a04960300d0003401450803040307504051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 487728678 1250 487727428 487727491
    0x705160509150a091802280512030d0b1203030703060608060603100522090f0317160e0f0d0b060103110c060604090503250606240c0507150314090303 66
    0x164a80407003410400140c550281111045007c04055684410541d02148401c0b405038040351244c009941401d4100901200b10344c4280300500021074100010310105404101b149104c0301144000810043c0c034680c1503000c1003d580705559118929100c540421046000c141c440d1041484514400c00481c42e000c0701c2d140b215400f600050280308500023070b41007141e904d640d00355001707500c11501c0410036901852102c1c01816480702a182c0b410a184c012402140040d404001e02c410115403040030340e641505c108041340e0041070303c11110b0003071602c540102d500f2760380709010a00741280c2c1c1114087c90303010341e01c1404a09006008540e80d120400000e0400e8102c180d4481c0810070500004121450308091101a400d644503503550203890301904607891a40607051000740d2505010000500c48001c1101e03000701d00d48100056600c0c100107007800101e81c08410f00801d640340326034110341c05810501d6170200039102c0701c40658031561120b80781c0c0b1048524030f2800200044a011a04004001c032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 487729928 1250 487728678 487728701
    0x1b06090f03070f0303020f0d05040b030703021e0304060e01050f0105030a08091503010b0a0f030b0906060702130516022b050a110105010303051c0606120b060705160509150a09 77
    0x107038940c80e40c911001440366450307001540140c02c103401c4a0071082c1f04201040c284401031811a00d01450f20b50041701a0002408003400c1640000e4420f070849898196085100140184140d990400345801030041c100755100403115400c0800085001c0c0910b4075031812600090064810401140c0d104183c5604c54840d1070b0340100503440902c01d0010550107903010706403070880c3e10b40d82d80e20035030081d143d500400703000030030141031081e48041a103e840040790000020b4070074503119000e52000a8051032280d200201841c64141005655020000c038421040c010b502910102a01c5040e00300c02081213070000c200780c0561012522540340f0440042100103078602d02064070945030114242560002c2e40700760001980401c02001e4588500361801600d80f61a2003000700520345500030b0001580541c10401065842c280b101080d205c1000f1140d0315640101602e52080400e01514980c042034040d0380d0090012100003a0f40c1e025210200c14100002003092901c0c0340750814040207400d104124 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 487731178 1250 487729928 487729933
    0x209031603081806130f051503040302100f0b0904200301060e060d0507080a0b01050120340906080f150c030a0612050604030806011b120215040507081b06090f03 71
    0x501e800155401122806410720034080e640452034401008403242040e41d424180c0ba00c100f0901000079000120b01b10084032013203011555010608016008081700d60b8fc07a900040c401d4104000c10940c110414030300e1003988400014001038106041c203c0d040360284e10f40d40804480030070744500e030805103489801e104e1000c60b2030a945906007507040802412080741d40f95400d000600c4150380008066486105155220010403919103d1980d2003090000c131007a0449c02d00581040c0302c02090500000304506030016950658443d0100300400851242c26254001c0314008100250007081d041c0400881084e2040c0c0fa44a2401c0116143e00c007174904c0c1589076407a1400504002c6e028640354680e0702590182c00f8500d400d0601802d0400000c0205040100116800b07480056100c0490219908050303d800c20001c1c08400b64500340b2048110044c10b00300b881000100f110018a0400345e80b054001c0e5012240c401012841c501002c0b80201d522103400e102c034903510b041c641d01c42a80d40e10000e04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 487732428 1250 487731178 487731187
    0x150a0c05040b0f131a180d0201020d0e0a090e0303010f08030304050d1b0b070e13050c070303020705070905091b0126060d1e0b0c0703050f0f040302130209031603081806 74
    0x244001c46405070008038490910118103107000440c42051b0201e0544180d4503101d0b81c01c42d0f80d00007500d4551703685c1032209019201c43e810600e51501c0e29018040c00c209032081100d443c203220696602c0d042445851800c0140d5140401c84510210549004036481300041103071802c200c43c1a03d1628001030a00d0880401e6030300c00c8041014003180a0045519840315001480c2010074002d0144a00d89050406403c0401340070b0501100c008485040d034241c0b1f00180c9404841c544242018125804140a1b604282c05d1000044001c640c030340c0d8140e41c0007000200c0200240c010743e00c90b174588042e0480f049076501c09880e080c01d80b42c0700a5114000410049003002c1e21346d10000050406280c1c3c5450946443c0b010040080014078245c000301100300e503508114160b50300412521070104107006215001c80d0000140c2581020f940103141d00400d220103601040d5010030083d04070710340d840e11900c684007400481481005816050704e820190340c525212640030801c0c00c2000315440550421010031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 487733678 1250 487732428 487732439
    0xc020304050913291005090c0c010b0a0e160e0d0204020d090f080c0d050c3703170c0703090b03070905190f06020f0c01080c0903150a0c05040b0f13 65
    0x1241d1404c00300c000007407101908903404248200f18801801c0c00c00e0a40003007418021035468a2881ea0b004000c004015956146020060301415008038910340101004002181c0003002da0011882545410100414812890002c0700c00500340e041e210b0300401440805400341c1019001405810504400070440b2405e66170b171814a00c2c4580000d55528001140782190743d07609000d4004034041c03a1524600303081d500070010380c4075003880750341c0c80c08a0132170310b00341900001d00e0224008071940000d07103004500d801e0074080e0201e5014040e003000b8010100025046010074000e444c0c0301605581c880f942e032414050414090b50000d0305031000d00c04807060014003030f0343e401e0f428080740c1854132203440700d1807800b0f4884545407204e401480940d00607a00e807000c070350300000f680c404404092a0030202d503101e007038060708280300e03407000c2d90713018040d40f211304498600c128134860040078050001c00c1010248201110301e80200e015910b04080300708251900fa081c007201500000c0071448203410360541c0c46 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 487734928 1250 487733678 487733693
    0xb030a240908030a0501050f151c1509050f060d050607030e010e1002040e010801060302061206010c0f0f031707020a031d0a030c1e0f0b031b1305130c020304050913 72
    0x40320103400741303920f40d001440305092004501c04c03100c1040d02c400e80b031801e84042e40151402065541c2c150000d040001d0101c2c4000754108042021001000d501c00980301c0005030b0180c1001c41e030f440c2202459002041050500800303a60100760010f000d02080c1d203840f00300b100030304011160329a180d906c4100b02c01500400f0302528400889074200160781c1c41c6485017821b44140c0580c4150f0a90745016400c0016071522001c417004a03281c010007100d25510a00140d44040344944060b003003007045a05101005000300c40400a40d0203600d903180b485050200008005504071003202c0160000106440082d000c8c180303844070381840c01a28401c503850207010a4601c01564020b82c0c030340d082c1c40401c00c040107030f81d0001c44d0702516031400e00e1095814850b50040405851042c420008400000100328284050003600f903031001c2186556245014030200b0300045880c01064411606011181350858651140c80c041007036940180d800d0a1a0404012010000400600d05410200039a03000a980c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 487736178 1250 487734928 487734931
    0x180608070602070612050609041b08030403080306131e020a0e0619091e060f020c18090d020a0c050f0d0609030201060e06040c0c0b060406051c05010b030a24090803 72
    0x40d42d0007005102d2900800400311002000c06006403403a01c0288203503600c03901140c03584a604182840429620076001c030700d01c6e41580c0e00101c0c15000124012080149000c0218000d02c0c046406e200c0c4903001d15085000c0300c0c5001300c000c0e01040900040c0c010742800d50050150760784981007081c40480c9a0b008189240d1140b5525240c890524100e41031040d00154408081c121030903003120740d80346980b0742c1000c07515607001d07080901099941c0c801e481c9100b0400c202194a000d08100c2040c0b40d9000f5807041040e0644070f400c0c0b540622208801018400100320f444540c20a49140f4030a00c3c0500740080074a01c11b400c15002040c01d2000c03004600e881c040e44444503c203900004285103850350340c10409c04060940d5105500f00b012042559501840d14243c5542142c130002240d10f5041c001802400076500c00c076003125840e0120481100050101c80703c41340075800074000081c1c5d910825803103606544004014040c0c17034413819001c0343c41410100500041c0b9a002074030311402e0705d0b40010f0303810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 487737428 1250 487736178 487736189
    0x180613060314160e0604020d1b020d0e041401090b0a03140c030607080f0f181204080106060908070b18090a0b0a0b03070203040e040c1d100b03010f18060807 69
    0x9034070410074807a402c1001960340429200d20318030603550a111101500d030a02610343c51040d038012608164010203544070b070b0f800d0310303031110020245104660041d469181207404030f004a9185411849581410300a101d250040c0802c80c4e54140e0902c10700d200100302044141d80c220400d00d0001c80041d01400444890320032001c024007825104004051500300001e000e13100308076185092005032500b9541032908400c80d44a050b0b280e0791900c01c0c0c0a505040c0da4001106440744007410482c621b00b040060040e41c903404001e010450301c0d0002500d0252a80c4a051400d500000c010403400c0e100c400900162042e0744529000ca2241500182000301d0035500c2046166031406910301614100d11070348010503001c20154150b28114001030749901592007400800c10a641c002020099095071040103070102d00c007882d165001504010f4012034046038030802da00c5046801142e910009410f50741210306442000103020704001d01605141c0f60700106002c143d45030300e03000c01c2203901030040402910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 487738678 1250 487737428 487737443
    0xb042f0c0717011410030606080109080307030b040b03030d090c050a0510051c02040e01081c20030f030109051b1612120f0b040b09100302060306011716031a1806130603 74
    0x281981407080443d440d27944425800e81c075250840b13001405403004d8070b038060700030b0800150450481012402506042801d03541c1800009070620301521240e20021109010380700962540d45c07546d051040400300c1d80206540481c81c807040c901d581e8443c1d402400e001050122410340d4800c00c2d240a410303600a6007000b11040e03480c00c01400104070403c034070201408000e8424520408151020b0803070904100000e0f828003503919016001b01d000c00490b00703903514113141d503541c07507a5680325840100002d0b2480b81319607108881c030b2806181c1d5102607440d4487c0c038001904004000396150980f0260050103c414050b56101e0070b0407101042c41400d00c010181000807580030071002c1000704580c00743c46034034820309130f200601850b440c15411010aa90b815a00c0b580ea90312aa40184c84c071100070111040000881020030050032442105002c80d01c2c0c054806000c80ea0041610300c00c0c04484400301034209000030b1260300003401300da14417500b082001d4940c081c0140140c03a104255032140c0c0040e210380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 487739928 1250 487738678 487738711
    0x109050703060f09020919090203030c0a2907030203070c02120d120204230d0c060c0b0106081530010618020403150f0b042f0c07170114 60
    0x400340105243c61440c0d079000c0003e16440e80c0021110030001c2c1c0400d404440e0f10f14140303005810740e8021481903400800f10303038031410804c8640d07070f48640201c42103400b0801d40110100044680c1c265100c071b6085082410f00c00e60711118220700035080109404100003a84500102680703550040403031040403a009800710a40c8024054160f60308029040c1d58107204110401c1110b05100b220844040041c40e41c0800030b80304000140c0c2540b5544010700001d94641c00044c509401180000c1924031840001041e03a0761184103899145085403c0d50580303040c5d2038100c540d850b110380412401248058a9115003410000c001d901c0b1002ca83e20840980d9100014060030f000180700c003034106c99070300d402d615041c1580d40392000048042030b0b40d00516180c10900c00427a0310380c0c0044090f420040c00c20040030701c0020124501c00401001c0240d0040d09030b441c5198460080308a4810103507400042089034601400d00e030985c80740c1c90610f9400c1d540c0d4580c815600501ca050703070b4010309146920340c454 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 487741178 1250 487739928 487739933
    0x1020a140d020607050922060e09060403030e150412090f1509080a0f02090414010207030924020627070e06031002090a181b0206070306061d10050c0109050703 70
    0x103200000e05104117010741808030130103039070740c42803c01e030498401c0c412206049a01680315024001e9600f206840000c0d940c10804200e5001854610890007075030203204071908014250303141c940e140300c0c400c0c03120a0340001501194102c10361103966006803a200c403801ea03503040c0307051112200e500512803440c0d00100c1803d80f554420031746400341410b10040e2607041000c0e61040422a46148020b005046c00c100140920108211101080301b41c04020356680c07003a03140081281096000c0c01e18005255001080169103942080c0e0440e201d0f40c00400864548485000f11003006a03099200a200b802044004010500542c4010a006552030083e818540201400c4c9049000110b00a070310520484404d81d641a49000803501d03040301181072440ea964003403020f48620f4100580f07188900391074110305030740091854030503449660200643c40d10703104100c40c00c0c0c04002910801c902e05080400c0b40f403808038031400c0400100d003402481e0040501c449820348146407000c3d600f41d08010740410a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 487742428 1250 487741178 487741183
    0x910050d0c08090a06050709031416290f0c07120506061207060302030a0e01020703080f10050108060405070c0b01030c1a090108040f020102160e060301062c0601020a140d02 76
    0x700c40940c1415a807510f000f54880e95900b81910001d040300352910080382c51a0302804040300603641203c1ea006503504824155070b520344503405081030700b54031000b0004d1040348449040c41c1e03619241d1284981c400310714842e4032458006940429113400c0c01c02c0414108101001004001c02c4244440d05500e407079814402e041c0036004000324003a2410540440504001003007031f10540d440c80c2001622900c0e08e02078040102810600d0440a602c0001c080c8103040c0c00c5101540b241040005400b02079039480000700f00400c0c03034413901c0e011860050201d040e40c0b0306604056444011880c0c8084000d04540390621000c50030b0f0b00c2540da400d0185400e0141d01100c6013420340a806d549285032a1512620000309010704c014000780189a00c0c0900302c1c21684203200c0100c81e0b60041b039100100d29154010f690211205a492030b1183d803030b0520000c1c0c0d03010701d401c0201204d44060010481012160203102c60041c004062904500440c0da8020005414481190800005c1c03001007806100000c4040d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 487743678 1250 487742428 487742441
    0x4022b051e06010e10031a100501020304060e040203190212090f030412151d011d0613020d050319050a0e1203090409060b060706090302071406090d0201050910050d 72
    0x41d0801402240580400c1c00094524111030380808019040d6591400d012440c258503000185417501e14000a401c1d0f501001c00d490082078030f43d100a6840365200d0041e42d40344914443d0002185d00c040d4650301c607103841d5010319440160907011a42124001000038101d1b480740c00302d00e8807942d020381030040c40a010081d101c20f03c0c080b24021450700b400c104400703d901c0c01c0203400a0012210050a0140e0400c0f038001d06c0a0000c000ca010361010100c00f0703070b01e01030300b85521580310b405c05101310120b8504c00000e40314061a54600182c44440c1030380c080c00317140350b03840d0000e0b542d0f1b10007001940c0064510034074480d05009142e954a0b19441c0c0c3c0d4100412603410440740342e10840c078603202a40390420110031a0004a42101c0020300700c0590702d45032000d0030703140000030350081000c2446014040240c00c240c0b0542e05c294281c80e1003d4403070481110070f076080801240c0040062003000b6050400381000c4e900940141006804d202c45400015028a01c0f031168600144002c034415601c0c05990181c034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 487744928 1250 487743678 487743703
    0x6020c0f19050606060703020f010e06090d0c0c09200703050405040b06090a0e130b04050307031e05030403050a030f020a030b10050a120507170c031b0405011704022b05 74
    0x3890580c2682c98a507a075810180c011881468001380e9181014002c022107028455200c009125140d68100340d1078a425007100c03000500e018020041007080e1007190000800c660149910b5001801c280345000242000c10604004610296000540041c081302800b1801e1103544d0b170585d15403c0005001c00c3c0c40d201d02102d4020b40051000301c070641d6406280300c05072940d000000d0300ca503698441c80000301c050135201814a0480c1400d000a110001c0014508a8080d8944100d0014808841d403012400200c00c42c000941c10b0000c10006803107100200308042c0c070b510700403a1140000c01510200c2c5d0040b0511f8002c21754500c0ea20425080c8509028901c940d40c0c28024100240281d0142c0b400380d20680200b8006d640340300107807119000700300c119070130154068014082e00d448400a0400c0d0700c1996003a140802d000c00740c20120344481d0455086c2c07a0b060b9508a250150300d811682d20406c0503004aa000c0014013405008646c006180c03848880c8131001d690260341903091460400b0300c1080c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 487746178 1250 487744928 487744963
    0x1080d0314070c020a0b0f04030501050606040602071a040f090507030e01020a051b0312010303200c06090405071101022d030f0f15040c2705150a02010906020c0f 71
    0x70340c021030030101c4815880706450a0501d01e54916200251403141503070860f942c4c0301c002042e80c20428882c1e00260050303a2152008100a45613a0200314986c000c03031280d00d00580c000403007031000b4031148002c041d0402402401038103044c1c880440100c510560b0300006e0b40156904100103240754503004403a100c2c00103400031464030507000d0700200940b0501e0b401d002c692a40c1c2d6150407000204204650400c40342c0350842d030301540c580c50700500c40b03081001350680c2458160089500620082181349003048001c0c4003a152081c254103001c00380000030f011074180900001d0078050304000380004c1001e918240890840a1860f01015400c007140d5070504081a20600030800050441600705810a000d0491040d0590f00c103c445601500b5400c0c0998209081c110403210040e00418950248020643c4c0c034180d4070420309072540280c420780b08103907121420200d0014003110000081061132240c3c400480c8148040e107549041e81d1040354181081d50065a031151548001e0082c64000c0041c07884 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 487747428 1250 487746178 487746191
    0x30f0f0822050705090705031801050108190f02030a1b0e0603060a11131404050c070308190e03041d010b0424120f0603060606210c020a02061201080d03 67
    0x480ca41d4405440c0d00002605080640310601000708041401000010000150361518200c01091a0401c0d07600451a4214860024101c0d0703060007858180d0746520018200d65000201d203117540c114002c01a11000d0301c508008015840501c401d0303106900507243c3e000582003d0445110900c84d035803001c0c0000c20300f4818007515a4000c94210381040f18180081014102c1410140e52445443d8244544255101b4006408041c1e00d41550400f20210f8040081c1da65000d84000548207400300140042c0100d800074030000b416510782c0c000c41728a4100060b0000680040074959406500a40c04186c2088405004032080012650141c000888000e0910346010802c804444c002c0d01c0200d08032051280300e04129108417000c2e215140061410701a440d07101074030900900e010f010a49440d410206e01095071401407008480c48100b800500e02c108820380403400081c1428420740c0c045000c3c066220300540d40c0c400190000030118521132400307514010116260100204421083c18240003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 487748678 1250 487747428 487747441
    0x20607050f0f150408030705220503010b12060f270109060513030c03050f090a0308070b01080c0607060f060308070305030702060f0403090311030a150b190506030c0a110a030f0f08 79
    0xa800c10781055102c90f031030b40c1b42d4464010030f486500841886600407c101647c074542041d40078000412185c0a0f4003c0200300343d481d00380803040e281c01c803006200b40c2c05040410800304181c0034107070340020404c02044003200041c5400082084c0384c405003140341c3d110020345041c80390a105094012103a1090054008601e5801404ac40a01315000c0c052100c081043c1056184410031280040d100401c001e05843c1c0b42d00d071004458006820664071400300100100e0029000100d00c111801d000b042941043d60554030340001c3c0004906c0c040315107807684d6000000800c200042c041603072094039100d0300c030300e030080002380b61030740040499044420030410b00011070340082c50304043e039402c400d04030300c52500d02010a103480c0d003203c002811003d903080010100800c590003003a031705030116581580026080c521490401303c0303010716a40300000300085521440480000c0c11303c01c18500f840120303107048104c40350900d2002a0b0940104900300051880340e64041103890040500f82480b07480750138104d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 487749928 1250 487748678 487748713
    0x11a0a050a0509130b0712140f06100302190c1703160f0e03060412020f0f1e0a0807110906010c0f1b09090804051908060a050a0207020607050f0f 64
    0x91242ca4010400100841c2030b080000c84804901034001010400c0c5090250000705140741e200c0b40d00e2144c3d480c10840c00085800c5042c054011508483c00101d1070b1618000c200130b10414004040906500b0022174101440d0041000318000300b540321107041c0d4105040036012210728261983c03001038200200083d1103015250030800005524204c1c0c1c00d10343c484425161445020340051b0300d0705c42c060802c010020b00c41d180083c4486903a0030b07103846a002c50b150580c0c60440c4007910490340c01c00040781c0c0c8040301c2d101801030341124a81c111650b803407168451b0130080d40042c209540200e802032240c003003820b14100740c40e0401000e11345480c0c8000c8584038511101c080b1000140500b07400120701600c1c620614a003005840c0004081105482514028075913901c117108090040300460b2454090078850214201141c0041014000c26a1221401002030000070b00c21641c0302e5081c4511405601e0b41e80180008a10400040032054442202146096503a103032160090f441402c2003800780000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 487751178 1250 487749928 487749949
    0x202403092b0e040905010905100612020607020d170408030706060f0501080a0c091509031101022b0c06060806060103140603030909190203041b1208030114130c02011a0a05 75
    0x1e034a800303403040010300005005064007010142c00b96080c61108400d010012607090540340c0c241c042001180d0399012099480100c1500195000c48144014405818018081e5240521800e02e104480740e502c045503030590460b803c803020303e41c00800e01c0001c000712403040502500e003480c41700341514940782c0024091240240130b0412a5251655006424003030840d05015015402050199411420b001070201c4540d10040d2021698810312162650011641c980c0e0090300c865188080c4014500c442403800d0940007007000c04c0203582d04000407a00c10311503078014000f43c01c0075144d541010000181503070340a480b0800d8944000080c004141e1b80001140d003485d4041d0f4030030f50260f881c81d0300491050541c4000740c2170540008200b00c1041010283c1701ca030081c0745140020050748450104150065407000101004410001071290580d50182008031400c01000380450740100c040712400e40b10a00c0700480580e4641c141140510305250540072505010342d01c0300541480c08001400c010744 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 487752428 1250 487751178 487751263
    0x3061d0c070311060a020903100506100c0516060f080f10060309020607020d0b1b0c03181908010507020d020c10030b0a0906060e0906010c20240309 65
    0x2000500c80c410035014143c00a43d850f20b520589006203000402c4030065480222402e219018440443e1400c0034070b031007502e005890107000c129074a2500340041e140d40060103401e41e41480b0320750110442c250506500009021a0f9480c3c101040304068098105000036208100d080e0303800c1c00700000e082c2c118012004450307580c50045a00402400440c19134440c20101030340200d5124090020b100e0303000c24003409440e400c0341185071034021b030500002c0790084040c06032040e002000320011141582d00320058100c070041c014510b0030314604e540c0c20b51140f150b100348016510380d800c01440302c1d0148482d200c41c2035035001400005d200c00e000555805400e80c148414035980b0100171030303030b51240c4078024098801c0c85800c0145036110f00b4050405005a220070b8401d1000b40005546540314918550315194404903003103061000b103401d031103c07a03e054004c54002e4158042104801c40008480f120440c100d40301907134074180071030883e04040c0441800fa01c0881c5001c01800560b40707400e04003030f2610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 487753678 1250 487752428 487752451
    0xd060f1434050c0106080a0b0106050a0c0b040c12060914030408071811073206070305090f150402100c0b1504090c03060203060406090c12020304080405150a03061d 72
    0x400480c0141c2d06406110400703081c640ca402004038050400143e410706c0513000d4000240c040ea0780b000120340ca84902040301c0001440304044070005150310a286400c50300c0781001d10001d503181d03450300c14681c40300c01040d20320795282c003428014008401c2031400443c01c204091450181043c1501369a5485c511484008603c0300e40c1541515111f42d02600e55148442c6185a42d0780c09420444000490082d030f8041d40c2010502c4824420a607103050103e5007400c00181003a0760f03552100f64010100285080034501071080d003c951000240858007444864404810f11401d150061014060540d0501010301000e503400c00301046e0f824840d42e41c48464140e01044080511010401400c40785100400d44a0340440100401caa140c014521072241070785c0030800c040d900c00d5004103440c46080e504000c140d60303203ca6142c2c0061034004507031060203901440e150a96481c04905071541440c5e49040c0040c1c045080003005526000c0c01000f08600c585101c45416611902d5192140140900c3c9905 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 487754928 1250 487753678 487753771
    0x190305220501110406021b01030b2b0206030903040614030c16050703021003020306010809010b0616020420091207140603090a1a3c060d060f14 63
    0x1c1c2500301d100e06040032034846803120340d01e06020395585406407da0030144001c418181d041d51080c450145000310052909809641d03140500041080608400c4200c6048040e80030250b2251801035000c0d00d080b1000355074403840d0100050a5010045c03000300740c01420014071200620207001d0300c0b6070310041e042100403160b0a280091030b1480302c0d4002500a100721006405242e0194040d601c604ea083e2542000e6a0301d42c40707058200c410b07158895a01010034803448130380582464021200038406000052b6501c86240e901c041c210142040070202c0c2800290b40080341810645070002d0000c12004004440c104010100c802450407000343c054800407000501924040110200b0150403601c21210300050710402c03840690219030a1021480016a44240000b810031030201003480a0030406880d1044c0300441c80768030068104d55210681c1e0003e100851881e215a560314120207000003104a54040c20346201100205160260780c005880c00c01d16550031004440800384080000c410f0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 487756178 1250 487754928 487754933
    0xc030601030c2601050a09060615080115030e191e0b010b030a090f050109020a0f0b030c0f130b030403030b1c0f061503080c06011403070b09150f19030522 68
    0x1542d5003141c080740c640d805d20090020340300c00c80c0e00c4691020700070102880929103d0b11904102c0c030404103900c00083c03101c8010001e03a001010fa90685100c01e00c0e010460000400b580e5240c040d0304162100740920b500140e04c1004100c051940c90030080001c11a0f00107001d44803122030810501c105081c50200100142034201280c2c4040d040720b41c04211840080302a051150003410423000c12406185007070384c0443c98044401030346c000c841e61601210314545c1c580ba41001c658100240306c200c0c0000a014900c10703006031004a0740603041c00c454031622850b250400400b956981c0030600c2c054040500d4840c1c8121049a00c10b51103900300054442d0300b05686881001840e0845d42040781c0c0c0c000300e03404420405172100070f2071a0020705d8125807090b40c80d2042502042c40300c42004e94942c3c441e0108010034240d0502a00c08154024686009440349055006007503007c103070038a8114000107000c01d204040e15002c0040c5a0451504101915144d170040c1d503200b85c0007190000e0120760481c51001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 487757428 1250 487756178 487756229
    0x8010c0e1f050f0c06060a0621090212061807090603080702010f110f0304050f0a050a1512022a0d08191104060c020117040b042d0c05030c030601030c 66
    0x404410040304103554950044c0c1103515008250f42c140c0c481c550321000000d500e40b042a0a0000e846007402c002820001c0c00140700c010640c80008a07004409202d4032810720000340040e501c43c030070450701c440403002a006900c1c200417080d0005c0000c04c0c50000306002007060313007040d51121542803e0003469000c03d141c0546660444070b450b0f015a21a0402e02104004044040d0040311400d4580801070032807401008500c0560780206074100d2070091081108241c025004210301115051040c41d04650f0130311082668400c091802d000c0101c801c0d02c5503840a4020b02100c242d201c50040c202121f0801c200500078100542007030480e10600c40c80c20400c1c0310603803120280702e0b03071102810341e12503480a01811407004104243d010460340c1d0002000f42c1a0006507901c510360280c044800c2d81d0b02d0f40c0ea8001c05900d0f08444c60b00260814022510001903030f112940c03407500492120745100c0c40d11041600e8101c0f0542d00c180a60017000040001072940c0d001103080c2e4180b045803000c81540f0012045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 487758678 1250 487757428 487757437
    0xa0210050901090c091506110c0f0d05010507030b210d0503060102070e040b06150406051207030e061906062d03020708032511031c0b060c060108010c0e1f05 69
    0x13820f0307030780003000054000d805600085030346072440003990059540d40784c04c0d54041c00590501d800c5401030040e0300858039085031001e0003008010211510740c8402e848a13402c444003180c2d1700d07002c0b03640d032091110b10b031401101041d000014224880a001c0d81d06d07503029120000401c0701801c0c4800440402d0860b0b000344443e0004c1c040070b0301c401e082071070710742040c1082c40001c1d41d00c58000c0d0200c06550907000d0f4054112419140261521443d1503821000e500700c142000344400b00301503585c9803059050f6001d224a03400703070980280c3c84030b20102c40d000c4101140c510781d1101d001e0003072180f05d802d280092861490841110250b01076000c1140c9101540a842400b00c0101894400810401c0040e43c3c401008032420594991100c1109040c60a80d0100e0600508400ba40d000740411004491400070084181d1a6074201040050724000490b040d41c00258135801550003842c01403010748801d00c00c90820708880c0ca0041e03490301c040408180711541200f101543d001210075880d08441c0078000b2103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 487759928 1250 487758678 487758683
    0x5040c090207080d050c070201020312040611030c0c06060f0f01120f06170c0604050f0f030f03041211100903080f0c0a030c020907140d0e0114040303060512030a021005090109 77
    0x35541c5801074904402c0311381c02410015007962070b001c0411418000c0340b042c0e80c80e4980c103030000c41c641070781c4480320010050300520440b10030391201c83c1c6810045071440a10300405a030140a9110f030004401107007040030013000c50340100300200d8a00b60301c0e556a0b0f03618905130828244003541c4042115080050f10540a8800c0000c1c00c0141c0080e1006880482001450424007591540001c00c81006294403031481866403000e0f40c2034910301249880070580103012801401c444141c0c0746400320500755001076000c0e40b8403030582c0e19100244a005006100043d0045480042c1668010310240c180070300c50101a022400200d50740d440c2c464101c0444043c082c4078011510328501d01d1500500c5910301c40710490042140102140103d07010300c5a1410443e1541075013410400c4285400005042e50b440f2282c1079921401e00c4101e04440c48132890081d4041c0c2c0e00810f01508050522007961004002401658020001d25440e5a404100300700c020b029001c000c40c0a460307041000e4050320840002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 487761178 1250 487759928 487759931
    0x3030b040212010303090b0c0c09060409060e101413110316081c08060a0501030c020a061a090c03010b070b04020109080d0c03090801110f0a26010e011203020c0405040c09 75
    0x40380b4401080710410340c100c0e813003555000401502c504050780a8003c4039086c003002d03032190b0850043d41c42c1803d43d1660014020b131000525001c41d40318181079035401e080107a02038010703030701000c1c00b92054081c0306a0a86282024255030814100f001c0c000c00b40c1100140c01703240c60307285440003070f9024051307598030603810b54500220923212440c860b103581382c40580c104d03141d5241190551941c090381e0002d10800004200c01703181440c1c0300056014140502e03440b001c40c00b0385e00b003d10000b0ba07a40306014462240d81c0302c0081d15420300d03042c8514203001518815921000b48010004c00c114a000c65148680c0450365101585443c40140c6004486070030140460080402903454194030100c0340030001d019540d0081700c5541c40c41418202e58481c041c2e03103481c00c410040041800c40c1e0320014130302141e040c900341c8480c403d40144926881e0540c12558500c0000700c00400016816210344c0d400340c00203a6440c00d0101071950044d503600784184003240200d40321400070b018440200021002803803040320 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 487762428 1250 487761178 487761187
    0x402040e07050405130603030c031101020f0a020f15010305060c0706020d060311030c01030e0a031107080a030918020f1611040e030a021204030201080408160501110910030b06031303030b0402 84
    0x2009010b680090048a00881d040b45440703000503924000c48003100c2d00b58072013082d109910340f0200c03840303140c00355542c1345503408100ea113690003079801c010004158954050200b540f01a408507003002c0042400b0002c0300c407440018008a0008130343c07550080e0010807029600e5000c2e10b000b501a005540c000805686802400400d01c05800182c980260040b020780d080791080c04c005604079230b204440000c8540c0890f5402001a000d01401c0d14203882e2041100c1101e50b031a50b04a1410303480450450000d60705140822260342c080c020303e1141c8081c0002541889846050001c0d01e00803d940c48440c0e1034520034400030300810315140300400b0405801840400715900080781d0700da000302552401442a1002241c445402005640c2900c0d0f0503902d02c502600c5030b4455500c990466116803a24440c00c02c0c101000136400d1050012600c1c0640f8002e0303c0300000001c00c100807940450032070070301d41001600b445aa650000b100e911003008440000f0a100501701100240343c400c42c0a03801610008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 487763678 1250 487762428 487762441
    0x90c031605130c050a0c0c03060c0509090a020a050a0c0201120501290306090406200304030f0801090b0a0302120a02120105060405060118050d2117150a0302060304020402040e 77
    0x4202541e40c1075484496070845011401c084030f90043c00400020003d01061003810b1043c542950424000c00400c3d944e80c0d125202c83c8110fa40002c10080800c070005446452428030751300f603503030186003071384218208131204802800500c00d940c01401080210444071003107a0090854003042e0340c01090400056848285070920198400002c900c00c4c80d0035042c0342d038200c00e0401243d104400103042090251030b01c0d0344403030150500071005069000ea00d036022002e94036100255115901035a920301940c8400400a440c1e00c0c01038000d03407003d41c10103074440d0301c54032421441c1e0112641920903a030040740c1c03200390f2410400d514000030361180c01d80b0341094070040e05400140c040c0d40304076020004d6458100040d1b4841b000c3d60b0310600c181802c00320421461414000104007907000d90817901450000c401e480e08030600051075400402c00c60600d012045034540c070f50300d502901c401146d5100c1148840015030304141880028850500000081c04544490701030350028a0031080f11000760a225 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 487764928 1250 487763678 487763713
    0xc090d06150306060b04144b100206061002010608100911010c0b01090209031e030703170903071103030903120715090b01062708010603140f0d08090c03 67
    0x1444251800f0342440c2002c200c000b0b904084400b15520740c4e0907402c12009142c00e010041011136100703140450003d180d04003aa00d914a0129006404016404034404401526040759601e00c1803a00030304001c0e1855078400d4000502076000002201c0111106c205440704078098a100d8210420301e0141d18100001034140d6040201d9041c1301300c1494401d80b02d0000111080b02d404017001d04241904001041303400041d900420610102405813220020709603088015400703a5030102101e036000060b10700c207141d4004030b5040c49034801c46032400b403410051100c0d03959014034800500408200540000250340c108100c5607000c0e8054240d0307405008000b100b020b0740d000306005842c0b03095581c184113450101072040e0b1040c154403041c0d0f08072903400c142007100d00120b04442080c40440e6a0480340001d118640340000508503000040b0700c290031480c0000d801c00065030303018401d44c410703080c82140b10004100d5070f03001e28142c0b41626240d511807980a00d000c0f141c036200d58041c0a01c40490f54259100d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 487766178 1250 487764928 487764971
    0x51f0b0406110d0c0807110a0e0a0c0c02010509100201140f010314010513060f09020a17191a060d0b01081e0c0102060606032a0d0b01090e0c090d06 65
    0x66150100c0c54a09401c03190344074000115000f00007200d0001070800600c03002c0140610901030100314a4400b211300102d50f44812035040115603135129420000c2c03a43c6280900100070641d890004081d02c0240d001802e64058142e025115410380280d100000c0d02c00d52001c0d10080c5003004400050511180c1c04030118000e000544010794681148410701c00140035060103001c0030500c0001195460325008003e000c00d00e8403103d42a20b501810001d80c1e034403e5548081c0824006d03404440c118011010700c0e0075580d50400c100304400803248808076a280c1c64160059142c940921500e035034000004101060210009012450b207000100340c0010004210000200500c258038031020b04016036035031194152103590042c0d1001c4c00060490800d50040d54021000e440c3e405491002002e58140b4000c1c494810312900c100850820903c1d0704902460300d003680203081c00300c503050420720040780c030b20401000c3c0c05407500d00041c0346540c1d8860202c7c00300d24541080741003025220645d01441d043c0b82 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 487767428 1250 487766178 487766189
    0x723030c0109060b1801060903030f1707021b04090c0e13050303041115070f1104020f04090203060f0909070e0903090a09090b1f1a07080c1509010c080a051f0b04 71
    0x3c2e0a100c900451040005c024187c400d240c07103044401e407070742d5400c40b50304401050310004c02c8048140544081007502d4140c0c01880306030040c00d209100d6021411344d91011070b40d858460780c1842e81000100d107d448444041d2500a13a8220095030390b12986050442900c1e0010140e00c8004100821b10002244044010604031000d44524800884151545c000c0c180050406500344103910001a40700e40b82c00244600500054248200f90000d414960410717031180c8034054001040001c246001000c1516400080360f10380d0582c144092056514007041c0a10410b042518011440c0c40301e0070426120300940041c080e02030140c4403140394010305a10b10b41114811050740110300e4071800940300c3d10085c036030315000080d00b910b09040c500a200c100180303640f007207404010080100740110000c01d8030060f00d6006114000814690075500c0c00010100400c2e64507200131140c0081e0700200303958210a0324500451281c80f0b806842d098800800e03010103c0707040c81800010102c2108000d007003100d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 487768678 1250 487767428 487767439
    0xf0605030a15050108130303060503070f090b03010c050f16061a03010e060603060a0b01120f060e0705070b0403050a050c01060609150503040c05010c030c1407050a0b0723030c0109060b 81
    0x402d512040e50341500c0781d00800d80072801d80c00000305517005a182c400940b80c000d00d001300c0c1c013958900c00300781003a4040c0c100120982c05010140f20500e050300807482208010f6000b002841f02c3c449000f0980e0107202001050102c00144521640104007418030361182c102e0010044500e102d010003035522000c0038458000c5d420f08645084000d004540144602006406481d55580d0480c140f00101540030b00da80c10721000070701c12014030360640300c0c030b0141000403440020014246001c2c80d01c40030009100008200c800c00282001400500b90f054010341c1c981401038450028030f805983e2809a41440e85c40c9620702240056065888050074003119007a4405249003200d40c203045841b4402242c01078403551201c1010002c03940b14811031083c00e030103460031201c000066901c0480b4102d1511030301002d5803100c1002d01140c94500811002801d82504d40d6140142c1c694405044842c009a12220702caa1940d1502c0140400e20031242d224010710020004050350340b030000002c1c4030300d0304000c5c00b84 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 487769784 1106 487768678 487768691
    0x60307090306140a11072f1206010f1a0405060a020f0703110a092c071205010501140d0b0a050c1e03090d090605180a0f0605030a 57
    0xd200f111001907042c10200d00410a40f4844003808250f01400c10441000030082004e220041c00700500d4000c460486281241344403400e010480e4200c5021620030740054400701701641a0b610400385d40ca0042e459030404500180700d0307423020300038880401c0f0174010391411001503d5121518030481c1d80c0003504104203800c0598680c07003143c1c09404101c0c10146440d0902040000d451450402c01c082e40c15400b0b40b964100c1c00c1031000704048071540010882a00a000d101c020700b000700c000c0741001b07546281c214003c0c80c09114501c0042c0581c03c0c0214249821007000c3e0045411001030092502d840241030014100074003900d29801c000c0081c01603144200046081451282c0240c5480b8a4a40c08881c02c011070429210108030b01c5890a00056801c441072321101c0340c0803200001c80551040c0441c100d190b10b03030002c61070894203030000280c9541c030000443c803c50703c680d01030004 = true := by decide +kernel

theorem cover : BRFrame.Cov 487589928 487769784 := by
  have h0 := BRFrame.cov_init 487589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 487589928 ≤ n) (h2 : n < 487769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
