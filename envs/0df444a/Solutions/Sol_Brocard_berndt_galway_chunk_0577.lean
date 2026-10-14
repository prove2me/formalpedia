-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0577
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:32:31.027751+00:00
-- url     : https://prove2.me/submissions/2a24e3b4-57df-436e-917d-f1d8ab9eccb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 103597122 ≤ n < 103776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 103598372 1250 103597122 103597141
    0x14060913020d0902040911030606190e19020d0b0f0f090121020d0807020406090506030c2e030f0c0201020a020604080a03090c080a050606040b0609060d1d0303070f0201050f 76
    0x41d04050040303d03110034900025035194030500403403d000310b40058845100c0030815003040001840e0070710442c04c00d04a90502100041081c098690b5240204c2c541c0d01c445072241200300d0000d2075843c0c0b1900000c1c0744c650106094002210b0000706882d200604820340d4204101d011a000c14680c2105520707004002d0202c0c1500d440241500c02078590080120540200e91a0b205056003030703807000c400080d00c40860501c3d100d050b004140e403050030051424040002507d070060b181c0068450141c654904020010031820114201c2034054030307504d072071020403000d0080c0ca800209540d58503c0d0075090030f503060043c000c0b1444103c031603000d4491642c0365130b500d101940083d0400020582da0b0400307100000c208104100141c0350100082241061a242c4245083c030010052805641400101c1e0072a40b114016114404c904131803080e212207400045800604940344148451442c5071000c68900802100841c00ec000e40da5821a8050400368141c0c241c03002620050780d081060800500c2401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 103599622 1250 103598372 103598377
    0xa050310020d240e0f06090103140f0d120e1606050304080d020d0515030a0b06011101020c100606020f0604030e1003020c010c0203041d0f010303051606060f1406091302 74
    0x2100e850006080801044510108641c3c3c071010155615143e401e200d40e820469403140d21049511100b031039494a00042950100c040c0701c000c003241c41c0a0020505804180150514907070300c403040343c28049500300c0003840c5111280305007140514004020607010000300741c0000303d5a15840305003140d89000340c1214960300042c81a40c00c0001071060420790003890000f0900c3d100200c80c0411030b0700b0400304c102c81d09c101000001d032082c0c1c00b42e1071440005800c0c1c0d20081d4401c0382400c140c0180140c0e5800d841c060301c0341e8071a00c0118000c5030341480c80841c0e00d0b4012006d44009900b103070040110220140d03a07500c0c0988016012641d03a00c03412001d072521408400014600e403401606042c8101c14039400d48001c400a8400746c0c00104040c07107901c1c0010f2001e40c0b05034000c00a000c03207003050b1411204241c4180806410441c0c0000c0150907003440311016408580d01507000c004031561500003003041d403403500030291801c0240b40180114902a004d0391000d050041440c01e00c0c5a42c0d0b03041500a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 103600872 1250 103599622 103599637
    0x150915150c010e0105150402031005040f02090a030b010306110f09060703030605090406050114060702010516030201060f060504030c0603020a05181c06020301151119080f03070216050a05031002 85
    0xc0300d040214180c0d1407820300610b8149a00303100046440d003418a0662001c10004a2507401541305108101680c011000c05030212841503c000441e1442c1d4001100648110080140c002e40c0b640b100200300140d0340501c60480b4060081000b004140003681c81181c0300b02c3c851002c1220050046064615050001700b0810f80319040c0090920b50f150041042c0103070885044d90342d0380e912001007080ca2520b1018048030141100c4207490300043d580040c1031405656020400d0b0a0101c91401c1054003d40c44070000d0410b80114a103e5541c81c0e000501a50050004880500a900d400105c16009000b92907034040242c980d6400e000c030b512281000401c86030811030740100c100384c24401e6590800002c000c014020200980e40b076041c60840707000d84001d40740700c00400c2411801d92402d1540401c0b103905407460301100000c2d601050030a07a00a010f40c80f0700102c0c009001042c081c0030f5800181c103116004404451707004d0903a40b0002c10034030300d0315032060315095000010f08070316281c0b80342d00a0409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 103602122 1250 103600872 103600909
    0x60102031207020f0c01020708030d0203040203160b0d150e040311100c03060e060a2601090b07050306101727030a030b0a0f08121606090506150915 65
    0x1004030011440015010036200340015810403080d081130403200b070100f2062200280020f0800520340080284d5902c18101c4699900c0d0b404808603045650500290704c60840c4603400700ca40584644031200c0b668000304900714000e244c16541c8a6204410344128110340340c00f04414a00d95030354805450800b800035102c031f8035000c2c41d034010110000d2031158680a0003e950b00054007070400c00011029500502402d00c681c001c007000700001d207940c030f050401e602091041c9405c440300150915026100f07960006081c10340c07000400c03081c298410302451091034125405030400104070b0050324422543e9440d003419050010001c0d01e4140860004030b045c460081040700400c031040c00041c216001000d03840001ba80b00c0380011800c0c03a212040d680608501d1400c07901032132600724081c0c0e50705103400748400460340118100b1040d0641d01c000c60015a00002d062110941e5450802e4841604030392215070030881e410808080d0604c9002c2c28820859403c0c1c22901080040030004183c0e02001d40520 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 103603372 1250 103602122 103602127
    0x30203071b0c0602120c070311030a0b010909060b0d030c121103030a0f060b0c0703031d0402030f09011a1e220506031219030902060408070e09010b03071d06010203 72
    0x1a082080100812a5030069400303103440ba003002030090030034001c202c481402d81828404503200340c802043c145c0460794080e54041401002802080c00c00c00c000d00301509103140000000f81140e540d80112004511034002001b4907a5074000b0040792548000014001404058840c0009840054020102c500c01d06201c082e80c0c1101c0c500d0b510319402210707013175040d5071580800c0000440358080c00c5c015000320044030b4104980083c0356695506a07100140403c07040201c0c500713035510b0203168500d4400c0d01030302c107558a02e445e40300e0400d070403803d4906c02c2840d8684020810509070207c0141c00041c0c006010fa540305449002602c2d0905001d140c40e607002c02d10800c4405000e2428000600b2401d034250007095504d4648109030512210b54240c85415004200e10942c030301151030400d0402c041428005200c8070103001050300c900582c0c10010035403240320f4000c203442122142c1580301d03c00701300003400034445001c14540c680f040ba2148100803000e0214a4425941c2003141c81d0b4080018030482e0f0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 103604622 1250 103603372 103603397
    0x30f0806040f0c120b01020705031510090608010c02070b0915030901020906071209051c03230f0409060909020303040501140c0106260a230109080d050f150a0603020307 74
    0x803c403601c0062403c0842c42c032203021240301e40140074803000b08209001a1055074a0032000c2a114040b6007642001d400210001403900c49000700c02c400a0312030b495081141c0e80d00e444449008041e1442000f02510580d50005a201e94003000c44000742400b0348410811400c0040f045801e81000d0700d9404295020b010604950f01c509015020782030088540840d071003100c940140c00c0ca0b040e41c03c150b01681007085020200414034075543d0780303182d040c9861b0600f0040040050856103521410010b400400a440c1140d80721080250056620403541003144c00da8410802c800c590518000940581081c03004005540c0500366013402c03c0345e02c1001c00d2030641480c0d450350860769990030000c140c0c0414121040c03800f0004480a22920f0320a0040a52215903101c0341d401c225002c8034400140c0d841404411040303000e400c50034103250b01130740c038036143c3d280c550705407001e0901101d2251000c202c1d8800581c0d00205020032107045003020f080b003e8030a003808411030180d40b000b03040100f88400f516581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 103605872 1250 103604622 103604651
    0x90e010b0409030302071403040305280f240902030c01110a0c080a0b070203090a090e030408101d0d0c02010806010903080c0a0b060406030317091606031b0309030f080604 75
    0x8110282c840c1da1300581c1d407850707803070070030074000350003507442900d0740280401e00000784006218020140058506c4c295a541c841305044039460000d0010078098000480104200320345100c2a011003128528110304a10007406004481c803507130000e541580400980082da50003405840b803c14060420b54040e0086030b01d44050f4429264004000d03684082541001e0002803228030380c025085101562515a01e48005207030030855020384a601a950000c00c40002800c00c1210010304aa030169900d2180c0c4404000c01010700b40c8041100c41103d40e03509240410204000710300c0e0b0302907201c03d03423104019001140e0502d402400c80d410b1190305400400411794660180404401c130400405a10079036203403e4800c03003400307041c441c00b4078101001400042d4109801d080c0000e40070300108200e03035801070040c0c03a04060000c07094143d0301000c008101c0315410f410529880240b4103c031800c1c900c00050440444040740c2010380014030422407202ca035840303815a00d40050008001103032000e02c90000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 103607122 1250 103605872 103605881
    0xb04050708060705120a020403020603041b080f030403140c01020304031509080c01090512030c09010c05010b1f0906050403031704051606022113030807080d091101180609090e010b04 80
    0x1004544041170b01d40e141080e00b1201c0341e02000564040d0300b41840c581c080b4059000241009040d1138a40d10080082200f8a100e54020424401103074003e011074000d0a40341e601601060701d95007040100d148819800017445502c0c0f100c182e00843c84c2a1641d1100d510044159151880c1e02e5102c403012030120314140081e00c0c0480743c8000020b195462480c2561401603c0700c031000c46003006004024000c00e80c0c1c000e49000343e4080c28140340c80381031b6242050041500d00c01c03450f4131043c040304035005480c8406000807010313040c3d150300e041640c031010709403040d01030342c072004001450021140a44c001c20500040d08640301d0b4080b1440d000b0204541e00f608200c80d0801c80060b440008080d48500341c200c407141b201c0a48a002d9468589001000c01407070b0003e0001500e00c0d2400200201000410002c4511800c158141001442c5403032505002a83c00505d0300740c0003c512072012030303e0020301030340d18088908a41700e010050b450024800040c04030100809603a541e19400c0054a0b102c81c0203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 103608372 1250 103607122 103607131
    0x907020c100207030b07120e070605090d02010306031703100905060607020f0f1f09050103020705030d0914030304030801030b060909060619090213091103070c02061803031207020c0102190b0405070806 88
    0x503154034818420350401d04a40b0501072080232a8003481c009c105c05600076044031040f00050340d59400d24022400141c010b4100c0c0d034401081c1c514200203111404038510051409102c5001540900986e56105038040c0c03502a28010f03072203a0200b00c29001840d10340000300d441c40e0042d103040141c40c0000001005440406502c2220034030416004800a80c491034400240c002424210302300a6192901e590b24001c0038580c01c00542d843c2c01300f0f41440002d5200d203300035241000c0325668541850300510b01d01d403e01c801c1311076101d00d2021603131360318040d0111841402d07894000c2016945150401c4040c1c0383c50035a036603500c072640c0d4011841071000c0c0000c6c424100d03080e910040f650300d0410b03000d0455548200c0b40d81441014002e104030720b507001e042c3c04a40e03030b01250f41da6144c0d14200403041e2101001000e060b032600c80095181c04242c400d0b010780e441900720741c003501c1b5029400c2005903107c07403081c03101206000d4000c1e02400028140740c4015000b901800480d1070302a202c25446180c05011782c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 103609622 1250 103608372 103608377
    0x90f0302010501030623010b1312030203090102011805030306010338121507080c0f0406020d0809030f04030821070503041b0b0405040b0310020d0e0c0907020c100207030b07 76
    0x801070041c8074407405441c42e840e44a44c006c011b04240c3c00f02d40b9854940c1030260460140001560031200102c0350b1150000d028152412504050f492601035620380c815490035015500b400c019007004002d41807804541501704020b58556641c0c5030044004085960000103001d8a4010000803d414250201c40c500301032812083d85402c6070080260180350910050a01d84c80044c8070203414420000e0705411515600342800c0d00d071180b0740094464080d840428041101c0400d000503030130f03400a0b40603d80d500b01e0319030703245584030b06060580707a11846501d80d20521041204000085200c03009007084a0004401d103059001c0304400c0b00000c1098078500700282011080c40705119242e075003620a4a03081407903240c090324100c2d030b4400304d0080e440380714811a07840810103140d481c18400560103506d401030440d40c40ea540710080c8028544651104900e02c05c440814040b800c1100c0c015018004607001450500c3c0364030100000d0f80900d8104a0441c00f90b003800200188141240030300401c0c40d074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 103610872 1250 103609622 103609631
    0x3210207030305011502190309030213020301050111010e0606060d02040504060803091504151b12030c0e04020909060909030403050a08180f0d0303050c0f1809060102030301031a0703090f030201 85
    0x7801d0081c10f88006800400c1c80c20400da22448640f50000745082061a02d840701c120300b01140d04094900740d005501c040c0d001484d440b08151001d800d9030045061310000d80b01d50f810034061315049400c0311042800d6100c6684440042609850b1240c003404c4954054138016140603141c40110302560010351160400b43e0000c101a0000d1600d0b0150b15145950040500d0074545841d0180e01e00351202200a01401076040e4000540b001c04084160300c030ba0000e00d1801c02c1010600000d00400c1e4844a01c40001c017034548242840c901030088403a01540100210515107a1074100106604060900e41070383c40108400000140d092281c0700c0a40c0c05035120640300ca40381010160780c00d01c00000f00d0f21500c03c0000045080e84e901280013400d51b00740c640050b03540c1d80c22003101c1840c4940d4000140c1c2c440e001c504568000e03400c031400c04803440c0130303102d0106a81300e04006903034a010038000104040e14545c846101c01035140c0340154014018503011403008019280d481d50b843d000002540180d444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 103612122 1250 103610872 103610887
    0x60c0106090c0503090601090209011413050901062316170703230711210709060b12010909030c0c0e0402030c030303011802031b030108100b0901120f032102 69
    0x200e1040400700740b914244103180d46440d0b40d040e61240c2050160308215940810100b030503901c911a072514032141c424005582d0041c4850001e0000072900c03401d0700c586003050003c60002c0c032a030308440d0012122001208943c50b86010446190444062010180b007403420300b0000c0b138046002c1b000d210b071041c001240d5581640c240104660441d0207609504000c0f0b000c60420842c5090440c0c0c2c01503041403005181521940000340b4078211000c2200352450881c83c60508000046441801c50b12400d00c20898156500f08410050040044c1c059290140e64010022101070fa0441c15500b4030a1900f100030143c16130b01c06402c01c949800607802c5a100c24100700071420100f040d80c612f048128020740c2150300d40030021285201c0449500e81898001c400b207404440481210b910140750003c85540b40d40e101c1180d02d45d100300004540704c18a0410044491034146440c41d0b03411fa41001c10400c10510444d100c0c40303241c0e908071000303e04001401c008e0080c3e034403500b00d0710400e00e0300b040760141ea540507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 103613372 1250 103612122 103612139
    0x9010c140d090812040f090507110318040f0902010c030c0f080a0305190501080c0613080106030302030306210c01030203150405160f0203120402090603070b030403020d1b020a030b0a0b060c0106 85
    0x4642414003034201c000c0001b80441030303c0500c40012254aa0700c089065030f96907108a034840180343e07400c88284000319000031111b0a0450745280e8942c01d5408209072a0b1a40c001410f0352010b00010340440ca95040b0000824030440400030103501900c10303c82843c0382552100450f42c00031502000081d500d009111510040300b62020301c10040c10000d1201d94180b082041d101c542d00d4165078450100085e030f102c3c8800304081c244008040e900d00810031300317030340b030070f0180d101c1d41700301e500c08c1c07241d8100148010541120050360002d10f407200024003d61100d0030040d4001e60000e00503000c0d40702c81d002c581c3c4441d9103a009440c4144501c1c051300c4c440314080d11025158028006065080d90424030001401341101e290040e0700540445148a0f541ca525001c00d05003840c5400c541071621000042006140d000901c0c00d00000d03450303941104c24085003890001040c188a80254042c0c2000404c00104410b00200b0307030408030f40b920001d2501c0106000502561100e424032800340d46071740c4100318601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 103614622 1250 103613372 103613383
    0xc0303110115141302030c04060e03070f120c050306130b0106020c090a020d1404060b0a061103070f0606080703050109140303040302030a080a02090901120209160509010c140d0908 79
    0x20392002404280c60080118100400500988111040b5403a4a01c425501c0141c041803801200a0855907070405440c00c9101d0303032044c050301021607c0c103004d00125040003d00740003182d01401807a26240d0910b40d00744a28130741c0000603100340c801002d000c50360703513401e2204a02691107204c04168007041850480c484003416030000c029034009440c0c00800c0e456003842e003a40409032110061f80c1703284441441000700320340e20400d000280d050302000100100b5501c282c111040c12210b4214880e0f43d0030084452071404410b5907520f410900c1001d0005001d1824081058420400890540c1d02c071424149404840c1c0c0c01560307183e4589000d181071003034842141c001810000091851403030541c81c00f9503030788a00a514010090301d03500141c04241e865040e14001304000b0060001940e6491500800e001e0084090341704980030b0307001c40c80000c240b040b40000d8504036100e00c0e040101160042d10408003003c0d0945044002d506d421a0b0340b0000c0c0451000d0b0085522980d9030715003401034092a24 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 103615872 1250 103614622 103614647
    0x706050306010309060c02060405280b090a1406100f1d090a0204020a020c040509070e1f05060301090902030606030d080c070c050303030a020a18050102030d27030801090c0e06030a050c0c03070c0303 87
    0x80d81c00c43c442f881d50300300120314421500d4201840317003215216142228070308550000080c2c0071340710700302146140000c0031807500d0240540c001440000c035142c0700c0b8013108002500c01c000920003442030600074459480000c0f42d000042000f036805440c055000704090307900071500000140c1003600111801d02d0103119840d003004c40c1c00000c01c0300d507062440e07000b81c60002420075007000210010001c0034085100240015040103003100d6100d5950b60648400707410940d104134801c2c01404001201c0e4200010402e4850b90107548c0c084490725120310783c0100758005281511410250320010070341b600c3c100011030003080c020500590302d10741041c0060101d4400000b03050303a00c0719114100200d03a40001a80da4a600f0600c0004410625034507484082c500d02c3c207484034a00c0601103083c10b068000035254125400b2680500450406900031100e104401a034164017170420320100b038003044950b01c204c0d40b00703082c0500c00e8034054aa00c200ac0c550303001014120f41c03040c2400d0003401007560010858960 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 103617122 1250 103615872 103615903
    0x2220605042d050c160804260703021522030501110304110108220501090506060301021c0e03040321020d21151a0301150906020706050306010309060c02060405 70
    0x42c0c0516200360404802020700030541a00c410108600d46480411900c0100704505400900341ca54500406144c115214540c0a108845080c411208514852101d2102d9820240c65964119420010007006042021171000414058070b803100500710704d02014408039414001600340341d842c0403400d490000c8484a18200140240400a078002d0100000b03400d090030b02c003d41d559800d6021b0380030100c40718010194001041c10200340803047d070003405a40d0141042e00d04681c0c4603c00d1509074071a5589008042d4042c6103040b210000c0c43d0b004885404400307007624509a52919100411600300321401c444943c1c0308808882142c0420513075422880d2820000303099440e00c06001d8503138807004228910140c481c4c80c05481121a610440c002c1c0a24441c0d10864150100f41102180c100340950202843c101020a03401c90080d00c0500494040341e0040840718181042111039400140c00b142c180747d110700c4a03100144081c02a600b0035901ca90040005160a0400618040d01c1d1002d0b80310703 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 103618372 1250 103617122 103617161
    0x61203070201080c0708070c0321020c060f1305041b1101090804030f0203010605030f0c03010e0304050916020f01020d02120732090306010e0103020a080114060d0222060504 76
    0x40c0d0304201004c0d0b1200383c0c0c20003251604164188191079104003200103101000c0c8410100410820f03003420380c502c2c00c00d0500c41080c51030b070300d406907551440050b14940c442400e112003030040540d0070040140651070164410001e9031680480d007601c585150f01c02c40d5400002c40e102660394010340aa0312a49500300074020340b00c0d191610782c068850b50002038404184107540000717545094204070011301c4054126038159004215468580710062807142c460f501b41644a842c200000081e41c003510070007070038540b00d512031203400c61282e10101e4442d000e40c0604840461810700a10181400004035080565541216403500380490b030020071100c107002d03500b480d4401c1102c40503d203015446008005100c488114450032200d801016442a8180b00317160001c07400000c03241d80c19048920940d41c98043d162219245030a8036040741010518106c01400a0b48520b84510f41c51402400a00030840700501d54070052110799604141f20007540d241c40040001e81010303c43c0c628094507003003c03840c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 103619622 1250 103618372 103618387
    0x20d050405040e03070c0609080d0908060601030b1c08040306060605131a0d0603050d09080f0c0f0f030d0305160201091e2102010903031505010e150408010212061203 73
    0x20400d010314000c46004580d269190a1520b60400468912a40000504429540e9020014030380c065030700440741a03029421103500124014011882a034401c00e002e003240b561002c004500900c4484a9940d20504103002404940004083c5200301ca01540350560345074190b08091080d07948541c021002c00c50100807818511b2003d00142090750304103000c025a82070241c1c103600700c500501c0e480564940c5402c0c0c1c00410481c000a036009114051b444100c1015038a020190320b410035100000d0681e0802680401945088605180024401800342005044003804a4504441c0c586d46202095840081c00220010070007100c0040c5400d100034094500340d60f4400d080124070b5140f038400440320750900c2d820000c5000d20004640280b140c0380341005004140240a050294400d801103403034204944403402a070140704041d00c0042e16140071440c1034000748030f15001c01c400b080d808504244804039010000303000510340d0600c20362400d08517041400401100704000c074100c00c01c9500400070301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 103620872 1250 103619622 103619627
    0x6050411011409100201060f06120507020601180c021905010c03050603030307140903030904110307092102090402031c0201150e071710080a030302030103261e280807020d 75
    0x85210b044144e505500e00c500c04001070b4013408050b08600d803802444d60001c620070364004241410460b8000041c4015111614140d0310b440084c0a8000000c10040451440c00d20541250b50380c0c0d0240d01c1120540b1b440d00d990240e1001d003c0d034041300d031a5102c1c0385d81c011239641401010f030490380480c0510710390304114502400c5d0141085480104440104804109540520030f4030800075000c1c10500000460195102d01540202c4124012410031080490b2130a00344c1411250204180b0084040350015000c004071800c0c0244100c0e49803082ca600120440741c1171500c00e41c03181d20341c1c00100303249000314450780c440c291079041000d4a42030241002105c5920040d514611140d4008019081e00c80b00010313200102143c11032401842482c004800701581a4011360407240611002000d0f041101e0201c0c0b5500509100c010503d80b05018943e002000118144046114a5000c3d86404440e1800070600c0aa80c00340e520841d25140b0542c04403a08200c3c1240d2183d8584003030481c0e080f895201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 103622122 1250 103620872 103620877
    0x7050f010605012106030f051e01050c0702010503060f0a0308090a0602010902030304030f030c06050718050111101505090c03060301050705040f03120c150e07170303130206040b07060504110114 85
    0xb52450780203040042403c0003545c1c480000f441d0000b4204401070340b9030402540d1400124041440d110141c4070a950012061203604d00403181884994079025903500111159000941001d6109000404509071030341e40000c414001c500c01c40d801500c400004d82006211030040d8030a5003564141030750840182e41c08401c440c150b0398044006406914103080449040701018070003000c41d49000103100103031350045d080c0c003404062013501241c0c1075180c60044407070040800d05a00a948100c209040c5000e86800103100c50124411401002d070307581e00003a00c851420396070b44e90008000000c1c00100d003028011071780c5c4844181411850985800c0c804a1214031a110140c00f0b9403207200c8034800c261140b4014002d190300242c440901d14a415481d40041c440c072690758004d0f00c1521000641c4a00d0061081080043d10000e5802e682c1c4442a41d520505101400c0340c2c8808100b20106030b043c80fa00c06081c40c01e0040000180610305441c100c5038554032240c016040c00541d481001c0061f280004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 103623372 1250 103622122 103622147
    0x3090306050901020f0a08010e0105180703110c070b070c0524070503090a0905091c020309010305041109161106060d11010201060512030a030f0209031218090c07050f01060501 77
    0x200007150780d0740c41c0b8128024020001d520030802000162981c07030070f504c010020f042c0e610000c1e40d00032590b0380f0800c018011000a1000f01e904500200107085980a58404818601e0b13420005162007d4400118244000d90704401c88100000c10b40800303000286500901070f0a0a41305002d03005540302d504071107140a19903604015600044000c02c0050900c00e840522002038014410b064036041c00d50041c0c482150f5400c0c03140b20b0b143d14640300250b800b084a8004d401500903501d00181d410044000d42b0000300f0540d254010a07002c070303c064440a620794421619102401007070341118100400c2013035140034030f6886502c40818000d02d5965904011a12944070f49910f014440000050b0b01400d150b910844e481805c401c03c2d501d6620001c4000d048602455400700b02074400340b40000102d001e8010030390342651001102d41c1c2c580d0b046000400480314140b0701c2c580d12044640015031208002c030380b070707116211021425208009007040500358401c1d00c44002e0002a06110009125500030f14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 103624622 1250 103623372 103623383
    0xe0105070203070b0702010b0a090c080a15120302030702031501060810080c0103050411040501030302010203090c01051e0304050a1707031b11060318030c060f0f07170705360d030903 80
    0x10100705c555000750f000c48a15000907000812450b620840040107000c0030110001098070140080c03503002c11032084a140c06021050140201e08049460307654854481e012070662008002c404050390782000402032518a410f10914a581403041c002c00b84400a0004504000400001d0140c04004505000d03a40c80a180010b025511400e20643e2a142d84032225001450040040309060b070640007588641440c1c01101ca16180500c01101d1341d200b101800940550b0960041c41607075038100c002c40c0c000380210116500b400c09034581d6008407814130f164949014002890310101600b1000301e01c800c01e003901e0350840303407102a00d0f00412041c85100d845d04c105c00000024044014945106080c1400031003100c1e04d406903081025500d0310140e5055003651682070020303000b052003210551186080d9620340e030841440c0080c1141c03100000d4045800d0010070b1281380f80c000d1403000300300b402980c3c0012144008003c0b154400142909a1925010307824440d8100007203a0040d800508036035109 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 103625872 1250 103624622 103624643
    0x14030a0207060c022a0a050d140706090e06060a0e150c0a0b01030204050c030c0412020f28062c030715080a05070503220609050303010609090e010507020307 69
    0x400004024403078040000c04082c0382003890000d0740d9000486102c52201c4400040c6400741242044c001c13401d03007041c0558460700c84070090226082103104151854440c942d400e40e00150160040c1c2042101e0f080280020902501003018022003161542c11480543c0c5891400e528100c0003440c00102c004c0007402610716241d40e0042881101c1200c15141644043e11342800082c640324004a03020300c0144d200754100000318560900940c100d07402050300117000da14180c54a803640700034038641e690580c0d001c07402c2480c104d901c1c1c4510803642c0900e00940d1540f6007208092032600001c80701e540104042141d9080c021640c90004c083c903640c410006150401e8442525002a2901d2080d401803110f4480030704c1c0d6001c2c003e07004541907000b01401c0b00c00384480d9903010f8048885003c1101d07012191f84000c184182814480e0100c2001d00e801454003003140549916014519442a44200d000508540e003c0007400064415010140507a034000d100343c0c240360130025a6401b0f00c403409842043d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 103627122 1250 103625872 103625881
    0x90b0f03130c08060717060f0f0d150c0504054f0e03030108150c1204020409050106300c051504080601060302090a08191506050618010f0206071403 65
    0x40b001c05000030f1064000311804e61800102c018410f22a2000c0b10707400c1c40d4058040343c0c071458852041403100c04040d12046034004081c040180100d01a8415181405985c0c0060f42004490045000305005d54440702d9581c0d2800b0140402e0822404103010011821b111000c1203024010341c00801c2003601c40300444034000054010102280b02c0c0e111320701c1ca0300e428880100c182c404400781d8101d03070f5031800795141030315071400c2616000c20031200b1101001c0208144040310a012240c580c1140c000f40002641010030342c0c3e20f6007160603640195100101d06021a40c44011f480f064506000c0604100e44a081c1c490350340c55100032640c041c1c10300c1034456220b50720402c1d1622040da03000b00100b208450055a4411002d0000d61000700070900078903a07010089101c2500181c00d032041a0a00b4480c40c1c24180c98070740c1018030a00d0340584d06034540b03c660024203566101d02401c100c003200e81c20840080710420016182e02030700180c0c4e40544d00500308000d800768200004080048110742c2d01c9a603a0f07036 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 103628372 1250 103627122 103627133
    0x1030b0a0e060303092d12030a0c080f0703020604020f03030a0516050c150304060c030e0a02040903030213030804050306010807180c140c01020a020c0f1005220e07090b0f0313 77
    0x1488001e0b0f41c00c070b005654150519540e4011b0544611b2040d680100c4602d0000e041c0800106000300100e5168403c1107880c41c07040c4602c2905520174092100c06050120322110204c01c2d5000c03c07410f60042c0c3c048020f0100703518121f140b40718030002c201c008515145101c800900280501c0080c0b40c00c5850220000081c41424410f00d01078601c014203113400e5410360804074103030703820607101511024500b1a46411581c001d1040d1703884840c0c20310040805610f03680c01c000c064294240102d003019006d1148440d280c0c8a4008000a10b01c510116600c3d1410002414513001c0305920114503580105410440070300403150480c07840c45d000c000898400c41d040300070342d210b42031950700c002e030300c40001030140e11080c040d4013502042c0300ca0b40c280c4a0500e51030041191038441c2200840e880301d000b100009010b40a48001e0030308403c0c03c800140315002c00f8141d10f20304c040e9603011648604004040044a5500c41a0320014000080c441c605100050107001c0160000030415500d44600d811154103200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 103629622 1250 103628372 103628377
    0x15171906090209091e0303100315060b03070302090f271302100507020f0307080606060c07050d05030a1b030503011809050f010f141e061c0b07080601030b0a0e060303 73
    0x340c000e0515482c0f41098002580d40e40080b80c45d9020321400c1c032040d10380c81c1c1800700403640603e45540307e40e2040340c2141c840c806240e03d803920400c115959441c000400800031005144104001d45005880b610080140070103d0311940000d4461b14404172002080e41c0f8200c07046440900c050407540301d50b55034912000103203203400310181d40160408880fa4000381d05c034004000320b034401e980000c0391282850605075144403d024421864116100140d00c030f09061019114540804089824955031803010840356981d100c4140c0711600300190100216801510368100c2500220495007040c682d03440040c428041809041d0b004408660a12050040c0b500700301071139900b01c1c0503a0100b2801d09a094002c041c4041000c01040c00d2400c90141d2115014006210325107484001031041c00c0e00305c204c15602c0c1c009000f140d02001f045c8031000c1070b114503511103019a01c00c619408480c01d00700700140810708020316142c105800d040b1b541c0c0d90f68446508010441d44400310940c1540c85500000f420350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 103630872 1250 103629622 103629641
    0x6170c0a0e06040b0f041403030a020a2405010b120705030c0304060213051c1401020901050912071d0709090603030c03030915021204020a050607050d0c0c03080d15171906 75
    0x84c0404034a426030213002d4402001203510110340403441d60100c100385603c90058114000140e0404c59484004c900642500300220b44008a031340d80c1d1000550a0404545007a00100340000b0041800c10340c0e41e20300505035030030100c181807090030b51902041c010f07a1440000c3c0020705098003c100c44000d500160b0491015200042902c0c00044201042c0180d145140009980300503008110058141040c82200c10b482d0703069407241e02e0000e1200601c44005100b079a0300c00c8910940e0000240880340c000c0454500d003407444101450b06100200410034a4a80c0010b0141881c01c0c034100300103900266222036040d85030401181c59051800d0607001141032908401d0868000144005118030b02d2803440e209520850380c1c40805174860301404114062000000d1003a400f10101000d040d00401c04d44006502c19410110f840340c41e84e1300c3c141c413030708021003c0c1d0b4001e480701450300d946d084041e00b140107485201700d030903407020022062603034880c0f00b90710b00b4082e070380b1742c80ca580b0501203140c000d032105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 103632122 1250 103630872 103630889
    0x150103170d32010b040512070801050405100f0b010f030e0f032208031303080d020d110901201002090109050301060308030103030801120c030602090d02030601090606170c0a0e0604 79
    0x60303400c001c42c0107800a996084107880d00004804888030154080b00d82c5040e00c82d03943c1c2c1c6a040900305018440c66106848079003005108a000c0020038603000d001c0c580c80f540c030510103803445003c841801b90655042c010080007581c2801812078190b684101c032007120340ca0500d00410003055011241e410300307c0c16107991246010000d040203883d00000c056003456031085030000e02e0190344815007038880c05040020544d0f90254041003000c44c010f50080c2c2100c1310b0401c001890119015240811140c1c0d00106035445040821070000c1c540c7c01800310786c85c000c5041c4c100c1d80d40f19441c140300c85c0c45a80003000c00b0203007640400e00d81183c8c0d108035441c00180c5005002040000d0701c4e420300c41e54617003091004400140c1d644001060b0301c418001c090b10441c2e03004074051540c0d41035903280c0020350826005d490700103010740031841c0940e0b41017102e0b81c020840200000340d182d00b80030004155014031904818071501d000c003030082c0030b440081102d620888621700201781203041c00000e0286d2042d5485001d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 103633372 1250 103632122 103632131
    0xa050903070b04150302130302010c15020a1701150c021003060f0807031403040605120403120513051c050d05090a02030604110f0111030a0c0321020d0509150103170d 73
    0x82c40a00c110060064507185580c0121210b10071004509038414410a01038030842c14004100650146616500705481030344066003201008203600100e030021604030b4009865801407000d03103100105128090000f0740c40702c45060300c1d4001d0203400144180002809404c407000d03c0048070740309a01440c05800003e0010748401e50300c01c8001d986005502040d03036003803000709900e0440040002106e044501c035858090500703160074030381090094002c10a9040c040e00600030455841c0900c44e00e84260700c2e9071400400406103003001e40c0741201d140356500c4581100c840e284a516004000c0e900790a40059000c40c043d80c81a074001d04100c880b44000707426110300e800b480700300105501c0500b030580342641c0320a20f1003484001141c105040040820060f001084104151445a00d920400c5800b908210b10075150b44005407024055410246180c91fa000c10070b11284a140d0048a030441000c82c024030594034049401e507451038040c0300003403000c0256a040310300e43d50018160341686a40400400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 103634622 1250 103633372 103633379
    0x1502090d0803240d1202030d0207080a351003050d11060c0301032301090210020d020601141011102a08100513020706050403020309240304080a05090307 67
    0x54260415101c160005402110b41407032007801d4440c440c000303c4000c00c91010040707a502c8000040010384c2c4d0f40c00031800b040200c520800c0813800100303440f9108950150f41c45088041c010202080d02c1c03010b0f814241d0030803072442e80203501442400c020104021403511130b119030782002d101c80d80701e0748005c015025038a25101102d4006402e0b0f007407000401d007510b6070356644002d285a6440309000060806110352a000501000e500403800100e0f101400040d000780a0303000a90b906070080781003401a401f1010f0010b46c0c6906011030b0b8010890781c403070800822000c40025041c1123440c0c4102c820059111041590070204100702e0600e10304429040010540356003c05901ca1009000300b5001c81110308050b1001d1b11406005105a80c00daa0920032603060404114054070200700c00d1124980a1008074003050643c0b00b400e008612940095030b07240300340400c2c4801c0c4414038100c00c80c2039880e0101070000300c00c1340003100c1d0300075405600c45582e88000c000683d058085e82e45d0340c41e018458400d012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 103635872 1250 103634622 103634633
    0xc0605070512070809030313020102010e151e1005040b010903080f120f0906010312050f041719050607050306060c0a0c0e10050a05062109010911090402010c1502090d 73
    0x2d040d402d00c40349000c10309944100c03040d90440015900d00002d0f920400c002004401481500580031f0720510021410710600c0c5000c500d8481900b1010115100000500420020400604030122045080025103290404803c1c241d21224412075010390b4540e90840007a80c4500c0262000e194442a856100c086000303601e09103403c07203014191400e1808010802c00020019103500c2000c41c44003c080036801c5035030748040903100340112010710005000c00c201011030603020740b003d00b08074407000218803100314104d840e1818009400e0200303842c0c1541c1001281010a000742d0181c000d04240b44d03070703482d108003084e1103100e280c850820501640032400f0820100c058140110340d040034a64500f604c0d040d02b20344401050340b00700340e80f02d448680104141d040080260101c2e021495810086401002c03801350a4070701222003540b40d941d610410380030090034000b00050800c090794003101c0ca1070194006411800805005003400742c0c61006010203c0f0a81c044892115010b002e0310403189152414 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 103637122 1250 103635872 103635877
    0x1f05030c06032a04150c020d14070b071103010c0f09150e060c150a0501050a050405130503070b07021207030e130b04061e05100f0c031101090c17070503030301150c06050705 76
    0x300c0281d400040201250148079042028821f41c00505040c500b03a2290784406401c107440124082c540240710307002035982d4408008e0f0a141e4007904110411048140c01c16085620113200f0405003c0144506030071283d10105540941d4a2a14010004210040140c58070684c51910a0f407243d00040c40c111030741400301e6101e010340240d0000c41c98a81f90110440250360090240903046101c2030400c0080c2d261035004250009010310300440343d038843d03858003421a8010395040e224401c0010920009541c100043c080ca070341104449030900700303181d50040c14480943c40e81c900c601d803104128450b4034581c1e4818800600000e00030000d00b9522066003100243c0c40140103c203010000002135641003000c03880e4809200b80d42c0d030756402d01d80c1c000d060320012502c40056080068040f00320a604c1c9007480703020b12032400b0f460340c94422450328682c0354018860070313800301c102c1d088840100a56100081500c2c155000c400303201d801c5205801045038241d489140241000e4184424012440e801400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 103638372 1250 103637122 103637129
    0x12030412030b0d03122309010209120a020916110114060a0602030f0d15031506051309050a0201081b03010e01051c0302070902031008030a081f05030c06032a04 70
    0x2024081c5045802c00c000e0002e040510240c0880c0004c90b1650081a42d68400780c0300c4070140740d400120b0045d840d45046240c00489809289a42c00280c0070024a0070122040310280c0c058002c0009001ea503020803215403016000788400c0c0d81e1b103000c13003002a001d540c51030350051401c0d000304801620102003035622001031328240d0040d513020402084c0c5620100854001c126444461480c05040b078070803034000d2050018954034040150340c084002095481c03030394500b4602c480c001c181c4500307000c100b007810314062008a02d40303450070507200c00182010402070812602428100079560f00c2448011041e20740c00c10202280d140040042a0717411300426903410b85405480621085003400042c2041000e02240640543e110410401880034990021640690000380045034a6500c00b201882d5400c4402c007100421992020846004001300c1018031861075072020400700c906e82004681c4841c05900002d029810003c005649941190b450800d500000300c0268424007858600540e203401c11700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 103639622 1250 103638372 103638377
    0x40f03030b01050705060c090105040f08030c070608090d0f1b0303060e060603040b0c0307051204050a0308090c0a0306020904150e0a0c030c050a0e01030609020f120f071b030212030412 81
    0x8100780900d5104000b500e4900e94040c004184c2c9481e50324252034507401500b00d4a0400108003c04030348450b40d80c0f00c3e2030040c45014000e54a07042c075190110300f00949a0443c2d002c00072014100103107042c1c00a0110500d543c10f0405c02c101d010cc0c0300d400c903452a03003401403c025204000e640410035a0603404103003240e5402ca06c0340c505498200400c45c0c10300c000d4401800001100d00451028040080110740007403040c100589400782e6400b00701014082200c00707030340c04c3e0020400385040c10f0300401101e038081201d8024042007040300b800202480214007003c0c00c200c0d40890007041a8071751764464245100c0e4192074030780c0c240c0d5940c050340c0842c0e001c58202c0425400e10b00040c030258024000e4a4520700c00d900c0c1e044c00c000808004070380c00411801030346c2c109502c9841c001072001061009040e0310200262807944c0f4041030164900300b01e4050002035440b000f080404c0421760307014441c5907051030000c101100c59405800c04914040c94070b07004044500d800010f1000300070100c91010403140198 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 103640872 1250 103639622 103639631
    0x17010f0302011205070203040e1302090117010b040b0307060e040b060705010b010215010e01360e0106050105070816020604090509010209120c030d03020a1205040f110604121b0905040f0303 83
    0x4440c020180c55040d1a1703a00580d000b40024402c1d600518029a0311090b150301d580f1070710850381c000600c1880d00780e020801b400c1c001070b103061058000303006080c2512000c1d0384c01d00c103180c0c1490121b561048140301d000100b20700c8240980d2a50703141e401a40501e8130080c069921050300c0c0c00e150380205210601a405407141011882084070381500f110b040781c080c40c4042209a1070184104200f00740c1444000346000e407420303c1c0400265142e034034030701e0340035a060005100c0b038150300c06030858003e130300003906108007800700c03900142c226000c5959003501040305004155041c4085440c0340502e8010f1081c140c2443c00300300407400b05602816006d00c0858002e103400d60b15406107030b1101542d0b03a003950950000a111421140207400521010b00c03580f400c190011a4400800112001a9401c84404002c01c102000307011205503191910181102c05500c0c0500e04546480015052200207040c3c5000da203115410541d54480d1740c008000d661428010762a0924110170100c040c0076085012a00c2e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 103642122 1250 103640872 103640897
    0x9010305060a030c0603020d0f0f050402010206010803070507120602120901091a010b0a3519020a05160807170c010e010b060d09060b0a1701060522020a17010f030201 73
    0x80002802141d80000c1044443d82c10f00008502950114802240c84c43c0c8486027505014110300c11030703240ca20400c80014040c101480024141003043e0b1103200250320900c0070f003001c11000700b458003c0304c16001c841d107c0282d403031409801a00880307201030b0310082c00808000f070829040d009101090f200c1d00c4008420410740f002103040000a00079000001c400340104113603140078480012181648090160218048200c4528100507520081c0c207140400c03401d10900c452a10340c03414810081c003000f54200b21810400815a0150348280c80c207607a0b0b034480308020f2000c034000b15640c030740d0080003e5200001e44904088030354054000b0703c0080d0b103030255881c0504010701c01e07001b224100034035045c541007405000001400381040103441960f620510301e006955a4064403000b4a4004d100c0c042485400041c1e1703084416079800980213529031020a040307901440c80900030f01d21003107001611414810300c102e405002c80603000105481240021500d0542024500101c134401d0381c540042081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 103643372 1250 103642122 103642129
    0x910170610080a0b0406020a030905060c040303080c0703140f0c030a05030403020f01060503060a1e02030a050601021902060d02180301050901150807050d12022811010203071203020c030c01110901030506 89
    0xc000f405468804140d000c1340c00034241d07030010080083c080c07401041500d50f54070341c2420008180c603150030010001908108154006d00040d40c0001c401e000c1301d042c10003035240036000c864190820801c8540006001440e24010019600019001011039449800280d0050060750040c0e4081d0054070a80440e210910414040c5c542500e02c043e01405d0651191491607003d840c0e100e01e400316981c041c550b81407c48030540b0255105d03d0a0160200d0ba50610344000780c2020011000c0d100e01e803104038452805615510111200e04c40c00b0034005984107410071078041c500840200c56070341542844140f00151105400c20745030440c41c0c0301c1c0c00503519501c1501d156202c07546c2c45669000544c40281001040c42ca030441c501c143c3c41e6005039591510300c599885c0c01181c03034040d9900d1150110281400b40326040000702000482030008500d4a416511030b61840d01380a55030504250700020f00c036103011024015541501601e400900190400480400c0c15400441c071541c002494440050050724 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 103644622 1250 103643372 103643383
    0x50f0d0c021f15090b01110f06071803030518060408010504050a12050a0210020a09030b01061815020a020f0f030a0803150103180f02180f0a0609020315091017061008 73
    0x980780401c1c0700f0b69103007055450180ca641c4d00281c0c18840d102d24105107241040c40410103400307500014000c1440c1c11200645110031000e4441076000500c542840007039001303801c8808a092040c001e5812100000004d5054440e5030040140355082800f88010040d0014a000c5518840c1e0003040ea02e07100004103d03079900030034003414010b0740251700c240480d000c0b5600601c0b0700d00300d41c5410741400d51a911038030b0280c80e00ba402800002e0640c8041540440f0000d02500a01403400900c04100c445000082d03858881003030180c8512960b0280507641e0fa00e00c1c000600100000e0142c0d00280751600f4020b05640081310139002da803280c505041025803180c03003a01100301290f803031209007807559101c9030701154104804a030011185040d1421074520500401d10600455448020711f02d00343c0050000d0394007550003080c01d14018014820a0b0b40c4c0e460484070b2420059422400c03a80d40c3e69400d02c614160f0303a0040d007128120321a40c50340b05402203081481451020318a81c4040c0d50f60b00b4150f640ca = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 103645872 1250 103644622 103644641
    0xa0e0117060a030f021f120c03090f021e0a1511070302032d1006050414011406070c0b130f0611030d0c050913020301140103050408040501050f0d0c021f 67
    0x9100b0b260b0a02c0010700320204d000c642030000e0400c00070752840910b5984c0e10002c10207643d000c0f82c0e0146140c0e0300c801c054040c0c2c1160305d81e40d00d400d0010903001e940c0c2e0f41420200f0f01000b4402c034002d82062440c1d1201384000034031040001d0001c4c500320f6685851001c3ca4200030844da0001d1780c0c4000682c03d80100250314012aa07001e4000d000a0540c0322603001d40300d0518404000303004091031107800701101046004100003030014006819481c020811080350700580c54844405103c3c80100700140c800317900034614010649507256101a1480c000d60114001e802c11208031001181c401a05510080b241c003d60703950800d4282c0e26625a0429030f4540b0700441c0300e02480c1c0c002c00440181d29080d8110402c400e20742d042c40e5003000c4404000800d4414410302c91507109902100401c140c00001c0d03541000d80c542801c00b04140e00300340d180c0c51100e2003a8090541844000101e0f50341040c48242103807426020803008024038003030b403a0001d4407007440c42490509910b40262107600d5403524407550242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 103647122 1250 103645872 103645879
    0xa03030e01091a0a051303060c0206060109090b090412020c091504060812030601230c250b040e04050c0d0b07020705060c06060906061318061a0f0304080405060a0e011706 75
    0x203104c5a400101c4080c0d1000400c5c116040404d00700000150036030140b170300e440000d40c0181ca801d280480c0014800c83d001e0348aa03183c03e0411481c441e454640d00141c54000d90030402501495542410076440c1c908003112403500440c018040203804200c0b03082805517080125414002d940e694203815903110900304100303098500c2040824901c0d0b00690107100700d820103402000c2d1003041c0c1c414680044c0c01000440350650020f81241c01070410340000c504c842022103420305049070030040030b03521034000d9020b8559080300c400086003e00c4020005810102c400400500e10032165107410f90381d500e0191102005440f03400c90109084c90000140ca1070740044200900503030765150704001e890780020f022241c0041b0100203c5028164455044003d07108084c0e0007120080c04650100803244140d1110501e00400b061100216142204841401c0103140242c1c1d107988075802c222040e0301c1642c2c440c5510240004107032a000760018101014076000362581e041c411074101e4820b28004045401551 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 103648372 1250 103647122 103647127
    0x30b130606030804230a0609030305130801021b0f0d12090c030210020703020306100e010e07021c0908100504021c03020c030a030e03061819030e0a03030e01091a 71
    0x4110140801082120380104000304140d942ca403101c03d5240c4c440d810088140a080d403140c0d001c1000d2128201100c0c4040c0e600c003c14034501400209000007502001301040750001e05000f424890130340071005030076401c0c002c540d601c20380700d100310342d00d004004600c00600840c8000c600410021a051030781180503180d03100301d0800b2200610091a91074000c0303c0e0340fa1101ca0100150325150800c40d805400f50700107203240c85c2075004162500400419100c0f007224440c40500042c401080319070304480350b250003000355803280e07a803c2c2d0400c0381c90540c510707951a00020402d002a808104001103c0d6100191200d4100d00e00190b016124100c401030742000b4503c1b40c035110b05003d680c1c1202114040c0c0305403608800050006030500d8249403003030300042d4510701341c070700b09207020302029420600900d49481b542c11703500c00c05a103880092482c264280161415142030601030b4088580c281030091003402c4417610b034a00640030f514002d92040c0091070441c000304010300344103400c2c070008414801320ae0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 103649622 1250 103648372 103648381
    0xe010f0f0611010212010609170109020607060203071403070f0f02011b0806061b01050403020607110c04050c0d0507030e07050303040b070f0606031a010e0a09032708100e1501030b 79
    0x1075200c01d9002030400c0c03e40d0708000696004070301c0c0030154040d05d501e507918440c0616104200c45107518030a40f0600321b9142003a20360040e50351500703c0340151b61259002d0384981d0759a0090350300810840d80b0307016460001040021207548000c0510020400361500403080009103403c03030032960003c90038071100301000e1807140107601400515a1000d0000c220302d1811902100071040d03502d100c55142d11aa4580003404201078040c4a09640701c06586002c88904072078110715079603056203011240c02160b488021440341624070b0211402d041c09580280541d0030080402802442902c0d1040014055158003140c185404011107044922000269040c000c80c0c3e2604100c49202440444101e95100340c00800509401b090b110901020502003d80e5032410141d2605844000e03c40103d06e031074030b40c88800298102c20380800c0d68004d0140ca11740c4203080da0004054206a07001441c00c2d116201002050448a411502d03c03a0032a1090321002100421611005134080c08010101e121020024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 103650872 1250 103649622 103649627
    0xa0905060915220e010207060f0b030d091a090904031e020c01120506060903010e0318060403020603010605090409062405040903091512020310030b150901060c050a14070e010f0f06 79
    0x10001843c41000000d40720381d54900d414220381c040002241d60540b980c000022003c228800c5040d1100140c001e01104002018020040c00c0300c0d0050080c10b12000d05442721790342c3c0107019580002c81c0a0003e031880d0610303040c0501410080c201119841c60074030285c05c3d12620105007251210b8040e1038201209040ca0409805030400401c007a400200601060700c0e01d507002d0103441003032603098018640d150003402c4048000d80c105e012003805081d04000800041c0c49960480f41100c0d8146800360700c8515000024020b081250300c09080d90b8103103078000003401c0d01c3c0f2100c842250b80540c48103180035615014401913a80c2417101501150f05482c08010905440103803c4080d107003850500b410581c0b00030000100c0c0c000f50741e403030707800d100641c011310070064503d0b40260004400f0f6860310041003204001880b024050040c20100b0507802e281c4020020308003c0c40c1c1d6407517841a298032030440300351034266440e0458400c030650500140000910801005c05240071b40b01804160803d603420641d06 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 103652122 1250 103650872 103650919
    0x161d061219050c03070f03120912030e03011805010b0f011707080c27310c110109060209090601050c15250e01020f0c010207230a0905060915 62
    0xd95a40c001c01c85103070b8140d6024400d40b80580080c46c07075401da2604600305001c9905c4282005001c0c401628014400d0601070300076803219075414545190302403014404a40900300ba1662a0440d64a05004000704001900260b00d909001d4a080c1d005000001c0115144801071505034108004070f404100301c5482203241580c0311074031400c03141c42c00e800096100c00c42c040c118400341c4000200d60010050f890001c1100410300302412262a86002d07401800c2401c01c0c4040145a065503030700010514903020300e21001024000348020009180c09040c0031019500003036480d480351803690b000403465802102503d40708084240104110b0002001e600101000580000c4110403007400d075440f060848581c0581e0400b1541e10762120f582d0107400a8902170501a051010f600100c860360b00700e0f6400603994003101c2d05401c406c5032000d00840b801843c0315a24284541080e501000440c40b5035445e00480e02031103080d41c0e480004d03640d003a650244008104084c5501c039844804121a039061142c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 103653372 1250 103652122 103652173
    0x703110403060e210d051522061701090501050a05160e19030318060305091b060c12071109060a0311010e04051008011a1f02161d0612 59
    0x131603038003070b403040004800000c2d10200c01c8103a1070001002d0984600300d0144c00d4028000c403000c1c036008000000054044903205d05030f46443c03880c1c800400c02503401074001000801525a4100d00003a0141b4414081c2100145c1a0750960a101c00b03c4d503c0d030351a1007018841c410402c4200160b400c070510031201048450051640101c0000310000000c0d0035428040085100740c58640e0601c0790717150090014059a4080000c1c589030200308140f003a0007162240049021000c0100c0c0030034460002a035030700441d4844000f42c4031b802d510002c4216064010318105e400b0b90032081b00c04130040200f0680002c100c0e051500071012400410010341c040b480f0b0000c071401410207020100d005400b00d01114003c456078000e5007140341080003d0f89080c400c2800440103101e10b0450300b5113200110b0322404000300034084000c007011209618134424002844401c0c01d6615080c8a0b541c1c46010006c00b060203059441e00c0d405d0880400c0b078501d8201199030700300b29500090301d006580304005410310a203480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 103654622 1250 103653372 103653401
    0xa0e072918060414101d041104080a060e160303050406051c050f0a0b0306040b040b071404080a0c0e0910020c0109050f0d0206010509101503020912070509070311040306 74
    0x2007400d03900c1d075114005040940710003031003440c03040c6500e4104000900c14020141c18850304143c10320001402c2c2201c02c2d11030406072004140d41e032200c02c1c4030500b4400c6a020b54098080e025000080016035000805101c000c00110b440e02a00b082c10f00c06500c1040c44014041401040200665405140074000328a040803400e45061549880c0e00283c0b0422a4012034010b03540081000200c150300c2104040e50007a0000c00d21840c1540d689007040f00c01810142480d01844005503e480c403484070404a05485070748a07444070340d40c0c4c5040b80e58003c25002151320f0703003103107101085401c0382c2034000d440b40c10b10030700a1841a4504803960000e5018410803c0c083d5242c521030800b0071020460310f620603641400070b07d031032005608024245441078010500c01d01404083c480c0030078107809010b06642900700c8520007031404c924254020300c034400101e41c0019003903195601c09074000c6000300c110b4009881c600701340c1d501c240f4114111a59880210204407040c0024000305200b1f901803005c01c507006 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 103655872 1250 103654622 103654657
    0x81f05061f0c0203060109091a090322061b05060f0603030409290f030604060509190305090111070501050d0e030d060e041506030f0305090301140a0e0729 68
    0x140c072040541000c544a40c4046045a0018000c600341000040d00620301c140702017226482c05e60f6200c0c1c641005845200300ba00f0a800422604034040c0100c80365003030100b0300800340603003c3c030100280c2c12030ba02c10880424005090f800ca124107c054940301d0580c0700700603040c541c1e940040d1070894a00900f0054040c841403101040300c80040c4525403803c86041000c0c60f03803c816450701d9101d40308078840c49005440d68a040300309130310001001500036602c0003011a560355000055842c18003165040e50041c8100072200c02811b4000d00101021a03081e07940c40001440c44454540d295403d1046500044003041004090b400c03035805507800342c00d040c050303d1a00b2480341040d8103031945900b2000074102001d040c0010000704c12030400c070680c51103505004440c6961a044e101500c001d00282c01d0000020f055006558203600c40d60132400000d0b540605400d040d225403008061001c090300d00380c800d0100200f204000108a000c44054904070650b4000354074160040e1508280c18111401849 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 103657122 1250 103655872 103655899
    0x616062315030606030c0d080f0906040311040c0206010614070305070c0609051c030507020621150f01020a050c060a05121303030501120309050f0d0b0f0403020106081f0506 76
    0x104003146010702000d65440c5041d04980c0105820041c0142005221368026290f61000351a006d0b00d84007510f410060850300e030700040280244034414408842d41c4000001800b0003003140c0507064144a0f1015502000218102d4005a9550900307005010206000440c40e0904c4400310f0010311440f403081c44c1140c206480e03503848500181c155008080400c581200030b00840c103164070310240307401c0c0741d0b003d101c1044d889032000751003481032000182c02203400081c2243d40038001401141803101c528003034565840c017209580f90303591107800c0080c0b00700d4032408101050743c800103c07030301d509400c03002810503c100d000402600d58801900038082c00400c1c0700201c0407c100300c10b0340c2d115000c0c81c43d01c07510000042c40c00404603170b0142c00282c4440030100810005c20340c061224003d46000365580309440500d50000750707240940b80130045c50904a00200140041d1102d8040d019074807e40082c4440b5072074440c400e0f11202c4550440540c204524107411551702d580e01301036040040542200368400c01e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 103658372 1250 103657122 103657181
    0x10906020c01050f07020313050d03090e0403021f110d0f09020a03050f2b0c05190c0503010501050306091c181e0603020f0429040e0a0506061606 64
    0x1080320755040e0b035910000c20640880d18a0b920b5030090703c82c80a14034103041507044480f01c0500e40141801004214111001c050151740c00002505100004502a00d03240c03400035034580c14881d40c0c0c550b400c41021000a1508540241c14031851541411410a0f0303220107503134010030b289200f40d4035890b06c0354660400340c1c450004a44c01786015038042c000c14184100034909e4580171240c4806044100080304c0c00000604109124805561138503c0290080b030030301c1450190a004034181d101198001c007410081ca1310180421120158000d0103d07030390f203201b010b40711581111082d456400902d03200340c41c000350085041d0280c803507080c005080c621505140381440503035003040c7d0090f01c8441c056900d800c800484900102418a03056103010010010a036960090b4460f0125140f00510350030000040f039010100d40b0300c3c0c20141c251710b07a5030364000c010202c1d8054070214106803511010504030300748001190010303500c28151240540d095501c15009122100c0b02070700c1594010340050320941d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 103659622 1250 103658372 103658377
    0x309060f090c08060c0405011b05011d160b030f071808071202130c022a040504030509011803080403170d0c0201151e060513090204030b0109050a140f070201090602 72
    0x41c0288110400e070b60030444002d00e41040034128402801080c00f0400403603a22a00d10900585c5400c0c1c141d000081c0303441d100303025046542980d42807401450f00303881c40707000000e600a07900d0f011b100e07418001944e5100240a512003500d2140c040040500010901c074090552121700100c84011384141c07694800d000c1307050100d00d421008020f143d0701c6255055242500761111803040e00382080040d041c2421001c0d68170701c3c448031040d03902d090b06c2e1640010040b0107100c910903c030014105000d546440d1900030000d501106540740410070b88410303c042852400e0741d14007500d038401d1605103080d0035070721601d51401103840c0082098504000394030003c4202c0c01200c1d9104040e400108280109104003000049640c120385052100890601100c004aa40441c1119540d04090b940c41d4078003403082d10503d606800c00c0103200d0000a00100f00030000300c3e5181210701c0b96000704290b4440c0c00411094815203200142807002c460041070340200c601c000990410110b000005080c1c0303042c0e40b190b090381c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 103660872 1250 103659622 103659641
    0x30a0207080d0f02030711010c02060114010215040b01171902010302090a05060d0605130b0102031902011103040302151b07023106050f09090d080402010e06030f09011d0d0309060f 79
    0x10b4011080c01b0026400090030920781d540c03040203101c04801500029078480c01440b0320404441d42440c0041240d0092040c2c1d41140100c40459940d854036040c4000c0e50301003881442e590800f108000910174401180c6813100c99220760980303c0c105540d400445c0079400055036150712000705200015039688080c010035003001031440c007003000c3d440c103410441c403910702c43c0c0103651050800d09410105da90100032540345201030001070806d221076000c00c90050a030840004c540400c000203010074141c00064081e10ba29012000740c40307968810f0518524042184000c82120b9418081c110052a100c05008544d21401003242460ba00f03210040c0300c10003c080d11000103964410040c001c50400d4031013008200400d45034401141442c001142d03803001e0044220040001a40204045a10405102a400c2c60042141d502c074200641032000030b034400c1e50001c01d82e6103400030700301d80700d801090908041205140074142072201401c0685c041c0403100c40450f54280d460200c0c0d9103501c807a00c14076440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 103662122 1250 103660872 103660901
    0xc01060e01080a11040510030305031306050f0906071803020d1b06030e011103060603040b1b0304120f0807080a020a020703050d02030a02060f0f04030c0204090501052d0c030a0207080d 81
    0x11440b15040540b00780803221301c001e020700c1c24882045120f06c1244800700440360705281503a80c0e40d4600c0f00e01d4110a41420004100a00300380602c986a10b20002ca5805034503aa0b003650320300d80b64031209607070701c2c2d054a10400301e10307500c1c4408102600c0c1803400c6142607030017a4110f15001c403807200131241504240c0c0080005c44d40c0c60801e414454008d2054520802d20055503615505201000840d50302000307100802c1c14880c031000400c00013043c40c42e064880d8920b20f645803241414980101c04000c0c03040001d001680749507072200384600c21541e02d801004e280c2c803800c01a40b036041910019501c0f49541c18250b1190810010000314108017000d110000b50b4003443d240c0140d19002402c0803400381019a61840d5502030180d150820020079400c640e050030b000384c0401e480e1010801500703100c0c7c03024019510700000c005400000e07061043c2d003c51038228020f0060b0145c110410f100341e09444040a029042c400103075096010381c003e00d0501d00950581d030a00e00b07900e02e03800030741d00c080458030036 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 103663372 1250 103662122 103662133
    0x20f0d1e0e0303060a0b1608030406060e090316060213030206070602030103110307060f0e180a0504030806011119020d08030108070503060106170f070909060b030402030d0f02120c01060e0108 84
    0xd8515100d200c24204195014502c0d40c103003a80000c0111900740590800c01d80005045c84460610040c1c40c803000307a002000c00e440b450a410700c0e000500d900e21459034658400400201a18408000c46004910f00c42d12600c4040080d202c200c0290840d040c1c00004e56540315000c409a6079800141a05c40d100700d0300540c3d01e60441c541200141007000320309000f607111400621030603070480d01c02040c04805240c010303140c20103400010080f038060003405a5843c1c03071800f404108070454100700c0c80340c4c2c001d0720352100c141c6415004660103100304420340280d400c94a080501140c000060404590000f011006000c81c40d8071009120b03442030340300a0169000800c2003040342002e0018500401140c01c001003402100d10382c054440d080103085140c04810040003482c0301d0b00a6894201801c0158010081c140d107803100e41e44254000e4a00307038441c0c400e011640185510600101d03200d1422507024102c0d80203001550045a000f110712840d06548421002c1500610b0b141a0390092004000900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 103664622 1250 103663372 103663421
    0x50d0b0402040c030902010507030f02030d0c12110f0702040e0307170403030e03070513020307090f061107140312070501090b040c0e1f05011b06020406080105090a02070201020a06020f0d 82
    0x3003102c0c0020f01400c189410010380303c000d80e0300300d015a45103e0305410155098a40c1140480c10b51040742e00912196180a9003c40002d610000e44125125070000c10400122103500c441c1071806109842c0f4030719101000400b0050406030844025505007504490034442e40c2d9076100034000112400b07901e107010119082081c55031200072008040c10030b0b40600a45070070000450692500400807003085078001010440d62031250070110300502c1a90707051880c95880d0030300207014140030940c0191a102e0382c5000301c1d103903103024020100c1b404000c0007800c1000072055110b010760084101543e46559588410000c100c3d00f1048a101d188500081244a414804201c0141c5e4007c0d151428110210f699241703610300c40f2a20b00d050310401d0030900e054525942200ea07981e615800020401c80c00171a002880640188110b411380e0011540b041d00c50340c0c1d68030100124016080040e0040c1d00104103000807070540d82c01002022201069145000070300d004403019141d114043c03440916081c400740 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 103665872 1250 103664622 103664629
    0x90604180e060708010e0403030b0f150c1002030108030403030c051e030301050a060206070c260403051005010815040b06010903140615040b03061f1518050d0b04030c020604050d0b0402 81
    0x140e0f4003000b181003813203c0b0350511486201010300100001c003415992600100b159454240012124400a10b04004140c08040720400d54005c810314500901c2182d00c10800f4012900940f4140c1d50003000550909180d610304903080c3d110140300340c6080c003a01c1e0b229a01158000d0140e51032040c5003005581d02e501d0001440440902c651100086401600901c41103543c01840c103840a500818403e1156900341021580c8000c81e0094803106540024004100040803c2ea502034030b8581804108a81ea40d80b0702c0340d250304040300006440440040054002000c0d05151500003130107250441d461a100d544034402800f0b0342154420304c1e400182040884003003680480300380501554240030a01420021075500c040140228680341c003a040c841000c0361b0610380d8000140011100b03114184c0840300040d00a0284005181120b94820404105401c0c4002c007050b1242d402200c414084c0d03a03070f4404440701139030644102d82c0201c0421001411b9074030700c3e00340100c29001c0c0c1c41c00c416038200703807040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 103667122 1250 103665872 103665883
    0x6150504051c080d0903090b220819060e0102130b0306040605061305060919030b0106090b03010e010509040c032f030708030a1805041103090f070b030705090604180e 73
    0xe8608140b607100140009948107081d5200101e030204e0114a540c018901a908a040f40d0405d103800034020800311030041304602171700701140301000306211b025201c50a141e00d403100c40a00c00c1c079401d0280501c0001400c1030384006060640d54000500703200901a80821b2510294842c0b104a50301005008062a051050741c004140c12129145800762491900703d03100014401c00780b00720808075000a941e00c03a550b1908508a2090030340035261b4407441d11821648080c06040001402072002082255040048074162142d800d8140310aa20301410071044110040c4221402c1d0798511000000480044913001d00d090740c4801c00c9120100423501e00062000380d07024034402d5222482c00c010044002c8211a0303a1400f5140502c0901003011a49482c003113640d02c020340107850507842085c0c032150440514080c42c0c0c0c500a4440c007082020b2026680c003d140200c404901c010008202c0c0f041c0502c0003008031000c05800c06007401da40c0d07003d00c0301035041041120007041e121100895400c401307021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 103668372 1250 103667122 103667149
    0x106080603060402030d1206050a0306020403031b020a03021215091b04110403020409020109030519031409090c0d09080c070303020d210b060408030a0e0108060102010c020a060c030615050405 84
    0x20b10040c582500001d985810211600d000c0c0070f5400e034002c00066054000307101811002d80f60b82400717940c1b8076044009600610080d00001e00754204041e403445192861007103030380c000b040403543c1410758003000400358000c44c090b280c9109140c4101c826400580b1207620624000c0d0150015100c1a06030b00b2160708000080d601c00d03440c085041000c50302e1401542c0981e501650000383d00940d40c4016601141190006050b03441000101042d0440c0d0f0214608005d12136616264400060a01d94049000f01e0000c2e50348240400300160207403040c40c014104a00d2c0403880410014120b03121080d407a4024021001c90380c015075800d0003450b404003d03c5641704014a45503215211017903010f00c0314040441c0e022180e984403440b02d44580c2e140b609070b4021f0014101525170362400c10b04094070080c3d41a030028041100d20b00019100c1d0b00601c140c624000440c2c000d00103034002030b82c03454000e00018281d03400741030ba10303400030a800141c0000b00c18489881d0b1030741c0b650380781450708002e00d804120741c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 103669622 1250 103668372 103668379
    0x9050709051f020f070e010513110306010804110a080a17041a09042d1b020a0201120929011509052202030a020414040605060a0516020d0b01060806 65
    0x420001902c40400d001c15032490414a480034079a0071a08908214107662405030a2080c100081802464164600c1c102e84e030444044545491900e2507000b80e40a0200d6141441014170001e0070550062002541c0244105e042e90002ca10050024109000a030841025903205642044c1088100304c4011000412080410309203807920b140c4290101e08020000840030f00400d68126584464024200c41190300b10b9201d03032000c0384684250b03801c059403034026815040421a045404550000415000c43e59020b4513441c45560010350758400003a1020150b030f55649802e00119016400c441c003801e030341c54881c1c42001040ca11546072554183c00440c00344500c10000d090154020780c1d201c04640098a0101c0400d50111145035920402c2c04212101030000040008440c41da500901c159605d55a06154045840d001e00c4111001c50140c1e40d004441004021103e90090029200011206028040300300495010509000b403c00d41160300b1003203a00184a202e030848205035109101b42c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 103670872 1250 103669622 103669637
    0x1a04020906072d110907030e0714060d020705010603120203030f0f090a1403030121150228020d121a040509070915080c01020601030804051509090a06090507 69
    0x500140706440b03206001455002400c0c0c0f040407440e1860000302c001c128602480504105a041a4202c0c2c80071018261182c1007440c0003804040c060b1007620410501040200121410200b090075101c50013011940d01c0700d03041c020400071a4a03030000f0241140710318004140c00d49580b80580e03031610b120004c1800c0d5002441080391207034801ca40c456000400d80895500c1d905c6008a80f807c00034100f8010701034000300300c0043c007503a90000045048034032a01100c241450603e210340180208044010901c441c100d00030009c1c0e20032500a03124003c03102c1d25010010152200c01c1e04500c9150000302d0160b0007180d60190300e15000000701d0207104140703209011003103c03260310a00d20380c1c100381510703c03036179032440400c451200070000100030f003500c40d808205500140800100c41510380c45825094450014049003d5101044a5040f25400108a400c00341090100a40301d0303648080d007011148144806c441c995143e845c1c0500502c0004000100c040c2024404425910010700c40018002c40c7d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 103672122 1250 103670872 103670887
    0x40906050a0b0306060d020c0607020a110102071404020c0c09040f03032a110106090c0203040e070207050a0324020f030a0e031908060d0203070b0c010605040506280314011a0402 78
    0xba04200c076445402120b0a0342d5681e0100c482100034000c6031200d07110342c49040d0802c1240c5070000b07129000301d80250240d4400c40e07500001280e6403a41c90050355110740c041c6090001c80d04040c0c0140c17504404603810f8400301c50b1004081001b5200840d010366500c030b40e00280006141d01841039449103102110b0390b50004c00c181125441c4c4a0f81c43c9507034020490003800d00d98540400b0750100001d491111005d1199a0200400070340c1da030024058640741032000c0c0041045d840c000607020303088420150408591610b5a181d0401442a1503c0d10320a00718803a4000704a29281c40101500c41401441a03140d05001394140e04a420440c01c03400300394410403940d4840300e403010091020007a5031034034152550f22400402c00e41014100021b40602c10180702041e054208030207854101d80680080103925600c00400059480c19074111b80c20240260039100300b8203c0809040c1452000101e00b86459529a281c1403115002003030f40c038a607551901035501480706007000d0903021104a41c10341c1031101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 103673372 1250 103672122 103672139
    0x607030c0f0803070302040501020f03070b0c0309030f031003030f0309030e12070e1810060b1c020c1605040c0e06090603100b2d030907090b060c03070503040906050a 73
    0x1414006010301102003151020016115880c000055015050b540c8a08005801401a4200b801214094059403201e420500c3c000003d8a0145030070200610103501c9513185804680e10203000d00c0070501040101d80c829a00b428004e43c01600c01c103a00715107451a41c01d008200c114200480f5003094203006102000c254049030b07003444403108942c2c0b540c0c21880c041d940c6143ca900c0b9440315081c480b0030710402140500a803030050840603804c0a444804001c4e4003008102c43c0b02c6e00405007020301c01c0c0311000b900c604038002c4036664140071400500e0000302d403500500e04a1040010300e00044000400c1c006400c06008941c020440c90401d080c03590401400144140103454485000e880080005240c40039408525001403c002c10300ba07548a656091407000514400044d12000203e030110f0402e01040504503840b03548a040039001c00d0f400c140c010317009000c0c80c0c01010341c4800140500c081400d001d0005154040c0303d0001940c0d21440d100d448400d0b03400380da00603885000300350410002c816 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 103674622 1250 103673372 103673377
    0x6022d060703050606090915041407080c07030306030b10080d0201060f09020a02031204080304050d090501080426040e01080c09010302011709100908070302070e130b0606070204110d050a0b06 84
    0x1c0c5103042c00b107416a15040441c0041c01010f00240e4486420340501100005201031030044071403e0324140000c1e10744210046a9500c1520390200084e5680005445442d180c00075141407403081c503020554550b2600c07120140c02e81526901a1943c00074420811400300300808441c0910030300080c080e452408440c000081d10358801c800c50281c0004005100d2403080c011a1021808022140094101070412030f1803500100d1342140e4610070b81c50030460840c000c1e5040012550169035101180d59141d895489100c0d18000300715030041c00540340c160840c88a000303000580710044400030103615010f18140b41020341081c40740a180c501c0c0050003d40da000030f1002d1410a8014a07002e40e81f40c5071410341c90501804041d94050b4508038150b020040800005c003500d501030340c00c44030341c00c2c0c4501c211602d0324415503048007016820b00000d4002402c01105c5540000000c011034101889a004a0f054a08003055402486c03800200d8010050041c4038164111500c00410400801c07198040755051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 103675872 1250 103674622 103674631
    0x604081f2721090305010f0207240f0204080a0b010f060c1209180209090f070918020d020d06030c0f12230d0e0109050603090a0206071b06022d06 64
    0x712405480c01041c051070801c02001c9042034105072000300034a800040608405010460740d650900f5001a84850580250358119410406c42c0041c0800513000d88503030700c440180406010348821440c1010350251000c3c20040c85100050499604c05140c800c6004c20b050b0081046900303200010301403070398810303206445e2544c070a1801c1e0740c1c0144000280c43c0f001682d407100c40796000d80c96050f014103406070050602c2601c20303510790102d40c40d82e40c07424500c03c0d0100e54000001c4c1f6030020070818200007130320f114040440302100518120b408c00620099070b215100700c1c0311a5031260000c00170080c100070788a00404d10407007210075050405160a0240358448800703080c00f22a9591500a890489221801c408111303088072000506044054500e8000024803408240f5002c80090030741440011a48241803480140c0f407d141c20313901300700c06500480d00a50b541403030590801c02034440454920050800307a00208031a00046020600c145500a40501d034030380c1c03a2103140351054000840a801 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 103677122 1250 103675872 103675931
    0x402030903041a07031d0d1502070206120105090105010c082d03040515010602011a060a03020f0403060b0405060409080909071101021b01050108070f03030c030c020604081f 76
    0x180e4803960441403840c06583c00080c0065085030000c01050700800003091002d200f0344855404d241304071021040c0342031102c10a034018460204d84800103416822030688103110740801410100f003134000c5000f540180781414918855140148050b107071607a0720a00400302482c0c6524010540e40e10580a03000e0361541105440c001082c01c400300d40008d008885180e00311800795124501400c1941c1d6412250f152005449080000400d04030f206000354289140c64005880ea903603500003d0040d207500c5041240101359003408900c05980d441c400400043d4014100400c1c0300345284200070817220050035407072241d403501502200041000c0180c80500d401258076511654803480282e44030b00390003d8234800355100050303042c003441e48481c526a500d000e4030001c0000781c2e05c6805443d41c815040c09056894100c00d101000040d20a1003100300c0f4a111f0b00d80113041110550109d40b150700a41c002200303640092248850410108498844001c13054006202ca000d50700180302004440d086c002c0d46 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 103678372 1250 103677122 103677127
    0x5040e0f07120203010b060304060906061e180b090702100c050306010903110d29150102031c02090d08040303180e0105010e0103090f0b01030c0906061704240501170102040803090402 80
    0x96584c20341c0101d0241c6006008540e03245410719190004104e42e000407541c0714075212011440070480002d9006452202124007815818404003540c65882c0324082d24140d51031f8201c00085403030f0510034500524080d00200410001203102c1c0040d41c080707919074030400c002482048451380c0c0c4010000101c030b8000ca020800515100c2c04100303803036000840542452001410201d414040060011300004c00804002e52038071000402c5c0c1c070054010b050307036006074010311810b002041c20440140e004010f9000040c944841c007004100b490088407800e070b620000224007001816089001c206c4594000700e848454981000c0c01c00c443c000043c000c10341000084215500582d009500100020b41c02507283c0c0310121341c0f80341901030700d01c090204071600e00740c40700c0010301004c0754000c0b20159421500c42003e81001105a104070080080c0103403110001001c0804a04003060040d0800c2080c000000c42c1c9981010800315681a00ca405103032560300c104002c05c25054040260ba030a040200c0d00581e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 103679622 1250 103678372 103678409
    0x40f020102011b08060a06050408030904051f060203130602030702010f030c02101812261909150b060c0613021504150e0405041a04030908011505040e0f07 68
    0x78010725400207103c900e201d000d9022011990400701c220312603c0b00f04e95518143c0e4a800c01220180114420611a0350041c00300d0010b9240907040140c1c003040c0200d0140e401c01c1c2911400801ca8800d0340b0001c0581c1000031178108100308144141c0c00341401d070009500d418940da000904811102f086181015500c01c12541c1e41031080c409103810030040c03030041c01504202c261004108028450031500c07502500c50ba40c3c2c0c80750148905203019008003402d6503200c1082003088000314001407070038100100032400110900c1c464030507070440c1c50240c8000410408650000021224040e02c0356108003400d001c400c0f0a16000902e1030b0307220209400da03003081d55803072001c9982242c204030307400310070355001c00d000c126034403140304400d0700e84035941c1d0340e101d840c004605000c00c403401910094500780a85080902e045038041c516900309200746401444955030300b681c03908491105084564102803403000300006c1c5080d0040d20103003800c0d100504a4030910f0310f04240d40c0e113001c1c401d00f11044004036501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 103680872 1250 103679622 103679627
    0x1080a0504060b060a09050307060206010f12021f020c030127060e0a080703020a050115030b0109050601182309010b09090a09150501031505090d030b0d05010c050406080c030f040f0201 81
    0x20808441c3c00740c003403602c90f030a001c130140507a915030142e14004c0c4254170000580500c00941d5030b0486050b8542004c1e2942000c400c1ea000008551050b40c0205074540d40c5d00c0c000492144061140d89039074060b1115028000416080d6422501214070704079042080c90961a1021414003c459000c040080d0140c0f12603c01420010328484c00742c44102c1c0850b070402410740100782410300c5480741c40204200c444000c894200700415000c090180c0804030010f00040d0070340c0c1c3c801d5030030410504000280144004c01e0741d070703c00c4094000000d10344103c00050360340307040042625182c0000721100e009541c18181d001e400c601030000d01da0301c22842080071070048c4ca00343c3d205601040c0c004040e2150340300203040040140c8000c0c031040b50f500f4440203c0004c10b050a101c0c0d1401040c4a4004d00a14000400b0440190040c000c00a50003103401e960000000c400748034400298420781c4540f034950303140481c01303400c0c02c0000b003d280781d100741002081400c1140a118690141e800b03c4040d60b2040d050004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 103682122 1250 103680872 103680881
    0x60f01020a0f03111204031a0903070c09150e0c031f0807060f0f0201020c0a060519060e0103110a12020d0614190c0c02030a06020918070e010306090b01080a050406 72
    0x103402c2c400da50712184145603100600500e02c1c0100b100311100d200280700c0d2001d0901c101c1c0302c09003402c0390140c07404c54207200e02c2d0f0344603411403107100071641003460680f16511880d078140d12001c071656071180f4089440740038280500c01002080503070180b500d0131603460429848003d02e107a8411040da80440c00b0104c80c0103203500501450b41c12203110a8171500050030b10500302030701401242c40c524bd00c4c4110b500c140202e4142081c070074040d1840f88056601d02000e000702421098800c02d5400d43d0400b040d00764490300340102410b050303200c095407660402ca8074611048100b075025500d5102c09210359481800c40c3e51450b0740c107580d10041018641000c20082c140ca600f10b4140511407428010782c11410110780c2c02c0e404082c20100704480002030240d41c840b441010094040c1c01142d451004a5025030250011802c080c00b4070b120701e051841d0402d4150700450300c400209500031740c0c04039156032612075a0043c11000b20200075120360040042c3c5440c1c001040c80c00d8050f120000502001038030f820 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 103683372 1250 103682122 103682143
    0x90507080307052a011e110102070f02040f0204080703080f09060d0506150307091a04050901030c1d060d020402070c03021c060509070b0306060c030408060a0207110109030b060f0102 80
    0x40d2501c40081d40783c060388881c9084d01a40b0503845050402e0629070304051400c2a058050b11492403042c6242035881e5400c500101c100d0502407400c6080d42070a070280000c00c00340e03200b143c0e411095030035481048203c070100c06405d07110341e00c18030061002c03000c000740c081c040d243c0081005072a2152820004021b12404600c00d80211001c110300c0c05d00c40d19604294069202150481d40400d4602690102070008490a10000e82c10031400c2045002c580e255002031110b0410301c03440e00d034844000c103c2650082e8002c8031011400e800401c40c0c0602019030141000300c01076503021078105140040c203050b001010281c401c0c0d9001401078100320328042881c0084d94054041c5403003140c10843d0000c10f083c851001d0303800710300b040c0003c0c440910110341d40055501c3c4c0340b2040d00f5a140c40e001c0c41059004050081d5180c0310411010078540c20403c0708520400d806c40300540e0f10509490320f482d11400380d0781c02606001107420705200003800e04011507400b01041c4c58000c8800e07442d800403440d00a103003e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 103684622 1250 103683372 103683389
    0x902041103060f030d0509010f05040306090b0105150a050301051521010602010b010203040e280203010f05130b0307030303050a090614101a04050402030c04090c090806101206090507 80
    0x12a80e85103004025511881d070488000181507290380503d601c801c51070044500058080214900035270181501c803011516900c0c026060584031f940d900c0407215501c0e81999020f054100401c014070b0006040121400e049010034101880d00f40c01800318001800f0b201c0c8610088601c0e0302480000700107030f41206a000713401c0307201c14035101d0082c10031820a0050720019420149000d2642d400082114221041507501c1402c581e50003014203464980d03d10f03202c4c600c10b100e07804000461172038009507010b0200c6800e44841c091074041042080d040222450042e01e00b0b2081d002d81030303038022031114102ca0705400d0102e4540d0301d10514100404c04440000c0020703160002c03400720304016a5100784554030342004e8901c0a40c4405120810f1041003851322944c4100b00001d121604080d00a1900031401a4016081903250000c2d00700f0f5881c1101860001010b806080100701c00800c0000c1e0000710481a500c1064108025422040728010001d45220f4449000e070040000400c010801000040b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 103685872 1250 103684622 103684631
    0x703050a0309060221220609060207080705010b0112060b0307110f070807030b010f1203050c01060e0f09060a02031b070c0b0307200d0c02040506011806020304030302010e0d020a0f0501090204 84
    0x103885c0c60450b07114a07806000303001001c200080702241ca1005c212184198071112001100680d0f5640e8041c2c2152042200c0c1e0540a100840001c1c680314040c0403d21700c58030021400a4050300014088001c1c1e80343c424015082460800065000008480e040102454603c0c07040c0b8414204910300030440208074424400c00a001030011408510b988c00c0e80d201e40f00003034860740d03111920a43c0d02c0e081d0040380381c000394042086000a004100401040c920341d4000300c0d0f0241e940c003581502c1070341110325940e589100d404002021200744401507201100c44011410742c10020340d127495502c0648940300c141380c0009109824000160b40c40b400501c003246800741e903842e2803100201090013034004001d2010000941102208001c611400855540d98800030000d440e502008040c110182041c0d042c40425803880400b007082c0c20700b15002d0040e54000b99601c5285142c001c1c21104032448120046e003040843c24001540407400382a01d5402940c503440b102d0090034202d00601c107008000307600500c1c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 103687122 1250 103685872 103685887
    0x60301090f0b1e01140a0b0a08130f0b0115080a151202120706020c01022404021c020301090615090506030c060a09080106080a0201030513150509031e07110102120703050a03090602 79
    0x201104900030503500810502d1f646d998160340c03030154a02180111303001c2000601409400038150074101e00403e850102401242c03a00180340b0820b07000160942c0319629007414850300400d040780c002c81d520a0030001c52100b0701c0d10780e610355158011000b4008600c4020000c0d0b581d09000d61445a000c1401d507540e05603140c901941c4d400301680d03111b025000c3c0c000c008104a4441a8010081c01e00c889266000e81d101d5007000000c0c01c9810b4901e808800d051500c2016880900c965090744e44501800034420300e0915080e1030106160b800000598201020800640c801040242c030f0040c054403203a450305e8a003c01230700c2842540c0c2016450b5842c1000000f9542c41c0050b005126600032780b41088180c440c4801c0c07110094030300390042c3c490a044c0c2c0e00c903860380c9141d51009610021174404e49040101499407512803945112545200320400b04d8000c0a0010500001e2440030f0240002c1800c203a681c0c1c205840703800b440101506010b0701064800b481c9002c6d4021070714455200302c04540d100c58 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 103688372 1250 103687122 103687139
    0x11030309060601080702070608060f0d0f0308010306050c090f060f07050a0f020411030112121b0303050415050f040602070c03080703050703030b0406050d0b0603160b0c06060301090f0b1e01 83
    0x40c2114403c1c00101c903080828a01400400e0440907a0b40f569204a1660740319000e03c00014200c40e130958100c59040d80c40b101049042d07064410080c400d60301e0120715403450401600f0381e8405007100d03000000c10041854241d4503810560b50394071050715955165130090443e640c0e40d002c3c0e800003900d94051a9200c10811200c10100e5a009208a0b02000240e091030444980740c0030034082c81440c040914000c402043c02e421541c0d03a000c800e031808018140d21903124188001d4176400c22804280c0b10310a100400500c0b6007658403400e03400b0300410151401c5624420000d42c090710207404c2542c00510300091284034001d18000d107400650199648400303141c002c0003a40a00c80030340019107050344020292a1030b0182c54112071000341042c0c1c40c65160344a403a400c0300d010b4045030f403510802d41c8480125800318991801000c0320700d03030151105004d4020302d04080b0024811442645002c0d0103c0c001008480d600e28040e4010120000603a076442044110703800d014002600150b205000085000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 103689622 1250 103688372 103688383
    0x6070219080f15091527010c030c120b01020601120507030f031d030a0b01170f10090c06080105150702030c0909060105040c180312050403060906090b13051c11030309 73
    0x2c8240e03070300349926641c13840050744420507000c4d40c01c25050950041011880c021114902140210383c41114685040f0612800c4404500800010035180c0010000c8603410000869402d00040300c01e004030502400003e444d904140a0041c2d02c49440401c4014860100a90800755070300c41c000e030034041c4043c00d0103441c0125194007102d02901200400c59141000f1840014455011800c80d901341d081c41e00205050303503080c600d041c0320301ca61860080401010000e42d040f5040c1c81000041d42c04c1d40c0e0405038252040f0f0f1304000c00f800450030042000e5280c0311028110b169007603040d20b0b1103030040c0c03001a09154001c40b4003a4003540d01400e01045440101c0c10604070740003220100120401141f0986000b020001200d51400c40d0382000c01c00301d50060545102c101051501da4906078032940c2d000111842c0100c2070350442da8403103100c010010321700c44054200d1041d50582a0b099000ea81c0e081e80e44583c01115158092a03502e20404140160161220703220003001350780c2c032890040f000c21350b1031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 103690872 1250 103689622 103689643
    0x80106140f01020703030f030b091005030607050309060a0b130c03050a1b020a02061b03040b1306110c040c030b040f0f060603090201080f04080d0905061b0906070219080f 75
    0x1092400502503403420070010441c0ca541a00a1301005103180c40544850f010540c29006258469104410903960740c0e01d164030035a0000030041040c1d080c40240b5251100051480781030000030400d00c115071b0400a85c007680203841013408071f10100c4920100b078012507e051005050790510151258241c1c042e0041803007654401020002c401c0306c005e441c4e500710303030141c55070025800c0302034140094100070008000c3d20030000014403428480c07442d40b629542c46035000350080790b00841c8103c205082c42c0c4510f4018680c0b8500001c2410010020545414020042602c00c40d0345d01032030140503010b9000a849110700a008000e4402882400405030600305550300b221441d04001103100c40c000d1140800c203e8042c0d4800545940703881c1c4c1556900c001410607240e030765040c01001741d04842409280c1d1940e2056002c0d03c0d0782d081400e0b40c05620511401c43c0103071182e0510080c01d00b501d036507064038442c80d0101c80d2070307039000b401204406020720290000e9240e4000c049446501000010312032044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 103692122 1250 103690872 103690889
    0x80f16120203040506040306020f0427060501021b040f0e010203090c03150f01051002030d09080c160e0c130f03050d02060c070b0a020f091008060109050a080d140c07080106 76
    0xa03010038040381c80e8402c80c018150b01403000c2c08180042a050b602400d298009a601145082d0310b59809145406091580342c0e4001c1c0c02003601072915056000d17603402800203000a044082c14039590074032002a58143c280140e59901c88111244480d0300201494005480210343d04d0070714824072030300c070402d25409034000e00c41c22242d81400d084480c0303c1c610411603070b4146c640503420703c2c0401c00c50121520b400c40c00c51000780f10028200d0b126124680d000c520488100d580c4040004180c2d040519082c440001d8640001301008803000e41044903505c5030907001c1051b541c0c1c0c115940e2010160442c1c01c4000740320380300760b00070040020008a0a41c205126001c450465a51189020091080200041001c1e560713034041103003200759802601c1c119005081c05400c16161001040c04081440003010010304404140000c42d42c00004180107480c2c1560a1940e031810800810364a04c5481c19040801102030011094204100140c640059140c0c080c2ca818503509d10800e80605998020041d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 103693372 1250 103692122 103692143
    0x203030105190e0c1b0303100f0504090b180106030506090703050705091501080604020405090f0403110307050a021203130305030c10020c0a0b0a0b06070b0103060c030b0319080f16 79
    0x4010700b104916008032900100710031959900c441c44805a0307008a1403092005a0780c2e403d4100021782440594410840e442440401500e000c0e440b00c0051a10b130701c0507015620f0301c0418004110102ca0f0f031580718944001c403203194006202c1440c01000aa40041c016010f14014846100000701d034120071207016a0441e11019105e03410042d5051061314034014001d03a1442c00102c55019408070b55200c20020001801d199035500898801402282c0c0350308403519000800c81010b0b04151002c0010500380300039407c0a1582d46e6007036890307003031403c003901c6016003107603c0440c50001c1086411000d81904d0300400140d407454842d95a800000191905014502203103504114038030aa4840700c4001c00180f80b07035400b64441d0380b400140504420010754a4849404003a22032000406819103c3c510a020b01d6245081c0340e4111891500740408060420b444004180d0f00061004490304505100c00c80e000c04034500659a0704c0f83c80c0c80c54034200c0002c200b00c40d090304900304200c1054083d401c0c260 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 103694622 1250 103693372 103693399
    0x1b07091d1b0d030305100b04090e0f16090f020706090b0901050c12010608101a09150301050a05060d0f0f0507080601020f1f0906020d0603031404050604060f020a060c0203030105 78
    0x8040010451415048807030b01d507501d40881d01c20f40041c2c0d0072010340e02180c209582c84840920b9240d004c3e412450129443d25015100c03070108215288401400340007602601000b41c0f03e82400350743c40d06c51803140e1601d80c03602a107002c81585c1100d100c1c5501840c1009070b8000c0f841c00800810045448c50900d5292000051408503183e045900b409007403001c050341d0303070b013411400e1b40c43c02c002910490307005000c40750100c1c1e101640443c802c600d0400d03280003034540124004000c1040000030980218520030b00c01001103440b00f0050300b09942007160310075221500340b50f083c8000c0081c58032a0890b942419140c111b2070b0f510346d01841c01012240c0d500f00f01c1d0347e2400700580c0d440b442e0a1a100305a44143c4284842d1030407400340c030822107256440460080060b4541c0c4042c0c0c1c00516640421a40ea014108209074000000501910f81d0076a0141040e24000009a6074080c0344103c405001c108170894081ca40b0901980d0b00c0150711140401c14480e680c0c40c003e69980090081c280588100000350 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 103695872 1250 103694622 103694653
    0xa0911032b020c0102060c071e03110c04020403020a030303020a05160b1b03151516110406081b0114040510030608010e010e0601030f05160602011a12031b07091d 71
    0x3d600400040e0002d120b00e449107070244000350b200040940c0c0d01d9003001020100e0340c0703401e00e034018400d02a5a17008052800e680d2440e0410020451240c4103910400c4100300585502901008483c0c150500603154a41e62406844510860309425101c00508001904001004000c0c0380030303d0300f001115008c680c454414014a1005070340700c0492500d0740d03520102604c1c0040148450303590644409062030b2031108020b03600103415008407041c0d01110100d4070282402d2180f40c00a02c3d03104d008182d44690101d0120310b00400d22843c0c3e040080000c02c0c1c0d690124070b17104943c01840003402c0507100601d0500010f00070001030007002055400d040c2c100c600907005008510a00b4402005401240d185903504008080228821901401010701d0384050401c465210401801c15030008035003480000c104810104101e0306440c85220800008518200b0000589107565940c400c000d2000b80207002051405035540d20405001c0d003017a413820074454041805260000113081110b00283c6200fa94 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 103697122 1250 103695872 103695883
    0x1303170906030f04080c01110301090c0e0117090c0d0f020405010501140f1c150305060a020a0504090510080d120b0406030b070c150516021b0105030a0911032b02 71
    0xc09900000600128500b510b0000700150001d21030702c269860080901200c900391610302c22519003a05000c8010050071401d8090340c03d010100307141040386500c2c1c07000041c2041041342c002e002c2410000e00004c580002c03c11906c0c0500100400c0b00403070010500c1c1c4a1440d4210210490089085c030340005484d501070b04030200b01c100b02e011494103000128031012070740c1c2c00036541103071000400e002080740c8601510030010854025400d8940142c21803c1041c94018060303e6068a6441000701c85e9150303500c0425181500c01280c801300d19600d6050800c00424400e410128a41c010f22b0713001d41d8601d4210400280c4011070040901c1000010005c020485a0034400178008542410010780754510903105170a003d44603502d822007541540b0428811140c2c1290f03034150342c0381d400c000000c600b40c040080d4a051030803a4542201c0e1044400000c066000c041c01078140e83c1d881b01c0000042101440c030f00e0751502d00240132034111071454103440c1c02c0300f420402034840844c0e4850740e0b200320f280701058 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 103698372 1250 103697122 103697137
    0x30503070908070312030f0c0f1d120102070b07050c060720010e010b0a09090b0604021c05090703110f010c02120304171c020604030504030b06041103151201090b06040c1103130317 79
    0x3681d41c400c035954070040d210344ac0781811031603030385440e100d580000380e0340c0e003000c4802c03140004c00068580350385160002400070003a0001043c0a070911281c1400b12000440e141d21403030a00d0420300c0002d00c9049541002a000c0a540c0c4950821070300d42c0641c441540284404001101c0c1c0510080d51031402404981007a8005000e44021000160150030250018101442051072071505040d208480004032182680c0440280e00480750030400e100c1c0340310250400c1c4408880990001c60700d0000600941c9074008002d000d503908018600e80850140309541c02403007450325842400300d001c080d00e5103610100596909040c1442d28007054180300243c420312555060322003d1070541981c441c200800300c001c00180d0303ca80c0329212000030300c1c81c4001550040c04010800d0045030004d204101796108960b400c2c15040c6c1c0341410850100380c4580b140e5030807101c1502d00290750048802d003103983e0704191021842c1c0f4800010440b40b882140000803003100d00511819071030030318400c1c440c0c002d48100e20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 103699622 1250 103698372 103698377
    0x10020307080306010c0f050c030123061002031603090e100f090908130303080403080f060a0608040f05010c050706140c0714010e0d050c010608010513030503070908070312030f0c 78
    0x440380008145200071074002005040642052650307955803c2c40303129045c401c54150300140c1420711907040074011102116181c0f240001540c001c4d0a00c18080c540080c003040c401c0515100414009000788101c840820800703031402d0240ea52030801401d40c070707840e10a00107444803080005e11004908049803003039810800100307202c0c84ca40008c48018081080003921003000c2007018000c042e2080442c03a0046219403961203542c41c0c281806400d040000303100d603c00c21805070030042c50307944c0d071076403242620554188100d003501c031414506050b0120b0351004019601e07080c6030345050794000016051a900c20202842440b40411500348a21411f88541521842c148901d030f0005011110100110f070300c1c0000061106441900303d0b113032418030005c02010400c0016a45451032080c003411015003182e000a020b40d0516840c031201013001d40c2c1c0c000d000c011010010a280610680d540c00060240b10104c0e940f09072607050501625400d0109003000c02e02d80182e60000084500414100c00f9441c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 103700872 1250 103699622 103699627
    0x301090b0a080f1c0e0409030305010503010c020706140a0509030613170910080903120a0b040f020304050d031136010206060a15110a1b050114040306090609020306040302010c0e100203 81
    0x82400e084200410f00031041805a880082c2c081900c86d440b038070181c4c9009540100f4154504024582141e0840c403180046400030503060152070f070450041c03440810100445a0344000312403044841c0d000b00d40c40540d250292005002e000303440030354a001900e004004804248a44420111007441038184440d002080c9040c1d205440e4082e0401503400140e45098901d0501c0982000b02500001c80c0c100303540a99402c00700602d400e00703114009010000582c00c6145081640764240c2c0e540710403040d4400c0645525040441650802c160317189403540341e83c01548428200c0240c0440c0603501444040f861031001500d00317540c40040e009010b00b002508100581c3c2c20085061040050781c0400814018680b04031040c0c144204420f2207064010310206446280c2110700c0000c0c2c10746588070034100540110420200d9100d1001c48040b00c0c2d01c0440081c0300d070201e24240c40902802600650f060040101300814143c0640062924040f540d440307501c0c480c00c2c101004008003010b4103050042c0c0c000d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 103702122 1250 103700872 103700893
    0x14040b18010501141204060e0c040207030503010b09060906030f0103170406080f0c16050309090709150c3306170c0603040f020901030c0e010602030f0f0304020a0b0301090b0a080f 79
    0x104e500031103808070900c1c250301c0c0a02985403a041c00d00251401c5501c2680c0d0012411070080034440301c1c2c012102224150324090711510000d01c40e00042c001e84910400004210680380d807071808480d07581d50050190350700c0f803411480c003c0c0e07001024401994861056145084c854010324102d8081d40c2d420307200d0b85410380b9500d21154544500421a01441d841001006d1003d429078600e10b10a9125000440d6133880c100240889540040e000c0e0040c0440d034075050280300400c09948646c83c000703150078170394548181000c2d021045801e810078004c107165840704940282e01811154038035607031001400110b6450780090060210310146407040e8008032600c070303401d01d0030b8402075400500554011006100030307000690381d81c90a0340700312504094051700308114151840958014072a500203142013100900602e40075110302ca490180c0c928001000038119511050b0340c8003c0c1c5400c4000a4880d03071260b00c000003c000b401d11b054840c491403c0300040c10080010000b060b00d242d00040c0180000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 103703372 1250 103702122 103702127
    0x602010b1e010e0301110405031605090408030703110406030b040c0c0804091e05150a120201020a0609060e010906061a071a040201050c120a1710060e03010b040614040b18010501 78
    0x4500038441d040010410804059130380c00d000f54010807510840d4960b80794030303020815142c1101d00341c90010041c1c194208002d69039440b040c095110b03811946084d62033b501c01600f1402400440c07440d81400d040420045602030303140d4899807020b80184d5040043d02000700b404c2d18000a618402030211313804002c140324000d0241c0002c0d101454248000c908003004000c0002581d01c1114643d0303400c1110100041189081d000c40c4009040700c020100a8034030740d400003501c4028445000d041380740c0310702a4a0400c08075600207030802100000810030f015031450b00350050105885002075581c0ca1880e1484480410343c201d42046a0102441001e9a82d00300140000328000340281e06002042c07043e210301e60f030140001a40c00200198495450301c404034060b00201c400251150409504010001030f0085c040e884025034010f420100d400c410100b0009024041000d070190704181003900018507148600d212a07180002206c0c103020202c071903005d2024112000394543d02031205074004015650 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 103704622 1250 103703372 103703419
    0x70509030a050102030108060a050f040f06020f121003030f0203090105041502010905031303050d080103020913020a08030d0f06060203090325090e030703140a09060e0a030b040503030f010602010b 86
    0x10005000e0728100706a6880d0142242c000364880300341500703c2810400381d88041d20990350b00c4900c1e0b114080c01403c15807140320485c91207000042800f540040c8060003044080281ca008035034100502030b061426042d40c8204075210b11003100490712051400041070b0021058a8041206950303aa0605261007040700030f1001d00103031181036550700d6803c0d00104800380010038111214007401c1680c18a10718010b494102c0007030020041041500051005036a500e450680020310960804000d031030303c2c00002c0c0e9030300142d400003800b844005551186044240c00640b00411801010090070783d64090a9032648034040009505400c400303100034016009981c0c0305510610500c3d0300701c1c0e0035101c0103120220303052010007541070b070b0001c82c0c1c80e02019440f065210341d24030302045a90504014960182c41d140c07450044106001340142d40700c2103030b190719541000858129450000d0382c102130a00700e849600c20341d1074080310784110703002080309801405011110700b000352800064803411513040025a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 103705872 1250 103704622 103704637
    0x110c060f0c0d0e0a03030f020301050f130e01020a080118020304080703030e070e0702011a0406050a030f062007120c0206031b070b1512060402060d020306010e151305041406040e160905220b0705 85
    0x1581e0b1980303b6000c00200b440603103541542a251101c1035414800c901c1e050b03680807450850010b00410070000003d4540c801d6481d1550b0504001c14805241d45140e0301b014015005000e4885d0700104002c0056070540110004407100c1c5951a03145115100340815642c1d0380c02603a40198130010104006050490303024116409002c0c002940002e00d40c9104510804a000c02c51948002c0b1b07402c1d09101450308500310049030760801003201912a4081912800008c00b00603201d401c41c05801c010085801c11541c40c264080e0380407140d0b1a10000c160a0310090b803920034054201190300d8000e04400044079405203400074480b60500c2b02d034242400182d4070081c040c070304000714000fa60708680c403200ba05803200e02148076200d8507003007803415416840e10594000e40c030031401e11002440c0d08040b101080c0d00040140c4001c140e05006031055031904040c03030048022401c3e901c4002a81e0312a90380f00d54044c8c201018810503110340300e14030312101072840340064000700c41034012440b528003a00040650 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 103707122 1250 103705872 103705909
    0x40209040206070605041101090605090a03081305092d0702060a021810030e060603030901270b0d05070f0e01020c09100522110c060f0c0d0e0a03030f020301050f 71
    0x1070440303036640c1c802905e100303940c03c1715814542d5441e440790350380000f0100040c207218076156043c60105400900611030921002e4002c040004070b810728503940008510243c0009000401142041c1400c84008801c11100c510740300c5000a101c002c450030013520b039028038000c0e4001c0178103488200b00d4500a5000e074101d207000407e2507071035014640300c1072400001c0d41307420303140000e081c0c946109445c01c1200007007030544250410015408c03da80c026600710350300000000702404414124483c0c207030070300e60b40d000750014010110702c1540002d041c2d004107204a403035580b0400e401d08098425111000800700d981e0150708110000c40d2075041030200d040e4051a040503c2c4a015030362804524020b001f240085511070070307003006000c02c0215006c1c510f00002c0702200c5034a014000780c0c0c0540c4414024101c00101400c00001c00c4c06040c1c0d1205a031000c80ca151810013042e5100d56545039170744102041100441e091692000a01c4600c0c401c0e203040302c901510100c0040c2c824420031180d800304124048a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 103708372 1250 103707122 103707127
    0xa030305150d1101030f20030405011808130503070e010b090f150c0c060f04061b02030312010608060d02030c0607050a0b0f010302120703170a030b031606030f02040806040209040206 80
    0x1640d40b40342008018600811120403400c1d6508001010307158841a400d6040341485034010072014204071290859034810191503e0780c0795445e10364050142c2a070001345900e8500307540c1c424032170901300500589400380c10403414244c0d80e805040e00e80c3d82c1440b6031000c42807250700411450240301e004190042c8001e0039603d00c40504000605500059160502030007000f0504140c40c400810010040c038000b12041814429000d21881d0a44078500840c030800244d01300d01c2c20803000c0001100142075000302580d8984214481c02803104001340f28250008185a010420504200c40307070b0b003242600503024101a00e500e40a004490340030300c00880d018440d010992010440d4036035900d0040402a8030b0034465459401001394680f1507020850407900030102c10400a0503692500c200c034000c00c10180d454a4000c4403d80c0208542c80501e5054019188031200607001301000805070349164400304085680700300624124042e0340502e40995110300301190243c03820b80f0320305500610040c076403403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 103709622 1250 103708372 103708411
    0x40216060501140a0801060b0d0e120a12060506070f080a0905120a02012c010305040f080c0c190308073203030f250c15060806060411030105030a030305 67
    0x302100c4007640071001078241c1603450259481e00c04103100051000d500280016810180d02d8452031269900c41705643c2d9071249030009500090241c5040c440703a00901c151136402c900009450034000f0181a0055490070314003082c146410300035501d6650304440302d110f42e070280e030303035070720040c1c7d0050110380148405840c0015080d900d20602c02401178a102c0509035901591001621624081c01d40340d81c403035a80c0003007040100904032407150003542468003041c10b07151402c0801207001409801307422480005905100d02400203010046d9241c2030b10540c42e0300d400503070004942400e90000a0910380c0400070200030507000340d1803400604140400c00d0501ca0809094030032200c0340d01a10065401c04420845145414119141d0120320088000d268a80e030041105c186504104040c091103002060305041c40700c01e41586c2000c150307031002081905d880d424116a03071402261258030503401d12003060072404802c000e5074100c40d0041c00510413a002550180d000d0b040007404080501030803207844 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 103710872 1250 103709622 103709633
    0x703050708070f2f010609021620120d080106080c0a080a0e0304060903062004060305310b0115050a0804080705010507050702041a0604060c140a0b0f0106020c0d02040216 75
    0x1300c2502c3c610360704c1051192080c0006a00351b60346030707000200303aa2051200117144034041d12408036450341b0460001c50407600c1e110b001c40307000d0402d401c107401180e0044601e140407400110400e0f2f41240c0e840e811400c1ea40e8003800c0b02e2207281200c02c1c0444410621840b00341c00c0c0901504c070b42012020001180140c822680c841c0f554219030321080001c1e2440008100340503551140460340c80c0f44034080c4816070b1710390428030382e0340c070031486102d08165075400001e03640f550b242071125a510301107880401c0c0d5003c40580051300c20081a09455405000c40002a000090084180c2500c41902e440c0d00701042c0100c2901c88031001081524081c008001c0710f4000340f4280704185c454606601d6081c0c9403951401804100da04031100e211011440c180e84040302c2d5550803e0390300300d510914248006080c80d25044ea009040000034520501c05d5180a07400c1142d041c040c6841420b9030341c410940d60b80e0b2040f00301c0c0d680c020807000756041199800154050708154000342100d101c000e041e000c10031810b5481 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 103712122 1250 103710872 103710917
    0x40e060913201f0201050124091229010503010f0b0307062d020102190e150d11160611030403080105090406020c03120714070b0c07020d08030c070b0703050708070f 72
    0x10400140d46d00c000522844002c03085244a44414031400950501c182c000504045440d01460400c2140c0c0304040c001c12920b010000071141206440c03800c00d100c50341018124020030b0150354425400c241b80b00b24024814458400e5400000740100383c0940f802c00103035000c14481200b000580e0400c2a00c450000c440061100e641010383d000607a00d503c10040400b034040980b81035400c00c050b2507446100c1c2d0f074950750503501c1503852840c041c1d41c03900d021420000074144041c0d07a640060700801c2c3c0042811203030034100111402380100780105c0811611424040c402190300a01281101f001800355042c041d0800742c0c018070417000185030503040c0844600c0d41c0c0000324040d006038400010003005550000d00550170006114034039040c61051380d030340d101800004000300c000d01c6010441e00d0956a0304c2e200070440c0c07500203d80701d40c2d905050300b145585d81c0c8012401d075400c5500c840420314031440392054520991507070307488401da603d40700400c4900188080f200c4c8100510300300d44800c00b4518120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 103713372 1250 103712122 103712179
    0xc02040e011d0607031103010509040b071e0e0312120117030f12070f023004090c02060a0e070b030627010617010911040b160503040e06091320 63
    0xc02c004c2c9090031000342921464200e5404400d030901c0100700c07589031595800d802951100008a80766a018030440314004044408000000d01d801c05400e0150840914035440805a00351041d0385401c41d01c1d80002d1240c50414a581c02c10140100104540c0b642490700144c0110b003035a1400f07401c2203c4c0302c541c1e0001c2c420340d542c00c5000e4080c0000b9035005944c40d4422070050001c0c0c800304c428210080032604124a22020120010074050003442e0000211000747c401c500d0f04221410300180e0003980d403407044508000e240d00c0c1c64220050705c4400100e0358215450010154a1503030fa0409003c40c01070030000007401d4841c55211200c11144403801140a00240e0752040c2e4100034200190f2020380060b44203400b5207180c07002c032404004014003140d040d9014054100d035505000409540040c0e11080054001d001c080b80116a10402c00c40007402480c0c12200c1e00000d49600020880c00900b8800040001c0700500c00c0381d244c00e0341074000e00300314140102403070341c00d442e000043d40400c02a0391 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 103714622 1250 103713372 103713431
    0x40504060f06030e0c060405240a210e06010909020123191e0f11060a0c0e030c0a09150807080d020601060c0308040206180301020a18080309010c02040e01 68
    0x9000d12100e0f91500ca00c02c82924014010850800d0400c00300344648114052140a4001c4c0c11054a03110081450492006507076513000d41d941c1c0c03814000818507000707194544185e04641009900030401c40c09081000c07136094002c0c02940c2d2801580c0350050147e410100d05112104040894400b0080c04042461000d030055a6441c2c51407846031541a2051904405103c20035044c9a8070040c0d5103110b1841f001141002c1d04e14260010b800d45420314001c5010003d44039000130410515490b070004404401c040e210034104180300000c054983c420f0070380c181d4000720034032802c2080d41c2c10780d044405010007140400b401a61500400c50400c41c903900700c2100c40c0d01100038003030300b2036040000d240144102e1130407882030326440d80c00401c07002000e00082e22a09012410000c800c4030745c0034003845600000c0003150703921840300f800303000150258a12402541034800021301038101008413418000140d41c0e070500c8515541c00c00000703007820802c1c03803210343da41c0d0340728210130240b003480c24407903000030303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 103715872 1250 103714622 103714649
    0x2d0e0a1b020601031101090e04080315060c010603020a0605190c02011101111b0105040503120a0f060311030105010902090a0302040207060603050304030c0807050607030807080714040f0816030f120504050406 91
    0x18184480c5c81a450401d203410010000410454111002601c0d44c200c1c1e400340d200e40d41c98440000d500401c00b000084240d02c00c3c00061511003034401584501e003102c0c402d96100c1c1040b030340d91400307654500074101e01c0368811000c4035030494807a1003209007070307030151050400c001c02000ca000c960782101c032481c840d841c0502c3c000452852031741c42c250610716516600301c02445185400e030f80311900c81c09002041c014010b0350710040f40f099441c60f017112401305880c04080294680d2820040e40780c0c14036600c12402035207010b0012501c0c2c58680201c40d40c4000213010300040303914603401d10000758814201a15080d644900210000388184000d100850280d21010107603810008490304100b11644440e00c5024100300d000c00182d00480400d52201007420124059031360400291103012800348401c0078180009000708824041582c8101580e0b0740004880000f400d000303d00d0320545441c080070b80340c207880700090b000142041c0c4e2481d46401c000d1901078103090b600da0204003511100e401140c8444d000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 103717122 1250 103715872 103715879
    0xd0504170301290f07230105070305150d020108060d030320072d030e030109050f03130609122907030b040e0a02090604020c0705060c06012d0e0a1b020601 68
    0x307042c003c40843c0e40302c1c4080b602d8241d0425503440b19208030a001002041c00a000100c24601030213610850703490140248014601024001c00a000403500704105246159012801e800d140513040c10303583e41a15580c6403a1621030406c8041c1c0300c1c5002c00c908241c1c07511400d04071840e02c090030000c03c81018500782c0c0c48910614004100b055410340b0b0b6151030f22100c094102008030206450607087d01400c01c218030001900200c2d015000c1c510000d0114411503001010500700040105495401d000b0003080b215101d030300403207204045104000d00012514201008070307075100000d5507041241c8a40703403990500c141c1c10032201c04c0211002400709985480054290429016100c1c102440700054008085107600003103140402030519406242c0c08905a07100500800c2004080c10004084c192500206031050395118824040c800071a201e0300200a4a481c06080c3d0140148128092179900f5041444441128000078041c10005e40c5402c9409613040903184101616030f259806410103605 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 103718372 1250 103717122 103717169
    0x60312020601080303090c0d020105251b050a090c0201060503071502060a02030c0a14091e0a0905040b07080907050a0801090b0121110303090a08070e0108060601050d0504170301 78
    0x1c0590050b032540d0410000c00c1480340002c64a040021400c0301e07401596005400125520b00800c031140b0000c8500304070b1030301210801c00c45409807910511514241040d45d641c1c681c03080c4054407a507500304290920500060080340c01c0905800014400011129666400a807601c2480d42c084501c0c402085142204294181315a84e44444200000d500c0d60500f6203000289100e81078003202041201b924101c1070110400c00c64401d040010080c1800b00e80c1c034202110514203c4801d50f1248114040010300440b07240242032155402c0384a5000030b680b8030005407050940117102c8183c60250a00105e019074804a040001d0300b6032000000d540c28052a100f244040c06800113802100c7c4c1480603c1e007980040701004580e5405004800e13190b02d05000306c0d20f140982c0c0ca40b1580403031010030204103420001b508004440803130070b030148a40d9a81c952941c884c0b000b901c4c42030014800700550b01c0c0801490b0001c0303402c02c0c85200050f501d02d8900080e00d0864000780c110000b64280503005921564 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 103719622 1250 103718372 103718383
    0x4030518010507030f080603070f1e08010504020109170a060c050306040b0f03060c0d020409050c0c120a050412111216080c03030711011806030606140c1005180106031202 75
    0x400030b0910074504040e030384002e0f060705103104c0c4000800c0301c144005280d0303880a02079007000301540710002c01080e0325102d4090b14407481c003000100101e1802000200144140a11800341744c068454208a80c1058100e00c2c1213142c0a090b0049446400e001d02d00140052041c2c070013101c0d140d0307160381c1c80b420000100401e0716284402241700b4010603622440966010840d2030b0001c600385da0076540c0d4a5500c601c000640910707402095200c1c945010890384091400c010000c0b0000c1d03d003564440300f09108802078900500a6a000082080c40184600840c0120140e071003406043d00184c1d5180003400038000c40c00790300300070195030403081d400030b4920035032600c01c400307445407401400c44400390300f0200b41c1da8001c03020302400b040040c80c28401180d001d5806002041004078000c00b03c25203d4002502420003440740c81c00140c0c4c4c00714540f9003080c0c000152564a00313842c004c1c1c81404580318400c4042c24001e480d141d4103413040d003d541300d003200074400c10300194418410780f07008018101d0041c2c20207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 103720872 1250 103719622 103719667
    0x4020a081b01030209040930080903040501050901050c031c05010510020a0605151807020610030201050a0c06022b05010b0304030207030605150a0801240609090b0414040305 76
    0x107a000009010440305201c015500c4801c1c2031a0050b15484e0340f0b00060040c00740f80c030010b040d488080031b200742e0600003015131484810761607440341441d00b101841100d8030042200c0c4403e489d041800300f80010b612510041c620400145032a90401303040c502039a003150b002d56520702da111412100840e8070310aa000701401401c1c1161400000c00a64501a48842070ba100050102c0d541d0000a2607070114140b180c90600c001a1401e814029041d01c218003100054585d0005072060500050385010010040740c262581079541c030b42000c00340401925545c0d81a44100c4910f82c003403104800c0c1030510a001c07803c0c02d5199044809030455051440d00f110b4040e00100f0302e901c030800070800801e0300000c180040f00d5001030009450b81d10301800350805107410101c2a171000f0b6801c070009501e9015002028892b05c0c0105820351400795140340c10580b0500c1c8505400300b0301c0403004002000c0190300c00100b010000c3d10200e02007046282e00300754000100d4045020a9020903444a030301e80390012a84c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 103722122 1250 103720872 103720889
    0x15030f0209010207050103050a020c01060e15100c080304031202032818140709320108100b010e10020a0308100815070c0b04030905030c010203041a0702030304030c06020604020a 78
    0x1c0c901580d000039102d200ca405524145929400800c1c00c8140c9a81229202d031011802045541c0d01c2d40c0910840c40f0080e0741040c1c2c86a1141402006454080c9a011440300d007601c1c0c110441446541d01d4035030303410040c415014401c0c1b0011403041503c640c00114410b030fa61030030707410709410346241c404a87c0c291a602e40b1040b40c1b4228083d40b400008a14100c4000e8024100004030403c0381641498065030780c20031040b460a180c078840d1f04100d4407400c02d615843c002021411103103c1c0000c0b4003600c80910549000d5880f81c0d041040c00141c0354002d40c41e100062410900204500020603d228000c1104a006038880701c10f60041c1342d40800c106803c1000c0d19280103116207000304050759503000d0000e0340ca03030808900c00b0401407402082c0703601c0801c0d4401d040d1013240c0383c6410090310000551051500a0103685491a4158404411242900c0d01103c48a1000091680c10b0300c0c47e40115030102d030188001c0001001141d60b040c0284028105e030740c0202642e140510500c20307c041c290b40050710 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 103723372 1250 103722122 103722127
    0x10c020601180b06041a1b0309010c1202010908070b01030318060f0e1309050c03010506040209010917070b040308040f060c0203250b0c01020d0c0e180705070c15030f02 74
    0x10420210761840400180b42c1c041124192240028050312803540030f112100041c44011408142c84400b03403070000794148492a04c02c2c80455126180d11407002c038980024400c00f08100050a1050800480401d500c00000c000c0200e596000069000480542d074048403c0010400c01d64013203c48204243c0c510241402d0030315000d4040e02150300012910140080c1c02c0a020550f264904a2900203414441c00e02106509050031601c90b80012840c1e4025400d09001550606141c007c9503641e110603517860042038034100ea000c0742c16604101c00740c26401200030000d0611062406000a14010604950380340d18100160401000503440582801805c540c01c901503078000c40d0901c0240c044c42c01c100f99808142c1c0c01810102c1780e58001040c40a4080b5605218040c158098002000d24080802030805200d009a480d10700d003800d0554061080c05002ea000000d40000da82c00400904265044c404035a840407001d007604c0c2c000d282a40c4141e445000d0107070381801032154a40c0c41c0303a002c40c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 103724622 1250 103723372 103723379
    0x4180b10060804030f14030420010f05090405130609030801090c081006080601020106090c020106030314070210050f0c01020403140c090f06010302070507050d05030715060f050103110705060702030903010c020601 93
    0x600d00c400041c4050700344603184003000d44035401b130451040d00c0070400e0f81050740c1c0d1810b4600400d50003031051490001a40300c6503c0e01c69035000301008c40d2180c101e61121820300d5011020000a4140241884502c906a000b054009103890203200140381c07007603e039183c1ca50b04042e908021222041025000c01041d0002d11030661400a000300585a4901d00342009640701d100603800b41c2859400380064620305650965000c0e410b512230419280300b9551014403a01c000210700c224040e4060203548180e2210341d03030103600d00034801001c0542c2020881400c0001351003800d403ca800c1607000703130b440e00a1484441100c04d010f004002d0f440800711040491820401c0c3c4011140030700400003414140e000414005001042249030014800109407041884051400755207036049098100c44200d4494001c5081c001e440c0216400c3d00c40c61003c04c20281c0c98440110050500c0a0140d40c0c0003500308640400700d8024800c0d207104207040d400943e51b5414080502d802c664400c0c0400741150040c20062 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 103725872 1250 103724622 103724627
    0x20f1b030d02070b160201030b031e0c0108160305043009060201020c06150303091203041406120703020a03090b070309050d0504050f0906030f0607020c1306140112060504180b1006 79
    0x8a02e2415561a85c115280c5d50f0b10040e00288103130310310543d0501c1a241d0f0300b500c08510204000d08591200c040d60000d1400d10700540e80b07d01d040c0ea881041e040070914140724184241e0140764030a016402c10160b1110070040340380c12403420b070f841c1c3c0340c2031400b10810912a600a00540001d00003480210326200d07161000326280c10014160500301c1c02000c48802c000c0c3d504005844030658000d015840c003044a81d40d5035900e90086c4030310442c240300d81019200915102e4140c0b00010b01502500b50141d584402c101d00030b50181100c0300c10306940d00000c0b80031078903a4400038810400d5440000d01040a0f0402a1900300d00350031107000c01c5000c0000740100c0d2180c0421501402c01980ca1070030584880303000030700380940d1654002c0a4807a407401c0000f060390006402030b030700505803a800202a07601d000c3c1d800b500c44a0064580b10007140800b4000b0b944109820400f000e801d840018801c0c1d107a0700000c00790350010700089121180707104000e040c06854100f141d0041e40b8080f01441c1c491420401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 103727122 1250 103725872 103725877
    0x11040b041401081915080d050d0e0303010803071704090e06060307051207030204020c122803050c09191e1802070215180a0e07031a06041203020f1b030d02070b 70
    0x3801c0d1290340705c060f040346101450034604060070500c403c0e00c00300d94807141300800c4c41e00200c3d403c2081b5400e122428201c1000441120705861910015604e4500703181c4501c0340441d120101d44041c2e500801c40010820254414154440c0d98017020340444c0c1003203c10140743c01c0c0c56400c00c900c100c0c1c00344030301d00001c00002080c80840e0b90644d0003503200d155001c0d44500b800c2404960070f402c042c2c0000e10010080c20008400301101000030000000140c4407170460407910200e0307130145506820000c00c1898a802e000300c2c5440000503c0c011111500d4002121b000c91545030031788030a00740d0300790620880500f513071b0002404200e01011420110b2507000103809412051464802d040c0018200d84040d440ca84a4814040c01801c0003902030b50b070b64500540300008a8a005c0007a19040b0031880018541c1800b071b40c0b5400003003c0c10f040030f0411410003128911301100701d00b50701c2004401b0000130402e204480628859101508a9038901170506007003025002d40f000464100c00003d00098400000307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 103728372 1250 103727122 103727161
    0x10915080d030b010903080301030606080609011b0c050a150515190603050c070b0f0a0c02010203090c01050903071802030702010c09030b01140d05030c10060812090405090111040b04140108 83
    0x2e000c51102c0c0c500c3c0050b50344051540015020400010010040c02003580117002150104001c840c0307a40d4640d0800ea0803541c1c503114114005a02c0b802c03000748a40b044180401c424011400d480401802d0f42d1204020210741c04500289901c0300c08001410b1030a8803030402207681640e52004196092041d488603200a0040390149076441c0041203d416004c015a030b070286e4040c14824072802d02d00104041d074041281d115001a08040e95031040038410b000380c80c065401c0341c00a0a40202250054940d03822480d0f02a80502c6868030002d502da9049401000303041c444e041c01692130401c000b00a003550b804c05019030074021405e60400000d0041c200150454194100f070000c00301306c181c0000c00c0d0701c0d0501e00c05040c03444041240d00003540045030007003108501980401c452035440e01555105c2c140e400d0541c9401405203d001b0190500b600565031212007180001200b0200d001280c4907900281c00030b40100724082000c1c800c0c02c0c000c070000c00ca02c40d003d0070410030700d20700200e030141c40042c1a034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 103729622 1250 103728372 103728377
    0x10f05010921020a08010b030105060a180b010e0307120c08060c190509060a120501080106080c0d0503041a0d0f0513080a0309080301120b0a02030403051b0703050d0305010915080d 79
    0x3070b0707100c00d40340c5144014070321258000c05441295548000090191000034041031080d482c190102d807444ca0704032080002c541c3c03801c0d281c0c00a4603007003450344010b00303540e00b0080c188403e014400380030b5034050003400d010f0400401c100700620740506040300c40c640650040a015400131041c003800d840c0350702c15034020641c0f541c0c050742501d24400080b22140904040684c10080200c1c444203a01d0308001641c207440d03041e240820450f03070307036100440c00d03281d01d1300c00e00b4100e42105540c04002d00b846030801d15241e00420440340303055030f40da11007451a10f40c4042010000d00c0424042910207042c0500365240e843e083c018409414080d1490841901e4090b0041c201000000c6545d80b090181c0c0116a41e42c1d001900d00d601c1c1c2d030791100070142003030404104440c0d0440e0b920005440401d5842070b20f0195400da81d070182030078401c0b070301068980c18900898900340708041e40000001e60030080c400c40e0040302d6502043c0c43d45003201170800d65409445042d207804030480148405000000c45191004691 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 103730872 1250 103729622 103729649
    0x140a020f160503090a03061e0c05030c090a0f030803060102250b030402130e030a0906020f0a03050f0f0403050c0f100e040c09090614030c0d080403021005190215010f050109 76
    0xa1405a25610501302419003114241d60000300b4417403140c0c005c05880842c2031440c2101c0b6070a0040ea0111101305e4541404254140b010905000c00b0102400001d030000e0801d100542d282c00002241000c075034021540000300100300306195034144400c000107d101032407a800148511459400321100340209004800b010002030155500c1011003406481c880700100602c400791001251a907206890000100303e000c60001182480001d50040b0040c8000240041e4445a581207810303070b01c105225507014a080c0054004908518000d100541c030803030081c6148185003040c06564108181554400c80a400c40c841542e80c101c400080074050445000404050254060300d500e1000e8000115092800c5400301d003035500e00241c1850183c2c21070072184110307010400c101088000d8040248080400d000400040c03c2030100d504044655041250415041641030380d00c00078041110300042c0c1c40300c5007880300c0017024001036016160200d0909a201d0521001a082c078175940b04220f51813114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 103732122 1250 103730872 103730917
    0x10507180b0304110f060703110d050f04140102010902090a0f061d0f040303061508040b0a020a020a1b0e0f060f01020105012607050d03050c060601051c1e050a140a020f 74
    0x45c1a4070304218a4001c2002c2d84950160500038044800d0200807070b040d1041d21a0100745130700030b90595072142c94100c0c12524042c2002002c3c4281c0f10312001c0c0e9415903485080725070050355112105449a44243c0300002c540c62481400f8041d40d6265101c40c01269100304445040e4060790009540040d89003c01c0c0d44507101c9103011001004180d1058140240e143c90400c002d0350301118144c001c90042c050561151142800344040b88242145100541d1060381294000348806405404200c469450514000c2d03441004151640007292440c211581180030091076181c5550302142c1c4c0320085c0700030045507050100304030050724440034254005001d007101c2ca080d180108000c40c05424068040300000003586005403030303a08283c1c0e203104d450107400b0000d1100d500c120103030380b400f00b01d00d800001c18a0810030118002d00e4980c03124118220b6400620015a019000c0c0d10300807a080140001e4644091510750b400d103101800200d4442e004120b060b00b83d140040a0b41d00044070413200c2c01c0849030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 103733372 1250 103732122 103732129
    0x512040b15090118050906090a03080709030b0109050412090f1206020403021206090706080423011506020d0f0314161b0b0f1302030a150b030f010507180b030411 71
    0x20481c100d64420076850010904540310300740d800c044408984144100e0b21803071110742d06c0d6081112400340d1580910007001c00300e132040c8031058000100f4142101130640344c4d00c4003d20340c5001d0f0010303095035032100c00780420058041c0c03528004418500c1c0c4001a06d090582da6151912648aa095500c10042c96201405604d504680c02568000c0480c2074651300e00c10070316125078080301c41d0301c032a004091002075954040c0526912a960154409000c9440a5500110b4a50889000c0c05075980c9105452141c0f000c1520640580030503002090080050032008100c90650359610382010f0900444007801e04640507000e42204c04440c01d410740f01131890040303980a1410f84d2800e68064070407895030a0000005280c1e0180074801c0c880700b50341c1d4800c040c110428020038070083d01039200e20302c888040360041d204107846101151002c07941c01000c0f00002e240c10700c041e104580d982d40d680e043c000b40313a4000c1010b41040341c40b0401603119601c0c20010b0003081c00024006000d2030802c1490300340640d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 103734622 1250 103733372 103733401
    0x603110d050a05071106040f060207030c120e15040e04060c0c0c0e01030506060604060e0f040605130203090106060e011202090109120f030f0e0607020d0f121706010512040b 76
    0xc800c40310802a914064504401512040d50400041400c000780c21483d08004201b840c46036412010407501c008007592403c000350701000d400d4081100c8000741000103034906c0c520801d54541a91100c0c10707980381e4020400c1c511101c17281c4c2c9c9504a000c0204102105c41c0c4000a40d0040d005440015000076911050700c0016041e080104020056140415801484213003507041e00d000e0300460b2003513a00e1100740319092050740500800300d074503410070032004d280c00f280c9644180030142021481540c1c480105150103604500b900b02035401204100c00074609101d228000c10305441c1c40ba180c15462030002e09900c81400042200c2900001c4461099000703c407444000c1c42090100c1698031481d0400481d081e20810040f000544003000500e015480382c100c25000303030002000d01e89094004c2d402c000c00144080b808440c072201041500700411a504004100e88200b500c82180c54081c029450400180081c01541403120500c1407075006c050f0440c0c142d0b44241d0003010344860f0b80711401e00c42001c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 103735872 1250 103734622 103734637
    0x7051c05060c030a271e06020a020c19050a050607080f070312050601030507120b03010603120201050702060919030f03022218020c150403050c0f16080a030207060311 73
    0x5100c0e00060208001c00a0000d42c41201c180e44c080000011107004644000220340340c01c1403494102007824003203a81030780340313501d00d0101e0310b07508226580e2075680d0000c2c0c0e04220b41500241c0c12944c0c50a00700d0420070309020200d20103040f00002c00c2e00b8000000e02c1a4040d02034107011341800f060b05800c10108100700d80010005071510398490300700b407800801d0140c0303c3c100680701609101c0401e52550090048034050511074032030070800c050b80c8503030000424140c0e0199a0642d2100c0000020440c003500c0041c000205a001007403500e00400040c0c036110014040909039407212000c01044402640200d061560524198a21004e00344c022006801500c840d2140f811351440c281c600140110110012182450100302100d80f010130302c4012409070f80c150208076041058100c0e0554401c04403e603001e0b00c00c0c00c00ba401e07d403107640328a247c00c66080c036401c003c1e8071070b012421003051503441650040c1402c42c01002c02d10141d9034004e481e491188034071001d02d0344a030328000e6a2420542568280c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 103737122 1250 103735872 103735883
    0x305070b0903030402040c030b03060403050f04031b090e0a110603040c05100f09060c05070b21040b01030606140315180102130915120b13080408100510050307051c 72
    0x2818101031690b200d0380180c904a11843c079000301e8020b410300a00446502010040241401d40c1c0d580d2005e0b04d06900c0092600c450300c81c10040400001c1d000c0052000742423071800c0c0ba400007824081c0300000c0358038180080c02c1507406610441d00148145031104140131342070394210746a407138920b4614014480e03608580c0d80181c0d40742c181d0003041c0d400048001d00d10035560320724150507942c0c3d400307075402050480007510b640c20070401805042d1050008001c40a8802d54900c01c20f16004205903d11304283c4084540419080040062081c10300603039010340340d0041a0000700c4004000681da50008070f4023041000f941800003850800214205005100b03280001d6640d400102d1080704424098062a2034052600c003942541d2601b4240601c181c4459250320311211116450f8200008002003410b40c2a49240c0040d400095900002e0001030240c04014000c003100c440c5540d0944000074003694100103070310010031036927a001071014122042551101d4602031012410390f2040e402c1d0b50301914 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 103738372 1250 103737122 103737143
    0x309020f09150102061005010212220305030a0806040209010834020a0201140403030503071b020d03030902090604050f0714090405070e03210a140d09050c010905090c0403080304030507 81
    0x4072202048202c0001c920990035104695107507a40c1d1760040c10341e4003440e40180c1c00b0a0800b4095500c0c003006100003400d4518103107200381c507010307203148482d1543c204649a030404070303400380300d107070003000160b0017400844065060000e980300090030307080002c0503011070b60f00640614040c0d0300381206c3c0703505103071051013216400040c040c1e01039900da0810b4012400907600340c1e1444030b41c08441c41030303a09036503160f65141d2031500e032400c04507101c10300c0b040002c50b856000f0101c1001681c071300850104d01c40c4251030209591805004102d400c480042c9010302070b42c100f07800c00450001d00c410f141da00580d281072444140d0b000b13129003101da00903840c90981251520050010003034011840341c1140750218100e808030140baa001041102c681444010a007500b8881510114081e183d0440d02c055041685410a090b41c04600141e60034100259042c2d080f0061185455034070400c018082d01d800d54155a207400d0a48000b4a580325610010300398034030220102e400c15220340c0459204680000c00710303a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 103739622 1250 103738372 103738381
    0xf07112202091c02030c01110f06070c060605010203030601090312030207020d08040906050d0c03020409030c080d14070f0206010b1b1f14040203060610180e01140102010e0304060309020f09 83
    0x80d4000e4014500c2044152140b0f1204001654855010750307002d00a004400d070444011b588203200c0180c24161070142002d06028a401049214402d110b10380c0d03406c0414000b07040c00401c4425580010781190030400030410540d030000e03500e204417903004d0503941440801d030504400074014000000d44c010a00000348080c068040054410380310f1050f410048650f84200308501c0060b404401000c07050714445c00c10240c940340d03101c0d11200380a400e1031140440305660300c1c1d4081d8000020400c0043d41d421403100306080c010a25076101c20b090034485801405410040e41d654014030518000017030008201100d00148110606000301c81c5049a000500083c40b00f150700da0062500040d45d440c0c420042c5502514040c400c2c01a0b401070b0162450303031a4007040c484040b84a0f09044144049010803600701c4044402c5040201150001545954104103c04155204001300e480c110ba04004002071b41c84e42c00310840d002c840c12070030001110b81300c0b4408602e0510a4440c195404181d440801 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 103740872 1250 103739622 103739689
    0x304080723010219060513021314070f0212030c07050708031c05060a060e0d05030318160308121003060f092906011101020c0a0c030201020d02030f0711 67
    0x60602806000c2081c1e41d841c403100483c1c0c0d0702c80007041982c18594103e800c2c00803d882d41c3c13000760004011001001c04101540104851a00c400b120308405c0799a0340003441031440d2401055008040352505850003040c1403c000c0d80c815024540448504001001c241d481e0300c10011141d81070760000655480c1c560310440340d03840f90001251100c0460700c00c89540d009020714410548101001014040d4050400e0400c50340d000d42c0d96a166084880006507001207a400c101461051407400140c002c0c91054015440c2401015a01485c0010301418240001003162041d030380c15500d1035407251480d684501005489034156800600a2468012a0640c403261030700100609400b40b1106500709950b0020311140c0007503403210442041d00384011038415072240c035104000c0c0046100160400401051941c10840000c0b0101d0790500b90100800c115601403154010030801400a1424500080d4000308541300301d00000b0212010410780300501d5480e16090004d40320501c04521880c031134441607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 103742122 1250 103740872 103740899
    0xb0a1a071b0f120201051605030d0c0503040f0201030902180106090f0506090f150c19030201050903071e020d060510050103180201020c0d11061603080a060b09090903040807 76
    0x3550410400396032210861410048081250404004081014074245100c40e0706000f00c00200d0401038100101207568003489a074440781070141002c4d5640c1d40c003104641c0c041310360405100041c000c0600401c40443e114076042170303040d034083c00c02042c5400c180c800507061f0070035407100e841c02c18007550001c210b066110031244140c3e081c14020010240e1150204911030240d001e0349a8042c140303448026040c10819000101c00240811480c28240700d003140a00b0a60400c0e08040d5a61000c0c0030300c001d05a0901030070360801e02190166280090644901040d03400010001a50b140e0342c0c07003420f04640f98201e24540140d08100100a6810b0000c074912402a69102c1d40717000900303200128401510403940e4141c03071a416001080b00c83c80510a11664624060080d80d44840d0300c00c400a41d500c1c0c520086c201c25040c5480c92898100350729018007d0314000d4a2105500d00d0040d080c000340d41b10b801280c0f0590021241a05503940b542107039481e5200e0f5403c101c8450143c40c000107580e0701d18010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 103743372 1250 103742122 103742137
    0xa050c0307140c0904150e010b0402071a070905030d030b031f05040b0903040605160c0905070504030606140d021201060812040501120b0105250c060e09070e0609040b0a1a 75
    0x1a981a200503a082042d022000d440140451020032071b0503004154a41c03000c003034602818004904001c6e1480001d04a0f00180d00c01d40f00d0f2007003154517140c1440d202180b141d00c000c0c54201444500d003468046603503000d1800c170705000d060341d4503140e0300d00b90b504000031410140211018182040c86151020203044142c80840d00030040001180c0c0c030105c04010754044d2080c07950781c2401c140b421050420900840c1500b50350341000e01502140a50280c0139031031140c440760f01d400360f0300c0d0702c0c520304001110003d1b80006c0c140030b0100418609a503500640d4100d00b501191800c0b00e060152400070700400580e8422011403090304820b2000b40c91020141c01154401d0301e074803100d20074044040741036940c46821580010400c000740406160440303d229206110044030010640841d5101030100400d5040140400c203080b111111910300600c1d01640306041d4985000c0a0b00b0788800b00f210341c095050000d10490302e4007403224850312440f40000c001d10714011100340100604888001c944e10050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 103744622 1250 103743372 103743413
    0x309070f1d0a09030e011803080c010b0a21060c05091e030111030603070b032503050a0e0a0f02210601030b060102071d010b070c0b0c010606090911040504020a050c0307 74
    0xc0001c1c9240c1c0307003846a44002030301501d070b905060520100441c0d0311650247c3c3c1c00d050005a1202002041140300074120340d988070b01c0005900720305003040100c00111079210741c0039004511742d04808007520b01900b05400380e0080700402d90007550b440644081c01020461500481c1c0000c4402005146088030000d02e40241c0003008888140c1c00e00d5016403104507402909940059401c00100711840000c41c0e020b58070b12000601041c440100180081e03041400100182c7c1f182d05000b1111401e202d0880342d034070340c41c1c02000a0600713551501e82a040710b042c040d10820850024490360710b51007100d49008400c05040d200749607120300e00b0911110b016284103005104458000c94268075241d4030081c406d0181018201c41d81c645842019543e0040b0070440303242d0009507000458602d8100501200c2a0202c0049140f90034010001d05031180380d80040316080c01d0958a007501c4006100300d90642d00c05072030240e990100c0c21020380b0b40d403181d0401c039a00c40c400000c1100c10b108084140b00010344900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 103745872 1250 103744622 103744679
    0x5060105190c15111204060902060a08040512071e0c080a03090e060a061b050a0204050403051b0d0c02040e03092d0303252a0810110702060309070f 65
    0x281e03280c4003104c2d14045844203001040000c801070050b000007641d401841740001260400c120703408617029070848601280414100b2080c801004410b2281140c6200007103c124145040341e10741c0d405480c03240c80c080701c101006c85100f00c14804000c00c1e640250035818207c1e00a6000c9140c01060003a00c2d100d003465040c0301d540031546034a0080310407801ca85e03065903079540031140f0703585d5201c0c00d8102c034000711601d01c100222100161a00d006140c4a94080e460b241d468809440a01c8001d034158a94481c69800410413241c5035604516a1641707590182e0300042c035405508202840d6100783d040f46580900b0012a0569801e2800014441c018903501510015000402170658a000303644c2c0d0211b00f040c2071700007500c0c00286500f01300c902038041c3c0c0032103109030f0b1810014824584d241c601c4e03044d201000b4100741322845042004d030b07540b01c280b10740c108a1513240c0380c51095240924803000707105040000200310051010005403000d00140560071900a903285050074202428480440c000d4018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 103747122 1250 103745872 103745903
    0x3040501032405060a0e0901030308040605060405010305061b0d050a0504031407020312070813091506080c04030f080d05100e090613060b031e0f1c1205060105190c 72
    0x10708030b000001c0460303605051015007020300700002500001508400c024400d400b09045503240e24100d40210700076215a20f107414141404004d41c3d00c0103000900482c1000010000103c00244869112082e100713001088100059104103520912104090240c00c040c240031100d21541d002c14000c034402c0c1c0301c6842000d541121800c080c010400d02039811303004120300119104061005000440c0702d40881481c1055581080015101507009800450b41c0c0e0240542401e018811303403000f6128501b01a540340c50800c0340060580325a001c020182c1c102d07409807008014445082e52440c19803041c05102c2890b060010070480b108510500b0307010aa007001044000c40d0105910b4024110042c4450720400b154030341c400130782040b40229415105091032240b0b0008111240030010490001401108201d60a035a15140c840511100030352003901580c00d100d6000300b100c000d24654100041919601c480051740c0a0044c1e0307910b8020803075500054440594040e000d8041c140c4100c4107581003541 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 103748372 1250 103747122 103747151
    0x60c010515180403090504110d0906090b090a0b0606160c3308040212030c07030809041b0512090703080309060702060a0203090a030c05190503120a05060913140304080304050103 78
    0x140e5002e0003092441758180902d0500f43c00c20046452449181858031b07054680d901304a4100c03613015114640d49005203820007102100c9030b50801b074503000a1038030003a0340c3c4842c8038a01c000741010b0310039030b000501d4010140d4282c1e401140c4c2c580150703a8a40c00c3d030340c8480903403011201018200180400003210403d140040c005000c80c54000c0e541e140440da595802d02011a200b642d404110340f01c140310300c51145030b042065501951154801d44d446404a40034032041d2080c580901c406030f115016800c5080343d00400703454641c441c8026178001c603168640000d060556541026200d0800081001180200082d109002e1031007642101d0032640d440d80103000b00c0c00141c40d22119604006401c07000b00344210702d01c403035541c006d0702680d00c4200080c003485040d02503500112269000440c4544111100c061026440a0700040070302903890211300103a0020300c0106000e802c90221403281060100c10405e803a01030030500b084a80d6541c64903801c0340d480d0400c3c81010700080c05c00e650b0400c6101e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 103749622 1250 103748372 103748419
    0x807030e010306152f01090507050402030601020309011209020306070e12070f180b06031510020604020f0603040f05011a03160302060d051902040b030f2a09060c010515 74
    0x418403810002c900d09400d20488405d164004041c41000c008440c0b1203845600c4400d007040c680c048030001800c20220b15003141080c40341e0788524450303881402000440e0360040200c4840000c06d1078107466075902542010003c2c000c42c000070f900745c403c0c0020000080d40000c4050321315032341110104498500003003215601e00c054000c1f02c0040398410b000300310359024008400740e910031180700441c040351a0b1010a00c07940003103179a00a00c070040c4080c3d0070103083c407160802c80100d40344050003161500f500825158580c05035414011800000058144000304001d04202a400340080c400d42d6822494022000e00452540b4424002c2586060f0b1901c0c0d00358000b01101d901078143c606041c5020300c818000c1000600e4030b219a042c0e020b4014171030366144014805000b40d04092922820107841490305604000c2182140f8000b2a840c0701000c0d1404464105801c025001c0f26076800a903004101140199443d0b80711660801060142c1a06103040d2200081d101360b41994107040d10b03404012000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 103750872 1250 103749622 103749629
    0x9060608161a04080f0c040e06010806011a040b0a08060306010801020a14070f0506161416020d02040609110309010f0b0924120f06010515040b0d15030807030e010306 73
    0x210001c6030204041d40020452221540c000c440300b0781025503414025041c10100001003140313400406144510b0b140520812404982d0100203101541c10700b485660354040c180198100e041c17600d0102c503103544078201207034040c1400014540e25501800e402821090084ea4880d00c20301414001284d400814400d9801d14501e40e41c41141c0200d1b0118404800e502009040e283c410f884032140000c281c08012032030150031081c48460311160750241c000cfc414a4035550006000700100700722814601d4010301610a145c0403120040c0f00f20f0700d403001500801e0154080c2c041b0750305241406114440440c040d512446c034060007800910041c110140480c3c01004c900350740442e100003c169049801c20016518031884801442c0418050002540d1503551900a070030560002c8041027020409000b118014042070385c0e550b102c490819010002c5002394000c1c0000580040b0f5041185036468000b001d010081c18403061015031a030500b91040e034882d05095021a014040c1c450007035110340b1610044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 103752122 1250 103750872 103750903
    0x5070f03050717040804050d050a0b070212070303020c07090c0c020f0a05011e020106080105240f100e01051303050a17030f040602030c071a0601110102041a09010c1509060608 77
    0x50f002032490b01c040780001800588840105200114040c0c403400c001c0c3c8941c0c1c1c080c100900048000e4900440320700c2006101004540201600c020030345214402c0e20f0654cd45424096283c2100385000da04c0d000865110340303e541d09003030b05400d043d50401c2181c81840c1c002da80c60300348000c1c417005204cad410581c0d01c82c090000da030322144c01c05a60080312040550407500d2001240c0140e44e10121405c1d0ba1041c0c8801403034000f2440c440380d914405501055403284152998200c5040d020002000900596a1071090000200316101c80c1da00c1441180c86069026943d0440c043d101d040407a91407840c0070307080383c1003400f02180c0c000310b481c4603042c0c81c4600540b4041003403c0d0b960341e50300d00c0a90406046680140d205000110004810f40c4c99075840c040810343c0c1d008140383c000c00050248084034106403169204200078000042030003c0000e110006110180d500c0c4c0001c4e004803803081903140080c1283d4014140710090625540156210a015130b006102050700e80070141d48800840f40c80100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 103753372 1250 103752122 103752137
    0xf200d0c021501120503070c1d0105121c020c061909080a0807060f090614090601090b03100507050f04060e01080c041d071e0e090c09010f050c1e0105070f030507 71
    0x13500400d4885120720364401c03415207061554968508000307085682100226810043e45400d0014514007041d0047c04101ca091038a01050100e081e180c00e91828446102911515400b54040c003c001300080403501502d0165900214245201c581501040160004822850000798204001107600c00643c0102c03c85184c0b41c1503690714001480d1100c0608945519050010040781c4188143d2840841030110381405180c00c020380340c1060f105802c1240f032240b4200070f0381c0d002d1700d00080e1292a510340500c0011281c40da11020394060282140d2002841c0b8005004200f040d0b0024101e00c11040a8940c0c42c45500d031002200041c0c0514003030172102030641000480c80300303c80745c1125044400703810040200c0d40320a28240e40c01e8000030141e004154a91203042503402c0070b001c1c1c2e981c03000c903134100c440c105192400000c05140040c14120308020002c01d8000803a8002d2002405600798596400f01211001c040107010381001ca4104022540c0d058000f00d0590023405458070070a080d50314601c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 103754622 1250 103753372 103753379
    0x230108031c060b070f0308061507080d1d160e07080c030703060b180a050a031101050d2a0e03060403140c01020702100203041a0702030307060f200d0c021501 69
    0x41c010000d0031103580900d0307200c1c0400112484442c004000290241c0125900c820360350034084e0000c107000c0c003103e0055480040c100c1c6800c8110f000c0d01e589a40c8581000d544021000700030018110350f0942c01501d000c03c4c43c0c1c152194400054514510118400181d000d0b5600c03001a50303489070443d6217101103a079100001d00c14030000e500950f400f28140c100058a00d40301d0040c1c2280b5002004a5920008000c0348038009103070071203490300204422039507500d1143c110745c1e03030205903c81110140d06000f8040313200c011050380f64200b00c03900305c1c070003407000340780c003241c89032454940a680342500104800c00d043d004a03007004110580301e607415490705940142500c4070440a50701c200301d420700303a540c00d00c21a401a92441032061100030030b540110b40b41c0b0700300050011503865190300310a450350100f140c0b60040e00c012090f98052500000700044441600c1e80c1040544119169141c1400324005a150b42a01d0280604024600c25004200803203082c64143c3c0c0d1840001c0d90070542c03911010040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 103755872 1250 103754622 103754647
    0x70f051507021f02060a321003060f06091b090501080c07060504052107031215150201050708090106060c020f0a0e070309060b0405040206030a0504170d23010803 71
    0x508810b88050b0180c01007150070050f220454040e200401c0044e00400207100039030150b80240900c00c0501d04003802090004c2804030b1094200c1d95a90551441c110005108056103d01c071800039074000b5401d106160030000346030020003103030241407540d501e0101d13010401c0011081d03071401c4001c030352a01940c881c107090040d02d6124008246195048040202000095590051750300403071044004006a020099820b0540389101c03a014820700301c01c2c07007001c021079406440460010a81c5800040c42c00801c40c40c100034807415040140840c0800c5411090030364150302c160f00c68850f9035184005070b201c0003030742400da5000b8030551000409440003034006d0315201c1106044440000c12000700d00d545d541c0d00c41c01014045400d0070119545401d4101031203014000c40c2407002c03040b00c1c20015441d00341d0018556000207070220900390b50352000581040002e0701c4030002c840c0c0c0b50b01090b07281d50400509801815141c4c1c8205500b1059260840c2d189803140810743c10b039241c04001d5810200007900740f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 103757122 1250 103755872 103755877
    0x120406020f0705030403020406051206010b030a02091e0a05011e080606070b010303170f040c060c060605040203010b2d1b010b1804032c0d02011205100305070f0515 72
    0x25550190308200d0021003685090042c44003e1091000d1a01c503455401084125666070b809a40500c01010b41d05951410205070541940c45150704551291188800d0a00078042e040c02c035608042001300f075075081088565005144c40d4200e415503030310340d00e41c001140d40b140607181200c00156015150b0b526240154901540031002130106800e00080b510303030401c0a682030f401030300071070a0000c00c070711040050b25220f175010601e40560078481c24544c0e40c6080c0068181700d044c0810000c2c111010030800301c0d40003c0d00602c00240255242d507180e000c000c0403070f070000c8180e41c10000c072424240001c2024041e0507845041c010310142c104140203aa603c00c10000407201c5c0303025540c496401003165190100c3d00500d4002c030895150a2030305240c0900301b082c01c0d06280700a20784025041505a0342182069043c200951301e210f802149440140c030250780a0901c80100c5041c041003010340c05031100710a088900a030121a2031541d00c0740300c00e05426690140da81c00203285000002c20023900c400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 103758372 1250 103757122 103757131
    0x30b010e0f130f050601020d02010504020306070e03190b0709080c090a0b010504080a030806041109090601110a140309031501060f030207020a03061e0b011103070f030e0909100609020301060512 85
    0x506001c0b142201c400d0382114103070200945504e81e2a41032000b07a5a0400c0107043c805010300080103d800c0c550000307650703002d000700000100030280302c1c460b5940d2004e008142c2210384050b481c40b41e140861503c8600000700715203090000f003c0420015506000083c4500c0c401e0000e00350024a85070b044030540a4041602c217107051000c100000950000100500444240a075907100344504121080000362004203840024465051005510640d201956280c001c2e409003051001200b4880d039941c104281c180024003c84104401e100d1081c40c040001c01034044c00710305941c0000303114015160031400c28001c45c1c0000f010a040300384034034000e44c002c04646000030504100c140d641d58030388090351000d00d008100c1d100d2400000010407040d010780c0e5228502424001c80e0400c402030402d40e6406800f0380682010a03400d1188241030066102000c010030240608603036150041c1d80c5662400c5a0942c0c0880914140c0d000031180010700c29281a210704d82d0701c0c030b80781c10f407440e107000d0801e000a030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 103759622 1250 103758372 103758379
    0x604030f02031204350a030b1e0f1f02060603060705040602120a0e0409081804020a0f05090609190614040b0703030213150e0a0e071e09050303070b0412030b010e0f 72
    0x101700c50340e0840054103401030207071600c2d1019030311000504000c099490012019029050004041c4c50125020281a1002009076610040310b0b815900040c4001c58904009414414042e20300c075003540d000c42d6040c4205804e0341101e03490384520301e082b03e031445240b04500040e044502842240c050540c0140b02d00c000c2441c5c5080030120820004044502d450700464031394200148802e045094003104041c0070404031002c6003010540a0098034900d803280d01001008000a010a51581c07590280c07008e248010f07080e0701540043c100f005d078441820b4085d04010403203a40200c81c40c0040380085400382c80d040c602c240d062001c0e80c0d0301034010303400190028088680c1c54101182401100d00c241c0070b000d4276551144206000d03201401080340950308030540340300d407800c204004590000e41461101c0041d810160110503000310803961300707915801181e03140c00001400f5041c08454841d250145000c0e180794036a012713803000140c1c101d0b0f5405060034017141c031801c410000b52814110000807544081c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 103760872 1250 103759622 103759673
    0x70f0302150703050a0b040e03030601030c090308030901050714030114010c0f1506050a0501031b080903040b04030b0a1a01020d05030a11040b04091401061205040c090c020604030f02031204 83
    0x8640c141c0c04400c640d84000a9590030400030385c56481c1c0a00307200c03030600b51001c00129001020064070b91100400850506403940001940e01d8030035058032004503000903520341c0720304045043c14081c0c40261042c00018910100d2642a940f10004130b9040301c01000726001201c0030040103484289403200c0907644120040e40c0080410f02c46120201100f1074030300d0006415042c14100b00c104046900058101880d201d00200125144000c8001d144001d083c40c1c912555030920301032441c425070300f02a940d44030210303000040164094602e40540180001400807003c0d034040f1101e140c0503101400d0044c4c2c00b9601500391180100d0045400c117144641c04941e00518450f0407403030340c0c81070788400c005c020006400c002c004010310852002c4040102e07099040c0d4908003006004450a0759101030143d99070740440e00300150300c28520700401c2146003d00c1008501d09002c0d40b03440c021141500070034100f02000c2081840401101c0e008040c02120a0443e05c0da500c84070025040b0944045201049 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 103762122 1250 103760872 103760893
    0x1e1003031209080d0605031905190602090d0302060f0c03040b18010609090b06150a02030d020d06090f091202010c0f0320030108100b090105060d0e0a0c090603030305090a0503070f0302 81
    0x202802040302c6056148041005c929004c03d05180a0501d044a8080c030502d0140900107040410f0400155564100340c08129520781000b00c0280701e40d0072101d52101742243ca001c105500031501520030103024122140d40e5030f078401c1c02043c42c803048a009001c0143c0034000707482201305560303c4c510720000100002d807a41e2103400380c1d000c840d0082c40689800c0000c0301004664a00081c049034070303070100f14025084c260003c0000c0e40d28003844c41c1c01c000f101c2c2c0100d13400e000001d0940c000750042040700b81c2400003480c2e050841c0010540e08d034068881c0d00281d4114000d00340140030303a400c403010030382d941d418042e101b40007180240710026002c4d1541810007602c114480d044005135010f4032000c13010f00b0221201c0070450003156001c80c0d900b4051040400100311541d03a060944d024010458404240d40d20208029810b24054000c01072442a41b40703000700740303c5684c0e40040c081e05c0c403e450800c0030352138145c88241e1300c0181103001080c0e03900400226000945c0c0d1540c40d12820320070700441314400070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 103763372 1250 103762122 103762133
    0x9030c0b030a1d070911090d080c0109080a031e05010f180e0106090b0112050405060103081b070305030414030a02130209031207030509040c05070312020f0706141e1003031209 77
    0x381162083d49501508041c0071304c42e081d100d0344151482c0003c0d6946031098844c049011034000d11009489a14042510b5040881c2900908491640500c2440d514507144501600030941411002021804a090f5550000072072140c00d050301c0100140040c2d051401101c0b0046a00e00c82c540991503844074003e050402e02401010044c0ca41481c0c00303c2e038060017000040c00201401040d504141c1800d0600011680200307003981903d810500e4590b40708820549658006440e01050400d446410300020900801001800560308040510441d4110450406984030340303000700130750300c90244c00c60803c0041b0030360f004007922000941940c1403070000032503001440e00121810307004103000040c0900540382c83c0c4240c0c00f0000640c02d003141446000d80f401000441c004443d00c5d103a69000543e8001c1070700403030590309200d41c419010301640c0d4103008011440341c802d4500c81c00d1041540c2c0c03005001d8580900481c4101411200c40e516685140c030211095940b0315140c0a84659a8100c0c1003c00c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 103764622 1250 103763372 103763411
    0x702090a09030e090f061504031b0314030c3d1a0105040308030402090402040b280e24010e06070b04030f05090303041e090c081609030c0b030a 63
    0x18254000500c030800e90038058070741c844070080f642c4a28415820030144030400b083d03142c0c0194060329071803c0d00004a0114001d885550809406424414005900151196201410780703100f000b484003003d242007805983c0e406800f1000007190008002090003c038103030810a4819805203040c41c10001060600303046100c9080301038085a19400b1605448501994407140d020080c40c2062800c0d10f180c0347d0051500018000030b00c10050b85c1c001c2829507a0301d42021200340c030020001546408400d00c490200203e603e0707561b0140e0b410f0321000808595031120f80d4851001505581204103d03042c0d0004034231015910f40781030148128803c02d10740c9600b40030384111403042030002800d0416080144c10201801d074844100300040140150644000c0151030864040765641400c1422840c00d81c0074006558101100170b07481d101403400165072012100b0302600b400c3c001140c00541d12003084503020024000a841d18905d82010400c2603104170042d540042c26401c00aa0804030840482004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 103765872 1250 103764622 103764631
    0x2a040219050c0f15060105070f120c020901120b0f040602120106120f051012051009060c1103030c03010b2d0301060905090103050d0f11030c0d1b05100b010302070209 73
    0x5680860310344000302d410420f1a00c42000d10b4000c244240310a1a030307940589006204604209001c06c2000c1001904c4070110051580100c5070b01120701000401044402284d81c141d120708466800080c0d25000010344194598100702040ca0540e41e0f0706070748540c014080e104031303601c50b400c021282e69441507042c0c1324084e12039541c8100307552103011101c5085e541c0d09154954020314110905c440d808158110004440250307008103070b24401e500b4014104801e00041040301401e160210341042102d6001c05440c0c9120b480e04940c60080b000099585d00084801c00c1d104a0100018840066520083e04001d01018005030f4441105060780a001c40c1d8602100c48004000c00107000103600604103602409050303a9880c200e614544a09544400e280101410300c502080703030030119885100200c44103602002100c1d5190704564983d5075a031141d00020340011581003244030351100c042502544250018002c207900140c40c201034000b4881e81400c81e050582c200f10701001a103500311407501c103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 103767122 1250 103765872 103765877
    0x61e150613032109060201020324060f1201030c0602061b280305070e10090302120c1504060818100506010504050d05010f05090102040b04140d0204060902030603010c022a040219 78
    0x100d50518402800000d1303607821100030740e401070003000001d035600703034400400310055081e80311075100300d9020071507600c540d03038100110060010305485a00104440306040704c0c403035410042c04958484040741c6905003a14640700c905912014031011800c000041c0c4030503c22590140f110100248a9203806c00d0b00c0a80400420348030780400042030340140410b42003030310981d1950041e4245d101300900940440c0802446142c9800851030440b000300102010004064181c1524596201c03010341950840d00c141e00c0002c800c4e50009176005041c50000c008000400020040c6103010000c080280000a00c140d0400406000005456a84511091221713008000008410190f5a4040b060313030303070060000d0041e0b03004110804c5408200000c0b01c0480356000c0d800c2e00000d004000007a2211802c040296020742021070100c0d012030306a0056010b000218000c00c0703003440410040e03841d014104e201c544d0100c000c02481e80c2c44501c03054000755802c0020030061a10710400034007441603200c103d91800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 103768372 1250 103767122 103767173
    0x60f0504140706090b0f0d060b03340e1201110d061e0503060f092401050310050f0a0b01021009061b03021207050a02030c06010305061e15061303 64
    0x3000030007841182e01070b01c443c0ca0598140350074242110000c6c410211102d4076440300161030300e1030040700d51254010b0a0720021080d52800c00c2050b403081d40c8501c10850114141b104084a0785c1101d40c1b050fa03012078442c0d1642145095220200200c1f90010300200e136055403603805071250141c80400600700c221502d85e0004405041007000140305181c24001d401403803d545080c442c0359000104564414103200c80e41103103a68071401203082c43e5000008280e00c0c1200d00d0000e81540b00105040d068074003d5003180c01418000784c1c44010b03a8010340d0f600ba81006144041524000550000e2110303c0040c0100c0d40300d0000030041c201141d1303030801e040c0c0d0f200d50b40c0d80b000907501c0c480d5000988005600d01e400e40c10501d0303040b007181e031060300034200e04203200000500308a510b00a205a0341503452044c00c2e034495682d203003095501c50384110f5205141041102c0000401280e991a86004440e5070180e4144007481c1800c0c0100d44c0e01284d00444100406003002000030304000c0d010b081036a1810b41c405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 103769622 1250 103768372 103768403
    0xf06090e0c010212030c130f06020102190201051302010e011404080106050a050d150c091503061518030b0601230702030c04050103051f020409060605090f060f0a0c060f0504 76
    0x50400d440841c90074119000495070701e46050040d0141d03a0401040c000080e5201c04081e03900184020340e0380681898410b40c68000360300350301075001c0c08562519081c581d207104c403410001c07422244102c4001c068142551500009541305803450400c240c01070621000141d94640880103a8201d64070100440e9140c030014000c2d420f2650003500105010381c0c2c0d995100a941d82e480d07040291008045010940c3c400c04040c4040c030801f20b41d0300510043e00b00840c2c400f4127141c01005404140143c59580f07aa0b01200d4400314070a000c0d140044461155010220f800e50380c503501c0c0003802a003218100800400c43c1040e0104480d2031007000d441c0110b84542d01c0c00248141801c0c80c905500703a91045142000420100300041350303e45004885012101d90b000941007648002d0080c0c4d0032102e000d901e801c2010600c1a00f11004000501781196028125144602040540d10a00c0c11880210406220300c0d656640034607540404a8850078020511840e040160001c4802c101c07030955400c009100b012 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 103770872 1250 103769622 103769651
    0x30f05010609051905040f080d05040309050f01090303030b040608070b070b0f040f08280201060501080c13060c050708030708030a0b1503130507030605040803092404150f0609 77
    0x18001041240d20070301080c40c4c41032107820581482c4007510440c94442c0700040400100d40d04a40003640c1c02091141c035104080300c8840209011982140800d040d80070104e4103280000b010211510140d6400200500799a81200541080596181c1040c1c0ba6a00420784101c203010b0f88000d006110006500e541e00f5041c00c291109000e0f1500c0e00308040f038400c0c40b022030b40c081404d601d05034208952980c1c500342c40413802a40350608120044011840102a1560b981900500304441c4240e960b03500300c0d00d03864030340f01d40d0b4462103003207589600c580102000218026040e020406000d102942c0800348d4691905041d44c2c019201101e0701507001003000030225151190050803038069607540480444a0002c00c51440050811886201000c0e100000c02c0420401c01d00903603400f110600540c113062600c03101540080d54401c040b070242031031040503210001800c031250403032200c00c400c0f0307501c0f10b80318a40a1041038220030350745030f100c550b050782c407e000b40540c4004284c0711100103014980300051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 103772122 1250 103770872 103770881
    0x30c040b0a0b0a0c050d080603030901030c020a0204052a0309030703180b0c0102090a08010b090c130306021201090c0f0e0907050c150702010f020903060c0c160b0a0306051c0b04110a030f0501 84
    0x686c040c41213007418082642c6000050316104102800c0021340c804081d441130f031901e842000025800303804c1c0002c200114040064115207011080c40e620452603605064499030b000449400100750b10610007400404d21480307000c1c0b050307503603008141036540d101e11501080f51300400d01744190740e40010758035400e400c1500c4941c0c010311905000300045052030000608152000d8074810040c4808075944503001514148440115409035046641c0c1d0400c5042c0c90540000b445408010b51038035208490003400761080d401041019699a0796054101c0100a885403001e00b1550030440e0900c0340110ac008104031202d00d2a6030b80160721241e1514500003425110f00b840b84a080600502040c502a10006407060700202d24051040e112101048454944a42080400c00b0171443c2200021031111107001050081c0ca01d50f420300160761101d052000c10400711b258000c84c0400c1442c42d1000c6014074010300c0d081803051f1102060740b802000040c95a9040d0303081581d0100c0034480340010084248103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 103773372 1250 103772122 103772143
    0xc04080604050c01020c06030603060721060f030605010518040611070803040b06030d032d0e060c041d251205010f1e0b030105010507060902030d05031503010b030c040b0a0b0a0c05 79
    0x180707a8510310340742d800309882f003c02800714424803610088202020048002040300015000d1040094030780d40c02001c00030b145288000e5619902e0000023285901f40480300c10010034901510100341e8445944010042a40402810442c40140a84c02c0061603040003180240d0250751051035030b003401010181801d91001c0d4400505242840f00180c80d480610b1075029240b41e041a543c19040c1e031411480948840302100d25203018440400c00d14500705000790041d240a0404e03542c04180ca10780d0f00d260310409031001c118031900c50726140000704032032181d62041c4506241c01560f8032044825002507800030303089002c422511000074007801d9035050b02592944018100140d0340c0303191041078030582c4418000c4504101000816006108980d0805172041e42d014044448514900d00000d01707981041d81d0907100e910303100c601d1590510b01400f840055100040c05000000055800c101c000c118601d000c641083c890580090000540c80c042e00903c0308a03265921040e415103091428041251b0303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 103774622 1250 103773372 103773379
    0x2060403060605131413020f030303070816051303060b1804120f0503011d0603030417010501030303230105210f150907060e060307030b0d050c0306010f03030c0b0c04080604050c01020c 81
    0x1424030a081034881c0c0d040c6c2d04807a0458810861030f000740040780040f050075002d00d425210001c144450250f11061043c0709500282c041403079044510340849a51003500e44002688803485003c0c0003040d4180c0c81010445402050b1309005a40c10390442da05a40c100c13010768481c11010707c409070540d00540b50b1150510329251281c915810580223644040180c1c00d4070a50100c101c0008146407070400403180a81240d100b40c2c0348007010381a419002e88024041103000a00700480005000080211245400d000c1c180d00441c43c0c1c240402d019080710340141c107940d0581d40030700311803c2103c144611104140443c0142460340c92061840443c01c20180071400c5961051074204071146d40028281000d8000b181c20641d030f9160518114041c01090741c08070340c80055102d89400b0810b0010344004008000d90985207142c1ea0707104c1d0103040c88914800540852000800e00c000242019060b03a4040300e002429400d09449154003460600704841c00c44807540101c80c111025a0100401640c624086 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 103775872 1250 103774622 103774631
    0x50106050717090f060301030b1504020a0e09040303200405041803050f0304080706240803180d0206071b182307030b060a0c030e090610050a0203070206040306060513 73
    0xd6603034004000e105034050b00c030a0780c00f1650f080c01c0c0c1d42e80440300781050300060102d40c403540c40342000007201e40c095031080807603030017100c00c1107003401c0500a0710400060390f141c441d1307404002c0084c0180301800600c110100b65030340e02880380c2c0003120112600c101d9021650310b03403a02c0c00d100c10300080b9034080909901c030f050f805400c4000245d20408443c0550f07040c3c0d000e507440352250f10300201140951200204401e00300541c0500c000760310b80e40b40200e550249141240e1555139200540c90b803080c1c2e00061628039480900351458148001c130b40030701324400344c0000d240045a8907106144045100045100340c07a240003000324802003682020030b6440b801c4200941a6001d5008240c1d80b4110400d80003c1601c10005d40194040c1d40702d000010b1026004a0352044080b80080605981060490100300310024980b102d08242c10709074480d4001410f0392202c0c019810042d00c054200388a65002c504c000c00c1a540140c0b03420000d0002580f0031840418007500744801c000030801143c40ca0001103180 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 103776978 1106 103775872 103775887
    0xc070c121110030902030601050121021603230706111b0607020f070b0301120c090c0e150310030209060a03061a01020607050307080408030a0b04180605010605 70
    0x115000d0b5144140140d041e01111507680010790190701a10040c8881d5008200094950b49076010042c2c003040407116000c140e900c185003000c422203410701d11a08054025110b0b00c3c1d0210841c20001a820402d01c4030f4565000c1c81e0406000705440702801b0242ca5101c004484200000302c00141000d4003a8074010345d42c0c03605503071410051140992480e132544002c44c0000a56070f1342c104151850346040300c640c100e400700303000985180d8050070f80000e0101c224801c1142c00341003601e807041840109020400068168125030986260400070421440c020800e40f0058940c1216407686030344911000c580c20001395003000f01501d02d0641803807200034200d245041282003d80c00c5604503500e00200312141d0105403000400b007169680450b0000d40c4030300c0619070000601c140052031186034000501964180e210f1a04406050403c580500013240211030143c0603600b405890102c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 103597122 103776978 := by
  have h0 := BRFrame.cov_init 103597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 103597122 ≤ n) (h2 : n < 103776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
