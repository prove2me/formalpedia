-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0548
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:23:04.045714+00:00
-- url     : https://prove2.me/submissions/6c26203d-fe76-416a-b3a6-cede89a11c25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 98381295 ≤ n < 98561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 98382545 1250 98381295 98381299
    0x180203151b0d050115020c150a111005010602070806190216140606040605040e0c06071a01031401060902030c180a0504140406050601090617060409061e1a0f0d0809 72
    0x140040c6201601c3d03010b141a2040001498080320f0342d03120980e030b114001d41e42d090b8072030084000300801c08104c0c0000c091350f03040361808407020300e01d8281c014640b08007203004800b41901c400040c0801541045804010300582d4010001800c02240c81c110b1a00d00304900e2128540005900a40d00107805400c03141542c000002107900c1c8124941540b1204260f4060388100d050402c000346500d810700450140b1411030f005402c08400d088208850741c0d0160300222410201c4030058024160649119802036005541180c400380301041501d0071610f1541051880134414402c1c49420f00000d000da40702006030720b00c000518045030001030b811900546c85194850708111007940c4003540d01c2001d50003070f480307204180100e444000041d00d05004a0159400086114056804400c81e01d031106400101c00f801c0000c2907000c80d01c8070700903a447e005030303080905000706d941c04030210b0b04c2c4100c3d1a14030070301c05901e00c00008070340010114601d141c2990300c81c2510b68100310902c040c0303a040b10504000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 98383795 1250 98382545 98382547
    0x20604030303050402011e09050405060f15030f090714060703030f0513060501053a080304060203041a150f0f0a03050c0901090c05090108040f0c0b0409180203151b 72
    0x160745002005032a044504a000840140c40e40080c581c8075120f0b800000c1c0191500d00d1400e0601050000510000b00015840080807251a0054440c80903840c155607103070341540e5503854188400320200300040c00e00d46c0d076a80100f400708100703402d0152074880c100e01140c0041d940d504900f0114082c1000c01c6c0c3c0c06003403524000612a00c0c01c000c40000401034440c00c0c0a2001c0c1c0c2e40c58007045800119980803107103042d00d8000c540e40002802c0402a0005a01c081c11020305417030780c90b4084240c000f00c4080b40c8007075000080c4011f01440c403910360aa1b090002ca000824600b42481080220303810003210b0040204030498201582c40342e00c5c2840b4018013030000f4542c00c0d17490800c3ca50303170444004d405000e0007180c2e001288503040c1c5d000d41d180045403515040d18140ba0f81c00111211100140140c64162036541e80d103000a04003c9210f00510010090a44450514805a04403800c901d03c00e4007103046000e02b20f0041e1404034409501c1c0e890711082030402d544151341d11541400291505507940c00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 98385045 1250 98383795 98383799
    0x15070f12090f06031a04051305030c06060f0f131a04020c16050105040f03080d0b040f09050f03070f0b07020c0d080301060305010902030606091002030c01060603090b0702010219080a0207020604 85
    0x80e02828150441c1c0401c15030861090b9203140544c11100004506800c0c81e4200800301080d04180c2c00664004604034110fa400d00c44075141d040c190b41086000c0d44550f004441400940c0ca80020100c4003890115160307408450705c500082c441d0042402c00214003500c0e0011410300340d103c141c50b6410306070090401d660711404d1000c500e4403018105000740e540d101001c0042101d51045007900e00362040c05125038181c600759101d4207071541104a000304030b50b46815030300c041c546a50042c01e04a0403001b0700454054030900d029828211104903244d15603205020307207002f1078014018003080c2a0042c0f580c0c03071240c413500c50403414200f84140c100c0e0810204200d1400b0001108020360403074a29a030200101d0340c81e8600081644016a140b0368000340511080111b498a29058451081a401143d103841c8a9028090070359100d07030f01c6540400e942c0c4070200d083c4181141055404941440211710f070071000d2585040207000d2490700b80400ca00d004c001080843c041c1d0403104041d80080c011501c6613 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 98386295 1250 98385045 98385047
    0x90b1206012f0703120822050a0f1103010c030e0a02131409150604050705040501030e1f0905100b030303010303201608011a0609011209080414120303010515070f12 72
    0x83c65440b085562007413907843c1d104003500ca40401402501c0e1001c8101503010f502400e9445040c0c0d90b0340540d5a030044000c8100050900000784c03017a94440c403c26082c0890600406084031030030784440c0c0c04d060904409045441021425101e070580c1144d0302e00351003107601c0c4040002c01c0402034800c4032a03007a2341032058101c0005065241303580801c41d82c8155645031820300c0180c1d5030503100140841c90900003403200758001d80124101d00102c104603000610140303603002400f2107900d9500b12061340c0348601e20900c1001d008903000f450703010744140f00701c80043c0302003a0b90b4803052001404009810807aa03510340c210f00341b9a40d0000b81c1408584a0700003100030201d106100f40709404d501e602c0e208502186580040243c04880310041100d814954048015070380c20b20748580c8050180e546001030030000301c21201502c0a8a085c000e5a101d040e9940107110200b02035034051201c641c4244010031007a6100d03524210300c2c0c0820190107444640e90310304950301d5198088000c02c6509401c00e080906 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 98387545 1250 98386295 98386303
    0x20c0303040609020316050603070807030b0306190f33080d0305010609120201230f04030f0302060106050c0a020d060f14040312060e06060a0219030207030201090b1206012f 76
    0x958021026035080341b202c0e0540008400191180541201d8140b0001744041c3c080c8030800e43c803851a05011807458a2800044d00b0840c003200d07840342e1603c0314003c0c0f1200c010706220306c41340f412440504001c2c20300c0b2680c034025040c00400052400200400362803401d124141b141d032001b0081541203c86012260902070301811007401900300181c1c401300c000030f0300b0801e088030070080398068441c0c51508000411700c044402c22003900000c1e0341340c204803000720700f01e440c3c0c0100000c0d4020010320406611038034000341040c50603031000041160074001034511200110321143c000d03904650440c1040900c1c035190016008203488070090a03d4140d44440000504899900c00e600c80c1d0344580c101ca00740002901200d81d039000b183c1c0710291490000380c450a003d80108182082070041fa0f82c082d06000080e8000008000201d0060704840c00800840d6000b803840e4010345941e00006081052004004421403401480c2e01e041000e02e100c0d80b4680c480440342030420240740380d5107400e0442c1100b51070b555 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 98388795 1250 98387545 98387561
    0x30b0c03150108060904020d0c050d050f07050108060117041703011701060b0a02030a0c050c04061e08010b100302090a05040e2103102601020307030e0d02010e06010b0c01020c03030406 81
    0x41050310041031607a40c07080f440a031041c0c0d8010403000311510369800f44000c070001e801c821500c2e4086044046a55500c51a0340103e8a200b0401001c80e0f0740c00401031410142c1c25803225040c0300c180c1d0103110851b038102110007100c1030414400c80c06a036450501c00e20803a141c50307181c0d21010703000002140c180d805508c00303600b0040c1c240090003c1c0f5550b2980100a109952071003006810900150581d18420021554414001d000311040201d920000504540c410f910084074980036020011a0112003c40c1d0710041c106c01c0c000300310b0350101101254022500902d0281011750000e10301c2c2c603550710001801c020700030107041045103081001c13020703540340c03540d2000c946130f4440c0158184a100c1a03000b1240310351030041500101c280751201d02840c06601e03203110401ca010010080001309130034806581302d61415075000c03035288140440941008440e0300c1c0d540469044c0a80300300310131400100d035411603800c048800c0d540c00d03070ba801450090107162004011404000280010300045400c0210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 98390045 1250 98388795 98388811
    0x9041b06120c0207030c0b0f090301110717030402010c06020906070f03031e020702130c0210020d0510080d0e0f0102010f020409060306151404090204140412020d14071209030b0c03 79
    0x650703080b14003e03655004103100050403910304070020b02014011401030722003248413025140c2418094000242519100b6880301c0d44814041094020b001440c2d59803103211101a4506146007815000244251222140a002540c0004405401e0303241c0703034120748146400c8038240760400c03214a030040241c5030000b13249800e81b00045100b49104070602c2141c040d10380c010500c443d41e51040d10030314083c0039000c46620a40c0a11103030701c101c61040e40014800c500700b60000140914000c103072044502640c0d00a007040345e11140c24841c9141c0c0003d030b01d460341038049079421085912000100d002d81300440c6200a11742c004a4002660005504024252031003400c0c00e124a240b0b030807400c002d2807018803a621260042180c2d5110a0a0941c0480d080900140003c180b00601110320114908191001c580c0074080d490041e060b1030703040c8001c40c01d54010b85048080c07080700f00c05040031405035040c0a1b1114140011204071140501c10b10001154003400e43c985a2030300d45c40013280c0760400c5480316 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 98391295 1250 98390045 98390051
    0xd030510050a030b04030512040c0f0b0306010203030708060a080318120c0d110f09161e020a03050d02120106020604111906030e011d03090310060b030609041b0612 72
    0xd0391904400d03100310156007002d820200140c1ca16216001c040a010300191300f801420845e82e81c1344c000a0074880d2013240100780160000f440c003601d42c103c20712547d2001480304418003d01c20140c0e4007008580d00080c1920705240035888810004100d600d803a030120410307200014140b40e080503e0100605000d404803040c044a41d82c000380c2980b95422051200d5004100c1070f60b000c001403120110b0710616031301800115002c040b05010894000b02650402c000e400b80380c004001031540490000e081c0c0d9980c60521841d20a0304501950b902420319009060107004101c92584d031443e80c6c1a6200f5103800c3c014140d10b075950b01c130060b40b180d00c02d8030140e80340860f02d401060320707041c4043d15455440105403c1c405003031078000214000c103840c4d61020455521014400c580245030300d110038a03450041c010796626032001301014a009402c029002c800d506225042141e581280103482d40245c05450380101c1d0340e1145041070f070360481c1d4002c00341c0101c3c1005011404582c01540e0300100207401100b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 98392545 1250 98391295 98391301
    0x3031c050c04060906050a0e0301060306021207090503070909110a1205100507020c04111306080601030605031b01030c05070606030809040507110c01031e050f040c05011412071e020d0305 82
    0x30051841640110f9000c1401458200a040d100380c0040143c0041c1d071410441039216400040c3c20340c0e0031984151410398000c50000c1c80741c0d0500c40629040034160030001d0101d45008046a25502c051160072046a40d800c0d5003010301c18442e0003d00400f200070511082c1e65160031030b900f0700d02100401601c4900c5060a0303241e0010552103414041d0b03d55800600b100c1c100700701044094078000c0d0300079250400601c10849584144103140c00036104070b484102080c6404000107080b203a072684240d10980c440380410062402c01c800170003030000c0030328010820194202041e14030b8444c50b40300a00140c609803000061081d6007016021030582150b0520030350301d074840200c901c980b01c108540307065002140c0038000c541c000e5004042800098089000320010317503032481e0495400702c17003001c0321010407820001000410803402d0054442402e21501404900c038001405002d11844a2042200480441e204d9402601015448550320002411401c00703020001d4030303006e602c2540c0010a06007404 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 98393795 1250 98392545 98392561
    0x30405120a0c02190510080105090907060503040b102615040302061f42090b0d090b09010903090603050c090631140108010303050403020402030402030c03031c05 71
    0x49030700703444003a618681d10039100c1e020400c82800d00c05210600611105002405881e0390002c49a0b09075261110760242d8074010034094510300042280c07034160050042400340343d03000016a5006500518101e003d40e445208060340b611103508092102e131102c100e2f0784d04864002912617441c00440041e1000c00c521000000311a95003614024007503009000043c501e000c3d240c2c0701f18456481031101d00c1c149655140003285521043c0f078080c040c0009860305809180139007059285005009072030b00d0071604540c0c8000c0002c076084c0205408503800040080030701b0000e800000507242c205e4040649414943c4c0c101b8024417100200324003040d80d9800001d1054002d104a03403190710705e00a00c3e4a0b0904050070000703107920240c140741e040d2410a41a1070340e961030341c84404105800c0e140820f041801c00071160688241c20384601c0c10810b0700d9005000295202d0240c03000c60b40e0560300580c40e80c0303c610000b0300303148607008119052712000c00c45071098042c000d40c01105202c15402040b007611a0b40b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 98395045 1250 98393795 98393797
    0x3050f0a030e0a031104050402150307020a020f06070b070c172106031c0513030506010e010608310f05150a0609060302030a0b09070e04050d03182d0b0103050303040512 74
    0x44045c10440005283d0036403414507070000c0382e000744000c1000c0800d410109180d4902e40091314400700581c051000c4030b04608144a02c4104500d0031103204d41452003076a0707101c00c0c06100a00d1082000b1036105442c041000c00307081074000b00170ba6108075840e90b007548020400115001c0e40100a5405080820500d04010076015178424136541080c20803500c01e070041e036155120401c0c41d080c40d102848000040303203040c040c1c81d010f03088001001019501d000c80050040c0400307002c441c400f18400c10485500051101d04002c4280ca50319400f01810142c2030503c40005080d40181aa0107206103002c0301d11031130700015110303400201042103032a45810154044440b00d000080d09907001c3c00d141d1002c108440c41d81031380304000000f00d49000b52920324801d590b1038181c40c1110603a0000c100d003811503805000340c2001500f0090140010b80490b2140b000e00c07c10317a0f008040300a0341da001c00034994a101110b080340c0350800030940035135a492501c540d03070340d00440d015155801043c0b0540c2002c03174540 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 98396295 1250 98395045 98395049
    0x70306021327020f120408030612030a0903030f030f05070806010f020109020108040803040807050d05030709060815041e060f14061e0a0302070f06020d0e0309060a110703050f0a030e0a 81
    0x2c1005900c890141000c080290b11481103845403440038001003440c2c5844510142c403031881100c41c25242e080040c1440440c40440c40c0300030954005003c90310420b540a5246c504a03034043c580460101070343d0a09400820a040c000c540c0c80307041408200e601c50f040884240981001c0e40d410b02c84c01c500990132401c960b80075000a00003104032001c20302154641019580240c05a0000d502e0420190345580c60b144000c0c0c1d070400860710100402029941040004004280340d00f011001c926040d00b00c0c04840084102440c4290390310703030000340c0c2a00c20303002c80240d04c025040104039494075401c00d405501828031420702482d05013044e60445051000036962041e0a030105005090802c114903030168205101010405d5800e01103000441c0284003c3d4000d20b00a000050341d45441090711015a941e901c1d189005070710410554944e512603404448002e2041c0c5404003245803000d03006420031081d0350010b4000e1003140701d00b103504040030855040e22440380d2100d000b401034120501840358003034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 98397545 1250 98396295 98396339
    0x1803110312130b030c0f03010f0905010f0f030b04060902042c030c0c101101050a050103060c030506060306123a0c0302030702062203230f071a0403050703060213 71
    0x2c070341d04009020b1020007442c2c208846003e89410310000c01e0b0170100d0f0350002d03401124884040d550070001c0e81c6442c0304941c05014000c81c1400c1150400e01c802100203a01c0c80021b042c480c2100c001010301c08540d0010380c00985c0140188020700c00c0c80b480e0403d20714001485130556010031030307044c0b40d810000102d46007131401c807002e807095024000400c01d5000703030740020001b401102149030402c0c3c00c080c8070f1903108503008400094654110701705001222034103410134092501e0107003408944d81d03c07803003942c1e80402d0448400b20010070170031400e8200419001c0280740300c808000065500803110101c0310032030060100c100c00b61409072800b115140240c1e00c0184c0503030010050000541048402403000b07800080001010115120356450444001d03881a680c03541c1c4510324002c850384118800e52842d209100400c440306c188580c00c2c3d2915000e203e2180c12004aa0000050700c800c1ca0a680055801c281036440c0b055690a04501070b6100480c44074105500c00d00118440c001b041d038203d103070011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 98398795 1250 98397545 98397577
    0xf0103090209070c030203071401150501030506030c210307080306091b0a0818061905010911030f060103060302100905010207120f0311030c010204120b010b190f1803110312 76
    0x2480c44103607004451503100317604500041182ca40442c0e0a8600103000f03000c4540005840b9121075040000d10506800040c1058100030502a107507500148600342070b04203e810320442132085086100e169000c11300c0e01c2882c0030201d0480c5c01e21424401840c441e00d41922090601d564104208141001e601c40351420910188041e000291040071115800840f10426a600c400031651082c81d041085911310482c4c980e441c01c00305518210f0080c18014440d09101740207540e0007400031810f5000040201041c14070050000b0120b0b8800e400000041d9009032240701844050348000b040c00340c00e401000d0140c0f0039a240007458200341c541d14507005803c010306007280310069404940070080c035030a60000381320500c840b2400d1642807000380024590b000d2001d2513003800d0320b016103510303605034003007030041c442445030101500708421802c41e100003510784199441c03400c010070790790041c280802a00314000c0b01d1021007040b045213480e480d4640308404a5280090034200c4403054400d000806400042e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 98400045 1250 98398795 98398801
    0x509210a080a0203120f04050d03020c030f0d0b0604030b2401050a0f210f050114031f02040f0e0712110a11030d090b0601120b09070e1c0804050f0103090209 69
    0x1c2010141061040c40e1054030325044104074403445000d0140c5a40c0c40b4041894180400c2080802000701000e00508080d4101000301d4401c544a0248104144802c03400140d540f95a03100c0d580148041d0b00020815a04c4544900b05020402c1046507a22a280c0840801e50994094a6811400c1a505035030702883d01003090000c99491015000210a00c060304980c12156401428198407100b1890000a400501250740b00d090381c078180d10480d074004410841c0c54007601c0204141e01d2903610b03100c06d038661000400d07a48000348a0741d44a8103011440410201d41c41310b030581214000c1040e90798202e51154000c0c0380c8400c448980c109400d00c26000c2000750710090081c000a164170501c3c07820380b400d00e4404407040341510341d9074100315001c102c0001008160340e00490f040650f100e1480c0c0401c80940514003085070300101500c180700b800410340075141d081e80d800c05000c102503244411a1107440c02ca14220580b900b01d400f590b48501d14040d41241503500c00e12807100d440c0e03002000318010351 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 98401295 1250 98400045 98400053
    0x50d021902040b061902101d060130110114180f0a0306110901020d0801032d0f030e01020d0e150c010b061308060618150102030408010603030509210a 66
    0x200c071501e6940020040c020101440104c0c00c04940b05d01e90358028091408021441808680c06143c0e62040103134200180d1480c0741e000200355054038141e0f064400c2030107002d1038100035810101c0f030360314801d50074402884c2000010f41c00d510505600b83c880040e940c00c1004407404a00800d05048203010541000c030400346000c2001420b40341001d0003008075240c60b5103c09080d00c9200040c140392540014110440b560304106101008003980f4202d450740d4190350340c41c031407201c0c0101064040b41d000f250511000b018040000710032540980c10345030038a12858080c00c0c44540240e42400350084442d110038050055040c6464418003d102d409032813442c1d00d02e200243c024000900d91596261040b01c6191600401017100700d2405030004d1202e4030b40102c45291080003065940500c0040300c0e804040054140303043d0b0030500f0220340030100c41c4d4080040b443c2d0b0141d1707071041a03a582000000402e00d81c001c0b0080c0000c6105899980800e190390980c40751400c070300c1503683c0442d400700c0480004a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 98402545 1250 98401295 98401301
    0xb122109090a09061107060603020a060314070f020721050105061509040908040902030405030c060a140403080603150a0e0f0708150c040806070905010e040c021213080303070309050d02190204 84
    0x1c0b0f00c64913000a9500d409119062070343c10a00e0308855050b43d942e810301c00c0d4505002c41000070403040c9030510084c03594522004c0c2074030000d0000707030610040342c0f00b803c0128020f22030b12002c1c0a00005c07030040043c003842d012003007a0407090165001d500e0000441c40900b03040c40906040d43e03240da0600c1c80c0c10402c005010051104c00da003503e030780c0c20500c0040391000080c0010743c0140d004400454403203803041c008a003085000303044001920320b0130303a990800c0e0011005181d407241e01424824159690703000072908212401401c1d50544924004108070000f05a000e20a220200d1342100c070441c10840942c1d90342c00c01070154441513840302802c1035403800240086580040340b03288050410359101c400900c0d181068924801080407000140702e156400703555020145821641413007880c850f49000703502c4051000c18000d0b84a0000b5000c410007031710202d0200140310110440e640c074034010b04024010245411304603814000c000d6a58150343c400942c02e038040c0041b4101841103e03042d0f00b00001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 98403795 1250 98402545 98402561
    0x30c301b0d0501080a0c0e070905090712050906150a05090c0a09090c0f08070305040b041103010e0a050c01020f150a1a0418030e0613180b122109090a 66
    0x40035420070003040340000c0390242c1030081400030002d198a000c0c40c980580404095003000000f2a280ba04000304030b584400490708403501600c0310b0806846889013120308502010456028606050520088d0000007170608c0c0b0516000f00040f0701090172008002030302e500c52141e80c0d845854130700481d10021700d69004055200d020700f0300703da010350340b03455040640300d8031110360340850b00c002e650300011500499960742c8400365280c20019460701d6a00d0740035900000c0d1010f800300c043c824101091351002d40c00305005a20840446101714110b02e0038a945400e0880c820740140100b050002481c000010b140003201c4c488a280800e40da1405840c80c01003401d11740303512119100380ca481e440c90300c442c031403412400c103000b030b403440c1d03010031810b0180120b9141602a80110000c001800c480c6150811000c1900c1d4803c0c49032684240410810020340b401500e000c0c1d0124804100c030410b0100054030030414200b400d501940c0d6110113103125820300a004906800840c96400034034a045030780e0021139 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 98405045 1250 98403795 98403841
    0x1050304200d030f08070f0f0f0302040f080a0c1e0909031e08060102060907050f010c020a030203070b12060423091c050408010b060c0307080c1002030c30 68
    0x1030490444000120324200010083d408118607107080a0b11301c0c2d02040b02da41c00461401e0010903100d50240040595400c0450182046080f90301c180900c1d03c03030340443d0003c0c054070000c41d596540300c400850711410104e0048030007109040c00018407403001d0101c01c49503410702c034017152031a14056514002c0c20b0460340840800201815400804241029900301c0c2201952170940b203260120003e850064041e00b40600c0c0c1d400540c04005a54615021b06401c110a103480c45c3d00ca00b0038804905002d0013500f0081d450b026400c00850088400405400140c100d441c0f600c0c85900d0707810510084481102c205010b50810b0350720940c8414002001b940c001410104440c0c40e4002c5032243ea03a0080c031004140001580020200001c2009004d040041a4111216450b110000503059034a20a04400811805000c0782c00505580e041c0b0009242d460080000e651745e151214041f9040c0d480200a003034562010490800d2455407404610000880c1040e24056601e58000c030002c00419040545 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 98406295 1250 98405045 98405093
    0xb0307120b060d0606090c0f02011808030703180206070503191701060f02150702011a04020c0d08060604170a060f0510050108150301111e0a050a0e0612040f06060b0901050304 77
    0x80b1b441803817007860001039840e40e40c0500400320b400004d080d11191440c4c080c1d040c070440c103a07902181d00c45084a400001609000400401100c25040e0211510102030b42c0141e000c14a80c1c14020040700a0110f4901d00710500d80010600c00141c2d01160500820140048090f0040c016140104481c1541d80d20a00480d8101c40204110701100402150b500006175140c5540300e048002c0c0740c1d003c0c82901022a004c0d4208481d10300c8940d83c4074800c446082c1000b0030b0030003040140e1a007004841c05071140349444400311108610f41547c8a005500440b4868904512005403601d50710134140920b070a4414948040c2c81d00004441600c40540304420b0b401320201140c045540074883c1d0b016947c41c030b040c0544c0b5a018800f803000414001d8002c0c0841500800100f48a40e501c6422540954002d040218600c101e560104003503000d01c1c01c5186041c01007005220500c0621104040000c1c031510052101584234109108580207800090340424428400300e0001607502801404100c0856480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 98407545 1250 98406295 98406299
    0x30f0f010b04120c0918060b030c010e04050606070c0305010b010f0c0b060120031318050601020a030c1704081e010c0203090918030f07110d11060703140406030b0307120b060d0606 79
    0x105c01c03989515204400b44055144000802100b405003004459045010300322580f80c1e0000a1b01c49025820168415561a070024440c1e03a02d02066440310b42d0001d00d0820801e4980c42e01c2c1307008014203003040340458101440704040500c240301d0311100f947c0c0085801201d03140d61006481d6500740d800b003a6441802201c02034004241000030740510a50a1020f00c0c14900d401030400c900388102501d20040c41c208400c100340b0b45d80005a101c075003079061802040303400f400e092410035500d810b0303440106070200207170000309035030001654540c49642680000c01c0c40b0075854400d0881c3c0d40c011818001da0803d0050320a04d140654429500c10b800f211151300c94240c3c4034009055134400140c40031110404a03c01040c800320080b0b1461058096800310180301081c0c80d849100341240c00c03140c0c42890001086000c26214102032100400942242d035104c0352a0039001d0040e00c00e0001042c000d10604900040703c82ca0410404c0480d80c01c500c0e50880d584403242800340e040e80040301500c1213500d6402c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 98408795 1250 98407545 98407559
    0x6040e070915020714040905060105130908071a0601020f0d050f0903060a0213140112180210050319060f030201030c020313030b1006081b0901090e0a02030f0f010b04120c 75
    0x325030001c0c150359001d020894217161920380c61003010308169004603e82400c140014800090362410360743c084035242c4a03104000320100c054030035800c1c02000c0a2000c01c0000400210300084074031030701911141611aa20135004a0340d490244504460f42d070300c42d55296000c0b900a800138000030450b035448925140c0003230f000c280340400a80f19011155400101440740303015100c012805400c003241c07616000104000001d10340e120f851400c032035480ea548910b41c03203581c1505070903600d241d01070441c1101c3c83c1707001d4001d003141d00102c8403450301d20100000f0075802c422a00c03680e8150b0741c041c0d1b03207000e40c0341c11030300110001e0511030005400e5200400170364800114203d20346009510035140c0c02c2d03e034075104801480c1c0640550145040c08620814400c0e0440206070b20702d1021108160b071900c4d060b50364012201803015a014036240f2800b04140000308226400552040920310740030085501c03456040c903170103802403040707140484050006110100701c400303444110300d014211054004e0f80301c0903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 98410045 1250 98408795 98408819
    0x60706060305101107030203030705030c0d0e070305010b0a0302010c1b08060109051509010b0307031517010e06090604030917010b12011505030318040f11032a040506040e0709 77
    0x1e4403958850644002c50a0f003d000b03081c01d0000c03c203849424108030b80d502950380d01010304481c041c4030000c4001030003403419005039100d0f00c0c9111b02c00e01039120141206c0391503030424081590030354204444541142000d0641804403603060b554441100d1407034444034801d051962404884096a03000096520010858103000c0c004c000c400044504011044010840c9003440d0140110b00c054010005c4c1c401c00b9055036404049801c0126996400c034808103902010f0b40c001402484000c40d880241d600150b11400c3e03070000501c200c408903210041090368a0f202101c1c010300081d40c0707210901030f013521801c03800140c040c1c0c01d002140020540f000507001061030054402543c1d50340038420b100111544e52140107100550140d40341046964903c0c2c00c403101400386a010307075124002d0202006580d8002c030013b0030002e414940f60308100702c510a0081d5002c00d03007a4100d480f5000d01d46a14000401c980c101d40c4000d001502d0036140c1107580d1600b4000800000078007030000700005036007440031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 98411295 1250 98410045 98410049
    0xc140601030b0f1605040509100506041203090803120103150204030606150206071812020f0a0303050316090602030304020111010902030a0c09060812040b0304052a0a140d1106070606 80
    0x3001000b95480c060b40094440c010003082084880602c080341d850b0150094101d031b0940b201070311000d020340c0d211400c00c100c050840e40000c1c0c0002d00000d00180014446510078462882690b54899031139680045aa0b2401419880c034107100c402801040010a8080703000c003e0203401e0030141c10305a41e80c0301c0f20100d41513507100400600191502c20101c5906001d29075201c9410b0604242524501061000000c5c45005d007090201c441f500700425580d036020800980d4000405803074020352603241c0181280c10981d4080a000c80040008070072a000780c10b000c042d100786034021400c5990f690011a0807040d04989440e080d50f903980b103440541c5041c802062640e02400941b58942d26100c04030701118900e40c030131425600086000c2c0d45144203402200c00701e8050041003900c1e070f1984d04107142071441c24019403624245510303420080210440078110708480480d007109a00760790320b110344984001c130380d08160b104908400d03a0002640704900d80c0501036000c1d200b58100070700d5030744407411a6040d0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 98412545 1250 98411295 98411303
    0x301091805030c0d0e121b03070b13140d03050315130207030305040308150f120106080708010b10050322031101020703020a14150f07120f02090a050a0f060c14060103 73
    0x36100e1000100d0b003218072401c1105082e03d42081c6044030017480ca48a044508401f03440b81e200140c203548540d41008214054075412207031550315000540c29030440c01c0ea51150349500312032129034019030f113045411105580d416469107403a55681000d17952030344402c00c03140c9500a814210684d00c00b41e81d440030f448014425100003c03242070900b03010f446290018140450700c640020403100540791081080802141512542452240c4010131809815a5004100c6900c0b4018000802490540dc4140425001d03a003007614400301550031600c43c403046440842c0c0065441107a40c1d0075410700c115550190191400078840340f4110308040c2aa0300840b010390050f8080c841003414001644403001d02403a030742004012110080c41e40011a44c0300820500c000e5403401c0c0050703195030088940a00700d842242c0300b0488401c021292100075000021a240552840c0a003c1080c0c14842000c0742680d208464565000345441804c0b200c5000701c1c941110855a01099800c00403c200034542c0610300c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 98413795 1250 98412545 98412553
    0x30b0411090609060105091302070219060f0806100521070c1109010510120b03030301090911220e1014011508060915010c050a080903010c03110301091805030c 70
    0x40c0030308224a4080c05000903100b500120140055aa000400c40f006120706694800d0903180c0700781d109009001d0f95030302a40080d2540e0010214a04100005040e602c07541c44800c00c030142e4403400c564032070003201c40e01d4100003000c1c0c00400302400390010f4210784006600c0c0004540d00004501c1c2031000694080380407503240c0204404001490b04000e00c00d074410b13201d0200940c94000018482d40b1000001d00a1000541280160134002e81000003040f4003c1d080703a030b49503504c107161801804e4888090310710410402000000c1c0c03500d0142006540c0705540e0403505c80c0113041110700200260181b1201605c2101d41c0210498000e004075101c45e02c45214503d1190b250001252042c5446580b0108202001080101568490740c1072900215040207003852a103d81005032210006044080c1c000c0c459400c1320010024010000c08113010700341c000b80903003912040c00f9015908090340c000c20800080c030050102509070703805031300040c41c240c40181e0400d449845160a42d44030f4130b0700e1661a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 98415045 1250 98413795 98413823
    0x50d1b020714060c0c0108090a0b1501081e071409090a020904050702071a0f0f0304061b0207051503100308040602010b19180911040c0908070603020403031407020109030b04 76
    0x80c500190641c40000e40e0f2051500c10038408454503109262035a40c1848140004980604001c100d01c200b92a804500c0640c81d0426903410021100c840c800b0600081000000440915204400c445986d24501840503240c84940c01034074134802410030400c0500f0180700b1849585e580d52821030040003151401039a038043da1041c0010b03907000400d94800d640c0507403020084601c110358000050421003107046c2d216000c2c0d1078600d501744281407040401c15230100511060052590200c100f4071030681f5070041e1009082030581e120709c458807920341e00400c00c055038022200c40b000119071103140c1010800034541c49558110464009411403401030395030701006202d508050100701c0000e8840c408d02c54090b40f801026601c9040d0000d0480340c1c0d00d46945000c01004449240320074041c1c0014014070441035500d20040c942c41403803080e480a4400d5803c0010103e0080c03080310140c1e50166100d004103e41c0301e9028105610052040381040031919000001c03d00d102c140343d0242c1d20501010f21585 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 98416295 1250 98415045 98415059
    0x204020d11120a02040503060103030f0c0204021b01050105150703180806090d08070e0a0311010306051309021302090102151513060501020c010905030606010309021f0e15040510050d1b0207 83
    0x8000102003503d40d5104002c148034540d03001800310704403903140c074140018050501c0225040320203a00020b41080c00410448030644240f03800200c09120074008010701c0c1e03030310420000c005012011010341c4101c200716220100f4032410912140304144d103442424103076500000c91800c0c0045400c204581c001c200540401c0da1b200c140f840d04846940b501c9840000c060300050140e00321440000c2c4465040c10304034003564003d40088004020041480c1d0312900b403040708002425028004a20561843e240c40c2c6000302d49100381e034012041a0300804040f100007200d00d4001c00081c29001540e02091004282540c402502400c15202082c002c00c0c405d2030b000002e0715014032049d946040c040240410300079601c00261680e403180c42403030f011a100340f07140003050701403c1c4280d0700000d426051035502201e5802c910030071310112040c0c602c8010055618049040c602480c007945503c0110b5240c0301e680302d1711510107400f0004807400000360340e24111302580c0005480803080c1c0096044030200b000341c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 98417545 1250 98416295 98416327
    0x40308090607020c0f0111010b03060103080c0d0503010f0b0f0c06041104061401080a050a0f0216021008010803070b06040e160618030809210d090906090903020a0204090204020d11 79
    0x180d40024613000d00b802c2d002450741407035540c03682e042010201c49002c0d41042504484e221032400350503035000796107a00300000180d10804c2190f0540c070440040180043c030607412a8121120352044100702400c0c2400401c403640b24440f20420302d030081c4507004d1100c406003d00b5020b00d1040c100d04121103005030501060301c01640c00405804030591546081da41c00c501c4442d800000390000040c1555452040402040c80c4c420000d000780c8041140400224489621840c0c24002c40e0129031030710840c1e504036040c2c030003400307040020b8100384021000945ca98441c1900548000c3c00810f4080c0c02e1f040d4140b5003916040d00440040c95040c04100c0a500300c1d840410251074100044100341c00c544030403842d032148110b924090030021510200c401c09a442c018030a00314030040e60981c1c0d03c5044001d001c0c4400d0300410401c0b034a4500b000503828041c0c1710f003c071816415000b403c90003695400f0400213140303040c801e0741c1164080000d49102c180901c5001d168442c032421050f141c0c440c22144244d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 98418795 1250 98417545 98417551
    0xc09121605030709140a0e16060203070b010509040507120809090c0304060b120a1e0b0c18040b13051009050109020a080a05011202060a02010e0d0905030c040b010f0e12060403080906 80
    0x744c0782c038190000b99822a5a0720440c1c2c40321022201088200c0d41e02882413030405118410440106440700c00304440e03901000505036180a03030150b1103030342d880740200291408251001861544880800c212010f050080e641000340100086800c00350140c01203454403000312034405010b8070000401c01044100e220b5541e0713111080e50140442940386a9583c0d03540213528002d08809480400c11b216080c000107800c01541d80720651595600340300e100d410340c07034001b481c10340b290b0100c8810300165402c06202c0c4143d20070004115003440c4400c4c0c2c05103001814003411810300118032003c08142a8030741d0050a000303100414006a441c19602d60051035050090301111003a403c02e0010046951070421800040c0e4045500e240d98182491091380184100c42500003d07018410802c4040398021078a0f00495000b541501c002d290701c0c40c1040300310f615080645011031000307402d00302c6992140001440b602c00c090305022500700860046850494202e400b200058500410094444010320010350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 98420045 1250 98418795 98418809
    0x70c050721031d0f0d1401141e09060106320408010f0501081c0507150501050906100917010603020d0f02040b0901060c06110d092102030901080c091216050307 70
    0x16003400d00740c00900c100078414480c0d80b007505d602102c10240600107810349000c00c045070081001c400f100315000b40c00c2c0c404480d40c0390002161190444040c1c0b013036581600c9003642300e01070036081e8206507065075040d000244d80e00d040c00e440c2142918150380794502051800e00301110540340c034509440b0f00c0c01d4cd241012200d54080c04c0000400c0415000078a0586503070443d18076500400142c1d01c11112409800d034042e000c074100c03c06403841d0364a550f1120303040e0b80041c1c4e081582c0c1d81d00c0206002c1c24210343d2124000080d021241003001c401980b201d020028074410000c20495940d800140416009400031b603024000c2d00c40e5942103262034407904c0140c02d429a0748081c550725001c07009c0d246101d202405010705489882d403174400035a072404c1310000e40d0a101c2c1004a041d00d8208403080281201e8200c2005101c4200c8032095800081600d91026050b03403207034020b032740d504600d42c800e40000c404a0b40160500310380c001d0225041c841144200ba440100745405440c00d0101032070403c10b688590 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 98421295 1250 98420045 98420087
    0x309140d030504090203070e0a0314010c050a05120601021c08160c1a0c07060507050309010b010206010f120602040f170d0e13090c0b0315010e030c030303070c05072103 74
    0x10000b5040401d03102102c4942d41c005880b81d8131801c1c29220b00142004650f07121011110100400c40040006070b040e0306114001c2004a80500c000d803860302c2980240d0022803002e010815410f403100c4489580b2040c1803041d034161a02c80041c03c0c9a10000301d0403179010682ca00100000500d480e540d42c2e4040c0041d140c032541070380351a00c81c070703858400c0d051007220b81c1c10980d4005520902c0354011140a658860740800c10f51402c110002c0c40c81d0002c1d101e0002e29428000c40d83c4880d0300c0000c09078103070341c54032865902041c40c108a44000d81d07459003040f62030070b800340030018001100101100003482c010485415443c05901030904007440c0c60008420300500a4100c0c9217921107043c00e406003408810001404181170403e4656980141e104149610001081280583c0b10300c107a0302c990700e02078030386001c04903c6004154440d03002c8403456030164001d01c00038024505c290b004074649406101510f012540780c6014003d2201d01034040c8010401c0290342800b0990b104000c20160b0350b00d5110f038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 98422545 1250 98421295 98421319
    0xc100e120d0903030f11100501030506060d0209010b0c0f1009120c031209020d0b01090c11070b07020d080d0501030803010509151003020a030f05010906080c0108090606190302030604030914 83
    0x60b244940900000e020006801c0c0140e038440c1c054800c05850100741c02c01c41303480604529040001c0d08003400100d0319401808003003495410124800300e151075004200411981c00c0004184d800e410030314103140700b442440010401421705100e80c0d003904900f988045146807040c1410000390b64020000e41c1049003074507015012070351080b040886130716480c1d00402c0d000c500340002260015586400303411803143c140006141a580d610041c0004001c0d110821354000907040d29445818504c104c40341034008020041c014a0030440e1031400c1d0b84250509410200f12150b82000c40b4000d801c2242c11410000041c042494030a40301640300c144900201155205031012481101d5400215001d0580108d01082c0c4107003e0340044102c82c0c807052040002d5a9201480d40107800355115900980c0a99030041b0682d51080610034441d00f0614014402c90301d8020600c100724040403003408503035080c3e01c1c0100c0141c1d030a0040c40d01490095803242c00c1c0310b0030808442d202d00c0c074034000c0074441c1e8800140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 98423795 1250 98422545 98422547
    0x9010b181e030102030f09070b090a030213110d0603020102122a1c020102071403040b070b10030804030b07020606040e07030b09010b04091a0705030103021305090c100e120d 76
    0x8106906401510a45000c841030000011203244101c5802c0d45940040200052000c030b040c1b5441c419090784d811659602d90b1911400820701c40d4562140d08886405c00030b101506115001c81d4045405800000c0c0c4407800150740b00154111162100384a40c48403010401e40d0b904101c41c00030180300c241c00ca8a030200012041300d0500200740280e1000407407007000c1d0b4140c2c0050010b16207014900300d41e000d01503e0460024002c1d072118004a03240450710b10081400203001090320152400041f00e1031400d01030b40c40703042000c80028402000e43c800c202c4080005200903024100841c4107540c10034890810000280c200b0000034006405249400c80140d1540c2d000078901e012290000d04d00e0700345440355a200c5014129540346ca98106e41400c2115041207a61040c40343c90031940040b801013074131400c504941030b00c0280300195102101c1003181156134a294030840e08070b41410100e07900d4201100100703612000e44140c110100d0303032051203140a030511000f011803e22505016156000e075690f8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 98425045 1250 98423795 98423827
    0x110708010e061024081803031e010b071101050c0102130303050409050f0702120703021c08190507080103081605010906020d0605090606030c0a110f060a06080604050a0201180f09090209010b 83
    0x441d10204094440898a40c0d120b458251b170000405034103985e90307032910703481c004a008103040f5001d100300f00f04c80000840a1514040d1100f07598071111540041a48400448258105800c1081a03541c2006100400041d40780342e03900130342c030076100e980d05e8910b000b80d100b0441c2c0b0010484daa94007458010822513940c04541c02401e8404200317130703c0d00c0d020541400c901d841c110400c0d005000340c1e0303080032450b01600300b41c9547c4030b0049030a1502540310301d13a0010b000d880e02501c4000110f001030005200264940015002002104108601026940e2210390a44050840c20b654041d80055890b0310780d801401100017402040c0d40b8030199051400208005110050600b40780c0b4001103001407540d44920001186030048030110703100300c40f00300c000340d40f110750507100c121207186480b50000704141d010030102d2040d6041405000441301c141c0054a040c0319440c1c00041d2030249a5020991509680c56600a0541c1c118001201111803042c444c085030113030054144104140090003498900300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 98426295 1250 98425045 98425109
    0x30204020a0e030102032e080c0609010521010614041a0309120705010506090601090803070210050d0e010605040b09040209182107061b050703110708010e0610 70
    0x18400503620018120119114910188480d81c907500001c14082c00404203582043d1144d0b40034021040c40241050050b07810341c1512403110030360440e0713030100c81c0391400302c024014815060500342c1c500104160200d50038110015015403917002c680040c011940e01009448021b903070780e80341c60710f01818400c410441041d802041401103c0000000b40584030501100314040510044c464440c1c0003454601c2c00f0740811600f081c0150409400114a584603a9204040740d000300055443d141c070b40e800b032000e0040a4640d4405000d020800b1090340101445032200801c19400000b0b07110342050200404e0b1145030424170f1260b0201014003015907196125a504902000c600c3d403010710038030f8405400d05c800b82c084000c100035030010000c11042d07180000c042c42c42c03050400f0000803030710808801d62b05000c0101e05000030024092880001c0c0a820210000c010030800c941001366590b503547d081d103105c40b500c6001500700a092040035000380790350078007501603800c41685402054800f03054105402d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 98427545 1250 98426295 98426299
    0xf0f0306180209030c031515040207030909020903070806011205070b090604060c0302070513020705060f1b0c07051002240105030a03030f020909012402010902090402040e1519060b0903070302 84
    0x50310083c0f659042200402d00d41025003070341d00d4116200307201e880031901103428104980310010b02909501e01072080390082070f4152a00100e250400001030020f402c8002c456401d07200d0050045000801000614000c10740c44c2c030f17a03507000761452400c0d80c00d14071700354004c006240c410b00c030f041100e80c0c6070b0b016902603440e01e2405059400d454207080380381c200d40350300440d00915140e00b0041042d40030b8000b4181c85005108031010380d12000a520f4181c48100c825850f0040c1c9030180501d58075154000340180c0c15000d0031101e2094440002602101d008082d0b8070240e444040ba10360116007502103950405540440c100c2a5071610020039182c0303080000040070150b40c1c809101c1000e80580c140c40c0e503a540500f10300244d44e159030b0399980000c601502ca84600c43d0f007100c84016148140101044158041c10015254543c1e40c00d01010f42085003400d129801070507140c0c599407100b040000c2c4100da0051a41e004185680c15080c1100c3d0140c121980041042002649030784001400343d01b10703941 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 98428795 1250 98427545 98427547
    0x1090b01172e0803030115020604050a080f040f1707051c03080a110307030f0608010605010519020a120f17010b19031b09090b0910330f0f03061802 65
    0x2c48000025a040ba02c60600084900500c0030032010000400356044c0c808038445e900c00209410300580c4d03103035030486004160780c2c4100500400240450040c08801050110084c2030907151003140c031102e62590481d128100f012120b00248210800c8840b009003416074030f03040c44601000300002013050048000d0144901c44010591182d91a446461195000c4840a07180d042120005021300a42050b004000341403500c0820304c0c1c40103104010440d903050b1906881d050380c1920031021000769035003010a5008050000011a03031504118481100075078410881c001101005804040c0b41031103554416020801408210b00c810700315140403145110b1514031145010702200130300840101c04400c4001030b0550740d00c443c0c220300c1850554448120911903c2c0e151000e00c103802c1022a0501c0c52001706000030084010610504d00d81c01c00300d00082400704034412030400c4d034078480c2c2200d5000a001c3e030301205e10b0b21340d0107107841d8a120030911302488054030740805288010040314481c058194 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 98430045 1250 98428795 98428831
    0x4030f02070e0712060b04060507020d020316060c1208071409150c24040c0303050d0b06070803040b090d0207060e01020a060606020304170114071b150501090b0117 72
    0x10003002280002d01c040d5001041515210200910f0420442e6800096900b0001d0108442c0100010340c0c064a20a941c4d4500342901d540800404454005042c0e03014080c111101841000b08984800034013a40d40fa0213400c15401d1409940c1d098400d0162401c20240400b07103d9500c1d84503448174459030910b0412a21030145000140032042c800c00303080c01d02c40000910004036480132800c1010a000d90707482e1081101c0300c40c100a01c50004131070060410607400c000b440003a010350003511344c041543c140000c2803215100800d14035405a00190741c0310a010080104000702020380a61110f0b07442c2c040c001d907100700034000c0c3d692207060048900340104584c000110364402c2040d042c0403a081041444410703514400651603a21a001d03040440c0054105001d140c0b8050041d100c1900901c140070041c2e1f991001c040754810500541c000c0d0015042c5910000700382c0381004080803803d12400081e46501d4034074480b00f11000d1131112818000300a42e0450100c016490080e4441d10707240b46000303284 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 98431295 1250 98430045 98430047
    0x3020a02030906180301061401020706021b0402070302150109020715090b0411032503050c0303030108060a0f022803180804030b041403030103060c021005010b1c021c2306060304030f 80
    0x35100e0b00c1121741640c0fa0a00020302c01c4142203a46012031000c2c2c00751140c19490310300480c0c40d0405008110081c031200e481008450515034018100c0787d0292060f602c5601c2514100d800f0b80340c00ba0311000c1a160040b52030014400050301035070000d40d054604000800e42580d0701d850040000707001808100c010003e0842d103031000c0c0002091998043c001c0040414440d0180410510030301003681d40e882080309645543c10004210f9050302c0c014801440c099440703503802406441103544c00724032280c0a00002c41030745110703400620f40202e03000101404803102c1100a00307e906803404205e440c6513501260000c41d000404a9059982202a8168599aa0a060551000c03200600000707100000002041c04416803241051104550940d6003c00060045a068035170030700403100b142c00d04004aa0700086042c05050541c1c0c0c19000140c1440781c2180820324080c0c0b6058030082503500c5540f64262415222200c04481040e103801101508000011540c1800010300003003e002070000449486 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 98432545 1250 98431295 98431327
    0x190605040c1814030a08130e0403030203180c1513120b01030c050f091303181805130f0807060b040501090b030d11060c0901030e0f010c090603020a02030906 69
    0x1404024106211000207844010410000e00e141034140d480c0548000c180f0760840507102c003c001c0000c00074204200140c030350032411b41c041d511056501c51100707400100c00c140007070441d110324043d0b140140ca92804800da440b0b10390700c0a60741c0880790030290851500e60764244d044680e50388000b8079130f510b0700f028031401d04003c2465080f5607140403044000608014034424400d053380d11840d08044d60341d82c2c2c1d9040c403000741550f04840c1e130302051800000d0500741410b02c0c41c25910340685010101020200c02e00c4005038010b41156500d0050041d90312640d1125005860300010407844c9000d4031001a00e0704803200842c8800200208000259003080c04102c1d0021040010018820801541e552000100924000301c030725000c0d01a180c4c5162805014090b400084960603024081c42d42e5040303c80a047d600160805042c550303143c1040501070700801268081e001a80000203003910501d5004d006500f1035849501094010081781c0040d60703022040d11281e6205580c0340f03841d000d0213440329101d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 98433795 1250 98432545 98432549
    0x40b070812010f05120a020a0b0a020a2f0604050a0e060303040f0e0a0513050604020108131e0201180b0d1505030a0b040308160e09041a040305030912090102061906 72
    0x28800c0d14000403c40101c1044400e080300c40c1128a80e03d9803484480301601c4480f013501c0071b50f01110040302045a40b007245c00501c500c0400e4410354a10604a41d1001c6200440080c1c1680d000301ca07010f03080681180488291809800b100d58604007407421000646181c10fa010745207840001c000416041c2c0c0b001c0060320060103052618121032030b2a16200c203212031044400d0003103241090003061504d02a54a21548603070450040d000c44d50311500152100304014001404120f0350070701d40030102c0d000011100398034400350300d11804010540001046082c00794030794506104001c001300100b600010480b41541e540410104070200072099500211003954000fa030940151003140041040455010780309034400e0301c0d00c24203915954840001c0000030001600440e0b504041c0c00c20500c0c095285039400b0f8841c00e0310042005c0310042e413006030041a64210b01143c00842171006d80e0005102000700619144091410660802c000035900c1c80060701112000400040540280354540c00041c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 98435045 1250 98433795 98433817
    0x40207020d050316110a080c15090a0305070504050606030903181504080d0305070509030307080706090203120703081311010806040f050903130e0c07030503130605070309060b03070605040b0708 85
    0x213211113011407105030702007000c9011160b000c200025a0781515091304180182c0325054024a02002c0c07050038459046614054181c2024003030221501c190340326520342000d107100c5c502410b2a10318200601054a001074542c40c0304007003c0c803c001551074004103551849154840030748a0a055501055280501c1d540090804200103400304880c100050320064801d82d9682c104550b0341e6221003100c1134010407030b08950541082003c41d010540120103050030700d0092038002b0b0321203c1a4000307482d2600003c4142241440483e150f0241a0810740c580c0d03012402d9290200700087c07035682c1d0007201c03050b80407941c10703c42c802010a07010389550b0301201180e8044001007005042c10600c860f501d401c211401d48a8441602010500000f04d07024207000b0b05039072050905042d850741d420342e0190001044440d00a005c0c00302840420107601403a07005150b80d0301c0018101d86542000d40c107491070000658020751181c00d08020196128088404459120401546840341c503d054000c038030980c40014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 98436295 1250 98435045 98435047
    0xc0b07091203080f1b030703021804020703030e060109090209041502190809191203020a05070b010b031b09011e1106041101021e07060f030b03100b030d05070b06040207020d0503 78
    0x41c04068004040381d010312040c2c40e030311080d40e91740c905028424680a6080440c88414070224409600030740103080344604c280e0301c41da42c030701c164004142240c2012405400103900d070700701c3e48800c0409010b20303805011107200a1000c00620b0300820038509025000900c140003008041c2c1866080b641a56803c01103a140c880b115002903000620401040e11010300c00d02030080c1d452288103513100107e0079a60b0007110000c4562803018264001d4000001e0301c42444020071218000415119005018000003841261242441d40e040c81007106540840d0040b05001c01200c942a80c01141407100d102d0141c0305001146403000341203a802010f070911102600c11030303060000f004029a11036081e40c01c2079003181c410160b00d15070f80c1c50400d800084903440b60481c0b0f030f05104d0f00b8801d8450104000e02d5041c0410b0405664000c00d02d01540300804080310b0341c0e50499a0754929040c040841003e50505d0142e06189854594200600015180d14455980055243c0441d12040ca0314242c0c59004400c3d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 98437545 1250 98436295 98436329
    0x8040f061b11040902060d09030e062517040602010509011d030d0f020d020403030e03100b0d11010314090303161d2101060602030a030f06030f082209020c0105090d0c0b0709 76
    0x21f102809408404801240042c480000e00741821020707190b25184840c51803440c0800b00c0100030301442c0e00c17072040d207000d642043c0c26240d035644140140020a5250300014861828030303000e60840794402624616000d4406903c0e203013a03800030982d419200401000644800c0900d13081009100703010750074078a54004a000814142c0100700801c1010066040d2141150308403d03000441d58000b0240e540100c002d4161804542540b403100c8003035006040001d81c4240b9004446410b203021696541a6400001080b100031130300d8070301020320301081c10004041d0401705411001d1a246225150003440300e850034450024060400c0442c41c0000c90007040f1117504ca441c025200d074814040c3c2c2000ca81070401c10310b00300342d0502c11841241c0d0400a200384448140d5034042d1554050003101c0a022003028120100c002018a104000c0425660040c0d0350b01140f11071509440c00180401c00e15002580103130070454111406901c07041e44000d50b05140e0742c44c0c107415510507179039821052005030071480c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 98438795 1250 98437545 98437567
    0x20319051c1a09060a12122705180c1b0c09010605030402010813050a0f0609050708060601030f060e040f051002040905040b0903030403020d0f020c060708040f061b1104090206 77
    0x10301c01d51248207071901601691510305000710817085108a8099107800007418010501440c2c1030040b03009685090b42c007031240c5480003003402e10003103044010210812401c018920f0b000c04003041040310000b40340e0752850001c00e10500707400b41c00c0c1001070f20f4200d0b44521500800c14040c140f5043c10041c003240c201c1d610b0703050013051600103c40490214280c407000c03c01e403030b1001c01000c1c0c03042d51210007001c1c400709031b03615011100c103280c0381103a000380c0784d00300480010014000760700070341900c00041c80e1501d0300000040c140c0300360800000000745011302c01e100007004d500300c00c0e40c0660007282c0300117104076525107a03140ca004080d02602c1d0510101d000315103008a6040240503a0107018542d82c503882d05003080c3d46034030040c1c4005000d070b030204045000079170040050104400301801030f00d0312500c0030b102081c0241e000600c125203084000509010044145400602408951808007030160703400e9901110748088800180c1001411207981020b541c864208281040d40a01480d4032038545240d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 98440045 1250 98438795 98438831
    0x3030e0d0c0f05090915011202010908060a0c020c0409050c06070c170303010302010f0311030403080901020c0f0a02031b0303040e100f03080d050a05060a0e0c0d09030503010602060106020319051c 86
    0xd2070f0320441310040882e0310b20100080c1a602c80307001044152659103414803010118440c0c2c0c104030b050201d650070000c0e9458042c40a1407160000e1000071a40a02c498002400c0010a020b071500c40c0c0e14040303480c004201c1c00560030381d90840076130f02d295480700ca505008042da0802e900038104a001c2c2e091121110a000c405981264802e80741c0c04842d504055041d404d0700e00300000740846503014000100480d200e8106e0b61342003004031000502c1c00c641d140303089061030402c05604045920003c216021030504000d940d01d003c24444103030381c80303a0000340000d49900c17032489004522105c0d44e000c106171050001c18030009290741d00c440c2d0100ca03503901d0100216004002d0034032056107040e00003511580c3c58001d0301e1240f8001004860054144414510318201c080d044100c203900903c03031660205418071580000c1e50190312141c0d12507160800080c030304a0160000c00c11908140940007113209a218038950010301400d01c0c544810345030480428001c1000350104800e8202000c0d5942414021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 98441295 1250 98440045 98440049
    0xa030f02060606040b03070503060d020303030a0204030c05150406050d06080a0b1614030106030f0f0507080103020a120f0204020304051f0e0705090114040e2b111603030e0d0c0f 78
    0x14081d40c4803a9250410803180f40201e210700e003a4440d04100041c2034034403d07802154041c0e00100406a5000c1a4000c40c0c81e5401c200c1c0c892061750b60000b03081c020300007406c440c0c1c4000e1170116003000c01c81c0024400e4803514041c502c0b800091020200e0400070305c480359040000501341a030304484c200503031424100042d04080c1c4041c12940c0c104160207801512400c80010b4000000000c2c2e0302e980d00e891021002403600031504140c5d966540d050441c024074078040d0501940d007641d2007407203070b50450042110000d00e540c050350300300d900280e8a02c001206040c0300c85007560129801616a926414518149102c06000140d4030420111b42c280220541e80280744403110107003100c15458943d810302194007428051111650384007410030b10b061400390401050094403070306403600070500208000c0c1100c131001c01c5460703088108a006c01c4859000d800c440011003003400900d2906400480e0001c40083d0f80805820032201c20582022500e0f401071155403903078071184005004e5625020806140554 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 98442545 1250 98441295 98441297
    0x121d100b12061e07030b09041506030804090f0b0105031911040806070315050301090308130606050603010308040509060108010e13020105161a07020c0a0915090f0504050d050408030d0506060c0a030f 87
    0x1120108221030305c640f00b403000c15803026201c0107075515191144c44c0303502003032404d50040c03a440f08000b02c00036001c0d001400080c0345801c0d002c00d94030174400d481d209072890913003044d04003c0140b04215039403112021000180c0215000000c2130403000d2100a02071045030443c046511031304080c401240d6042c1e002104614031510958482070721242094260340050030040c0000b160704010480e071a03500201c6080fa180700f0b10000911982d500040381154100768820b940200000c51300b001641003070960380798064001d1070003698540c14611a04401c00e400740190040c140c02202a03811039005000b101d258811580c4041807450561400004c174020341072850f804a00c210b40440c403401c2c00059413440360000140611403241c209000c0038014000d100006843c280350306000180c0c1d40701307882a000040a0030401181070324040c18804d01d00300d5090464405c005080008001e4041c0101c1940c003032401144003c25036840303881c00140d941c01050115401e81c02001e0f2080c04040c0c02210f241c00ca843d136 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 98443795 1250 98442545 98442601
    0x2190615060e040b030d09050913050d05030403081b040603180629030304050f0904060b0d1401050601020c0a0501050d0230070c0302060a0e030706060303121d100b1206 74
    0x80c20905440300c1606c081c100c04282e091400780114071380354407040da00c1021030800e40c1a44500341c840501d0090750551000c086030000061009042c0d000728100e0b48411240c03030840b80c018a0329501c8909104030711910f0100b40e5a00f010059034000116402c01d090303040b20043c0002d8071212446034000c0d00e10801e0440c07480b0507496996080c1008400c1c1d600302e6a00030560080100a0014000004001070044070f43c0b0781d5500341400b060f0f072080c0070000e00c0c600400380313485140841d514850842c0c80c090034080c150b40c002458100c10b640e0703c210706415142d00f0329025032102d405202100103801048002c1285005000488040ca2603003590701600c91059201031145031110801503903544e8500c0406001070300281c00054401409421030740000c071500048a140c4521510384008a40c0c03181c00480001d0b82c2d110000c0c620707084900603502c040002d408158208805904065910440001c40b540c41a454038079545299070b8101d80341d0504e600102c02e0316102d10b0040002801410043d100d0107440070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 98445045 1250 98443795 98443811
    0x10912050307031a0303120414030a0509090105121f060902030103080901020106050a120b060111030a030e0705010e130507050715020a03050c0f0d0b12010603050105060f0603040302190615060e04 86
    0x260b96400304ca40480041c0c045c62416288001e8100c820900030020b460039060070541110a000c00c10082035070307201a55a403a00d9022000412000702c8069001610610455804074074130880072071031143c4043d890303100003005001403401c08040c0080b41d002111080c40800008140091707440185000704099008000c419150400c21551406038043c02c0301901041c04d0312000103603a0362210380c02c0441410302c3c4242946105900d49560300600c1942c0000b515203007620800b040800c900390103000c4c2407c02984070804080800e800500b012088140c454403040410341c89070044003290181a0449410501c80f81240c10b003038007943c800d80036100000d00d048001501e070400300d07042d10f001a60080066242c1495110310a01416080e03454075403088007031700c80034801c14007445008019407103040082141e241070410080600418805140100700410400000a901240c920075002524800100c682a1342c10000d0041c9103160031800e55803060300c00850350580000d42c1110003941101d050007030f00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 98446295 1250 98445045 98445071
    0xc120c03020918060118110a030209120d0212030a090804060206070e0a0f0b09130e011d0a2619081f0506090f0d020402040f030317040b01120501091205030703 70
    0x1034043c0c2003000d8103400150040c0805220258101c94405025201040045115503c40c1d07003a4000c8518001182c0e0000300d022040c00c1424000004002c8503000d0041c4041c600ba001c4c3d1a4940c081e400c1c080344c031001001518000803507100c1074070103800075043ca8031240c40e000c021b5603c6100340c03143e0000c103181e0f1a280c0f26900d0030000c41701c00c1d503603010901d5000c41e00c0d200f000000c1e40c100400642c0d11a81c25070b03804960406a11465012a2014001198040c01e07040e9242c0d01c0801007210750166017012410002140fa50906014456040341c030800030907038020440c1041c1d000e442a12178204820071a07031580150b008036864029071222140612a01985000305d10301da84078411035400660034800c640c502e10349040c81c5071a0000203000f243c5681c50300c3d0700250880e4025005860101815002441403683c8070042c500f4803080d0400342d003601d0505440f5074500350014498101281002182c030010020203410120341c050f4829003013440150f0554014115400442c1c04400181c90400402104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 98447545 1250 98446295 98446321
    0xf070e060310020703050c010f020405010e0312030610020708010f02071101050a08010b1602040905010e21070206070204020906031512010c120b0105130602030a0e090105010503060103090c120c030209 88
    0x34000140240b819220302e111210103034200d6601a0305200b070501c5134150001003801118044040c4e07080041c0d950b0304040c005085000c0f5000d1b080d000350b008c80c86100d18260300508a0341c2040f8101e0702d8505000800c0e46c100d240450751b402c110003a5003820402c800080302900a05010ba100340400040040e040c00112003a008e8280d101e030010303400307070010000a1400310040c001c0300e5440501149000064000ca001c0d504201d004445c1c5a540d0701c914a03292800b803060486010005180c05020ac0b0080c05142160150340800b9220b001d0000c0d102086690f0f81d0304540c01350f2009004542c4074a0950b04003a4050480c88035140184044135161089801c184522040c5074200e0321050310101072422810001c00030021200d040c40001c1003035801c004246500000188515802141c2d107101032000142070500402d9a075004108980060003545c3c0c10000356540300c1c200386800140c441d0301c0c1c200030601d13003069484003900402c1c55030400c0034008440310356002e90380261170074081134603480550715032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 98448795 1250 98447545 98447551
    0x509010206070c061104080f0c0109060903061a040e011506050c0d030515030303010b0a020d1e030b0a15030903021902010f050a090e010b0901110c0307050d060f020307020f070e 78
    0x160004000111030502a1032580003150040d24002803188176150710005c0d80c0d106400c04a0554011800301030b80382c1040104c81d001c25000e103051a03110349007540280280c045400010030407622002030007081c103c4c1e00c01c0c11b600000002c1c0103000140101907120b00a00f4803408400c2d001d42080804140b0a00420880c0c4000c00b022000b44907070b240782c400440041501910045204040c2c0300501c00d0761781d0400c040c6010704840c60405680c0d801d1080081e25100b040c0310001e040c0000745440c0202040d50347c03000e08010307065080200e120010ba900160640f901c90301718407013041c1040001400e4607810740c01300d01081e2080e001c42d0820800d0b81988210b0002c542e1000380000c00d031102480b041d034841e00180040c2c0e446c40c101031000d41e8480340322141030341d4240c008074000b490104200e0b8007036034040800601d0700c222401031329171003030180040394803140540110307405115182e4544040006030b41c05102e14070002e030001c54607030a22240017500c4049040d000a40c91041b08400310fa00c010044c10140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 98450045 1250 98448795 98448797
    0x30201020f06060616110402070b09060f0403090e07020a1205040f06050c2d01050106081608100b09010c0b01090204090608030c060610050706180212010204060c02060d11070b010510050901 83
    0x100384010000329a9048403000d0085854000030f01c6c0c01c07081515240007814045114040ca11130b60300d0a0354655240000040c140f00c5088540d0040c040401c0d0041f0300c030401e13034290b180350b0040d551340e250040c2d103441a40500101560303104407030010100c1c5c4c44400341080e40c3c2120b0040c030001d43d890703c0441c0d103405211144c110340e40144522104201c0254855107210340c42c5e81061207640014080c56084070701c01d07844600071071025003c02480105420b40c1c080300c00100d08100d00c80f41490302c03000d4180348040c0682c00e811103001510320243d078000e41180040650003503a040d1650b031101e84180c0a9001440b03130000042c10500e01152011000c41514198903a0400a010703030f43d509070402405203480300300c43e024820204640000704140c3d008066001c2003100742001354100c00c2c0305010010380100e40010301c2c0d0340305000510100d0341c413202511040b0f0f012a07404e40c89507520130040005003054100c154660a0000b01c00c4108081642428101c0b0400c5454001e4500110025100d0388115140380f8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 98451295 1250 98450045 98450047
    0x406110d0501030b060a180213170c01031b08060906011e030b0306090309060703050d09020d050a0b0a0c020a0f0206210a0c080105060f16120302070b1b030105090c0d050c04030201020f060606 84
    0x34147d0b00c1d06501800b8020170004070b4001082c0c4d19008000788a01c00c82001103140c00c01c0c01442019601030180d07100c55a001224074403a102d0340c1500401000d0040c004500c120341c10381c086065a0710400074141e41541240204040308814480134005001a9103401c2c040c0c090b68001035524040401035680518029080d10316160096804680a5200c01400701e0440c0d41c0c2e03044800541c81d0605420b0300c240c8550b000300602c040500b008200c20304002d0003070001904bc645041d00440e8081003506820f94401e1840000d0040d034400514131f8011030010340f0308181007050020b442a0109a42e502504641c013040149001200f4111042c4609005040d0005030803c54841031880790801040e0103980d46104100b050b556950717412807035a40303840e001c0010340c020848200344682c620720103801004000e081024800d0075820310450740414442c180c850490f50001032124041e20040322008481d0442c20011f600d40000150125000340c0010b0b40140714014840d0313a00000041c0e05e034003e040c024242 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 98452545 1250 98451295 98451329
    0x201020a080a0513033e0d0f0506071809020f04060c0203031b0c010e03010b10052104050a060c0201020a0207031104110318151e0406110d0501030b060a 67
    0x19480b5400808000304000c020080c0c1003c981d91420340344041e41c07144c4818002c02c8054000d4406640c0880018071a05504040c00d8400f0032660310384d0107407180160f47e0840f05c02d00a04024044104250340941140030303420070407121961000004030b0310001941c5002c420341d11101c0901c202d0041700210100000108011306c01d03603000304464010144010210b03450510103508e00c62040e001d6640f00c1449034402c04a01e80d031903804c0020320f00310210540080002070001d4000501c252040c071443c4007802400900b000c40140302c0280d80d0840e4101c540c0c031400a01341464490340d1446070705003d0f18414941a19803030544e1041c003c40f5a5001558001c0100c01d081d600c50341e0030075400008440d4000d03507030b03112060042d0200010310300c039050305c00810440001e5810354600b80101c8101401d00c14100808201d4000341315012074412210164080341d00d95030324508440208040701c050b1a24502c0480c1888507901241c2015042c0c0f441341700304c0461074441605110980016006410035662034000c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 98453795 1250 98452545 98452553
    0x1030302071e0e06120d1d0102010c090302040b06040b04080a0203010506010801080a0b180709051f0e041410060306020306030d0f05040522110a090608010605030f1b0a090303090e01030201020a 85
    0x100c07542180c0b0041407080540d0350f201400c0d262828446c0c082011400a40303a07078168030301000c81ca400e00d0b0b500b80020708c000311241100030000300007400003e00c01c5690300f40f101d81c15180e00341500d000c1c0c001a41d6043c0d84684500300c180d0346500c2481e00724402d609050015145504c40e08400b41241d140340f0007000795039403030390301c600c0810300c0107140a5042c2100600313280485401c22241c00100407480001509080845c02d03c043c0300b0131803c5500502d0b50995080124090320f42040d58050f070008260302d00754005d5001c8500303001010b040441c000d810000b0100c14441194015401244100c04a5410210109041e104030001010810119000780710800081c1044a0303088140d41481c0482d46001101c2d0000400b101c080d8032203440c041101048a031502504065400c000e0085400c0221066152003801409440004d000080d021022400305002508079221140d5000c00c20b200d00b80c48009640000300038440e40c1c802900000c2c1e040100040301c0806c0e88900f41600e8040e03001c0c00380760605442d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 98455045 1250 98453795 98453819
    0x12040206070501110313020102060a2003150d03051210050907030c03020c070b090a0f0b030601030908090d0326041505180d0305310b0a02091801030302071e 69
    0x1c82690155242c5044259044c4440001d51103070744821444043e1400c58000207107071440080201002c81d203041c14400130540700c2014081aa45440b042542d80d82e80d003002034080d0050314482030b41160801144c001056000f0000c2d146130051031503051910b0340d9034148800070131824444c054200c02401e000c1031595200745c0020100c03031002d090142c94400402c2c80c02e45040c0040e80301104145002c1020480c1d80380200d4030303c0041c00304200882c40c19082c0300740e10046110180801d414035645031380d10b4003001700e0031064408181c4014800100c0c18010300b0013804520000441d60b20442c04c506040409044550000c0e00031030b00b0110071079000003c00b0301c8900615014043c08440d107039150341c0990219080005034108246990040380c41d09100328800c804000303441c000c10035800c208689000e1a00b100c0c0d02c2d42e10030f5811880211a80d2140080c00d0028400c10b240c007078200c1c5803014a695089408440a03040364444c0e0300301c034007180c0c1d01d01c56010310761070042c503c5130104c2d82100b0400c1107003020350f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 98456295 1250 98455045 98455057
    0x90f060d02070209040c03030e03030703021b12100b121501050f04060807080307030e0d03020307060f0b19050a080703021804230c013e0307140f0d0512040206 70
    0x40145001c2d600d40014100400c12a0101c2d5002c070907000170b0041640c0140c2000050300160005c5003024103e40d80a512401c03260300d010b803401a4412038440555904900f0300140c44450161403809070300c4103820b8060510041030a0040d1176600503000741358000210f8404a0700f256030b01401503400c000030402b2001b00601c54590054840d2804500c03c441400202c00a101480043d075036000c4170720f400380c00000c030150414440ea1060003800c002c00c3d0044219105075a00400000b0482d5000318000d00404081c0d415940003940800d00721841d16244011205491003280d2428400340d40308110b50792025280802900b000c102d010b1a64603003440d804c901d4120384141980700c00103941e66018201e8410081040701144d00081e035406443d41c200b25015030a003110142c0c4050f0300034490201e440317584100d9140701501084150360516107006d01c1541c003601c4d405241c08202e28010150103588052401c4800c0309401480c0078081e2032070143e4105c58200c046108440c1e5281e46035001c1141c0b90b0414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 98457545 1250 98456295 98456317
    0x90c0f04020403140706030f0b15030a06030605010f17121902030409050732160f05030c0f1510030807291501080f04060504140102040b0301090b010302090f06 70
    0x7400003000050380c0c650038648a0404d41c0003818100e1510304020203071115000c0c02049285089000081074440800e0956014540070034035903251504424640200050350000c1d20b21440c0c0400814035804454500080724810161003801c810740411840d11422408204000d02d0407c10180301405c3c850100020340e40440c0c015242055902c00411069400440b00c038070000704503a800c2c01040d00f51040805200e00d4507030b006c080e9159401c400c5011072182581003207141901c0c0002c0c0742009121a031209401e0b900809030ba840e810300d40e240c50345d200360707401da10446405000945451540d010300110310945015003168003941c80c0d601c50308159400fa07031040d244404d8403030400550255007001401091206411854545040003401c424000012811410000101d00340065002e89190180d0407a0b0000720015143d195482c14101100c00c01d40030103015400410f0001d0b282000f070015504841d4190410701c4a0707031456004601300e00c1910340480d88070f105030b1890880c07400c0c01d6018007139148007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 98458795 1250 98457545 98457547
    0x9010303271806080604050601050405060402090a090911010c0c1203031409070305072114010207140304050910061d0303090d05240c0a050313020a060e030d08090c0f0402 75
    0x350701c01004900300d40124888400c46002030b0b06812162048034001c042035000380c1310a0615680c1c1d151603410600c40d9a00c2251240c02081050369141e040700c6000c0d8005100a648540d00e00d20500504a1904107841c20681c2031607980300c0b0350181e01400d0505501091a42c403140c107103071141c0010100c4503016030415541da401a040c191801c40894000d800006c010a447c0d4a075240051a01c909070304041e449008810001710a00c9031048041c1c010f0380c1c460420000740c4490300c40305009010303000c1e0140000038541400469008084001d10903510260303660655980c3d4408032440b0300300309201b43c00c0020b40340e0800150702d24011902d4200a0300043c1528508980803000444c02c003145401a12950001000382d80485c400384140400ea0136100c0c0d10010a03d0285690b0381c99020340d14003101403000020015004581c1081c090002c1c590081030f4041d6a61240030040c0401104424240170784a650442400360b4002c0c00312501c0340340c2610003400310700c0905c024440c42000100034681c1142d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 98460045 1250 98458795 98458847
    0x30c0d1503021e1e0a061d10090801051501050a030b04090507080709060e0403090b0c0a06140106020105090a02060306010e031c1e0c08090d030c05010e031c02040509010303 76
    0x15480201c10340c0300540c0011003c003a801001001126402140c0f086610395050181c48000e440f0140c440c070440d0000c0c01c00c1242e01d901140c1008180220641c0558840381e03031403890000f41d401c04011000c3e82c80b40d60003000036950304049098180c000450650104001344405801c2e140320340c01c60703190b40300050404a800806036903194507110b07580c0c220000c2074000da0070a200c464071031322481000300440020070480d0304090f1006485145180503032945190b00181c4130360b1101d0108048030722594002d0b8200440d181c506400d2103001c03420700882e0015420000452034025001484080b5160018101032440e166075006503101c561144401d41c042c09031209141c0c00003022008500c1c0d0f44c0181e100d41e40d25018120f02101102a404012020300c003507180c00802150704034041d91103001d420340709021410610305080d0741d402284400242190b01b4240790035400b0070044050080150700d050751035621184548000c069014a00507150040d00520040000c60310400500c900031990141e1120400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 98461295 1250 98460045 98460049
    0x9040b0d0c0e16080618100b0c03070201030b01030209010e09091002030901020a0e0d0302030d02090a03060c020f060a0902032802130501050a0f0305061501030605040c080f0903030c0d150302 84
    0x4829500a002a0310004200050401e1040031000f0500300c41ca41413129140c01c4d4000382441d4100042c803403c61500c0340c000f486460000c518007000c1c1840311210b680701c20a132505950350b90f104940480c0080d0400e01e00c4400ea5019000351400d145c416144c0110300c902260a1000814005109085500c140c003a8141000ca241c80114003070034440001681e01c03494484003a042080c4422010702a0281d8082c0e000481d40c040190f501c140d42c3c0c98005a5522081f1001552075000354001030300340e0789480a007810050b00059030300714042096045c3c2e20b660b034034214101d0498a00340406500754122000e01c2c480e248011598884820140001e058890305c29004645c0069100511701000d50303a81006200034540040344000501c540e01c89803049900310766855445a00162103041160b814039020b0150740e01980245014040140c810009414100c40060000741d080e00d040b8960703002170012480c1c03402d010080380d200c1c641016001d40b0700034a01590a005140f00e209295408203032500c040300607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 98462545 1250 98461295 98461313
    0x1150303051201060504120602130b03160807020102210406020d02120103050606040513020108071e021e070f0b2d0306040e0105060f120a140a03020d0201020a0509040b0d 75
    0x6140a9038800d5101c1403040381c000420001a0460f800741321041c402007080d0201c041004072041d610407405a15000004041410b503d4079030084002c000b404002c00c0203001401034081e0452205d80e0700d2071659210340c8002d80c200e02c200102d00d82c0500c440010000b070340b10882c01c2240c0162103072800600d030042c1c20200c1012a0001104034029013a80d81c010424480200039513500514112410409400d26506040c004020760400074184581640001c3c445030080550444400c1c0c040714a030540e408400d4004e49038400080038581c200b03004204210090b01c001030f40740550b155108a800031034200941c4081c2a0440100e44410500441d400c20f8060340e2040800c2800d8410341001d40c50342040780c1000b090381c0d0b6455038124541e241800f08003082d0340e2110000c1404406481c10b0800e51401c004290500b17003488000b901103411002d180d00c09600000c0e1081d0410300a40c2030701c86210348000b0807400e034440c50104000169050140a0052030294400204444010b050145a0f055a601c1c0154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 98463795 1250 98462545 98462549
    0x2011b1e09080706030902030d0525110405190c0206040822030503070f0b0a020c0d0e0609030109110a0b070b0601031a090f04030e0303040501120504052b1d030604060e0115 76
    0xb07901ca10041b0110f0800700a4840c0e07008941c10b00a0800d80c030400e80c2000404505021560394000078080d4052003000d0010304405400076200340200e1401000d50003003c0c402103410f504451810150070b900301e10100b980b070300695210521519100c0492581d80d01c984112145e840c1c8000c130f02c0d40c0040083d1f000c00051223130900c2040c040031696018100700082da08000c0c00060140d0040004103450040481c5a0305007003c0c500b050301c54961445d001c141c2c24021185c09941540c60806444140041c140030451842000c8515607030f010b0f15801c0c0f4020500610000400c1407910f4000310b942c540c007070382080000c80718001c90101d1556484001800401702580c0118003445040c05006c01c0c564405805400100190020b501d400d05d444002040384510380d10b40003600340d60358003013402c00c00203028450104d00380c1c001d2000078420320503111901804501e04940400c014804c06201600000213210302290001c0280c081d42e0780c1e45e240c1201900881e0b10150040d560703501803040c15902c00c588500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 98465045 1250 98463795 98463797
    0xf020301110c0a0302210909190f020405040c0f02030d0e100c0e130605061804060f1502061f030f020301060306020a03021e040806040f05030408031902011b1e09080706 74
    0xb000d43d820b410044d00b4400500307200d52824802002241d028113481e012242403035025075a01070181d81d94149010320184c00140a40003c1c10081b20200100c82c1e50043e03c10703150129000c01005002034010361f001d2404120a402503003042c8040081d5007907540c84040101d11101c180d41d2000442ca4510048500003d01040854182ca181001500340342d00b10008080701c00c8400c0000906010014880d40211200c94010846c2d4081d80c20440c0c030303140c01000090180f040340940e0581c585044050f0301011100b170000600c0b42d035000a0781188040700600410032016052908581161500d07440c80d49000c80990b015034a0f0703d8004000703515807008068141042d03500588076043e0a0f03100070b0032040c120001c45c008009000a201c43c440c0440c2c11070f003099110510056096580ca002402c40c040c1754020341d6140004100e01c1950308aa0303070078105a2583c0c1c1e00800c100700320021500f282c0b60409002c000041c24910a80c0350060180103240044a5a802d05900165461034424a00350251708940 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 98466295 1250 98465045 98465053
    0x408030a09030b0f0103081806070c090c0f030519091a01231801260a060603170705100203070e0319030305090607020d031d0105040c03110a120f020301110c 69
    0x10030700005804044e04121480b00e010003651440c0c907040a00e0040c0718000341d00d00840d86c011407903036483c41c08541100754842840d080003980c9205920080c080c01c05503402041d00308518110b41e0703110f4814140315465580401025241512080d0010014110103e404110300740310941d044100b2141d0070300070001e5020b0201204181020205002c81625629005101d0030040d08100301c4062507050641d4a00250005642c01c3c00b40141c0d0240e04417130103000540078400d0b1500034089aa008042a00e0043c13003400c02d000305042c907100091040400141554000140c0103400d03028940045400c0043d03454000c40c811000400203003070002014100300000202d520348020140c00d8051a03074480c4001000d004245003440c0048d4951240c043c2034810159600a03081c101159400100a8142220000c128a24040c0742c080d42013000b500003070380d06030503940c4160040d1070404611416030f4002101890380c503003950349040b0002820982241c1c1035403517584602e00380c0441000340c408040c0b072030010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 98467545 1250 98466295 98466299
    0x21010c02010609020f04050d050a08070602090306060604230f150c12030f13080d0513030e031b0103020c01020702030109050a060f090206030429010909030305090703020a0e0a020408030a09 83
    0xa42152400da0042120071300512011005403240400d840440380c0135074410303c05030141e20f4158184400004000c028600204403001804415405842215000c0d0200c81103a00c44c1801c07c11240036500c1848003000604aa184031442c031b2181555000e04013411034a003503a00c0c000024200220202075009540002c190035507100c0b4100914155a40102c1c50b0f2840e43c18001c01c03e00c03100d40f0041543e04441241610038003040711280403181060320000c1c080100d03042c0b40c41c9802c0710303c80842081e40000c0e00c9a0111406241c003060480b03d0000c4c0c09801c0511168100065003c1e4002040b01d11041d50b00780411400760701c0a0007200c2000384030704003601c815401d62800100b19007401260303c41c020300e800d0070040180c4440d070450750059000103541b03050741503131140846440b00c0e403640041106802c000000f18140c80e50050102c083c401e403010f001955410100da903850300c140c032010798011000d040410401840200b40c60300a6280c2c0000b5250588598455181d58022120200051000041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 98468795 1250 98467545 98467547
    0x20702041a090402370302010f020f060115020307020d030201050106080906041a040203010f1b0201061a04150c170304150515041a13020309060f040312090221010c 72
    0x40303842034421090060081441e100119a1810700100000d02504042604511040d0030b524842804007020211303c0307680c0311428210303580040522049012135100c0720314044090005c0703105150441c0403402080c0c1a860520300b44280c1060245031020350100b00000d00241e100d411030807a9460080d0008150b0b945000c3c40203003020780c000d0408003a60032100900002805d601900140395240104031000c2c0d03140c0b400041e004004401a542c007142c607100c0d003c3c00080c486200508a400136400030460503589040309280618154154484048e0070071084c46000b424201d5803800200e580b4180e0030303692040e56036003208030220808240482c404000c02041044800079a10103d8040c2d40c1800709007005d21080d500d0502201950b13220302c0c2c41d001e013a019013503003224041c0440d500401c000d4800b640f0f204914005c0d4000e03204a0f409010768000100c0381d0030a62013081c086c0303601d81d9031038110040e89010b01c00100050882243c1c4141c1e140c841d4000d01d15421000012003a031440001058466910 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 98470045 1250 98468795 98468801
    0x40f05030703050c010c0303020f07050109060f0204080c0d03032d15050315090f0714090609040302030403030f120c12061a04030b06121203040c0806010e01170a02060a0302070204 79
    0x100991003980000303002d0000482c041040306031150282400e50014a00e407400703034041c3c00f0b980c044544000c0040340c00014000d05401142c42c490060f20104a51040140058185d01c16801101d505900060300ea008600703045542d2909a4000e15001482004960b41100208043c94039070b94040c400c0d080710301e0500303c0c0d84170343c00c08100300d0201d000706030303180a0120703444440501e491400b59540c1c0c030000c0c088402c14002d44065280c481c060340c400503242d49001c0f0b842d130351200d5414000c080080019001d41050641300740602e40503001142401e19680d0b003107402442e01c6100b80100309980c0c2c0d021101c681d050242501d004c0b81c035202c0e40508104900003a040758050307407018808011488899080749202030440c0c050329004101c1a000765a9031001c208071900707510281000384180001310f1914441240510b000f94413507824601c0b0b0707e5603802c041b5a03d4000317000d281583c82804d80100600860350841c01e4041d588181500e0b452000f40d00002c1032900b000002e940481d800182035405c502e403500c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 98471295 1250 98470045 98470049
    0x31008070b04031203020a030902121608190f051c0e010807080c04050f060405030604060207230c0108040f050706020619090807060c180803090a0509090604020420030a02040f 77
    0x14500b07040c2442c42c0c0303913058100030688981e8141a0700040320754042c4d102e50003c503000b680180c014a40e01c8490701301780755940500c084520403c0e1906001042240e1b0206824100c00590b1200844186072a01d0700604000f886004441c01d10403408500410094881009501411902d03801e141e070074020005003131804000d110400700088401040b10b42003005064500341c500035103c18458503492004074000e8444d81e048140c7c54800c1100b044100b103101c0d002002024807070104818058001c00301000030f005603656200301604034010481d4503511800b01c0551050050740c940c0503a010300c0d200d842c20f01609800200040c0c0058007006002454003a40c2e4804006900040002d4410b0380c8a4010a004800004000070788419031081d15600c96100503450100d2841c14868840e6503041e80d5a0740d80c0b00891a07800f03050041000281403924022152042062202038001035840717a082000404031008588544244000d0142c002041080a140f040068400c01030303455051802146c5020469 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 98472545 1250 98471295 98471309
    0x11040f05010306230a0f0f3b06010c0c0e150d0317040f0602160309171e070e07020709050a020921120a030b030601080a030c0b0a200304020a0e1e1b03100807 69
    0xe04600304107070002d000c900480d5914238185594613202c004c0100d440b907000c00300c0a4011908101c0108070724210301c00050181c41c9c052403e00900c6144030502208050055000d404242c2e61203010032584003468216a01c10711481241c140c1110b641d40741803c0342c10403000007884c0c1c400e0b040ca0404044d0400004c80140204808806030390102940541c1c0c0e0340d2001c600741c080c004c280341d242042480200903440180210b40854a194940034074004d40e140c2c40c1348992402d0f9810003006c0f46140189200b1501d444202130410b9020340072812001c0c1c0540742621260300f00c0d21503645d106a00d10500340203000c42d5501c40e0b070045003460030038040510341501030f00001403a030400c0b5198000a0381200030710608a5020303094008555492041d100140072407041e0164620200d001c0c80701700c240c0000107610072403084814086143d21414110010701007241c140b001c80b42800c0d1810034424000b50032a92102031a064010303101d040d410510441e40094440840c43c000c6401d0920000310148803040290400e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 98473795 1250 98472545 98472599
    0x105100219081e0a0908160b0903030405030d08040501061e05011809051003020906030f0a0209040c050307060f02010c1e03020f1b011d0c060301030209090c030111040f05010306230a0f0f 82
    0x400b44601f40c0301b400c503124042d0801e10000c0c0d04411900e05000762402044018242e65400610101c05000c003074088404590315460311001090303802c1d01c102c519030171114803403a400b07086c4c0c2448010340e02414000342282c0341041c44200021200f4079402807a2160540c40c80c02080c8074078610622681c0d82010700510311030b42000241c0d00f0f400c000040c410740e500d6011541b8100644850074a00180e40304e035008190540035124000c100c203074020030040a403411725802040081141502224050844403034003803c15103496081c51510b120b070700500b08000740140420b141007521250350b007000801c40c0c1c084242c0c0e510342440d500c0c06004c09050040a202d42e2010b816070b810f5280c0081c04502c01400000e200721610408180c2441c0308101d01c2d02050f1015008010011101410041a1300184620450701405440105441d482400369000b03c0d85192458840c2000398000c12444902820249030048910200000c035001c0e403407d540024440943e00d080402d0911450f1803000e035030111450903082e8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 98475045 1250 98473795 98473813
    0xa0806040206071e0c030f11100206011e090f0e010608030a0512070c02040911041b02100c0e030706030504030f080103020f1002030903240105100219081e0a0908 71
    0x1d0300c00880b58010b41c81315956442c50280c007855100181d00c140c026026946a600220405c40007203804045207004070403405030306060304200039202c0c2c6400788800c010f801c4800104400f4090000c804a284034151000e5801c03500c1d100d0520807640c04240ca0984103071038031140c4000720820f00c5214060940c0300051480c105921002810030301c1060001680d80e000c01000980041c4101040655160300501c18401c040c0340342040d80503110b4000025120360315044242184c00040c4201c030000a00d940c020744840380385170041d00c0c000c252007114402400f081c007042590035501441014042c0400b9207001070182000c0c1030080c00301404505081c2442680e20061000d80e88050400c4a003920499035803152602110040b420740c0924201540c1510071400341031807481082c402c0b03081402c0c503a56854a0343c2ea0b201c0401000c60b80020a45016800040200c02003040c1d280b5030304409809941c82519180d041c0034000b260070602648070381034010105690700100d5100090400400e0000000d144040b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 98476295 1250 98475045 98475049
    0x32319060f0b090a09050c0d15050d060e0f0a0c03050f010504080f0901031e021c02030c0406260106080106080702010908040b070f06110318010204080c060f1209010b0a08060402 78
    0xd41e50003422010003010400c9412984c4074103012000e00b5110030144100d007040003280500e6001125a160b034a81000f142811000b041060b1400701c4030024400000b80c1400e031515002001e85251014890290003503052440e20200300e0201480c1c40f0f02407048050f40b440c24030504011000350008c40d10390500d0107000124060500f40c2e80310880110020f56650320380001170703004102c5c410301c0505407001080c0c0b09440b10060303400b030700751252034800000000000b216407400300d2108031068042d051042c03000380681442940044103000e03c0403006000c1400c41000d041148209070300c10320014041c0c500500400da4011b001d07541140c4140002e200f000c1003076859446500a038040c80c40c5c0c0640201c0d01800380039180710195a0981c0180c000c0141a03a00c1d441c8021540c0100c419101c010591180045591014822a0b08540116001d02510300e002020414a80d21003242182c403480140424000c0100c50010117000350403c0000240e004101400d200c00c0023003940c4084070642104e41000007607 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 98477545 1250 98476295 98476319
    0x2010c02010f030e0f010b040b06040b0f071502030a02030703060e040201200a020402071b0617060d06091203060503060619090b0a0e09070306050c0906160303231906 73
    0x6030309003442c9a807105507900460040011140ca0b2455101d81070540c0480e0b00194032214000d031080e1b4090120042c90028403190b84102d21458100c3c403020000400384041e000007038816948501280325490743c00d01c0300700342680c100303403802d4060507800070511040c80c1d058810701d40201400707807412843d07140c2030300040e00c4a1148900e0300b010022a0140c58100c0000341f01d010281e50f80104219182d0006007072400c240d94075411040802c20f142c00011a94500401e403961140040324000306980d238410341444a0000c4e002c0c01183c2d40e03920741c80a240050060091900f010440e5500040e215107031404144c07070014040c11660080034031b080c0c00100c06030300f4000070303007640c1c41003101049815482c03001c20300b029a15031150070920502020300c441340f58046000d5003268043d270b01c107000e9a100c1144054542c802d2540e042e9000c58100942c072400d40146424007100b500174200020b1007500c00f100e004520419100078828900001c08000c10201c414100c40c07a51602d2510070018213003480420250 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 98478795 1250 98477545 98477567
    0x307150212010f0b0703031512060603050706030506030a0f0215030408180103021602040905120c39010807091a0a1101060e0c1c020a030e0d03050c0301050d0f080705030304120c0201 80
    0x10103495410528071000d034450202300916490f28807980c03038207850500030010b080700e0100701c038240600200001d540c1d110307014141c041c02c0001c0103024401030076a16103002d000e10190072a000344110001503011607002000c2d43c0b00b24090b0280301c0e96141c4005000702c6500c0a41100d6052510501c0703000741c03040d901c00010038015415500050f4540b164200149004003c00d1010344542c0d00249854504c2c001207192010020aa4840d103206140a40d0001c402b07442e00f40080b03607070b8603180c542c4040c80d8803580b4070982058a508000703040c02e40360442600368010110201844850015034800c6850f070140e850300344510b044008201030b50074402840500d4901034412071401401140c801e107603401007003d000b00c5250b0703000215a66001c8074006409441c41c2d5444110303074066006804c24407070082c05183d200b03000d050b80d2980b6603800c00d81040000c0205600a44440301d440d007541c0d0005240b04001c003c600c0c0030703c00558aa15140c608181c00724568031280c0304004040502e000140d03007041c1200e04c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 98480045 1250 98478795 98478797
    0x6041512020307050d030302070b010b0307140d0b0409031112090a092c150f040308010905090a02040e060402090117370f05010c1b0204020c0307150212010f0b0703 72
    0x1010140c0380c0000380ca032002c40e4002a174081100b00c904810150150b00031f058a610507a00d03401c6513a0b0719905602e2034002104c181c0081a420b01c0c20452420310071000340001041003000281c4441031002040803100040c40413030104003032000010102c0000c00c1300601c0210100d034518500000700c00410490100c520410700c48640350112010885950302c0c1d440c40900c4900031440a20187c0c01c004c6036034024603143c0900e101d04140100700d001c0303001d642661240740c050303e43c21026403809035601d00511000307004895900540100e1070051b07555008143c81c1c408000c0040903141858010032041240691004c0b00081148030742902031403002c01c850280e86408800440b40040f10610714600750090000b240c035219182c0d541d001080a052884a03a00303024100802c0143c2d0416001d032080e41c03a00c0300300e90f00b00d188094a000180390a800820038a0300c04000d90b07051015913507034000344554000410040070740100346a491b03803100de1030082c0103002d4850800f035841d1521820f04010310801c60064 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 98481295 1250 98480045 98480069
    0xf340909050a08030f010e010605030c0a11072315090102071203090b0a050d051f030b10031202060403030e0a020a120516180b090609130501060b070309030b060415 72
    0x40c0c01d20000340090102e564000711500e42d00e203000440703144030103000d02030b4000d145050000410f401d4800d00c26603200e100484c1c14079107401c1030100151282c1d0907110840c03c4610406c50082441729441e5010414009083e100d2810400c05404000310885100d0003c90345010511400000382e900041c00407c884c0c2d40c000204030b910290804903107004450300005030b0f400b80040c80e85800c40d803142c0180068403454408000070f4035005000c0300341c201c46002040b040c001c000c2d0203101141c641e04241d500326821000808a10b030b0b5907647c124040708031034010000350b0171480800040c190140200c0c8803640301d00c400340800d0007044e40003800f25800ea0040622035400030364200f04024041201007080003010a001072507541d90004c0f0800101100701000b0010f092821042540c1080540d0750b020741c0300184041f0080c0e540000c0408a010182d406894940d00c0e54000111240d86000a0020354003035038a0001090850520280d00d140103410070f0f000d1480d12016408070a041a103080a0b2200b0329009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 98482545 1250 98481295 98481311
    0x1081807030b0a021e091c12050a02150906070909050c250605012d0305060f0919030801090617060414070b1b010b01090311210f3409 59
    0x203000030302642a03202d907005c0030300640111500d94a80a4249101c0c1100c074400c110090150740f58103941840001002d0f841201d2070306000780d00580181810483d107104640940c0e1344a003284090706400d40d98841e0b990040310911103960342c4040640701900642d002800642829450284030303105884007401859004442c032001c041d60f0744005400d03d40c00c10300904c02540c41e10301a108020383d450050690710f03040c48200c0318050008000004481d00440506899a503200c1601c0c044072004001c2c0341e403800303600030031949400746030800e03211036003e5a1005e07c03660505802800319810b0350070034407400e101800c11003800c500c005503540c3c2c081d900440c41d10494400c0300c0300c0c40c03034040340d40c1014840307407000300b5082c4003900c07808114451402c40400034000d0b626218015168207425000203007040344284400c88031810007180c03d0703940c510703072030f481d01c00a039502c0a0030fa040a482d001c01c10090707002800010b0741115082d01400720410030401c1c41e8906404421074078403400c610711540981544508203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 98483795 1250 98482545 98482561
    0x40305070815040f170c0c0405070c0302060402100e0904060209101d0f0a170a0c1401080c070503090901030f03021507090504090c08070b04031401091e0f06110901081807030b 77
    0x80e8102c082800d04170780d0345445105100382d0f02d4604412125016a1402000400480c4941c95a403101501a006450b99490319003d1240100c5120b0b480c00902031003030340c051029120440000d01c07032405000b0060f01c0300303601010002c0481841120f0801c020000c83d142d07009140e40c100d00c1c89040d00443c0c0d995080744407036000c031304580d240c0c0d8481d0b10f6862000342d00444500c1701141200382203110708078504800d45c4481c40071028003a202100e50016280b080010001054840181411400b600c2101e080500000000c0d070350703100036041228002103805070f0f0420150100140c2c40314802101201c4210300d001c070001080004603101f518841c13902e0301c40c400300340290701c01800f029041102c26107000b6a15912112040c4c0e000740f03c11501a07040d16400400400c040c400c6c15041036004100b8543c140f0441e0f040e0182c048510400c3e01e02c81500d9800c140007452620407004200b030b810018948602c1040700240c4070352001030102504148502c2500c50a14001c40c88909899100741880065280d40350 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 98485045 1250 98483795 98483813
    0x6030a020a0c02031b0a0b03010602030a0c050106080a15050a0501050907030c0c06090b010501080106050f040b0c010f060e0a060b0301030b060415080d0c060e0c0d060506130908040305070815040f 86
    0x1002c1c4d0180114100300d0a501300c1120503900b0050300703071600d44045a84100d80322040c80244210300060b00700703000c0701005611403401070310030b2170086001285050301c0e0346020f414907251840440b49039243c40c01700c0c14920070030302440c2e601c0514150204003a602d082e0100d407060b00018108010581e0350151408201d0040a241034201c0c0c00c5402000145424540212080300038040c03030307012940343c0c0e0001500c40e10031022241440b820a60f1142400d103844141d11442d006101d5403221f030f5488540111a02e400d92050b00b00901c00c3c00178500950404500e400100e84894012a60b0b0340300410051011900800032030750440c0c4c0a0320002852104442d00000da80d921f07070852200d5000c1c212111803c1680f0086044519000356410800d00e000841c0741a500c445200070a5080144040c0100c04510183e00c01a40480060018a81c0f600d08404a40880f60855400c40321400c0216051051082c1046080d01411211005003c80354450843c0302e8070200041c40244070b807462120301010014062 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 98486295 1250 98485045 98485067
    0x1090627020a09030507090501060806030601081906020403060e0105070f031103060f0a030b010602030a1e2f0307030513060309020a170c040504030e010f09050a0308030603120408030d060e040206030a020a 90
    0x1821b440100380c40301d030503501920081c4110030001d0001c40c0414118980800e24604071001c0100500803815846056492090400825a00c2d544c3c24800003003c40c840f0700811034030f84100b0700009800d2801130b102034440400c2c0755041040500d48102c001007920300b20105d03504031070b0440703803d00204502c134001031400f865508002c1500c801c1e0307000042c0c0c05400002030058868191034400461724072510740c44c22200d42100e1140000d0f80442d811000c070701081da502c010300320510f02c1070946222010340d40e45185d00c01c0c4421800600d00040031405180000c0b044005024540b034140413030281d43d000101143c00c40c0c00f4611071400303440114a01620b0801607038440401c00382042c03103149407505000e060f000c4c0d02000c04c0c2c0400d003140300c00070b5924410420107082e40d030010b1100f003d860454442307100d40d8200500080e0503204410500c40035651040151008000c00001542d96206110070700c2e080e54250b03840603070b000724184140300050b540e03070040d680e103c0c190200068543c0701100c02268603444007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 98487545 1250 98486295 98486303
    0x40e04080f071203060b1204032616080c1201170a0213091509170901110303010312110303060a05040e0109140304333501090627020a0903 61
    0x8110b02002600d0003000000c01c41034804010b501c1c0d075041c1c807046603ca440c098695070301c200c9000038000390244420209a44a034101d2401075040b04180c4400c02900362503403005030f4240f50741c003203c46601c5215980d120030504900c3d82880000d01d0304e414210410701884001d007040308400005c0d003c04102c1491000e070000c11000324114080c1c206401080040e2065840d80c02c0c80341c100102c05014050405003961190001c006c511505407071180d982c001101160400c0350b101c110020030b06003000618041c42c02920a0840c0d920001806000340c03100c800e420409130003d1003000343c19a1000d03640000c0743d00550b8045070325000d000c42c5500400c03c040c001848000c5600748e0500544000018000fa075070040e40c02d0351810940c0d104440d500c0d0380d82c0e002c415003441c00003401c4080da00c40c00c24181241403410706140c1547c4030b02c4070342c9150100b580446030790038000401003100c0115400703110024159603207101c2002541c4240c0c4d11036861a0b14400c080c19400040040d0000e103e443c200c0002c0da00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 98488795 1250 98487545 98487547
    0x1091104081b0d080313030905090709031104110304080c07080a080d050a111c0b0301020909040813032405070509030d0f0905060a030f0f0621170304031110050903040e04080f 77
    0x2042000c4000c80c01b10182c2500000c00c1080045011304103c03101c0703030050f012900d941402c1c0746180d0f5410b500e4540381d5a51034106ea00d5181281c07802031003a01450285205206958651500c0c5441d145803484076401003203503070b112031024804100c00c402100c48101c003d280215190360781c480c3c9103019050b0070740b10740101c100003c0d00310081801104500341e01d201c000000e101d03500801040500b40c0c003034900b42d00d50292942e0007240020303055000800f50786400200700905641c0d2030329550280800d00c0e50410325001034406100c11882c8902c00d03d6400101d508245003455047e00c0403236559406001e14400b4410103000500d5014010400c01c4010a40104000e9890255880c020040e000f455801404a4202810211030351460b0050078180c801c504075441000c000c000c9803500d02e035010081600d0050880c40c240c08811a07a100951140c0e01984407007116a1010b10071501d0300e0801d0404848541ca010240500c5201c0441100c0c110382e01c0d802100020340312810665000c1c4500700060140100c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 98490045 1250 98488795 98488801
    0x102011b050909070234050a060507110603160c0f0b0a02040f170c19030c090501080f0f060a091b060207080d0c0308070305070309050a05030301091104081b0d0803 72
    0x80c0c0700d8010700b04058103640ca09400e8039220410ba03a10360118000510702451224021102e01ca50b40304860582d8004000d4441c940d911808104841c1543c0c0100d000280005646005d102c148030b0207080c5001c0941d8954590319010b27060100859008100c5010000b8007100c42040c048000e00c1162072a4100d04e81c4074282c14002c80d008005d5207e0311034600c03110703007854000890102031a201c910025640e005440039084120400100002d001d02190107100783e90f0001c00031404041d0b07840c019101241e00002c140d410601e000c2d1030030b044001180700e40d81c02242c1120003031002061003604150001d07c0440d2456840c5000303200842c9022484007002903403000060070560010380e5404031400c100072340e5000084114111099401444c018011459601c04928030501c03c2e48401e40c0901141b4002950b203803103645480c00c1c40c4074110b042d1419400480103100c582014800c4600e03103002201a07614142c40c2c641a66103412000a00307401807130134901c041c0d0003034071194403041d091a8801e136040c1d80c0c0d00e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 98491295 1250 98490045 98490047
    0x51b0627130c0905030109080a11030d0504030507020111010506011218021c0212030f04031113020a031b1b0b07020c030609060106181d09030c0714040b0411070b060102011b 76
    0x280c10b0004200080c0f40700000245800d06100c0d60341d48540203d0340ca482c2071509102070303c0d4090040c0c030240e11307480304209070400c881c1c0500c10b09000f80c0c460b42c1c9981e0fa81d1030900006007017a487d010b4500d803d0b4584400c0c8081aa000160b030380040d0b1119201149841440309040518210410b029400c0f1400c182190703201c2400388038031a0b00500c201c3d041d075040c00020000642d01e00943c0308900f0817540c00c1100b4004a035910310400e4519200805000288903101c07103071f80c26a04007880801c0403070b4451308198040d1545082c01000c00b545464581c03002146005032480c030b803603841c0024003090b515801003480346100307100d0a10007141c090100c41c40c60400c9984ca955a1000340b00c0c0800040e1445004c40100c0c00d007020840817a102c0c80c580300910850140c0c0781e05c0003600500a111944803c21100c1c250f014180b09003801890f00b00d02c0c00303950105a07001d000070380d80c0803020710b8031591600101d1115284200203075400e050b0000c2c0050059641d085c0141c1c01000455180684404801c0b2051002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 98492545 1250 98491295 98491301
    0x12010e0106031a01060201180b06031c030f05010602030307090b1e030f1005010215070305070207171006050409050a080a11070306050a18120e0103200403051b062713 73
    0x10104414443e0b03441da903a50b000324201c656191300d45e14000a0703500303194040355004080356000f442c02800e079400c0210640044800b0714100e04590301282d00d0340c40c09070711500b492040740c0c01008180061450341ca02030400034640002c0e0b000b000b440381d00216640b81e405200c686941429003101d203203640d486c10580141101c00e2001c0b6400c403111020104080b03425440855041080a10352040c007d985e02c0b114015030140c84d008000070300714031400f000007502c544074400409080d503150020706404d1a911042a0641d0019008503020741e041804d00303000a280000c9002203590021204ca441e80d00420701101c2140c6903038008800d91081610200501c00305622490143c036004c902001942d0050709250403180c0c04250240c0b1046220b0341c403003d100d0107620042458801450002415101c0503506039504031001501034400901003828000c1160800040e82c078618400340c05145070000d50005140b0340700316001104601c07419440109106134224608000320f200405050305d140016083c4001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 98493795 1250 98492545 98492573
    0xf0f0301300f080901020c03100e0c0307031518050106060206070f0e030601060503150402040306141305100b011b110109150e0d020a0e0f04020405070504060e12010e010603 76
    0x5840702a115a0720019000740c80d00740095441a080c5540c204291298007854201d1030700141540100f080d074440c01c0e40c00780041c4c11000b410100000c2c01e1014401c00703501c2c202d0100005402903110300401e00116401c12182001c2c82d6220381c012480c5070140015403e125103e80d4001c0507176084c440049416500030803440d1064070707155260184202000d10869420340c01232449a007540041d001880b94920500003180e215444082e5580544602004134089034000d600580700150b0716055540e00c003817510440c0b0780008170352002d5130303090303c0680350749880d2100c840318002900e640314102d1403a640035244c500ba07124080d00e500000420141003240007040210f0307146001400081e0b01040d952104030006a0750300e0607940e5103815140c0d02c41401040d030950030303090740d0041d014400000c903801100c01d424802c0111000405c070b070f414580705002c160342000d848201445001e00050240f04d41c03014543c0c0740300380c044885104000d0188017040c01440300c0800840b0035401d02074007006109568101d90700e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 98495045 1250 98493795 98493839
    0xb120d02030d0c05040b1e22030b060306060306150a090e1e01020c030a2d09031101020a0b040305070f05030a031a03010b0a060c241d071a0f0f0301 65
    0x1103031181c03c4508480074071840c00782c412012014084002c0640442003800042054206000e1a08a011116110b80b802c028184501c02141100510801034520191504800150020405810201d00082e20303904028008a200340000b2405440c170f0f51075000340d200401429078200704d40b4007074075540c988462020201c15514400e400000c14070309014401c44000403c0d5101540c144591542d04541c5407500390041c602c450300e0f0402690a043c00c50f000030200d4203c54a80101592075071402103840e02c841454141550080182040810090100b8903171069041c41d09940e00e180c60300e40400038810520001d0b01920002c100d1016160301540314020707078095405555449a540c0d8101400d84640d40e072029001a40e55904010190064041ea07000c64841c208020481d81040c56101510325654203801380140c41b00d60900b080c03515440704043e4980314001801c261828403440064a18014109140c1203500085046107521000142c03060301c0d080c1d00515540b56518020226004100140c0c16 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 98496295 1250 98495045 98495051
    0x903090d030306230307090c1110050702060106030e0a11011107030302010e0c12070b1c02070302060406060e070206010e070504031703040203010c09060c150b091014010908100b120d02030d 83
    0x381260358100144c1c03440150003401000c0d00750929503404041d000c5104c05c0c500344600388951007203003041400b59100040c1d10a0000903585808a0001d140c4201a4800402d1501c4c00591100010020403d13460240c3c0210007060182115070040f40c0400d076058800f40349014405001c4100b5030706400c82e4140c03402075003c84044a898508105d84016903452510155201100801242c3c450710050f258450104421300810451080c01100344e0b40403407000c070010f030081c0d01080100301c00c034441c03100a45203000382c0c3d2415103003240c80070750340f0001800350047c0c41c0c13002d50003c0c00842c414000caa0203158440c800c1d150703091440381803181039001034500b00e11075400d02020034038083c0b0a0359190210781c10baa4070f02c00d0070f0f0882e40701c0c44081d144407500c8450984d102c9000200703607115402c00ca03018000000c196000180b500d0120b030014100c04c1c84035410882910010020040005511000b0829400000070b80b03801120015044480300c0b095088240581d11800c61103a801001074800c00302c1b081014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 98497545 1250 98496295 98496329
    0x306211b0105180405130209040b010e0c0703050307032a020303040519030804030e01021606050a140f0703030f090f0f0506060f013204120c1a09090903090d030306 72
    0x15251802141d41044242c503412001c1c107491325098000941140d0132001c070040d6042035401140f8a040f040700c0c02e41c1d0a4400c0c2c001045010012030708035901000302c01105081120b40d1b90010311354400544070004042c0c9503011810100c289891142410201d03010310443d8101c2480080d480f600201c800f59481d00442c0528480d40300c650741820340090b8140d0360400c0f41d60710f60380e082d100210048034490441c8210707100d24414614000200c00502101c0d210b06031140c040150051000d81000364100191030284884084841e242040e1201c8582c036041c08a4000001485017008200b140f00c0540b07882816403408050100c41081da40032280a50182d503441c2d0340c0c9106100c50a6810000140000c0a0341400c0202448030844441e0701d200b8404143c400c90100c800c100c4298005412000031010b42c5040031040009841d15800108488000c00e0711401060310100464007441c9100c4d4050001d00c4001607605605000b220f0300c0b0a40140240c01c2c03d101c504008009180074018244140d020f0141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 98498795 1250 98497545 98497547
    0xf0a090621022209080a030e06090703030f032315090109061805040501020c07171005060913050a080406030911040e0a02040b03010b090103080307020111071101050306211b01 77
    0x12010075103030060000c2d10a50002481c0d280800305404407550501e5496070800002081c000c0280030700003c0703035404525030300541031071800c102c000783c04541c2640c0300c248108000b0360030071503001c1000340a080c0060744000000803500301d503501b00c2c0103040790031502c800c024544801c0d82d540c4080b400240c07440c00701680c8801d140812106a40100c944849204440740380d461840c1c0c20041d4403030300c0740c0b00150520302080351642ca17040c0e0b01e0700405000bd100c81071207070001004102032444440c4100043c402800c00d4004942e00690103804001c0000340700040005020041004080d11944100020b42d0b841e80c0764070060050113100c400f04c0e00742d020440304480c91302e4540204034400c0d00c0b03000034000060b00c950030040180f4950318625015500d034254010b580e030301c131840140203600400041d5600d18280500900b100d45070903420f420403400b444080085100e05951060b91b54003828455600d4941e0703000211070701c10708440080e000d01c81c0d20303802102241c04254100510340c0700c84445805411480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 98500045 1250 98498795 98498849
    0x70210021207020c0307030b041b08031201030209060a260102040f06030507090626040c050402040b0304020a06080403020303010308071b0b0a032f03190c0c0302070806061302090f0a0906 82
    0x3c0040c05060040009c1400301d00b4652604180c89138000c03000040e50b42d00d07040e850031a08460505a141e0064000401c03e500f800365985601c40002c8840c000268100b40c4810924100c0381d0360070310315407601007104446074400d50480c0c4c00b81154070800b00d146682e441000b0302a01c01240c0c0a4000780043c0400603e00d805130a4507500082303800c1b4101f50b40a0854107264055600070820b8540100c0900d0003d40758603144001c1001e890003104c46a070706e02d01401032080c0300408d640900d0401500d44108000300358003000f680d0640340d1021020f6513814040c24060100300002c040040d501308000d2000812191743c1d0018004244162400d000500300b500c001a483c10303400713006240079a100740582e17409554000065a0191121a090f24a200d42985460840d600c100031030010901100c000c605042e0100160001400d03014001d01c41c6240c410302061a10000c0065a40329540100d28086281d589442e0f0a03460340c030103440440303025942d03502c4030050b04d0a80316052480840200811521015038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 98501295 1250 98500045 98500049
    0x4270207081209010f05091605031b060a030b040c0e03010e070501120903030e0307030302040503060a0c0e0d0f0b0f1504020c0c0d020a030f0605070e01050c0c09070210021207020c0307 81
    0x22550501900b2000e49464a400900e01e014079542e40c907414075209864402c0d50700a44141c0c00901d20040407041e0b080990405d5005a440b9501001140342c01000d40b030049910820141c031003d80b1110144030580142003140c2000d5805810260380f01c940d02d81c80107900105d454120024440311120942c00ca85804082c000c43e4005543c42c0f403d080001030175000307030191a200745400511001c80800090440d0016442200000d40000f41040580750070040241c005182074800c0007075620768840079040305000010a4002e28441140e0018003010b02460746070a07401106002542c903100c044941008801c0340d0070460702c03500301c3c0446810700701031080d83c8030801401c005210598240e0104000e8507800c400c12a0b2143c130b101c03008400145000b480d85c100500c2504040b0b42810020400f0f4a108505540b85042210a02580000110000380c0e1940c4982c107581032070464841d00801c03802d01c04198044403005000007024003524180140840c8540f40941c250b0304032910500c2007603100d03c01e034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 98502545 1250 98501295 98501303
    0x150c0304030c03080601050c03030f0619120303110405060a020d020609010e150a06080f0f070e060f040902240706060503030c061b090a1404060b1c050a0b0604270207 73
    0xb07180c1140001d00503030311142c21500504111342803241c650001880c0d40c1c1300700d84800381c4611407818480380307050a1a0186402462030191000c440c1040c85040031003114040207402c040d120205807020101c0726046401030407014160a179900d40182d0080d54807400084400d0040c4186000100c031a4010f10a100d9416a10340260044040584440c6000c00c800342034100150f42c4c1e13110024403908104100207140c820310024100d82c0d4210080c50341001440d034000c5904844000804c46d89581e0f414000790034400031a0005603404081c00402d0810300c408580c0106401c2c1d14410b8859901800c0140c1100e80c0705410901010b5141d10515450340180e00c103141580d4000d0380415820080307200c04401e14243c404a850400100400084400b06c0660108000007800341012803507007440d0090b40e000d0250112420b02d00703220f900c0c501300c48020007404034000d2a1703503801140b80102d5940203441307990001007404c0c0d11140c590b200c1100c52231528400b1a404600b044d00302620403031500035900079a0300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 98503795 1250 98502545 98502557
    0x50a0602070b090a080105041b06030b0a050607060b0301020310180c0c0201051e040b0307032009010f09030b0405060612011806110903061501111501090207080f03010305150c030403 80
    0x42c004281c802c0340c0240c908030b40d000300e00c10030108401c0400d00c50b0342e110368000c0d00c807600d8220121480080070340a54000b0300c101800c125906980e030300e03581407000848100f03a94680c3d6503807250134400d00034108404030704d80c9940004244450480c0b4003801c0402e0b00c01085c10340d10500002c034640340807103590b03581120100b9181032480340958040c0001e03101c0003840040511103046102030f9800c03654456003103043d5050003c010b104140380d05100d14104c0132559403490860444ca078050090314002d80742e1a604220019110b01c4c2c0700c0307200351205002180c0c4052004298141850300a0f20b801045a006005060703489124074807400501840301040582c402c0b070070050b8080d44510f0060101d038144815503500c200500b0303016440401404d881003413240311860170021101c00042c514180040034100390b42c0030070802d140710b8020f0302c4080d045419074680141c1e110043d180889080c02640742000100f00007000000034000d000c0350841c00320140c500c01c50303035595401f1800080382c00184c9020b000614 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 98505045 1250 98503795 98503799
    0xd03030b03070806010303050a031406010905060c0708100221040b0c03040807050610030b0c040e010b0d0e0a06050603100203041101030908092d030a05191a040503030709050a060207 80
    0x40a03034082000d0200280035030311101e880b00c0415103010800c1c0e1045001400000300314000c50f0349841000c00d1002c4e00125101d040c140040002c0100d1030b1809400d00c01e400010700e81c07072014030030040b00000f0f00003001a81c2101110244038002500320021540c210074981c3c000700b046420300e9016511075035100b00880344d0740d2501001d903901c581005004440300310b020400706000c10420071020344206c103003540c0360f030942d030440c0b4040001c02c00c050f0190070310100600c0306010302c00d00c1340c7c0c07118103441400100c0b91701c0785806002c102c06842d00c401a6040d500a0300d042d03400344810358011a1052106804070768003006000804400c0740710454003d04045444405004190301c80c0e04860309032409907492a0500c8220000180048019549656010b1801c5d40301d80503070086200600d2001e800314007810455101c0c0c0c6841d078465a14a401d20316803204012001c041200c601029000c181844550141e02c0c90240350040c0d40707900c00e542e180080343c43c0c1c442c00100c1e40b40c0000c00340140c85003a4003500d9454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 98506295 1250 98505045 98505047
    0x1050105061c0908040b07050c010819020705250e060a050f010309020a030c080a0501110f0901180b0307050904050604060302060d02092b0b07050a0206040f0201020a0506071805010e0d03 82
    0x4540401c200300c000c3d0702e4040c55008110100c000e0070241a101007120347d0b4012030b00e0a0f40c504059650300605005011080107151458070f40c2d459801c06500034003617642c07080c07458030718144443c4590082081c0c1c000d55162600c2c2c030a158002d400c2d40e07145985415191242c2040016521880c802c29034400300c1481e4281c480d5209412906c441480500803441d143c0d2603603151008944140c10816103544400e090b48184102400b0f5090010014031145203050401e105074083d40c41003124190500010800010180c45c1c41044040180b603038500741f07907e80c28642402021a0b0011b040b46118038141070101d101490700740f1825040302d03401860646010f81d9895003c0194018460495203e54009071200c0540301c1030910141d8203e04c40c0d401101240c41e0701c2c01c2e0780c00c11009040c210401000b480444500c0b50000f4040b908243c000012010035280d07480101e1812010103c000c189004010034450400e410500302c61010000407201020540c4600044601403210a261544030483c00803045c046 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 98507545 1250 98506295 98506327
    0xf0e030d03020f09040e0d1409090105210109111e01080a0c0903060e10051f0b03060d0203030d0b09130302060105060c120a0203090a05040207030507021018060903140105010506 78
    0x40003e00202400c000d5a540090100e403262800c900d4103070800c20030007450342e60040d10003401611080c000c070305080c210000b1464040c0140190b50081001100311203c1d8020b22035174400d80f128440c02070001120510b00100e940d40403400f100c2c00340030b44107882500143d0300d807520031507a50181e6400505a540312088409400d4420003402400403a10010001c201180503154400140c80e0080c240d42200081140840380020902c3c2c4441300c0403003810b09205100c2100c141154950340405032691680c1c0001074280360710810007903140c88001000c030080804d54001305013204048840c1192075580b1060a0713551a0703140c000a0050700310030f0050141c2d14002002c0c1410b522244211003165000300d8a00b01294000041100035a2000c90610760500e4000c1f140d20181038165800e608250341554060210b0280c85002442402c040c00403000c414070401c403d084007006203003050302e1030b030759080003030012030982c0016100c1215155004425002c14024181292005400c0910348581c2da51203241d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 98508795 1250 98507545 98507557
    0xe0c040c0804120905120f0d0503040201020a0605040215040e06091b04030204110d1d0606011e050d09020a090e010509070509010b030403050d0c0305060f03060f0c070c080601090b010f0e030d0302 86
    0x9004c598a80400d5641700c1c1100c015040006c0d4001b0030348900a468910314000402628a041020403c01c0200503640451000301841d4410b5020603503031128400201404104400b02154003404900010000c507500003403805110306640c528403513242e255900c7c640c9840c00c894001440810002040181059070210034500c40d407500f142c1c10704c10580047d0341520907004503007201d415400c5145402400510038243c1140302420030000c005031b00900c0b045003180d0655258144480070480c6510100300780c12601c1103075801400011a161541c07040c82c0100514440e800156181c0000940c00200c005200310540f08010315400141c0e1800714408007a81c8018811007c011080c8000e13400c007149401403400d80c150035100800c6e2481e1401c148088204c801c0b00b0b10348240d20140500c255030b80c3d0209540c0e0485203900c80c0e140e680441c1e05229204181980c420b40040c840d00d000068840e90a5100c1d0b00e00046c260384034402c55640c800c0480f404c0c6d4a40440c59803640000070700d121101c0c007a60003009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 98510045 1250 98508795 98508797
    0x10510030605060c01091e030807051c140a0f1118010c080313110910210209130620120a0b0907110105090f07030f0201020304030c03060e0c040c080412 67
    0x258552502c01107001c603009600b00d070b0f80aa44540c60035042200019000008004841002c41290f006407802064010050003010070b00200040c04100310b140503584000f0446814028801654512001c14a800e022140050101d20f007040361180c422907400340c4c009280c08144c1041c1445186000510b44403420721003181400f8000c03220100240044000e1841200a01c01103008034419040c04140c0146417004bc5100b4231010703041042c5d900140d1508015118111030004901d003440c0040f10b1500005a0069407100c4d0030003c0000b03481d0342c03400d200c403180e10500052124001510750314a030a48842c094603111801031144040101c543d07000c071548050803001c04500306084001141c030022090340c41000040001010251045090044a4210001b18001e000c08100078041e13680b07905a90000030030b01c0945c01090400d582c0300f001030301c014640100c044440385941c0e00c2e102e401820f100049000d01e014075183d40c3c2c5245403620401038041e260361101e0f00681d40700e6031804814a8034102d410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 98511295 1250 98510045 98510051
    0x21209060a0512010306020c010b012a020303090a0803030a0f021c050a110408031b0d0f23030c041503020a0503010e041a01060512010f05010915020c03030d020d050702060c0301051003 81
    0x80c4a201c3e40c1074181d4001e502500d001a9a84500c0c200d0b00e0940e515500c40034140003844049a8100da0944c100004610321301921907981c0a035880043cbc114459405201e510000b00b10010981d4940400210b00526020307004220051201141303109a003d459802c5c013122246aa4419041d401c5812440d0f0014141da400a00361840d180f8a00c0603030800d0b00260b446500119094405601e8242000c2c500d0200100810450201c180b0081010a0144100042082c58181144c4d000c9150240d00c4030742c4e0403c0e91040d00d074a4040d030f821007940c0091080c01e90300d400c00d14007900402d010341b0844841501565600e461a800d1842e000f00d82138019104580183ea99810723852118000c0794594040c03d140da4503250740e0311104c8242031480c401a00a490074000554040019a8120040c1c8003110110728503044080300302c43c021b0341020000d01485405000c005071070501b01c40c00c1d5004003100741d4441e4040003240c40313008040ba95070310120740940c1d0b101c2c0d003000184104d01d0f00c1007040549128614000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 98512545 1250 98511295 98511307
    0x50f04030501090f0201030c230d021b0c030d051305041e050103080d0e0105060a0314030c06010b0703081806010311030c03070e01030c08060708060603180d0c0b07021209060a05 78
    0xc6802c480c0f0008054802284542c040421982d142c014646081442d02c2d00081c1d07c03e0340d949414803003010380070304183e0001c00036066140c050290103450720041c00305e02c02d040c61041700441d20307140e60b50070240910030702649444864090003070b01521541110048840c8603103040c101031000404d500c0c1c081c40c0107261044422004e4a1050081300e02030f500c02c10410b5100d00859920105580c0211405110707a410401000000d80b00d000b5200c013180e03006a801640c1443e0490510b0662088280700881406610300210711380300000010034040e0f1080d9503071009692180340107500c0c404044c0d08a03040c0e8104100400204070b0508441540075030040a4425024100d00043d15201c00c036885008103450750bc00400901404502d0b0f02c0c01810010003600442c9045000145410340080079903100f144c001c0007051000203200030300355120b6002011a554100040c0000e804d06e03941c05d804807450006800080d0205101040391210441000d4000c0c0c2080d01e50400c011040c3c001480040c1003100500003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 98513795 1250 98512545 98512553
    0x201090302090a0c0f090b030402090c07020603131b031a070327051c0c17040e0a0504110a06050a0518030105070504080106050108010b0904051905091b090115050f0403 74
    0x14240280f003070040000e0024000400540720044941030380090260618040101092020843c2c4c4d000307504076a082c1865031031200500d2103025400c001b9402c92404410404020400100f2001903401000410040340c038549100f00080c03580d00004110480618240742004030442c50070f504800d45040203d905081c01da8000a8a800148082c4100c142e03c200141489014491110240c0d0003500c51031a1a030b031140041c100141c0018000c0c803040410030b032500380e581c2d0401558050851500d0491072420011146c601030310f0f0030344084d250910f00c10080080352030510984c5040740d8550b103aa17800e004085000b610035400c40310021000ca50b0310075845450380e41c20310605104912540700e081d20349041c90044c0f4210740b8250041410b1202240c0180034a04810007900c56160084901049603075480b089802c41009045559420307a00f0f100c1030086c05c840108032f1420980e450030b09440003c0c0880100054080288524000b031400c900c104140d03148604020250980d01640b51860250b0341d6403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 98515045 1250 98513795 98513809
    0xf0c080c060708040504050a0b1003150801060b16110d0b0106080a1a060f12040c03030206070302090307170f101b0c081603110303090a2a0506090109180609050f0f070c0201090302 79
    0xd00d00c002a9a400d26203818003c0032338400003820b0008000c202c0c460409070750340c1c1648204c1d00500001c9045c034107034404010b44180007500b107006c080d05624070461685071002208000b8091140801c402000150000381c01e0b12960f0065503c204140d410710021300140106a03110302c1c602c40d804c02003003140320918645544d185008d944102c43d00131a051a60500a0401c2000740c02e10341054010040a01203540c00104401a50851107580c0455991158101d01c0d00c4883c41041c1071030300800320410307140c517015400120400c0f03501c5020038640b000180308036004194000c3c02042c2210a00c0303c400e000e220440d070b0b42b1742d4610a007054815205042480c91031900200d0311584940d1000d9214010803044001d00e000c008110b10400e020032004140d01c041c01106402410700a03540420600c0c030070385c412040c090007071001801301d01e0300b0300e607208615002e40007030f004501c602030070003021034081604da8040e903205107507912882425071581c4004807403009000d44281c0c1006403001000c805683d0b260 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 98516295 1250 98515045 98515069
    0xd2705040e03040e0c070506010506090a33030606120504020604080601031b0e060102031c11040303050c0105060607080d05060103020d0e0303040c0b03070c060f090f0c080c060708040504050a0b 85
    0x20000b1a00c0750f10782050003601c00c600800b800c403003c00074040d02c00041e2002640a05440c4203e0f00c09840d044000081041007445521003100003028504803e0504c0070500e414180740d038001490000b11840d00c0e0107409407025403007582c2c005400c038441d0004d062010b5000c1038015100910461403e43c4e144200e81ca0100207030400d0312003080580c0700710f50b04220600744000804e000341209d11689460f10020b5140d00500080d007020b460401c5422040440da40d02c480048031302c15550702d454540381d08006100b90081c0c440c0400301c0d03280c1400300304646040002d407881607521040b85841c0945000c4d14401030940540072038141074080c055510501c00e64010008800c005000030341d103074a00790828000c05000c943c444c501614080041c040110f038810307691010507412280104203071588a10341c00c001d20002401900c01c041918031a030800140321400e8080f5140310089070b001c0c0070302c002041024802d0110007001d44404100810050034030760030580c0c3c4817800d03800000b1005426004588100c0c0d0704 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 98517545 1250 98516295 98516321
    0x4050d0c0e010806010501090b13261203090304030f06060e010b0309150103031215030507060203031e01080a0f0515040b010f14060301060c08040b0406080f090d270504 74
    0x5103000d10480e0700781005680108928001040f141d450300c0006404c901c11801030180c03803a000102a0352203030328081100000c0c4550520310107655888245c854104030320784a11040e90003802030701d0801e25441c905581c020390806020310b191500e140e9800d01400f0801b00100c5400ea195900022000175050b00300d0b0091694901c02581c034138000724507904084034403201c54071a030705100c01840400da000601841c0d51840000000300b1741540605403070707031600941c00180785115080011840d140d000c00914001e18416200341a030003030007220505180300074016401151700c9105018049015000c1c2c4d800c0581c051015102c1c2c0680400c2c260906c0d040445040c0d441108080c0104101e0344143c2d03a082c0180307080a00d01402c031000c000005c503188010f00c144020869202502424041608100d0b0b000302000c405a5541d50f98550000d4440e20044840d07100400005000817000304001c40c000301da18115503901e91511401c400280300000700305089801e0512010b00c003089584032031140c112203440d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 98518795 1250 98517545 98517563
    0x100e060103020a0b03130206130f08010b010806030d050702010804151514010309080d020f16030305010801062403051b0c1b0103090203060412031b0309050c01030203091203090304050d 81
    0x460050201c202410340c0800c1100504100700306c0006440c1032204692a412141c860b40e4588200e40140003416940024003028818a80010007030380540c0860304200085c4c03910f030240e80e11070302013680743d0005140ba030020030000c001e00c600641c070481c2c108d40d0061250044054078006104100304441c4680d0007280001134a000c240820514017001404180003440c2c140401040c9a4a80d02c03540914007c49040927000f00c0d03450481500d001c15036015601003a00035081854034140200601000e120f2103400394600308020078640050b86020300c0070911440c41071448200301001310000d02005040380380c0c14a010440c00d4050076124020003502e03260304001e01d24400d82c2c02c4003003864031580007100d041c9407410319540c00603100800c0440d030254000a80c85541c1c03152090960180c038a0041c0f05c109a080500340140f095019804050800e010b40120341000f10710500540880c4001d448100c0b00c2d9000240e010500e0307451400860b07100d0318010590b41455503500200e003444603014412919034078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 98520045 1250 98518795 98518799
    0x303020a091d0a0e07080a031d090c1b0604020d03050903011b0207060306080f0a12090e01090501090e010903050315011101090b01211a0a020903060c0912030306090117100e0601 78
    0x1c3c01d8092841d090140e0409840824640f070f00031035841901c0344004003400342c41480c803203d901c1007181ca0b0410f40005000d0840e2490504078481c2581d0280a0143d010910708211168810000543c6440341e540a000210102010744003559282c0021710030f039a042d901c0b180d2010f4402c88255482191031110b40040600f9800c0c103401905079041c90b08a09429400740604114030040064506000b5410020324030140d6000c0c0000c880300d1115070000303078011461500000c0c410556601050403108031200410041024a031502e003a21000e9101800150051010440b40f900f4040758407032107041418007800e00020031000e2425a2110582628045032481c0100191040614080620a00c1d4541040c81c2201960303100b41c60274041c40c8034400341d81c3c8040041d100340d40d075604403041100000c0232954246021300403040380343c0c0b100b1a4103008030021b060091074864000f080e40d020700001003041c3d81c81c0c1e007841e68100c0c3d00426148150100d00c070340d000e03000128800d03200740003104882d440030b400d00d58 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 98521295 1250 98520045 98520061
    0x60522020903013210060f02100509150f070c1b09050c0702040c020f0601030602030a0b030a05060103110402041a0c0a0c03050c0102150705120910060e06040b030a020d0303020a091d 80
    0x260b920b1804d600010000c00c200122101032071103010648406040000184200300c400700d00d801010548011141d1614040c44810080054000429007108540f00c203e5614156540400780040d40e5030f0010408140076040080c6200d8403111a016403141c100c6032555a81d500c0390305035242a103c000364806d00190710320950a0502610008040c680001d04070302c25424461690f91505100150020740c1c00303c04550303d9a241c3d000480c0c01d410080c110b80c1851243e0414545400080c44115800742d803401c411002ea013014000e0f0b84c00c40d01659020074600d0780c2071000170b055034017108550955028058890000485217642c04016500820061000440c204006850000382180a080702030240003000b1115030b1041c2203840300d00c000750a007490703070319003101a6249c11300041580707074050300b40040458240004011140b04001c121414070000c4901400e040d185c0c084a0406900481c41c22000c1d000b10380030707400030030f4000b00d54038109104070317917031070230040200180007038060690030020070f0085803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 98522545 1250 98521295 98521361
    0x20a0c020f0a03021305060d080403050d0e030d0c0305130302060403140606010219020d050a050706020f0c0d02010212030c0712080708060a0608071b05010204060908070906052202090301 82
    0x850707026280246000e0a6400280800f0203400041000c0c03503c580000c2e4460301c0e848800d10744968403c8165032140d0310b0b89401c0381c845c629136441c040082c1080c89070034410728000520024081c40b0740c96070010341c40152800c54407903111425500301c100140300c0000044c0c40c0c030402480114080e44000c11540410780d05241049400341034541107501c600b20350000c16443c0856800c1d9103034100e508503594501490074a007028903c21025040c1e004e9000000780c110380106800c030482c102c0009a904004212040008000a0701d40c0a0b005900c4000101541c0d1114401960010440840b46090a00740c5e9560340c4048154110354000400e0f010a001da1745800518240d04000c0848144103150b09010008244400c010515010004c6800324600480303104e200442036181c00600a56030b807515a000a00084403511448440d480780346d41c000380b12045849103405450004001c100356000e0811305014050303104005a5810b0b50820400006603024400c0c2d401943c0703003a050700c564010b00000e100070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 98523795 1250 98522545 98522569
    0x50108010b090603010b390706140301150c0611090406091a0609040f0e0a0b060a060f080c0c0a0308040201110d1403100e070503011a090f22020a0c02 66
    0x100c0304082c0626007090780c3e0001502c3c19a501c2440003501c035280c4000800070240340c4402e042c1c20002a1118484000e082c50b84085040071260440301020703541d44c0c0c1190040300e403120255810400348014840000c102c85007100044c15842d001040d0106503e40c841120b40080211602e03030070010b6081c250b403d140c002c01e8000c0c50110000c1104504580e80d4003442c090862680b4420300002481010640c3c81741d01c8000300100d089010803400080c9203144d650340b580d901040e20310500b4040064050b140c12146a010346a4170744d00c0703080144401001b43c581d440040c202c00502d4400f4040002681030810500500c41d000e5a152129418140000340000c10740241c5010181c00142c40e070740000d5080283c0140b141c400e0100c0980d243c1c1d4555407581c0400503038000c20044527000003070058456011000e1030585961070380d00001c0c0e44080300d0703045280c0700303241d5000d4110801c500c1d541042c2ca0000107100001c503410420303200c0248143c00c0c040880e44869030010218410002ca2000e5080c0340c104c1c808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 98525045 1250 98523795 98523809
    0x308122202030c0907021e060109060b0901050a030b0d0f03020d03050c0a051615020708030415060f05280f0602010e030301031703040602040504020a0c020103050603010c120e03090a0f05010801 85
    0x9000380241d000300b0f80740c8040002d40c9024000c003802180c0310074802c0141207000c040b100206004031812601894035401c081c410b04550074141800400c8249018086038194401610303114900040408154041e107041d10b20140d02038040440b0002003038105088004051007a8080c1c13888d0078010703601800b19980a04110024101404072646403504030040312000714101c0072522010100b8500801d241c880d50000b00049170010480d50304001070100654020342c401c4001c40d10000199004a0444029202d294452204e045081180f8140194166800344103146008017810807102c03040e9011200c0c2e8080140c00300c10b540300b00b14076076082c0700d21120304054901440c0386500d1a25182ca0022030460544050358002001c81e04201300c90381281e008110107001952941c03640c0d00702510064002c43c05a02080c00c0400044441c501031188070704c0394079141c0310240c00740080c220007401070420749081180d0703100400c0207a003680e4407608007800900e000c2c4000d02e0480e040c24001040848107a004d15 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 98526295 1250 98525045 98525101
    0xb0403030603060c020c2103130f03050d050c0c0609060d050906090c04050f152101090c050d050a03050c03040e0103080903150705070602090604030f030305041106161b030812 77
    0x4181d80d91141d40d090542c7c010318164141c0c00140c081c09003188208070740c0210b10005904006071b591072403510325044a0290081d120203444400051f209440740e03200c4a401074001c03240c14100c62410001400082401030300180c00c00803800312070f00c200c036802d0b07402b901c165021404102801c4030800c51402c1485068a00384400d050000700b0491100018140c0e1002080c1d4805588140d00c0c1d03040a050900542401d407508401406100c4e0f009181c0e1001c1952940e80260011929040c14030314100040e91001c020032010045032421540da410454100b40c1d240420400000c0745008541168081e5006480d525929403440040601c0d103070544480030070103070f04002000041a0020161091190000000350f40d6003602030000e80b151240781c100520044e003c52081c000d150b13040c2e2080c2d00c42c40c4640c28000b030002c00341080040c98054240e04046000d000126040000c0413000002420041e0f0031450b805213840ea903c080481e00460780c0206a01e91034000c00c089650202c0400780d4481c016060b04d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 98527545 1250 98526295 98526313
    0x3060f0903054005090705070506040f020402040f090516020c01080f0601050403240f020306060d0f0605030105240108071b050c19050102010f0b09010509130b0403030603060c02 78
    0x501907000345003010298200303180c0c0c03400e40302c03840c12164005000002041442d5180480c03a000304043d15005041c015880d00d80020206c40c0500b003110880c2e0b030040000d110990701c2e65141005450f5404040342c102d40c09220010305180160741c10030281064243c04100f07072130005018040c0c481c2d0b241c103810441d03101000840d4580d82022007039030003140504042d0044c0d5584001620705100d141d0000301322491100d84000098402184001d5604019800f40414017801b40c04900341e00080d81c016900240400c402c01100c0240d5003c07403a080c8801e800824100c1da1080001c0c2119000c8038141410b0031f007041c6401b2800d5498240d90042c060900b0448610704100702c3c010000e0b503500c0044418440c8200c04441441410002c1145489c0014140d0403544480f010300204160300b80720700760256007010313402c0d02c40e480f1900a64507008009015031080381c0ca4041040080803001e08046554082101003101040c41c80c000544502c1c0640c5010400300d107145800703c11584c9000058003150003c10308 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 98528795 1250 98527545 98527547
    0x14041109060406050d09050303040b040b0612030901030e0106080105040c0518040503040308090103090606060207090f0612110109081207021c0335010e090708070b0a0f0509061303060f0903 83
    0x250b6050760300a19049444100300f4100310f00030f04c5445000790440c400401000104003814008070f1040788a10b4041140341c4132041840300b9011000603600c03184d0018400074149510a50100d0546003000c000815034a60f00d4440a0860744252016183c0010030703001408503080125000b44810002800f4140a140c1925504d48034060740c00002c14400d4005540c2e8003036171181d0410300b4615000340c8200030003030ba40c2d680656980324030b1142d0b058031801d0000408240260740311b004110f60140348076100c402d515640e500078280121200358144070005c04041014001041148100c05150706499a03d24040c010890b4188503050119058011100090006a4802c450390300210990040d0650300510107480480b007410150300b1140d00071034074000156514640d8015020700f89440170744440540b83ca40550304c50b680743c05420000c40003000500c00c0603100e0a40012004c9052601c070303040c00000000101240d001075005031400041400501c00d0005501c0b680c0052546244200922032090390 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 98530045 1250 98528795 98528797
    0x11a1c08092709010b03071a070302121206010e0603010311130e01090f0b011e03080c010b0607050a02030d050301060c0b0903070b1003030315030201080a18020a1404110906 76
    0x11008025400200320381d04551030b04500c002c40000215040b440b0010410312420140034100c0d0a25203d60034103112a80300d007008542e000c1602c3c030700e404120f0444088a000c061070381c0814021421845941c0341400340e52510800341c14291424007400e00345050820005007562000d03441c142c031840b0108010000200c59582074490401e007616013195400380001904014005031140c0c0c0450350a0804c60810880d10b4035806000c02d105a03000241a600d801c568030b9041ca4802e002c40442080030000c0c00420410340c043d108144100c000403840043d943d021800a4018140c1100e19a109070003840c1180b40c10300060b60426080d01e011825036150550042c0764420084000d04651100b0010030a0b6120510031180b4a80e04840c1280b51410902c60040b000f110502c001d0f000a803800f180b000034500400c1141e0300b05d0b43c059507000015142c2c0300055008060107000321b54000307440611000141c540c1500c2000a08500550764100d140d8070007400150380200601d03424803a000c1180030040e5803540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 98531295 1250 98530045 98530099
    0x6020d022407030c020a06020301151409012007050301110306012c060904020405030d081b07081c0b0907020d030f020408071a0d0906020d0b090601080406052205011a 73
    0x460081079290000e40c042c2e0501a4803503007d0134980c000800841c2c0100d00f00e51101d520b50841c2da45000f02d9440105030042801400422400640c004480b51500314940146002541074030013070f150340c5580c1e000000e003100d510640190002d58040200100c0b50b030040700804070180085502e85a001494070202c1180b010183c800d0322459001c04ca8074120b4031140c0c1500c3c081d040140c212101c030343e880d68000c0e21040c4100e0342e064002e40401200c151103101d040946c1c4402d64003140f5941091500c03601c60300c84001804500308920703030f114000e50356641c070180c0c00b9011f48001d80260499500d503800003419203030030502c00c04809004100400050000003050000c0303403881454813071400f9454141c0a6a4880c02d0030110000d07003824115828484d482c0e00030405001218402c0080014803410f01031004412034003603011800b6600001e001c101c0540003154800c09031004c48040e44100c003d032600b01c00b248601940c60383c0d074400d221001c81d1101c4078610408034080300d4a03035039611a03030325000e402c1c40b101d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 98532545 1250 98531295 98531297
    0xc0a0c03081b18030c0d0305091c050114090601050301090b060907090510050c1b091302030c0d11120304030b15040605270106030b06090402090f06030106020d022407 73
    0x3000000e2086101d5141c20b84680004410103555140c58000c080e020a1042500d40d110b401104200c018528080c5034500005a040c0c0f1100d04052541c0100030142031074045414035081d1035001e9000181013845515070100c0640e000504a05061000d1072415005801081c080c3c0e1510542c48081140304060960080c0200c030740a070030365a076200440701e8580e103500842d0442c0c8483e004c0380e00e039900074001d021020504003c440c1c2c03203180380c07060215030249400542e030400300070301c080742031b980784030658108050002e800c0f5540b248064000c16030045072031009a03880f264200d01800c607807504111030a84404098011814581561503034414240064510001c9405880c1d020700300342c03640e412a00041a000305600000e101c04034010036001940d01d103201444800c08000b00c0c00174040d00c07882180c42c401800090030b0580070030601c0000d511084516a05c880b03029500d41c0d2a503190302c0103501030060707a03014200d040180c4101924144901d1803052500c00305242101001c0d045040380d5a00082c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 98533795 1250 98532545 98532557
    0x100203060d0b040c0602100513030f0905100e0f041a0120030318150714070302010207060e0d021911011d030a11030d090e071812050a0204050c0a0c03 66
    0x100000124540385a550082c0040022800c00c4180640104018100c0314140c096034002e40c44031501808844c0c0846001d10001820310802010901c00e044075a141a22420080503040d210b01c005800c0344c0c2c41c803d60600240e01c03020856224102041361882c1c1400948060001120790030314040d0071200e41156504101d04c03220804a1202c0d0351642c11401440d0005482c1e4a0400c100714112120703400204e00d000380300300501c1c003100c16040d4034154890461540d9071182d9119015050f150b5510100c0103404540d000e1021030b0100d412403160001e0080700100030b100483c1810b00280c10041222920445070301e4001403440890f40350190955a09800d1800243c0070751061070610040d0750210f650b94252040c0001c40c0c0411842028201b2005c60442c00c4601e5883e0b030b140d04503890b006074000c2c016240c2c80c0303401244100d405605241e43d0115241118840d81e0f88980602d140030708d0707076141500c055205008807410750426200c0c550304070901070501407a1071710140020740f0440c03040100070308000c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 98535045 1250 98533795 98533801
    0xc0103060305030919030c060309060b09040b010b030c0903030c0a02010e03032b0e16050a1202010c150902030f060406150302030d0807030e150103021005070b010b03040206040302040c02100e0f100203 88
    0x3103d8240365010b15400058610303c2c48c1c803440010b000b05543c6104440d0f0340e03d05070059045152032500584580d501410b0b40c0c64076802c010100b501c0d6040540400c04141742845a220180c2c1c041c40680149400503000b040354282c0760000500c0c00800c0c446250080e08100030346044c00303c2040c160061700a140d414000407210080d6204000c001c44501c2d10f40600404d04180481c40c006190b9a0842700d0031241d04c800d450f142c001c0403400006d5000002c0c042064201c0100002c1e0900c50340e000c032a1003150001851107540d03000f2a04000385401c1c00c0303a190b040f40c03080108005240c414140880f4080201c0d070751035401c46d80030030358801c001804c1c001409122000150383d00d2194000160342100003040c0c9800c8049100064031030002030000300e215000c41e00d22113031100d00c1001501c0da44d81d0000003071000c5034078015080301c03642d00161050f60840001c00c008005626140110003260500380d0080500d84403404103902200c10000e0109196000403030400c0340f0007000100440e80180395800141e580e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 98536295 1250 98535045 98535079
    0x30e03180d020d0305030a0c0f020a0f05160b040303080705071a091609020403020915010903120527031c0906031107060501090209100206040c0b0c0a0b15030c01030603050309 77
    0x1205440c000c0d07100c2e66405000301013543c050042c5019001e8001c081c000391500c0781c1c0c1030b584080040142401688541300c102d000c100b060038904c0d0301d81d0180b019503c4071441030684180406043c1c00010200d100054200105a03204031480e03440001d603c1c100d81041d401e50b03550314003400121071400780c0240403000b1840c81b10050013500d469007812958081d1461380c4020210203500700744426803040c0c0c0990b00040d88500c018031400300a89059480d0320100341190f60f0301311002c4190b48207070208401441300c81c8141da00704920588201a0748410140c4440c048200743c5011800340384044400d0b04040a2446960020f07419020b4504500f40480d007141452514201c601990f0b0024104500340000014010a154000c000c0f041c2d0540b804450400991001e9030f4484003560000c00303240c4140e90800c50300360181d025000810914054a88180b07407034a500c2d0502c4400c3c0c2e03402c142214540c0705100e00b4601000b544004410a003014880145581c0740c01c3e840b80147e0200500859080481040c2c4c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 98537545 1250 98536295 98536309
    0x1050304030522090b1522080a0b06041d060403080712020d0204060e011103041a0904020a020106051207210303090b13030e040b0607030c0309090e03070210030e0318 73
    0x2c1c0303018820810014980c03d0441e000301c02c0c14841c2d00c84039840c082d04040d0504103221136056038140104c5013480c0810542407004001402c48215410516003080425a80d006000c42d4035520300940c80c010050a10004000468410181902104035215075601c2080c2d000705100394441d0309420810f0b0180c2c1ca050041c2d0f0804d9022185010b881e1000400310413809960303000d8016151103943d00100150514010343c1d4454801c0400c500d84c1c6d000340010015800703a011803800303481001803804d0130106235a0129050b0303000b4050080150351180c00a1029043c030b0098220b270096000002c08440b45080c4c4280c910b420b500b5240d007500c0c6205461310f01894083d4000c00c03040303980100310044920301075000c0100350003814812000986440c8070543d00d880d1a0041524010005120320302e000043c2e9819a0840c40680d012010300962110004d00c0420620500344040175045c0915a030b005a4410090840d25442070541030510b00121200041400400c0d1044030303000200144460545000007214 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 98538795 1250 98537545 98537557
    0x102010b0303071a0109050c0f0d0b0a03120311090a0509130b09030d05090304060e21070b090108060901120201050d0905060106050c010b04050402061602061c0b010801060305100302010503040305 86
    0x58800010031004201300381000d80c2c141d0a0349208684140d8844085d42d041d16010750310310041401c01c0c084076445581c100d00400010181540010b04110144082080b80c82c0580c811350304e16641c2102e4800c02da8260141c2e00410144a052529051a000005484480324010507004800325000268001d8155041681403900100c1c1900b039860302a2913156642d102c3c15000c541c23142054040350a0500c0003066030188c4038582c4681038120b1451082c000300c4400c1d01c070140031074807681038205c010107000d111030400781c0003130303040c00d542c13000300c0e0001410200c80a41018001d21404004005d40841c2544488080c0d80c2440e02035038039441f00703e801d4040c26000a01601c58001c000000a829401c98002c01d01000180028010141c18a00b00004c40f682218081c0d0030880c100f115800b200c20381c030386201080384018139840c10010911011200401e501001c000c00c10390b51411901a980c201c14018010000f505e01440075140600740d8550341030031840000c0c1407000110104080500900079201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 98540045 1250 98538795 98538799
    0x90c0201020715050412020d0807030507020c0a03080a0e06040305030a140d020408010c090801020a0e040506010314130318030c0905060402070f0b06040501091103010b070507270c0c0b070e0102010b 87
    0x45502c4980780183c01004d0580d0701700d640b541e6080841d841540003181010301104162030380241d41c0d0362030b03500340c010382130042161085000c2e1101d02ca03401d6561003045006580100c00c0e0036100d00c0783c0100030348402e0f200c0170020310866041c402000011000030844614035042d24140c8181d41001e0004907450103038030281c420b024004100466032000c1503202c421106600da46000c00d640c0c1d104851400c03441405515170004205461101c564100342d0070040d0080c50624000070007903100e01360020030102c2a11981d81d0301e0681240b20043c56800b80a405802c24401a16111946540d803000c00600300383c464204129100e41c00036182d691160b041e0b401940d0071604140c2c0325007017480c01d0500414100d684a104519090020070022214415440b117243e04c005094a981d00749101e00b41daa4010f42000c80e4a881003041c0881d10300d0069001e8480c000d18504100c1090f21681001c0302a11a2802c507030040014400303c12007c01d55410100d500171246060150a117000d80d03004038090300c06410019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 98541295 1250 98540045 98540063
    0x313051e3003130210080f1302030c060403030314011403190f021002100c0809070618031a011805040201050f0c010f0501060c020f0306011202090919111305060901090c02010207 78
    0x41c01103980c2443c4840a0b03c2141d18002511440500313940d9802c0c11b443c1d036004072560900117450340c05410300c8802403d000404071201c040a00c40080c106900c260011000031340c98a5106070b4a00503070401d03a01400140c403402d40c103089c11030042aa1800600c030031007426401650390105101e45c17041d40350407494025000d0f000441da40030019540b0301c3c2144005450302d05d003030040056148122005802034100708003a1041500d0300200b22010325188658041d00c1e2143c1000000068138610103003190950110a64610340c9485403110060751811400c480d100c0c100420040140c0e80001200d0f0964041c611329602c42c068402100c3c0103209244003907101c03034500000455140c1d08002080f401500c06c450035103901003c6030038503403182d00030b1245e00e044624408a4200524100c0507040e400389010301200c0181c2c003502c142072000d1303e1500301a00c0c036403000212040e8600348040301960400e68140240712504090f80468082e40052040b0a2020780d9807072800e440c01d1003034049444041e0000942 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 98542545 1250 98541295 98541301
    0x5060f07240603080a0f1d0120010e0d081b0306100309140102040f0906050a0603020c10050c09010305150d020f0a0308030a02040e01060f050f0a0c080313051e3003 72
    0x10030480d03204c4481d11011407540b0b025240707107503c18586a220f90722818152131f0300c102d51900540b44242d04d0184020803003554510701202050911440d08042c00b5200102810b0400150103030101c0805054201a2124400031213400d40d50201102d4000c0c5060f5076008a030012054114010221018002c010600e041c800d101090340c150040c2c0141d0f8906480303517007910f40e10300300d91080f1110b500c01c0c00d41204003114104030303a5010341d02030b003030a040e0913098500300c6044241d039100712142200c0201560102203061011960b15104482c1d002520400c15401300c01041d0003e0351107200304100a101c1c1c034000502c042661070741c260007402076601021060b16030801d2810b41000e5001802070130240c0c00d20100015005114414800461300582c60350381ca40b401800b482c1c0c10300d601c1054000180200d42c000d40300080d00d085e0003584605038440b800c3c1408041460144d0810100c0c10030b41c15aa03080d860074001507031000c68003e4400c03c800c4207459002200360741810003461105110f600100c0080300b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 98543795 1250 98542545 98542553
    0x30b1314070503070503150406090c12050d3504020604080d020c1203090108010303030f021c0207200307170114090f0f0601030b0c161202030c060105060f07240603 72
    0x4401e0940c1c004406a0751496142c10a0554030105070000f1500c2e280c000b0040340c00700e0a00d60104840c58010307003c03800804c0d2140458500d100304140c086409a100304c42d4020fa07203078000070a02c01d108494400f9100810041180c00011203a260002c16050100b40030504540d904011a0003c01c03070407040c0c800d030300b00b80b02029480714a10192103015842900100380280301c048100c1d818200141c695156590841c2c130100c1c0104140211300007120340c00c010f2001d1030190720407200608494002c0140e03035204146841c174034904000528004c0b41c45488540d2009a8010641038191100040b187e00c10039400c900300340c05040b02e80021003d40c1c1a020034010328640101c0c00500c0d00a466046410a01051500a648810920025001c2036411010800110001e0001c0c042c04e4000a50382d001051f086d1100d01c10815400303070001c09070740001442841401e0500020380100f1045907010704255443e01850040d105200c801880f90032903c3c2d428440c1c80c0840700c681604104218100000c948900d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 98545045 1250 98543795 98543803
    0x106030c08010503060f010e04030905150315030c100c020d170a0915020a03050702010302072310020715020304030903170310080c0d030f021203130b01120c030b1314 73
    0x1214000107030020340041158100004d14900a4008088905c05a80b80178840c80b40090082d20071001c10027404c2001800ea55800300491070407400d0200c9941d03034104a580c0805039030a220303410f1b02a0300450111a042d07501c10700029105100f40c00c01d43c07114091480042c0c00c2c440c010a00134070b100002e4030482203901c889005071401c01e03095110090303c1e6490384039008019101144d680d006a2048140c0340000e4812400307494810b2040c1009030074214165202240e1241c0c101507810001e02540441c0c4403c1c0082084511541e07100c842107141c641c40341c482941e96261004800401e80c0c0003c0414101441400034000860704080e8102d100070689001c081c17140c0c0250307203442107000064008148680c0114140b211840c1c01055a42c0d02d903c155010b80d0940b090420380401c0d80101d04009a0600280c002140700701d429070b03501c800b1800240b820510b40348043e0004040c40790001e1304800054040321400d000d0b250000c550041a6940c1c0c02004117403010004010003044410050848140d4002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 98546295 1250 98545045 98545061
    0xe090f07030b150306040b0a03050c060f04080f0d03060b0405030c062805030411010306080c040f0216060b040e070f120c050d030507020906150a05030a0209060705070603180206040501110f06010603 87
    0x1a01400701f860200c0800144a0032400007501d20340004c04003c00318a0140020f100c4103000305c580505003641d484000b0b082c170071a1061400c41d41c10569801e080c0552510943c0094805031000741d04003400c06000c243d0300c030350000105004001c000f988102500305845407240300303100501760b0781d0102c480f00070050035a003042e030701103e00020005c0c400d907036503002780070320420348025200030a411000d0b0010040541304603200c00c0d004683c00c10005099082d801400c1000500814010503080c0045091100725044a1070800c06c40d00320301401c1c0700c00d10340c00b90814216002c4c002c2580c0c0341502403e00c100003100d168459a0b0041c41e0b03405071020150010003130a40343c3e008540e81d5840e070756440d061110054104102d6500d058041004030400790040c80650381002c4e00400041c213040032540421419031200c00d00f0340d269444103804114030b170360500036010b05440b000c406807000ca14540c04181c4c140614018541400000e402d0000700400c1000003800361410320003201c586582d10030000e0001c003651 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 98547545 1250 98546295 98546299
    0x103081e09010c060c030e010c020d0801140d200a120b281503050a061b050415030e0a06090b09100e0a03030e0f07091406010e090f07030b150306 64
    0x88204100c4400c1991840c640603103800d03e030251a03030764040c02040d1020440e010705659641c03400380c1e84401d1043e00c00ea04100d030002c1501c00d840c01300191600704164001300a00002101113029900c179802c88818840d400b07100e040103804002d00c25828880700540d5242c10002180000a2a09040c2c0b2840c04160080c00d02a07903648501c0440c0c0810303105240c0710250680c20f000650b000c0a442c0e840940c5d10000300308080b000c01d480ba0764032403d01b90085401d5a250752621100c01c101c90300d001c0301103001403587c28006d2a161800d41601c9406480c0400003060559601440f01c110381d050100998581d489801004007116a01d0503000e0b8610582e12103000d4400e0700d014400c0303629a40701d02d4528180801c01070042d00040d80d03040700070b03103040703131280001c4d00649050f1200300d40c0802040c0c0c007810b801c1d5400b04142003040351040e1101c40c020505410400200c4801100307480c3c09242c150804422401200c195a4000c1d0a80240c0003480c84290801d1400304100450b8210700007440c003800e41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 98548795 1250 98547545 98547577
    0x1a04020d08030a0c2c1201060302030102030c0a030605010c0c03030c06020408030304050a1e081204080408100b0907090510231305040b0f09130f080307081503010203090d0e0a090203010308 83
    0x13001740340d02a0508180c2055030310418001d40440c0e240c00ba8031a406601d0007400031409580f20790119080e0303001620b480d02000303408141d100d409509070091001410080c0303003440728905030f5102e00156003c1e84c840a400d112500490030280041c1e41c0444020300b80000480303a582c2420310b071041c0e03a10001e1406440c0748640004400c001c01040314014113007500030a96605220407003840032502c0001034000c8a0020303040100040800c0c0c00d000889030710035a1b00c03000038100d030840d0500101040050a040410840400601441da1403615200000c20507192140031406402c8080c510361340e00301142003d40c007010803442c91805400d41c40d03106a4a0544082c826900303c0f8003400b884002010403194410350079400540d41c0c54030132030003800c0c031401900c8003225120940c03507860707144c1c2c81681c19a001844520411001c07008803009422241d206900862652030895071060716000c190709807004104e110504030001d070ba00d45a00d180034144103481190307a940d4a18110006500c100c00c1511340002c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 98550045 1250 98548795 98548817
    0x111209212101151407050d050c01060f03020607080304030c020604090e1002130608090109081c0507080405100b01050424110109020a1815030c080c0d1a04020d08030a0c 74
    0x40e14844504a030440d0010f18220000c5036001e0b92261044401000d845800b0700152011600802140b84d04200584681e9524001180d0365820740e0381d140c01000100402401c01c0005858000803141c000f1b403c003031107c1e2640c80d6407400304d6003200a6000039501c000c0104011071409400d900401b40b206400301120b503d1400326428800344e02403c0508200705c2503103101003060751b008102d03103503000082d10000100d0505035030381d560090300454030b00302903415500717911600e103420340c030495801100500b04211540341517600d1641e901070341d20343c81340d4003515040500140c0c4d010b01c2c19600680020551010055900b03013211341140a8010010300240e4112201c2d0702e4500b0601c5005002c3e600501080c03080e0341402c000c0241d64001c000205e81050340d404144804201c41240c03180614800c0240305112840c0c056110300d8100d0f50307410a4412603000b40c840340010282d01805458241d8500c0c0c00180c0d613950300000780701034440f404c06841c1c41400002c0221084980d40080050125621098030005c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 98551295 1250 98550045 98550097
    0x907060305010302030a030503070912050336130b150304030206010e130803060a08010c0201060614040b070b061f0201060e07090602060601081906090213080111120921 74
    0x707002848041d400d900849445030200340318600440e40a0602c1c241080c0a6039200720002d02041054000d444641010580e444e86144c144402c0066000f12600c1182c506009015032826101a40e416441086060007c01c0941312076044004180e5004010340480d9003d146141041d031f104941c2100103029010001c505c0f0f803d1409210301034040b000c1c0159051800350344070b601e0703a40040d02c0194407441302e4170f00040350417090080c1c1803100100c0d40041800c43c5030000160030844204e10136001c5005c2408284034524000081d01e80c2690468510012515044003280f10201066074403000c00c1c008070003a41903207405401040c00c84154240400d407503a58034908558501c02380c014032005800c00000318460f076120701403040d0840e8101c00c0b04860103540c00c0d0540111400d40e400000b58070f4003c02c075640c2110920403014001c04100c4000d11580860404000c483d01c100c00c62250581500800309052040c108018100354000c030546c0d5040c17442c02c01215000d03030045000c1603800e81291160122003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 98552545 1250 98551295 98551301
    0x8010b0a031a0403140f130905010501020c0d06060b2a010207150b2d040b04110f0a05090a06093f020312030f040311030306090406020d09170309070603 67
    0x880c0c21014450b00480400c2c02c907092090068815010007605010200203840401c00038183c20384059105595400f85060429100742c0c164000b02e40c0301e00e440010080da03600820b42c1100d4900455480c685007040f403910f00010644d03500081c421290100b030701460124503040d1148400f00b40c45070341c3c0300606c7c0048500d090f07209084000f05010000c042030200c00c080780d007050302104d0004051411002c4040b254250111918071985440c0949040d90f00040c00c092003010202e06045e178060010080d02650340809204010111621541c002142c0c40603038801c07402c1e10b448081c0100280d04455a070319004042e40c689000d0260401c46102125501008580d01c00100d2090140071070703101027055001683c81c2076083c2c01030360980915030310020200c00107c020741c030510140c88481c0940c00c241c140282584048006034803507610070818003210765185480c41c0e5015601ca5005030390b449001c40c4180252201c41002006c0030a043c5400a001c0041c0f0041d51282d02030408440d000d5507079050407015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 98553795 1250 98552545 98552549
    0x10801060b0912100c0201020a0f08010f170708070306020304020a090b03070303050a14030406061502070303050301271b0e0a030c05091509010e0115050a1b060e01021308010b0a 78
    0xc5420454220a800c108a42c0da07207800c003000546132003003501001001038801d00c0400b50010707540001c00c0c02c06140c2003c641c170a101100d2901090310740c186502000e200c2028010b01510480c000c0b4014400141000400d000d0100917058420a0355245444800303504203071002c83c40340d101c1100114001c1614812170304164001002400d40d585151415102a40011107100401c0340113000090701204800045020303d12401c0300081c850320b407094564418880301c1041045403c802c10402c003091b03005064a054035944c852004000a1000315028981103644488841030305054100d103690443d02d19080d42020940c8a00c1d10a090b4041046003074049800000c1207207840c1d80041c881801c0600c007040c2c1c0059003041510000b2920000101c4c4800243d0090031001880d80041c0050130190b8540c072040c0c441c40c20800e050841241001c1c05040c24206003070b0070040c04c003403900d0500c08550440155000403900855944200c22001291401c041c000c00740d440d07003442855003040c01c002c00d003001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 98555045 1250 98553795 98553809
    0x81009060b042702040204051c020301060605031e070509040504110a05060a0f03050402040207060203040f051b0d0f0f06020c0d110708030a0c0c030203060c1b0105010503071a0f0a0c020901080106 86
    0xa2440140309189555030f070804004d981255003030102054940303c2c1017000010709040c4d0b40001101200d40b04050a4401541159041200038000e00c4021680f000c10444004000700c1168050703034a001044510b070044013880d9a2140c00c000c20b020601c04410803440c018142510356a1655031180d051140034461801c000e00000c0710321221660700c0e48030ba030040344c10901c01403015183c44a00e440b0b9805036002503c0036143d4070485a40942000030800c103610920043c0c000e4038109640950008664072045100603120b000310309540307003c0043c03269403801d680c2d40c4034004648401e00c150b82d495481011170129030120f03d16105008070000001544001c60f1502c0300290710f000302d000400c86055104501c01c031111614104c0c0800166424840c1c1c43c41114010300c001e031101c145c000304003698040020201c2182c1d245c80c1c0144180e440220f403041c00d450005c0c884450300034208460340902e100e0f0800404400301c01141d0100c48a0740504005007182c000c03258601140d0b290600c0600700d83c50303481055 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 98556295 1250 98555045 98555081
    0x3130501110601050a0b0c03090406080d080109051b0307030e01060f151107060e01090305030309010f0b060310060f0909230f090309150405061303120314040803060a081009060b04 79
    0x24622041b401803008545042c04e41c0e00304112003001c181650071541040d1065084408100d51682d40611410b00600c42400b041c401402d008070384000c6480c0204e0b09d20b10030305001000810302030190b0443c000c3d0351740ea04000c101e81940c03219072014010305405201108002402c1d0504018420320841101e0500b0f1405050340601d0584180c4120011a0510307060120f528400008100180040c51103a40c1150000c07512410204880c0202c80c0e5840f0400d108030401c1c01440010349241d91a40240d421a081c020010581004165403034000765121143d0741c1c0c100500e9440c1658050603c04c2e15078040030740c032040340d101c10901c9192000c0884402903e41e105001d260503515090703400d018540c903000c500c0c44c40c1548a03804103075143d000301d400320306c0342c4080841041001328807100e110755000b887c501044006010540307400364040140c400b409c0d010000c0085078096507a201d240c070042961104031600f0100380d203054006071150440c107817000c51414011070a00e051a0081c010b184aa0031541 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 98557545 1250 98556295 98556299
    0xe100212010e090703021201020c0607050a0c0b1b04030609050f010501030f08070c090f05041b080705010804060605040e06160206061008150909010e010609020a0804080d020c03130501110601050a 86
    0x54140c02c04000e1100025104641d07001002d0707200c41013030b885481c510b03100259a80e0841043c0342c3c0b91002c060184810064200450140d071a03000c41c840c035580d81d124401c038480f62101800485042403d0035100c0c11701100041c0002040210707405240c805100c0c1e401e480c4010591015182280c40c07d01c4007800060340d44502c103000a00c554006c1900710f1044005024464235190b00310201c0340400750500700280d07030700d09210522100500708200350340c0c41d1004859460a020f0f146403501e615125542c1844600e0f00820104040c54210784050403018008128501c00c40d241d080e5562801e0705d071941c00d1240c500100d80028404104944540c401070301300c9800d101001000c07a12400010b04945403120b80c540441000c2d668160f8180c003810301100081680340301c802d8402e0031503905500c0300300038500c10082034645c2d82e088160f42ea8040c2d0000500303511f070790b814094500a44540ca5020010f400001480319040741c20022143c10ba4600780c0c0d9000c960204140c0d5558ae0710020b000301c0350300405070001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 98558795 1250 98557545 98557559
    0xb13061101180b190c1d0d050a1118040210110c040603051e03090306010303050a180609170a150e010e0f030403030201051b120c0702090a0e10021201 66
    0x21081140e484030380005410701c8050030403024010404401ca480b0200441442048010350030f000d030001c10410700400500c000e2503809004404410140c06002032014101c80d443d5039040340520800d40c11400707998010325145004030000c503018102078410349203c0c0d04660700f40c45101c0014403032603000c0c024161020b00c55805a855003030310300d01840720344905c014201c07003034545005040003107101f1402030005003d1407280340301021502400c10015441407140001c05d0b41e00040c200d0440350141462591118005000c07211862002600402c40003a0440010380c2940700c0d003107004450b588040203c048040c5da19080c0c640304150303000342014552860217100541d16520062580d600c10300006031200445000c03500b07100b07440c1440100e607080401c0c01c200b415028001d680e070101a1070122103201f03000c9515014070380903105107220700800301800240034100050441d29400d0300148060050700c1c0c580300f0003000d01801d0b4001d40c15401000d4020184200c24000d4600508604400e0303071450f801c081d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 98560045 1250 98558795 98558807
    0x60f030312020f071208010315150e040804030b0115032009040b0609130b040b01030e0a0305130f0b0a09060e130e01140c0a0e03031207080630070b1306 67
    0x40f0342e4058810800c0118005254980180c003006001d032668200d030742c99410302074017501c1d940f03e00034442800e0280b07401660703031040c1c061016201d5050181c5540d480d00e080a0060313000340d41009084a8048001054402080c0803100c2c182c603680c1e074144a0011441e0040c4900e0658041c15072222409224441e568a8540c00030060001e02074106824501080000f805a541e10b806c413403600d0f65a0032440610341800e00507201e035242c003820103201c21404201101d40c0c03286040c1c800b50410001040e400381145418035200003c1050354110100141c46a00c0c6401540c8010032000118842c0000001e40c3d90081c0c2c0c82d0300c80541c000700b802c1c0c41d45c61801c03075000180501c418006c04ce95641d40c292314264141881030b80c00340d004000b0b001d0300d8002c1007402500003a0140415480380d4405d00480910005800c4a03940c004403030f00d0f01c1003441c1c440f540410364001101c3e06204501794820500c003c681c440300e02c1040c20454105c1150300c030740c2d952204440e107489000c4080203030485403101407000a0140c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 98561151 1106 98560045 98560057
    0xa080a0f0c05010c0c06110c0304030b090304030606061205090c090703021606060311030f120d09051903020f070f0302030d03090206130b0901120b030c0f0102101a04060f03031202 79
    0xb0384000d6481c004c4bc40700828800c101c100103945540d090069070019a4443c4d400e003c441c1d180d070b102030315005c1c0c240c1070522024075001c000b8510303a40001d0084152a800f40c180600c43e103032000100c0103540218208075806804145481c00100c003031203010000d60052510ba0f40300c00b410000c050621006150f0b540403588040e2002c255000c0301012070b40349135a03800002403520382529280d42024108544c003a084003107509580c05050300032951b51540d81001040d07500b8a5102d510540018640d404085e400d50310214607803004a020354049041e540c00180540e050592007000200c8001498000c0203605d4804603411401e5600b050040d800040c1c4860148400400d8802003992001d209003224440e444405480c4440c2e40240100d00090100070418030a07a070807000307020002c040c41d071002409540f42030000141d00c1ca40c0e054040503245d140c0d40f0340141420140c640d5010703400003 = true := by decide +kernel

theorem cover : BRFrame.Cov 98381295 98561151 := by
  have h0 := BRFrame.cov_init 98381295
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98381295 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 98381295 ≤ n) (h2 : n < 98561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
