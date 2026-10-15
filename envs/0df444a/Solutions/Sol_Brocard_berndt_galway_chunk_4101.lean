-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:34:04.641333+00:00
-- url     : https://prove2.me/submissions/bf131ad0-b739-4d4c-b980-11682f1a9746

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 737410071 ≤ n < 737589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 737411321 1250 737410071 737410073
    0x503190306120f02040e0f061308041205070f06050a1d03010209030d05130f0302060d1505090c0c011415040902060d110714061003121125230607 64
    0x40e0300107038003800d42d80050545100032400d158091081d0308400b030703004900d0804251003203a40441c0001103031200b41c0061529032074400b4590304101c180c10b02500e0040b824000480c25561800a01d081030b80261b0003000800d080412180c000345031a071000c024000c0812141d5800c541000c5000c8440740c1011005e550080b40c00c0100e400780c404e00c40c00036132501031802010003d98004010744050046d420b9800c1c03015071600e11401070240b050002039030141043c044140303506899040340010080761094a10000e03562000f04442c51410744e4a58071000c80401c2c0c5c02e140f100c00f441000318000300109a00240d0501080070342034405099100390181d920341c1aa9010354840c401203d030415002082040386d940408008115a00103581c200c5407048140d98003c4410f00009036580a180c504100181e55132442d5030f0002e000306d07415803034010703c6500700290382c2c0703100184400041d82000c503820346036111000d034810603401e0050304500000120f010a00500840c0c45c0c56202035a07400741c034810794035029 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 737412571 1250 737411321 737411327
    0x100c080601050d14010f170307240e0a0303050f0f190c1404030f05191e03030b18011d160e011b1506050103050603150a09020303030f22050319 63
    0x40312500382e11080000081c0d500017003500e0344111149447d004820b2215000380686901c21484080c01030444151584919203a140c104500190115000540c507102d0018045c00d19104000c00c0e00880da503841007088107240380240b41e03440b00d600c136040003140ca0007410350132070000b00b00c4a945155039101c40210382e880c0941084001c03c0c002e00101070721141d4070f20784840034aa03180c000b180d0500488004085000303003c40520021548581141c801c115030f03107034403c4400c1c20a401a02059101c80c51f04010740c0380c0d85003202100041f11540c60b101e40c18022140c04120540820f08900034094080281e50142221001c100f42900e2609071040701951004031969085618410b904800030215801004038103188a103849601c1e0307a062004a54940041d0111582107800c80d40540104440405c5e83c04112060390380084040e40000344070159801003807941e001120307500c161241401c21b1002d03201c1c0c411907191200c1c112034000000780805554880c1c8030301500c0406841700070b001510b1901d042c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 737413821 1250 737412571 737412581
    0x1a010818010b0a081c020d080105060a0c06180203060c090607111503010b04080706050726161104052d1005062703010216031b05011b02100c080601050d 67
    0x2c006000c444200e40b1590700303030303218100c0c6601ea08410100d8004450540c2c00030400e100f002d4010b48440f18103a00c4d00d401e00201d5881450090104030940d0002785c00604a0b01c00d40f82d032001562145000c0c000c4d5031051501c0d0030400303482c10382c911006002c1500c45031794107000c0307425841d40709079006400c204040c0881c400700d20b1340c1e212458004020001107200c21964014104407002881240c081030342e148000d8450f84525103010340000c10b200540083c000103120700c0d0343c0c0c419080564920b804044507a2034000005074608480c1200e02034a2230003145024080c035034001902c1c00301e40c100c40203c0503142000900008011040c04241c100260144030f41520007802030801070295036940b401d4200c00c00f01101142290442140c8000b060441e6003070505c01c0d10b030704528031519124014019101a903440100c5007028403a8050902608000340003805614240310035211360403010705d41458040e0400026544c199005031a0228500380f007a4016070241e007141c0e003130030441e03a5280c100000d80080c203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 737415071 1250 737413821 737413841
    0x3041e0b04060216050a030308070c0302101a0f060a0828090f26031801060f06030510060503090604110f09040c0503070905150603091912031a01081801 67
    0x48011500050b0940c01264498044000011420440f92a1410002a0221400050001150000000d45440c05044c91580c0b060007401154071001d206c2008400b6105d149400f0000c180300c071040c621440c2880121083c012000b180c540c0e040021181d001004054020a01426286800b40002d44145c66840340380c03134860f0045003807080303055a0030002c24150070018120741c04564440380b40c0310b0005403440c00640c2e1040750300c0b8518548070341070146011603040c40742ca849550784000000f00c00160404040041c0f010391008640392400080d070302e0001d442c5520613018000100200b20107210003191055000b5808200e00f000d00650201040301c158100e11a41e4214107808188000e2220800c1d00c00202c82c1c0032030403188082d03280d10503001034034401e4800001c2c0c205449081c2c0c90515112000d9a4040004403c80c0c4600e01246d11401c1100500300c400c0d41d4a01c4052400e000c0340f0f51500620030704815a100380d1030801e00420009010080091036505505040d083c3c00001d24000c4d00078001c98 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 737416321 1250 737415071 737415089
    0x80123060715021c050412032409060e060d15050c04181401081501050409050f0303071e030209030a060b01140d060e1e0408030702011b050903010f0203010803041e 72
    0x3000c00d030500080294442c9240c0900480d032244502c1c0c13410f0f080c0c0141032013a07600100d00c10b07007070030440800d0300985410260400001c6500303503254200d000304015680107011440c1b0201c1d006240240d51108410045d1005000d000440d1801b00407944a4038002000c445052b400141d03a591880f22101e107002e9604400303562000c0d10400c1808040c04d800403800354691106406290b6698042155101601e8880660202c0ba10004000520b041e500c18007201380141d0542e0034003030044810341d003903902c01c0342c0c040301203154040560b80000702000c16504001450604500d00103010b03001a65580c240200140050b840c0c01ca6000280d201d03100c1c1034440301c4803002d02c58407681c1100d8a130003d800180102503014400000042c0142d1000010400805c2140c8200106860384c1d03c414226500080c0715000b95900c0b403040050075840340031800d16829251303030b5558481943c04101800e485070294041501401800140140a40031007150110340b22942440c025410300c9103d13403605480c0f0b034809440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 737417571 1250 737416321 737416343
    0x90b0408010903020c03031617040305160807080c06030f090c031906143c010e070f1701140117130b01090501060e09040819020c040c0801230607 64
    0x140c0005401001e19540300313400392901d8100000515a40313000300542804461031104149001c640400041c00000038400e0055190540b207889140c50691424003c3c05100f400e00402c1100c2441801030202a01150000d0540c07601f418001440500001c0c7c2800d00c001080404511141d100304800b41c65032501030b003555148d10741c400600410780301c01d403003e0301c446003420349030309110700703001c1c98a0f00c1089440100c1484c90f041e06541c00383c01d118071404104103464031008052011007004031500030500c0920200d864686a20001c0c61200d1802c080014084c600c1c444a1800081c0c0c2c1402e410741e60346241071200c89100b9401242c52010012007010a040c0c8601170005081449403081c409034011a034800d05070b40d9584400040794424440d000001d02e00c00203941c1c144c90544d0f40b00350003078059490207040134401ca056000c0000030800b0743c80980d10150102c0c2c0207081601654006a00d58285100720350315054542410130007a103802e410f01d60080b0011416030355100709491895410502e05c0c0d403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 737418821 1250 737417571 737417579
    0x11d030a0231052e0f12020f041406151315080612060c09060403020613090f0903350c04080c060a0e0409020301061a1305010801120b07090b04 63
    0x1042c2545000070b03801400c101000702c07490686500400b0700a1300e10514142e0780448045004c107048490b41c00c4841562010f000c0000d2500c501c030303110030203421010038401e41a600303841044004006007029501a506141030021548410000254070060590b07404900480700080c01c68180714007040004000d041c040301003100b080780f4842c40c00602e81603c4000c07280d20b81e0801c010600c1c01003a08055554030680000c0c04800d04500a000c82a07009400582415160340c0007600c50b802c04040c100e0741107040c0300100310709803c1d07001d102140032142c03c007004000c02588005000302030000001d00705052403e006010404400c0c00781e00c50a4140c9035000b000d0400d000710000603449071123008424801c0c455040e4040c41d1080031100d01e00c180e0b440c0d40d001c0c0034291b002d00001d449040c100380da142d542c038400010000701d01400c0044000301d0040250351014900c00d92003c0c400380746c02281c108440e81e0014000c041c01d00c0c0060500c4d540000c000c0f042c4d07980346001210101e40f40c1e00412031100c00820005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 737420071 1250 737418821 737418859
    0xa0b10080f10030b01091104090c1220040b1804090c080d0f0f0f0903150204030209010e04081b032b140c18031c08090f0309011d030a02 60
    0xd004800c1d03100e20080948400488048080035800041c0240044d14010084000117038000d0080e04803c002640c00d05648541c4101224031000c440000300b41901d4400c0d00600251240039100c0342940c4501c40282c000e034960140302d001f14041e04111450001d55415800d094000340c0500000050040c0b03d003a00c10f2070041040011882800c1040c4a840d1094080d24000c0c0e40361041150182e589007031200441c60111814103411140700140803541901201050f9592114504400040750240c1e41d40e1541c414400c10900582c06000da00b01c0100c188000111050211404134044044a068284102c0c00250441c40360000c080c0902082e00300d00d000c5e005c07480b805550300781704212040229040f0522a114041c1044501200034031040101c501c18064a45681c2d03e1041c000c3e0895035189050280c02051194010f400008911141d040100c441810003000f103203210590080c604102044002a06403414040c0d10a000e101001c08518103440170030018140c20307001040c040009215079441303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 737421321 1250 737420071 737420087
    0x1803100e0d0f020c131806111c0b0a06031d0303010906090e03030405060f10030813150c0f02090c0d1803020c030a0b0f0703110307111b180a0b10 64
    0x5008900a80481410b031800800c00c02d1800d480942034245450840800c08001e2000b00381886d540c1a81c5042100407600754810240341e020504c40c3d1598600113687d0700c4e80a04009024086041d051018844484e111503150804070b403c0c80c140840c44608502c01d03c0e841d8403607001044514480031000164240301600940c0403184410020001c8565050b04144c607448101d802034460340c880c8010030300c0100d000c20615031040040400d0130880786c40c3d41d81c4c1a019804a010b08174141e060130001c1c40445a032000c0003804042d030742000c0e4001041543c1c0c0000b4000d5000010740300d035075000005032040c0302c010200c0b0030395400510204159049141800c42c502a803440c01c0d4014801c80c82c00e2201070400145409291b40c04c00b101072402d030707100c5031340a000c00c42c02021202010b48584050766080c1a0300040c5004850395121024a1712890b5085860110501c07030310035040d242c045404c0d80030b458890209140700482103880d4101d90b40c010101c005031240c002404d8000c11810201000740703500c8113003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 737422571 1250 737421321 737421343
    0x17060a08030a081e0c16020118080a02120f060c18060415090e070e0d060914030403120320090a080601090b090c090603071214010609030302060f010305031803100e 72
    0x402c22180d0081940384070807090480d8240400c4404121290310403030280b8030316506c00c1c81458803945c95580e0050080c00b18160b54402c0c1c000d540401402e404521b81131900d0107034080b9510051a005410104031681c400001d400291407450011f103600c4180201c640c3c0d81e00c1d03034102401203995166116850079020521907104000603410300004180a080c1c0101035015258030740d03818140c5202c4404001001c2e000d2101210400e654114402c0010008480d1031086d040e030801940d241d0b407550401e01348035002c11540d42d040524007910000303000100315218a400150408454541c48110042140d04030311740c200090b10b00c1100c0c00010000210340000c035908100f2b0714036903d541c81d0200038800301d01070b18081d05d60285041c8005103440344520410104d4810040020031201c116004110301043c00381c00c001c0004140e03460900503d501040050f40007110754100036a01e6140da19202c2d201d01038216078010b10214901c1c0c203926a41c040051080c00400700000700310020000415907034900c50028 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 737423821 1250 737422571 737422591
    0xc08070e0a030803070e19060903030f05130b2b0608010c23090607060507050712020c03301b070e010311060d0f050f010e1617060a08030a08 62
    0x3848500508100000104032540001040d055031503100702981c41d620308019190f00000c010504152200040890000a023001d4445d424450308504004040328594403a610912100308900e034194400141c2c55030880782038000282e2956080604010701280c06000340b0118219103030300000340b60303441c0c4c84442119100c00017040a24404e60b000d680075000d00300368040b01c01540000c0c0818095090042c540328400810041c94143d040e030310441251800d5070f11400003640031a1071404c02c1020070001205a2041c002090424050340c002079641c0500061080710180240c90002486004030b410300c1e195100b81d00c1642c0310300b100403242a201c041c010410505104000c0002040900648180e05980c1c1101c00318880030000003d004180d03100c4070201441550700c03450804c1c17000306032084a004490008561545500d020042c180c2e030786000c0e0442540c1c10002c0720070700c0d001e500544283c0910140a00000b61135071241d001400d40b642c80c2e40214400c5c000001c02e5524550b100d00854801c8502c05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 737425071 1250 737423821 737423837
    0xf03100e070c08040510020a020d290105030307020d03111f0f0b0904061a060304060e010f0e0d110109081b060c03060a051924110c03070e04080705010c0807 69
    0xe0300b1141408454006441072400b04002d10560604400c2c0410401050045030a03862244e40404d01d08070410f041a5680c441c802c074000118145110800032103a00601141119410040060749a125841c07000384035083c84e88000342054056640c5201c50115441070f030320f40007808080c0c231041006442801c0c05d20740c40c0103040e10030101d052060782846c5401030560403d80d99141d036003400512510300900d0400310304040c44520f960320320740194883c40c451800406e400c0400c3c4a128252120848007090003400c10000e181e07194800070303010243ca8a01d03e00b0310030541c031003501c082c01803a03058170141800c140040c0e91400e01900780391401f60040490110340031565403844210041c001510141d40c000d036281001c1260340f8104c40100401c0090b1408036000035a0742140d40211714030040c4c940c0224081c000d0686010b904141a805411600c1e400b52181c8420400041d480b4a52030082054491b03044003c20706005007a002e4610712a07014008125050301390b60702134920310044a21000081c089 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 737426321 1250 737425071 737425081
    0x50703030609020a0e09061206040201050a03060b04151706010f1b0203030d0e06090c0a09050c0c010c030c030b0402030103021f11030a1713020d140102220509100b040510050f03100e 80
    0xa0311223200f1a100040140440d519a80e00450b01a8016214502055211680810003040802c0200000c1000c44404414600806405031550010030f4100c80b40740100c42c2040016608820729900c00c004610b00410100c01081d442d102c3c685503480080d4061001149070750416050f9840349003107401400803200c980d035030710300300a03994404003800b6604451100c0302048100c1080e0802a00a207600391020300b0401d0106040b030031140d440980300c0000e03441c0c580712145107405d84512000c02c83d09450941c619030441c0c000c16092607591300010ba0f0309440e0f5420100c020300c01c041c0281c01801400a91343d40d0340264100034400116803107010442041c1e140400d03407882c0001640c03a80d1603406809002e803541e050312144d01401c044a85509195000c102280803030b208204c0d400480204140305030b090f01d04200a00542d40801480281d040310504428030000600106980482e08122001e00018241e1101182d150003201051250b8801c04020b000c50250a0001c00f404d0341c800e910a100240e4175 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 737427571 1250 737426321 737426329
    0xd0e04022505101b0e041a09040b01061806050f070204090f0807050c060403030813020f1504090e0109170702150f2d0403060b0d050304030308010e011a0307050703030609020a0e0906 80
    0x20304d208001c0413901c140c40c80c030110304090304039140ea82c6482e085850f6000c102c1c00802d4404030111411a5080316100c0140a80c5400c80c0e0704181d40c6195941040e2103d0800902601c14440e21040850b00500451010708541e04d41c1c2019107050381c441c0c013902c881c0c0090b203130100340ba80003003504484601901c0308912040c2400d00648003143d0b01591040341a0b120762004c040c802d000c01405980140b41c028044259031540c50018840c410b22040035651185428060401c07103045a0580b40a41d050085520208000140b44a01000000c482d2503803400a231000903010017029201641013540481c003c5501c4000c1c1015283c03032891190052030b104100996001a001600c02c0e00302200010b11060021a45642c402040b40101138400750a0b0f104685480b855901303d079008400007619000181b106c1c8007410f14090042503095000041540c1140101c2c5181c040200000c04004004c101001070501c039800060003000121702c02c6585681101c0000c12921000d82801e001f002c0c60000305000f810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 737428821 1250 737427571 737427611
    0xf0403140a1a0606070f140303090a05010b0a0501050a0f1e0905180c03151203220e090d030f2301051011070e1f061805030d0e0402250510 61
    0x3d002020711746822007640d00e1030304050340b0000580d9403c0668110a406210400007140500f9000008040c401c507113151460075220030401c82070161034060410409642c1210980341d40c403a05051542903492080000c603000c1d1907600300f002400454400084450f41c02c80f030f42e20305950090301c0b004e042d2100f01021040005042c0c0700300340d01420800010381100f02c2070050b0503000350002e06140c02c980ca407501d6036155421541040401603081222000900101e510010040c8501c07030741d440d401d141416003d03840b10038502102d42415110084a9060031143e4850744480b50003c010001c02c000d241e85101488030309001f8240a61188004c0301200f0380661440c03013800f0b11041c000c203000380c01c00c1d50b4540a00341c0907001442400e80d410342c0148488481c03070003c0150400790307901080c03407030501c1041c1070011036a80302600a8121510a400c1d241d400f10345091220029240541d880c0050941c503100c4484054100b0100b1584a4010702041800300d503070f00e4144503a410501900884001d8942401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 737430071 1250 737428821 737428831
    0x6090602010b0f040f06030f08090306060a15030c0306030203100f0e010603020a0b0d1404050a0b0c0702090402042a0207080d050c07060807030902120c090705030115050f0403140a1a 80
    0x2114002070f6211841c243c2c100b07003550181e400c400f246403a540c1d9107000e55035031070042c00c60b6800340108800b200380c1420468664405c20480303071a40007a00e8078510451103030212100408160303d501c0b40d070840d00d00a4000800860340a070840e011a024031007014024507090307030301015050070b1441c034900d00700c814085d0405994009090750480e9140c841a540b065001385c5d03084038099210744600340c04c8004170705100d11460188000d000044004d05d01028000c0004101c12244e040912028015071104441c1c603600c280d041e540010310802041c16135140c010b100c2c003c018042c1840f8841a0b40580c0440c129045a0445080f00d01d41e03a2200c4056542d0f014000403a403241c0c0c0b044a00300703c00da2151000d290440854200015050042d4002c2031030354841c5000400b45038803149402040d424a041d000e0741c0003141d4580181154101f40b40780050f9104040c40c40208403001c62050a05041c0404640003594041e600c0340d25104028401c5d41c1340c3c90881003c0e2140100800c550240103d240744c0c0074451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 737431321 1250 737430071 737430079
    0xa0b07170d09150c090b07061b020d020607020615040f0b060c0706020708061612180b041e05071202030f060727080601180b0a030506011a09060a270f06090602010b 72
    0x9203042407006d901a0b00229829900c01342c0341e424525a10044244070550303981e050f4050200d07480c4082d0041d1402c0d0f0080c083c8001c552040b42088528142e0007803508030b113507044801081c0e981031481031038050450341c00041e07840f80002408002c00303070000a0754011100c00b42c003035400845d41c07182e0890f200c1e0300450341480e81c030450b646542c0c0c1d030501c01c10010b40190b11751540020a0901d00359011540318507503408503074401d51079042c0414008003201a1013540700c017030300801500040c0d54030780e91a81814450081103110300000750045680c240030b0b041e4a17504440417140c0030320301100010000303c2c102e0600902100305142006a0310716111015082c1d9600f20020081d0b40d2a04d5032042c2075008a14400029955030b004402e12561652009001103000e800103124950419138200c0d50343e0400d00406a056800308202025500d894041d103403059440d017028001503e100d10300c420300624404e049950018203104c0400e918a0282d80740f0152922581c481041a881d080117034200c0740b42102150b84 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 737432571 1250 737431321 737431337
    0x60e031603050c010f14040902071a0405070314010f020c07030b18030405010e01050403080d05090d051606090309050a030f110604051f090b040e1b090a0b07170d09150c 74
    0x882d409a000b40e60021744174500030b00e0b0014403001c0e003600b03501300e6009200c0043e00084c801c020302409030403660902440e220400394509080c2d40d043d139200c040c4c0c8002008ca0401c40301c0c403000140c1c00c0d884000000c0017428255959803006812540320041e038001180c480d10f110340030407407900746060142c801040e1f40005610b0035062000548180c044181420b0401c0342c200804400940e00b00007400c0310500d445004103c600300b011016007060055001a0100401407114208d00c1094048500302160806400100700d4160704080f10407000315081150401030060f0300004014507114030340741041c001c40e504513182c1203a404110b000e00c43c9106266120145c9104000c2c841d80300000c4e482c105100e410710740c7c01150f0b9850b114030180c02c0341d40f20f0042c1d10089020403030324000c6100700c00d818144000c031070b03854407944400081c641c0c1041d00440342001d1001c00c84004200c6d41d5103907540c1c504540041c0a4071a101208000041c000040b0200c81e500411b0210007150015406100d5603282030b5212052 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 737433821 1250 737432571 737432593
    0xb1c15031a060d20013b040207060e06010e0606030411062b15080d020312130203120d0b090903040504090303061e080f0c030705041a0a060e03160305 66
    0x1900710140c1607561040540d50034200244142d120110311602a03011603a1090900d00050000d02c502015100032900c0c00180c400e0307420500d401c9542d80700a004090341c5e06c400c0c88011400078082d101005115510b0803202080311240042c02c54120380c007002079031285907200420b000c035030300083d01d0080081801d441e8045c0340e85480d10182c810b5021a20308200c03103d15110700154054500503883d904159a81d80d0400001c42e00c01c40d180141410070003c003503044a6100081d500e20510000c3d43d04d40807004041441c5403540c01d80b0160254000741102c044800000356485140c1c0300d00308a40300030340b074134904011504120003c00d2040210402850030329140c007003400098144010100c00301560f815002c40e40b80211041c2882c1882550110050b0038181300d4540e103040040d40321080303a60b0081d2a280c00c1554002002d005031101a60080f07001c0c030811000c00c8000750f114064545c0a5020f09000c141c040d441082c009407118110101e41c142448000988080800b501001d00355070081c0b25184 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 737435071 1250 737433821 737433863
    0x605190216060206250e0d0f060f020c010c020303090d030b010212040306060608060f1f0509040906020307020c030a171e1204020a1208160c030b040b061f05030414070b1c1503 77
    0x4200f80908c1c0950001d011554079602207881001c1604101030307021490013004038092240307034a4108140025032950610008031f56032071170720610440801d0340350403465070300ba4400d00074246445541000360362543d880c0d25024024008078010702c0700180a107000694030346802071288102c4a80076000c2088083c4040019070182c01c0b00603040240103041100c00c078161600d00c0340050180c000c450050702d070305203000024202144000d40701e200f42d000060701804201824140c20b409600c214040f5594204040d0400c120303403103120141080d40c1c2c041100720000f000441280d1107103100311403407421161519881040b090455801510721001408a40c0300000c070184500d0415020f8601e010b50355540e66600494070004030707022584e0585040a008030713030800402c4035904540e60b00103c408203c081e2002062408014000307400100300080008052006203c08030207014803d06c006e42d66001e04481d0b806403925a85103d0700145021008140115607540e80c030705980d4002c00340301d0b181c0c015180b90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 737436321 1250 737435071 737435089
    0x5120703050a12240e06040b130b0414090d0e0105030c0d021c0203091b0a0b07110a080f070302120303061c0c150c06050604060605190216060206250e 66
    0x1008055407900d0303040e280744c55809026a0141d100046070400c0741080c0c840c0c000050b000d0000c500036810401d04918640d0b9040140c141c5400c2e081c4002045640c03040018054501080003101c4080c6550a10292034004141c10074079078250b45030784040222810045030355200490340500403c10900191011318150b8000f4800340326001c00440184240d0042d0030126402907032901056030005c0402c1d1051034a0f803014200007501150707005110340c40d204c4003081e503100304400201a6504041103000a40d030705a030764401341140804036984491400925641c5940710b000503840b0b0060710312081120040042100e1090340c0240030081000c01e00450240d40c4107051030100c0d0400302402d404030303c0800100b1005000512580c40300c03000c00e42da09100040700c0c8040c0900b8041c60401d00706100e0709070170104552070448610f0300b051909054001c03c0382031000d0705130303e410310b14501080000c0b07450380010064021a52400c00c03520185a0101c408054102c003070780c01c008125140c0f0703031808504d801d01507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 737437571 1250 737436321 737436347
    0x80c1510050d1b09021306030c090302090a1e06060e030a050c01080405030c0f0703060c1e08090a0203060903120718051905030f0f01060f03081c02090607060905120703050a 76
    0x40700343d0380c140001c1c1440c002c08451300000b06003903010a100005d01d4140c10718034010901e81c05c0400c54800d01c44d8000700004410300002c2d01504000c40031076040d061300d6010100340303000d610a040083e0600f102c400050401881280009500207034554503a241c007050403d41c00b68803200520311310342da4000544525000400c15641d500051001249507082440b98030182d016200c0540311440c218540002220100001c04003003241458805c1e403000055420454201002c4c20808038035543c0565030f0b80f4000c2e01000080d014001e0b407050005144000001d0543d541c03410380c00c2038035139540c800700311011501c000e0240301c1d400c00c5040c1000603040203200a10741e002c5004940b041d00c0d4480000c6403608a4144820145a000c03d2004207440c00a2040c10094424580c043e00340b1403445c6c581740d18070702075030800081080c040c24240c4100500b5034101e0341d01c40c03c0034000c0c64480040d4140070703008010900f03090320540280000d6103520034140b41120f980c16450384038035041c414003090071a030031404010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 737438821 1250 737437571 737437583
    0x90c0f020c0f1c080c03130609090c020607080606040f091409030c100c030b121005010e070e150c060103031211090904030807020a0203032b020705071e12080c1510050d 74
    0x111111702c00c4824802045002c500d02c643d0740300c0071702d00311001300902516404220140d1800654a580c103a010906541015580c54044819280c65000501c0e901c1035610062803243d60100004181c1c455400c4800807981c40c03607402e441c03940c070032840ba9120703c25500b4070318450b004404c50030807400c8940c2c0b107165510814a03000851210b940e02043e4244291021000759501401ca10b0f81001c4542c0102409030184424488040c1804000034120f150507906041c829910a8000c0003054500f9095469590780b0300100c1b0f4003540e590401912000c00d184642c0301d19802c0402031614545a1700443d01960000b50412082d50360342d45044800500107404102107006544200740036a50420181445860340341d40302940c44681502e202e002c8a441e01d00703020f003a0050200b40c0203d80045055004c66002000b00100110000b880503c03001c21904540c1d11030700003284074014000301c18040c0440d078413030380200e81403401401e03c2c1040c89142110450062011041c00303010b9070400000011009100300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 737440071 1250 737438821 737438827
    0xe121602130f0f050a0e070501020613050a050601121a040f06111c0b190b030601050a23040306050f040b0a0c03020c1b0a0b27010504090c0f020c0f1c08 67
    0xd500e0307800743d40440d103040c003410352907209226240d503070351086516070043c2e40001c1014610b4030001039102e44004010600d008103015140d01842801e000c50900b080d440820b840003580c540003415070070f2510800c1a01d4060072850004401c0d0b041100c601d005940041d003408501c801030f40e80c880035101c0003070700b040000d4050144602400039800c0c40c0e060803050720000708181010008ac0407411800c0e03010011000d00c0c41030304015682000c0c045a40204081c60310075940c07a441d04050700c024154000390840c000c0c0c0c00310305400880103907001d0030546c3e10650007072003180c48040c0b000c42c400c60b050720003420f040d03222008030310810800e500c171214040d01c80c1400350804180088090a008030401c10450424072002c5101e00c03403802190000103080200941d030300703007109205100174500c4899071000121a0420100540d82c0c01281554001e0545000030301114508482c0103060703050980c4054058850303e0b009200310315041c0a02440e041d400740015240c0846008504d1080002c40b0098651850070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 737441321 1250 737440071 737440091
    0xf040e0c0d0c170a09150f0b0d080301060f030b09071116140a05031225080d090506010509060607020105090a050603101518030f15020a02010e12160213 67
    0xe40219030601a02c2d496014501019046001005100428403180b01e031070b1010740f000168840034003410700c2d5040440010b00d15201301d880707002040852065944419410341000030049900002c0d81a180281d840940f0140a00320035010780b0b1910006036401013030712000444080c81607030414030800188044610012407000d1008040c04941c2000d00410312400c480c5996007010170000b0020507043d402007510424481d02e9001c0c50150b0f60180d1500f0400f4605028002801c0200440054000c91480e5446014041050062990300400c40c1d40b400b0312000041c0034640520302d18071442c000782c1000d150030101c1c0d00440d8594801000c041e80040502004a000e440d070001039803158410020181c00304c0e0030310705802d2209040341000000c11031000f4081d804480d4080d607910443c3d0748640038181071106440c00c0641da817600c07004909400d2000c6140c4030559415040f00c4c0d4000040300c00c0d201c8203440140802a40c0c0b00d4044811003a104201c00c4400608080ac0318603020038020310002105050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 737442571 1250 737441321 737441347
    0x1509200a0b0a0e01030b030c03060c07080c1b01020d08040b0a09060204090203040c0503060a02090105120601050c01050901020a0e030f150601300b0402121b0708041205060c0f040e0c 80
    0x44060b80300140e40300709442215600340c03083c00d01c800000c400038100303210228002581d949000340002403d5002085034000c0000250030381d074080c49020141c1d480900c0603240d002c00b0308203840c0c0b45401440342d0000c8550890051240a00454002425000c0e991f60300410b94090f040030041114120350030000001c2004252018500032031281078800e039500d14003030406240c014054000c451245c0b040100f480b1981e040812142d48000700d40322101d1079030f500d10051700d0703501501007461465400c080800c00c40080650003861030050a4030f400c000310750290141980d80c0741c031480550490f840b6586000101d684d801000d03a0040c014541000d5007180d0394000341034803400540e001903100880ea003248400b80c640c050f080341900305440071418800340d034009990500c4c0250409016003201c405500c648045081181c80950708000c80c1ea507141c0d036903000000c04001114041d202c0d401004045a8110042000c860110312404445c90070103062450404901c800a07002c40440041007210440d1501d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 737443821 1250 737442571 737442577
    0x2060901020c1807180e010306150e0414010c0f080a050919050d02010515010f0f0201150e1014030a060b030c10080a05060102032104060608060c03041509200a0b 71
    0x1240482032103c0703050032a005005080d440d5000c02041100c02401d1000002e40c000c13240c11aa00b203440421010408500e80260340e10603081010400100300401040c80380e1700031066004441c5100070402001e008d00c0840710a02242d1030840010310000110b10f80c62801c0d0400742e007084205003070300c4501100b070398000c00900382488120385a40003120002c0d6504d0302807054552120400d13504042441c0e0207000200740c05030040448080c040450311020400e4070035070103900d10a10390010056a203848812102d5a030a0032900788041054202010603c5640782203070501000001e001003001956560b11a0003414044900542601c81d0118901003992018201c140040c0d2640b250002410252810f1003070300c2d07004100b44e065610402a5403012450956580b409880020000c4055282c03458210041c051303550007030000d1303c1154140070007410540000c2d801188106480d00c1e0f410030820700102643e90f80b02d4054409441180c29044c0e261411418120400c030080c24030074480e403100301c0c120342030b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 737445071 1250 737443821 737443849
    0x50f12010b0619170c0d050717090c04181e24050a05090705090c0c0106091407021e030301180e01050906060310090c06110703080301031a150a0302060901020c 70
    0x192850715802c1a031034204c861110f03892000c0040780700a103000402c45900f0701c80d0f0314010000ba81e4450000c0c5140c0d108d44070302105199103d90459003424a0b626550f80c82c405484101d20991410401414100d2101d95036034595a010540ca03020295000320a070038003c6a0400b5034068240000031b090100c0b00090803c1240c4403140e00080ea0304010142400b1108020459072320340d445403100703003e01d81e5414291070780312030940a516a945c000c042d0440c05016103501000d4158140314580302640c1341b1001540c8104a154200c50b09100c100c20a18601c10070105042e410b41c0003000144901c1e0300b10800c03c1309200e40301d0004901c00c24190714580c215442190765448541001042c807405140030b110710707191030000c2c48040c48590250780383d4506401c0c9a10a0070300f40300f41080840a064410301ca002d00540d0000c0c0b00035181c1d0f03907a00b084860006005800c1d0741403403010f4001071090405504000c000ea0000d0881a00c0500b50750074410990b118500b002d056210342c1d2221481d076070740c00b00600c00176 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 737446321 1250 737445071 737445097
    0x10050408060406091103060405060c0919080703050f2b140d060306050c071e0c0510050903010b0103060b0a032004030323250f150b19050f12010b06 65
    0x80c031a0510100300c4000c0c0017010f00c00c3d0801c85c280000700e1400620300d074200300e4029419913250110000a42c03070810102c1010041814488000381421003c00d4030002c490092080d10210440c030b900c01910fa410b07031284a22041c015403d0500781140360f07803241c009003e860400c2c00210841d010715010341e4106e94025046213886070b00500801c8950f000303031a084000d006c451420202e01c0c0d0f03585d04404500f881c10031800d115100501c002c1c000102c901d0310042038041e00f0700441a0b00c2140003440c6902c0303413080500a600384075050b02d440d4400d103c2e142c104e5821000090400840f41c800b240505070342c440d0221034691610404912400c200001c0c00154031130345500014025030329152982c0d0308030040310810014180211202120766908494003090450b510040d01c02c40741c030b4140000c550340c0070003800494001c0420000340a0075401540d4240d4102d4848403e04903200b2004901d1400380a00d81c0c2042c0c40002100a906100c2898200f4080740f1002043c1551084041501900010504014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 737447571 1250 737446321 737446331
    0x70f021009050c100503010506041404090209160834121a15090307290711030609010507230403020d08040501120902030a03051602090106020303011715040210050408060406 76
    0x320b4513103525008103068880c14811309541c54000040c915002e1032042e404004080c8410b10016a01ca600c0003c60b1070b4002c0504210341072a48009030090350b00c0b020070f004910000301080c14403c050f150001da250740d500d039040c5981c035160000040d00a00740c0c20b400501017903481c504c400071401d005550943c000c0d1030755001d105018070100108212a2804a010740c02d0400c5059210344020681d0000da44500a4010b11f024200001d04035400d20040c10103500d08000c52802c0c100103160601d68111343d002c50031902c1d5a1a1034031014201c490980740440882c2440c0301192440310b0084401c0e84e09444004403a04143c1d481d000300d843c000c04c00c04200c07045040043d080c0591341e080382c14004440382e1204100000201540440d0362590341250240a125020681d41004030706c0ea0070303110b091a4040c00c20b02c0e2039656040042d40d20b800a004000e050413901010140c45480028000d138040320b442940d0301151544c1d021702c1504010440c4985c01c0003010003003c00c10200402c00b150055200350b80c0003072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 737448821 1250 737447571 737447593
    0x60c0f0d020105091605060a0c022409010e031903031503020a080d03050907061b0c230f04020c0a080904060305190302100e0c010806040b1804050c09010b03070f02100905 75
    0x105007840c4100845c1c09450a060511442e11400180d4240c48128145075a44040c6400015000d40103803071403111000003130344240d80f440c26120140850711400c0e01c80c003112007190300030161035000101c10050600c40068075880480d00c26004000c00b52486020b0301c401c15120b4000c81e1124610b500600e105600503440100c0181c0d141c420b040d4004040383c003601503a401c002000384860300b1000d1400ca5484444461070500076192207103001031801c208001e000e001104500103d501c042e030506840345007100806c400e01d00b001e000b180e401e1180c05018001d041c0c4903661f5006560802191583c0183d42d5001c0800046e6040080d00303400500c0c08840000c121f22450002e10b440d61002a0710038190074070340800311406002031089298042420618215076569000c075008101301081d00d81d100c043e001c0540c5014405034000c3d0f0149000c1d1050b11000707100b010500c00900302c00c0c428003116030000c02c001145c40e44100700104403208544191a9041180300002080d2002d01100303494076000900d10350 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 737450071 1250 737448821 737448823
    0x30e0f0109050d020307020a0e07120f090507090b0a0b0d0213031a0a14010e070e0901061d060c0a20030105010b0409050a1b03110f070b04020901060801080c060c0f0d02010509 77
    0x1000d000743d9803009502e0309110798003145200031300d84160301a50140302e01165085000e61070586510320408400c00103011503d1b41c9001074900e0020641d4940240365011541070f000380205008200007404480c202c0f460048080c165a06c4040c2c55084903a01f40014440400391100010040d4051121500055220300b4460100c4c3e4002e00340369011440c011a02e081100442e1200e8110703001d20078554415580d1504c1030350750401c00b5480c5940b2120080010400070b0700702e514900502652403940c1c03240a001030038003041b8804c14011800c030781d10443c8000000307400c684031510484000c034038142c40400650702103420f68100ba0426450154041400d10842609215031684600420418040341c4091450100200b4034407009204050701e484408003000740c00400c84071102e907040c0041d641c4a07410704001030030f020103940403032240ca4603000020300f10344504030f6981a1f07501c2c03070041c0c2442d08020041000c40d0380019406007180c007600700e2010030090f0610100600b0760181d000418649031645102e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 737451321 1250 737450071 737450083
    0x114030907150309020108071b0515012d050d231005090d0e1009030c150201060807150c0c030206120703060504060602061305070f032d021e01030e0f010905 69
    0x2c004040c50180000d0150381e110514035001180c0d130401a0030640022014501403001020191a80c8900302c800011110329804050403141310344010340700d24200c00341034001406a400d08603818091814140010305c0c143c0c000c00c401c80e214103404281f510b884507900004600400a001c0a80c2000413400e40000c000c0c05595030051b01ea03130140000c0c0c0c0b0101c5d4042c10400f0a000f080d4010540010001d030714601030070129010315001401084203030b60720041d20b2131250200b000400194208040050014400141d80c0180c0b1102d456540340d0003015681100d01c5000c405094420300740892000026840e02e1004014008428900c0c3c8020300d080303100a819a00d10b940980d0140d0300d45082001101e9000c240f01d604005881c040000a01d0941402c1d2b00d840b44d190000101c120012a000040100a901a40140490000c180d01003080f140524001410071036003c0d41010207600d24699800709030808a10080050400040031400604210302e00300e29415075000f142c8d558031401007840010414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 737452571 1250 737451321 737451359
    0x120c01140103050a0b0406020f0711150403080418020f210105031b04050c0904180b09010b0f0f280f08070305151b0a0503180c0114090114030907 64
    0x4a00d03549565206039844092000c054040041c41d030100b420407185d034044909030802d00f01c0d01c54a4611900707211078605400d1108502c12550901040c0d41d005a0303005a500303d030341101001e030600c0c2ca00740002c0c1c2034000c4005440b19480e401c01001c8200a10702001d0504034101114070000e4580c25500300400c1481070704500d1181d88402c1440142c0024083d5607464144284d074040383c16281c09250500c2e038011034507650707032241c01c02e00804c2042080c4900c074001356004614544050321501017040c201d07a40349041c15001818003d5101d00c0e4241002803014514010702000c001c00c44e1134095518180f0102d271103002004501c4c50801c5203546641003240a03090407400381407282e10f960b889030b82da941c402003400d400c102d15000054901e8110205008841c0080034400d03034565416a00504aa1003240d01c10100100821100441d5100096826039034a04cc1c40d1643c0021900f0528002c64126030309290400c03043c00781c1036041da00c000c0e0103035008910103802815001d09000c1d2203400d404416074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 737453821 1250 737452571 737452601
    0x30105130b100c0c030b0c0c12040e151f050c12120a05041407080d08070809060106140c07030c031101021605060d0e031603030c050c0a080901020c03120c01 69
    0x8403a500d1035881c0c192a4031542c107607007002d01e1990241d207000c1d03c503c4080d0f4006030040207813104202002c0002c1c0000d10b00050040107032803800c84400080e103001e0085000b060203821944c000124000e0018103841002c01c1c0c001e180162580c0003100e036580311040d01c210800050030119821390300c2d42c1c0401410f8800040403a11a00b001d000f2480710308400c900400840b00c0544510214092212a454007510700100d242a03408540e01c072041c00e230340d550000025000140311000001d6400348a08201030081c00b0080180c10180d20302002203407000d1410709070303462074181004a20600f030b07010040c1c080198412080c0503c0315180d030403c440350120b00035000d815500400714584030307080f0000b603400c1902c10890300b0310b0321001898001401081c03010500e0005100020f0300d48464000d154400b603100c5d20070b0b034042c422403a00700001c407200c0c010f00c02c4810b06a44014401e4000412444c0984a2014103104407003004100d000041c3c44c18603010302186042c0c20015621000c54002c0c00359a03100303c2550 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 737455071 1250 737453821 737453831
    0x5160501020d2f160f05090f06011101060807030b01050307060e031c0c080a05070c140f040207061b0c0501060905040213050406141e0a11090108090c0d0803010513 72
    0x15002030400c80781d460095141c00e014082c0610404450030707000f50b004000000300c031a002010711403d82404158000e6641480051100045910300104000d200300082d01200c10251189070064070795401d059014030700b95407034803408181401c04002202c0114002c18000d03141e03501d0705080c10705208868110300e040126a1a003100a030b10000390040c21240d117064258075820305c880c0100d03500350118900403c3e481c0d00013107001c1c0c0954880044e14800b401594812111546c4040280840c141c81c0c100d550005c2040030721007114646a801782050303a01803c03001c242105640807005a00003000400c0380441e89290102d028070009124460150058503820000e078101030300003030040d14510f07008036401629240020308110964001c01c0d00c42e802c01c03102103440d042400404141040700d0b91480b20107040b5a00051008140d40901c0501ea500398900900e00319440004495580c001082c032030282c8a00362030305d14282c07a00c0210040b0a03015542d104c2e120350405081102d1a03d400705160441401c01c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 737456321 1250 737455071 737455093
    0x13110301020724110d050109180c0918021c051501120213020d0c033305040b0a030506040602071703090721080c070905060111060103060c1106040516050102 69
    0x408840741070004816100340d2086580074004025110790703607414091480c017261106040300290005030507120340755020f0003d001d8800003075108030710303c44029000c00502001084a0352040d4403d490b134800100c20b1070b02c81001d41c0c000c58200c2181c20644080760000d00843c2040c0242400149002c00c5000700d0fa543ea545000c0f40c410300300c0721028010748250b10044001000c2e03440c2c0d5040341d1000052103022300ca4030741205006001807862a8030001c0d0703581414004d03005907101c6264446520800032141070900d003410188001000c3c085021354111a1981300840424401c00c01a440b95104a1025a0700d00c032628050038610061108044054824000c3c8810030101142e5541541d800c454103c4480040d034543c100c9800c042c180180c400c203000180091313201c2e0042119020b840da038003014011604e400c001107415048203444c0310b1660300644014000500181c05c90001e0b03d21600c1d09581c3c02e802d0001e01801d0071320035907040307a442e809103034180300007990301900e10000c2000b40082c148280003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 737457571 1250 737456321 737456333
    0x8240705071410140714030a0e010e060f090c09013818010516020d170c070e070203040f03080d021b0307021e0a06081305031209010b030a03050703030203060a0e131103010207 77
    0x481911b0b2007078010210004001c2245588061149122580280141d1060010782c0761a5101511051078000400000400c402c40020711300c10442005800b20700e032a8a40712820080d240d0071a061160070f8a980303244d0040343c81100d99400002c400242596552501c014000c02081180a2460600c6001d01c280d0b0318009140c1940c0ca030440d01658604112907d03440c0c100302c08621222030701d80410001c1004c1c24000000143d01041e1801c0000800e56521060740a0781da80c0500d200b8041c14500100081c000161203c014000c0000b000034050b04000100c50201c40c280881224002140d0000c01d40707109502c0c1075421075403518070007001c2c4500070468101040c4c800724907000310810701c103030381c00803d141c0c041102c8228030890304582501c0e11190004015003000c10b0a403071303044056080881447c0e4600d0701003074001c003190307041c0c44091802c1560750707095011390001000e1940c004044140003c0040450085501c11208102101c05409403883c0500c050b031540380c0418000d81c070601c24040042d032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 737458821 1250 737457571 737457587
    0x4061202010e0a090606110606120604030c0302100c030b0f0405100504020c210a020f0d050a0807110f012403080909330a082407050714101407 63
    0xd028607000c0014000c1e00302007014842c00f42d0024804600e02000043c0c1a5405060101d100c0300071000c0e1502911640200300405e16030200741c0d12983c0040300850300180c0102520a00507101c2c0c01500ca180f00c01c6420317801180c88109461022a4444422078880c0c40d04440255000008075007c002e207013400e0024603515001e50152a001e681d00060704040400c01b088410800d0521084400000300c2d1030901001f243c110341c4d00c2c80c01601c00da035010384000e1b41c046071800040103542e4450307041c03501b502d1040b2501d031406003100d424000c200301c500a81d02428059a141c00f032403e0008107080101b034100d135481202c00088244108842c08080c400030310b05104440c2049801c540008140d15411030448202c1f43d00c0140005144050702c02134620781c2d1204250301d1100c411a40345100c42d984203503054549041c560508078014941d20036225070140380c0c01c5c080e00a1b01b5407422a01300031080c2d59441e0b1042012481621315402103c03446000c0582e40039104c0e00d50598030980107542000c1d000600801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 737460071 1250 737458821 737458823
    0x2c04052d0c01050a12020711040509060108150a06150309111e130b091501090510080a0504170c0f19050706050a120504031d0616020d170a021605040612 67
    0x420700240c4c0000e8a07120b001d22801001d41d0100031555407100740390080b00d0440300007100e4003035403d000c00200310344004500181220141005800702e00e80d000503012026070010000c41155a0320710006c50300d0390f0641c6031a0962100c5072030001c1c56090750304142c40166074003000c144c4281c00d429855a50340003109102020510f05035108281c4203001600c910280c000340070204d03080f400c00801c000c604ac100180310310910300d080c0c071402096926001403000100048110402080b03130354000c221010789592045620034025100805c5180311023400c0310b1140d01600e02903503d64800107031645000014002c03000e00440d55401124180361341d07a40e0a40b15127451203a201405004241110300601422a0041440d00044108050b16051030b0141c814082c4080e400c00c402c04040c01e490031401c001007262909250182021074410096080002c1440300308402c542091032007080c42c1e03801d03a1300d501411030b01da0240c001c1c1c5844141c1500c21402c0115541c8041e201c2c03400c0c000108858094140c0e000009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 737461321 1250 737460071 737460077
    0x1060f030203150d12030e0109031b0203010f02180a0b040f0605161203020a030f0905060112030509210609070e1918030f0e0402040b042c04052d0c01 66
    0x42e07551103030402c02c503540b200780141d0840c4d525103200381005024015591108401d40b070070000261004603103402c0703500018008001c01c003501c030424010840d10003101103062005001140307100070740001000b6600259100c03450000601e20b15403961408140120150030b41800c0309003420301c1c241c04000c2403a0030788643c8044c0240015080102c140115501100341e4000c500d00c003245064101c000c00a510650554000a180c43c0d00c1e1070001000f4000d500300d0542010040c0304590a0615407123403502c1203601201888800c010001c0b090f11391081001c0c6561340d0300c0303181c051403918113000ca04200d001450000903410850060145100800c1220f400400000c00d100c0300314400001507004285009505070342451450000c010568003c1c5040500d050340e503206407101d00303241705200036801a40500c0400c1001404144411203481040700d58820754500301322501e041c809001408980f068805443c1e0344c01014081c908005030344040c20141c0902d20540c40c404000b001d5482d11005030600b60740c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 737462571 1250 737461321 737461327
    0xc0509030d03050405280b13020a09020c150108010c020712080403030c0c08030d0e0d0509030a0f020411030a0209150a021506040e0706030516050702010903111906052101060f0302 79
    0x34000104031120803d1403440e8200c8890990b40c0b81c4007a0411111007c07078620008100060b620181c2804041c056540030b402641e0090602c812140a0341000c03542280070700c10018185543c0b07400032641c900074005400000751241200030028180203940e080030445081782e941300b030002803d440880b0100c81d00351501031951103003440c045071803c0b00741c1e00c0030b90584004100c80f000403410b64061b8840007102c83c1100d142080c060816220b41c06001c580300c4e4184c210150010204200036004681c1d01d100600c0010600802103d40c90613402c181c9150f00b40075804941040182040c014104100c010403081da030811040a800a42d81d1348100d403143c001402000200d00c480d180c2c0c1c0c0204200040c03003c02d03a104152907030740c01001810704958801320125441049850140100b046424070341d01a540c503000303c2c4c21503d03a841d0b204440440180c200d4400c04041582405200e8410003801c11907490680c0d4010702d00410080302c41d0b04040c080c007010200010401a5040085403031000001d00300903031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 737463821 1250 737462571 737462573
    0x308180d110606041e020d0b0907020d0306080f0a0305220e0a060b090607142a0f0d032a0503030403080402090a2705071706012c07140d110c010c0509030d030504 71
    0x70240c00c0c0500c8168102742e0340e031f007880701c4c0640214143e40c414015035030030402d031036440807000c2d07444114203940d01d000e070040380344100801c0c03052005024992081c0801c1130040c40c201f00c61001c03103160b070340094a1419000c0c00d0010582e0305000d944007c020740d2071414101003466000a15510402070000c0c401002800500e010704014009101c24101650101410041a4078043c0f4040201001c4e2031040e500603190038040d00e003134000e0503006034256441c03101d003194601c21000c1c01044180c01134440d0a1188038480050010802107116620030b41d61040039007041e2040c400841350140560003d1401d242094801220b03590b0f00c2c02c0c100042c1c1448070404a03035030a1076801e050060b0001c01f1860000c40e207a0511402c0042c11a049401c0710402198028010800d9503000c0b084440140100074002c0124900900c681b0000e41d1104040000314605420008280c0455400001e002d10f441008910700391220028401c600c44d400305410114034010440c00040d845a604509080503d6582e0001c20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 737465071 1250 737463821 737463847
    0x109051003150803040f0b211e090c121b060901050c0f1c020d020a080901170702010507350c160f0203100e03070308180d110606041e02 60
    0xb0440c448200489495212603096031a640540510302c440c1111210001c1c2c2c00043d803045070440a0011000541e0030800d0385d40c0002e002018080c3c1c82101001d1006d030414200e00c0d500305000703070303440c0008050703c100300001c0c4280a41e1070211544150070000c000c803402001030f204240100c20403201c4c00d958400500040e50580104007507a4501d116038074030741190050000344046803003280524040c410310182d104030382d2200b070798104000603044098000e00044c0840045e02452405060505000b0b20100c072945c140601125000c006039144d90a100302550810644024602c580c80541d9215000200303400a141b20b601091020010410000b000c220b030b49420b840764100b4090038003109a07194100b05401c0c400251040e846400341c00007103100c4800c244103400480349048055401d00c807403034030700365a44e060044c01c1c202a503e403100039600c2c0c0602403060901c640307844d440d00d1829011060710180b40178401031090740a41d00d4251120120b004a90220442141c003040250382d80b05200056 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 737466321 1250 737465071 737465081
    0x5011502061506130f0330050d02090402030f070f090b1b03040e01082a010e09060a050a120510020f04170312040606051801150509040e0a080a0906030b0109051003 72
    0x3244c800c00c100a0200b0507094405ca40d008590140840306410405299080341d082c400900400d89000d10880019030305001e000504500300001e18014180ba074030402140580e80100c68030080c510722602005000d0743c000d0072044d071503940c2e468610f88150600c0d00c102d4491154a19010050b0a10290200c82010401c101d4000d050080059405941d491039031545e01d1940e008860f1000c0720718151400f10006c500c41503011040141c0d98010005c440500788028648050261034000100040128140d1580701c0220018090b44c40045100b4920b82170090030004818200700340240100100b41403450a042568255aa40c0749503a00d0404040d10480ca584a080420300c3c04488180c104000d01c04160f00c640d0403180140c800000c4c1030000c1101d0f0700e40705000d00a0340c0f00c00071842c0c1d012500350710400140444c10f001a00000365030018082152074003551610440e8021800030302207007180e07808541e480c010105400e00344000507030000041c003120224041c0380d0003901c445020707141c1c0354466000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 737467571 1250 737466321 737466337
    0x30a180801020c070f060201110a050a031b080105270403180f060903020a06020604241d280309150e130605041803080f06010e060f03040605011502061506 68
    0xc543c1d5144881d1841e859121512072000003181107400040c07000c0c0107001e100c001e40445250700c1d01e480b00400045e039007500302c80840350030540d6a14040c0242c40209190b41c40420300741d00c402c10103600d030000f0000c036511405160002915a400e95202130010301c0145a00540d25040c090580005c0342c0c07501034041c8841d032140c6045500144001680c5411084101c02d4a00a58009803520b031112001e9035284016680200a8000945200902c2031060540315040007201c4001c03e485502248407110341a814405001d03a40096240a0314000801d0680008031100080d040400c200c54030050318503403c512501d180100d240c005510814411101140c14980040008003800302c400c541900500c0c941c010355003d1072500040f80c070003010700b1138845015640359071010842d036240f4501102c00711717003d44058140501d008071001250340d95130252680c02d00d42e01c11030f0b84030324190510380c00ba5078040c0d124071803501101c00d400158940c089a00c9511160507441061103110f9407020824034810b80d84 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 737468821 1250 737467571 737467573
    0x3080f0c212206090b0c030c190306090204061d0a0302090a05040501020912100e2805032b05100501140a090305030307032901020a17040e040f23030a1808 68
    0x819203081080f9640f1600301c1c9801784101621994400d502211544810f64900700c0c4003105120411091440c455008a12a40d030316000c9026540c90f440711080c1d030496003055010401c1030f424400c1c01080242072400c0440304803565a0b4491079a00070a0341c801001c0c04202da00c5842e203002406222003501120a0101c003e045498090051003500352901481455801c6403070070080b41b50010000010041c48030030059004044401d403c2d6114041d90b558141d08a8071404240001d80d05048014802000c201c040000c1403494801485804202c60005100059005213140b052026990181c0b6000c24082d02091301d50b40c85480c441c042c0c1d5902c4150f80000d0282c840042008400b55258000f103901300f00364018000008012001009414058904540141d02c5060003502040b038a0400201c4101184d841a14054a401041e40f203a803084030142d0390115051091001c01c1b402d0380b2580c0f001c85607045065a0500380c400940d442e4071808501400f000b031008006803a1210fa01031030001405160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 737470071 1250 737468821 737468881
    0x1605070c0308040905070206010812070c081c1b17070203191101030b0f06030604110d05070302090111060f011703091c11060c0a2d03080f0c21 63
    0x450079440e01c3c1d1042c0512070800c1d0911001c182c0d01400003445da8180d40c55034020341140050045d5100c0e80b9013081d139003500c113059140c070001036080c0144200306600c00c241c155548035002d00340010340807460700c8562485060304041840080b980e81c1e40d44080240000c2007544d030715007d80c000603140c040d0001e00c6441180c0c01d18400020001c0d610407002e06080280c80038401c0d001108100078525003607003081c1340c00c000100009007951500341c0c0903a000d002060ac6250405280081c2c01044540848050010030f500082030305442d84c10000104030040824010200341c030300010040f00d000c1d0184107029020038611003020403494140181c844143c1c02500500d00440d142080d81a031000d5444240d40b60818511740b81c402d4207180041b5002000e055004021054540d610440c9028240080b00c1903840096007412000846211001140f40070b0b030b0700ca04076814110080110b03090081c2a5002c1000308004098503480c011000352060014003000e00c0d4669114058098010307031a501d50200031060f1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 737471321 1250 737470071 737470073
    0x4020f03061303030501090b09041502040305070303090504060905132310050123010c140109020901090f0e0105071209050309060408070303110303061309051006060f030b03010903081605070c03 85
    0x82e0100002038004c0c0d4050040c1d03640c41c040941103440403107113150880b04010000e00401c1c481c41052090f042c41030b05c0145015900c0e2902070030440d558004500041e468681000980741030b00a16000e400c41308008c06c410f0600c114500b070009240c8000070000c10014880c84111034403c04e050990b4410301342541c2c800c42c95440308c100101002d020b408907041c010f104524500c5441154800300714410307161001100313820b490b010080d4101d05c0303d03c00a503489420400060b10307100d00d5a4004c100710b803c0401c441070103200000030740c0c0c61011100d60f036a1405040014140c0d1000c100c682002480100084203046030400b1400c511403150605d401500010340002c1a420006a40f0100d901036075039800e000d848401c0081e00c2e0320041d11920350000312540602420043c41d40842e0741588100300b00d50420190781c003404192810307540b20501040c19440c0d803981254050003929000c000880003040504071b50b40d0003130f0032070cc0040c1041444490201d070002c1a90702840869151580007a841030825680e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 737472571 1250 737471321 737471341
    0xf010f12050f0d0e0307090c0f05030a090606031406060301090804150504050307140a0b0403021f12090309090c02150a0c0908030f19050702210a3207060e0904020f0306 74
    0x603001116001e81b040003070018010b900d41c03082004c0604156111080640c0340a001c032410341020304001605030356406603000180035841241c00541c4518003915500900000e2113080c8840180303076038020b0341002029800180300c20111010749400b801580d0701400461006c0310b1601846e000203030144206840418480c40f903101803010000300322451703016181c40301d0000c5c40320f0195100c000d402025071407a20611802c03007403001040300c0311485d0141080340300100d280c06891942005402041801c070b814440358942d40148a403440a0307000400845100714410341c10114014048006c140d903c07000b07000441d105d852080c0042850f142140d484103008202c450781a40a50710403107110169160107280076005c0c500303481846070000c21000542281d4940103c22090030000d41d295030150b102c0e89000912480c4000d17009a1088080381442c00c0d088c42005686038035600c454001d6401914104902a40540070b000000d20984803882c4903200d0b4400715444000440840341d0600a5030708012201302c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 737473821 1250 737472571 737472587
    0xc061a0418060e280305070f0b1602010903080c0703020a0c060f1709030d0f061a040e090f1b01120c020615041b2717060f010f12050f0d 60
    0x4002c80007007024503001c2004507520f00301541800041481403002c5440b46083c060407016090003400d00c185412a9a92100c103035030302000003107d80600d01c3e002c0c4500a2410700001c062210303d40000c105019080e2070152401170010300c1c1207805000090f0700420184284000f0300400d83c4524a08483c0e03454010107803050320019060340c0000c0c03981d1200c205560000e00e85c64000c0c04948003551500312644810000b03044c9800101001c1500c4690000d0081c6559110b0080003071400c040948031800c108900324540005030140d1500c7d4041d10242180880108482400348038030241d1203041440c5400607168200d01c0e04003010146c3c82d201200c0300840d00452050b00c241c84011203030780c140c2c034140304100072101968268145140c0070203026425a000d8111403000f02d403400c0e503a50740d06d06281000c1d150800260440f509543e60100407224904040141c00d8000c2e05034411800950b060410400d101c0016105807400703921902e100300140402402042c0e80002004186c94908024401c0a0316103d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 737475071 1250 737473821 737473823
    0x519090618050708010b07020907200705030f210304060902150c010e15010b0a0912030201060513110304020103021c060611210f0a050c0706030f0e030a0c061a0418 72
    0x50700700702c00201264030540500b070598038804000c50510010b9020f0105000c03005020f00c040c06018101144182c006040e042c02d04112038000b031500038104001d06007001b0001440d00c496900150b001521005519070740044043c03445c00e00c41d16503659040410151282000180d00038080911800010094400900ca0044040000e100d0312040c09962655002c1ca85010700029212900512540e030b2880f009141c1803803985488003000741c5400741c804220040c44400c40150399aa5410043d03810110103500b0b030810340c074400700f102d40240402d80741c075071000500c002e0402d9030018199141c0c41d0300c41c1c4c08114545003502d0800205d9102c0780040c1c510340d041c80c100c0607948540003030280c0d04420040b07003180300500380340b19074140f54006031590490f8010ba6030440502c041403180c074517840c00800405009207501d65002c2118070308144084126036148207110501e400070890105565080705860384881c6c0e10010005429424a9591151405100d030301c1c0c1d48541011890f0141e0794622025000e09 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 737476321 1250 737475071 737475119
    0x2601030c0f1203210e060a050a051303020c101713031b150513050a030801151d100e0d081902062e031509030e1905190906 54
    0x5180c6074a080b42d61489611070050018030440003034482103c403005140e107191014200403886040200d01070381441d00c12284aa41c490b920300401503000c4003409400d4210300b054004101040954900079200c0c20350251aa003d2002c9901c1e54481c7d5224210b4004009510380c8a0180303401c0903102c04a583d0080101a800684004d0048261085c404e240d104001d50008041095460045452005c0d000081c0440320703040580703407003201190080c40b0700400503200781d940c00c00039030403d042400e1030b2094440a004004118a0070070248031610f41f074004a500441742d404403282100760407070345102c3e118a09a00403a01c480e11000700308101e0060803155071055411280341500c1302040740d54410884104095107054500c66400549403140a00b000700d00c03003805000300d6181e4403001c80040c041407451503400c4e40e0700c040909043c1d000c00c0418107014100c42c005440101d910022506180385e0144602c510141c0501c440b8148a8041c480000d100c03048040c4901030366060750805444111200c0031381 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 737477571 1250 737476321 737476349
    0x50109030f05090a140324010e010b04030b0c0c010902120c15120412110703122304061407020d0c18150303140c070b1309050112032601030c 62
    0x4030600880c1583c50048000e440401c04602c0c0c0024009800402c010441e01400784084104880c0030034000d44800407140c401c103030300c0c07945032004138200b42070141e205d40c564202c1070000f880051072240e0007582014000303040b5501c4000141101d801000d0b400c034000d60210a240004a44110100b030080c0205c0d400c40741d0381d00701310240300807040521130f018103188024805400100091400c002c40302e5118400e1070031003000e24030303100c00c5450030220b50415100d0710701c0404036410305139106040d00c81190802401648407618006d00c50b420340124017880d414040d1f8020030080780c03290501a40c07032054000700300d19224001c03070404155222060050540303816601c0c1012281a032240074011781c0502200040c00c00ca455900c1c1100e21001c01a52400c56410421021004a03420080d00d8040c0074001c06103035031958130151462401e400340e804095100d042c030004210006013545e00803001c5415092098440c070074107c94203444d06801c0121564002d4103000402445030840304901940c1e00003ea80340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 737478821 1250 737477571 737477597
    0x13111306150c020d062003010f090b040212010e06030a0516090b0d08041503020f030702100c0e0108040f020d05100b0301061202030c0d0206090d061a04090206040b0c031605010903 79
    0x2c028000240c0a5001a06590224001442c41c0c0c4407482e442d00021010f90002d50480344e00c00d0a500a0740b040600c8514002c080c4210b90803481015020101250b085141a024030303a1888104014070035004070088120000d04192000d02214020356444000c0d6010000600c4c81001c04044502944c2001d510741001030300341d4200010808030302500303d0000390800f4500414040c5c41207240b0b9a034810540c0900c102c1941d0710060f00074502951958014040e401c08241000302280d26080c2e40400304420620700c902940d81001120342c01c6a0440000c03e101c1206c0c0c0003003056401d640c080100140314010300d0001750f0384145c1c00380c0c4200204500901c011503071188003011403c00064040e6043e0050210468249403241141c61200d1000c1c0c41582060100c000140c3c09108001c030079245280c454200804445c3d070308400162540302142c0800c81c02c20150045060350045001e86207503003900188520000c8020001c3c0c822580b00d0305100105560f191801a000c0d080941080b00400c409a078654 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 737480071 1250 737478821 737478827
    0x110f0301030b071b06020309010902060a020a0b06091003080d020c0a0c080607021b010804060b0a060e01090f060c02091e040c060f0e1c0632010801020a02061311130615 74
    0x180c1142070f001c0064404c0d01032504c48100039070024003a0320b06e80d1b42c0c4001707220060b11400044e00e1101556005000003076040d0800c03514402c002848544900301030f004000440200311050713000d60750004070003903c07200c440800000902c1103c01d01c00c210f01c165603484007003151041c0e015041d20f441c00c3c00c0c6e0340701c0c0e1698a02a07903105140312703117040c00da00803d140c40c65652140c25180d41c42402070340086503041840d00420b141c0405500090f000404c2c11342ca01026507080760701c0c0401843c82610810301185041c200400e035800035a4001e11541880c008500c042c01d00d42c58040d812070b0100380005c0305003458900004180828031070040807911641000307400701d000300c01102609501400112002022800100780070b6948182164103a959880300c0761560b0003280e848102c1c1d085440d908803202e0000005a4807040141d10000a683c01040074007140d03680818966040401840c140100e1110f502c3c02d40608034040e5503140d0408041074180820f4442e582040040f121212040c0c240e00000403812 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 737481321 1250 737480071 737480087
    0x30a1509020a0203121509010605180a05330f030402040e150601051e0c1b150a08060a030b13110111060c0c070b0403030c15060e19110f0301030b07 65
    0x1026070000d004411754524224802a0b1048802914004c10740380c003000110420401e8000c403000603c0030031262091017a442d403c20755504c045400301c0c5000d2070000090540f00c6040d000a00b160402114841660f04103051526030460061006444503203008a00c0020740080701c0a0b0301c5142403500242c400707000421840452070070000d03418503030f58840d001900d50303134000c44038a08085d280800305041c0140840160500300a404042e2080550042c04951010400b0290521442110040312090003e180c100e07803601c04103042213102075851100040b4030404c2c65001800c0c50312984100702c040490150300311200740c8100401c1e064407030786100442d6413a5000c02d141c00c0b0f660083c0045800000d825019200d240718017000c480c01d4503280d414096480e0407a51045001c2b07070100d0022030403ca007031001e5518000c40042d04104940c0317000d00c403600f44c172005400300c070701000b410718403501051190300500c0c0405042d600c000e9407030201c0301542480c1d078802d21064950303004a4022030038140c030070301c11 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 737482571 1250 737481321 737481337
    0x20c0d0c0512071a151c02090606030f01122105120a02090a06120209030a0c0303080c0f041211041d060907060206190605092d190216020402030a150902 67
    0x10f02402c0080b82e9525508004081d200702e650000c5442c400000e0b50300c6d01100e03003400008059006041103144140101c0c1c1c00080d020520075001801082010341d407284106045842107a0000c00039501401c1040a030a1000180c4c8440c07000c407903445005940000081c82c0101946051070f1466480380360380422409400c44050784440d107403400300841d504c0b8004207030700641c0d281e000525180c00500082d150039074005007140c862004500030024140c1200c581940866400003881c940814916504c0017403090380148043c1d642055406030a2040c0c0441000214001500c02c00407990704050b951046617120000e103142d44103400004e0728802000c6420070841c0c4658006141c1c640302e05901c040e1610005055110301903944100241640c0c0e5829602d005400441c0000c1100f0204050f424120201008440800802000b400418410215204403089240500580791540600090501c03143d040000c2d5005001000f44103100b07900764800440002c54130b201503005581c404485040c1d0190100e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 737483821 1250 737482571 737482583
    0x150f030903050415110f060f0f01031a042102010501150504150c050f1c17041106030709091b020c0109061403060d050a030207080705030a051c03020c0d0c051207 71
    0x1c001d550604103c42c0480689401c0003036001d1407410449181140d8040c050825a100c7c40900810b00008d403c55034001e102c40180c0c10556055440b00b807407020742c4281d01c41418080c00000f80c18002d50001c00d40d0045140f20042042c1000c0d860000e0103410217010340d411001c00d007882e105080b07008608480c1151944211098604020340d000d0340c412203079020039500e90003417490706a0901010b0041a0309503496503e84009018600401441c0003821002c16080c0c4105d6001d00004c940f40f02c0b03440d598520122010b41d501c2c0e64105044400c010658481c21005d400d20700e5000615080c5051b5031110146542241ca04010070401180d40140501c00c05c0089085001e2032600c8504c07840003140d1103c00a003007034030072000300d17668540f41c0840c6903810303001600114814090300340c09002135001003000f00d000748100c5000351615a01d80111200101c0a10700b00110543d981d8040d07010740f0f00708001c0310283c4e803040c0c0a0040140011400d107004941501804502000070b005520a48500f0740c0c00074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 737485071 1250 737483821 737483827
    0x601060f021b0301020c03040e0a0b06030432070f030501050709050a17120f0304060f06050f01050903010908070b01030311030403030c02010806030a06110405090a05060d0b190204150f03090305 85
    0x781075203401c003503410b0b0507509035408100d4a084d0500400c010001021201240c00301480c0081d0341d030040701c0203014150b1084104005210105000c00c481c3c10510b10724481d41c15903020202c200506810066880c031069018910740012084811900e46085078000c0c0024403083c2e03101101115602203d0280300e90007284035500380300c1002c500c9050b0100007180d0044070f400e4a0a04094035940e0080e00300745520362000010441009918010300c0429a540902442018200341c002288500091b403c03074104400881c0100442e6001d4001d50201904006103035503a0849051240d00301e0002d01098012948000c04820b0f101c00000071142143e0b0135540d0351140680c0d0350700440d01c00d070019100b41d80c140f1680c0701c600007046040c03050801038101604180d55a601d48000d01440300c3c001003044840620340005c201c2c094450003801214250301540d112240e50b40c1140140019284101d090801480070034085442c542c100203150004500341c50380721b62443d8040007101610b0b240000100019814 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 737486321 1250 737485071 737485093
    0x10501150224010b0703051e071202120a030b040b090906071b57050411030105210f030703091e09020c030702040f02070c0531090203030c0706020601060f02 69
    0x20140005d44c3c828684107290030b40800121b1042e08030001a10b50003280003407a45d00300502c650070150b84e42080d0020780817440c1c02519404050240700554014113441e03c100512580d2140c0c020450000010b03c3c600107400c003100e0265484404403170031004169101290301450711802c4903403c409030f20403070a2851a980c100c088006c86503094080068840c08501d6820052444d055401004502d0540da4040300000c000035441e0600ba41c4454050f5280007000c84000518508407419190151000030111081807502a012100303030b900e02000e8003a40424007908800403004040c11406070381c07005079054684040c4145103d401000040c1030b440880100850b00d51030300a8208007610400b41d0382802c0d61500401e007541c0c0041503a84400390300045010812400341ea0a20240c03406a44000d4190b042a8035040c0d00078081141b264144c00c46c0d44280440c1c003142e0000f501d080e0380a0142e98807502e11030350039076584601c4d004880241c01414008500303244104007003060541303294000d0110000c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 737487571 1250 737486321 737486339
    0x4081c0e0306011526070f02100606020c1207030b10030c05040509030910090b07081908010803040e100b0d020c060109020a0c14070b040605030f01050a05090f130501050115022401 79
    0x1040f1902c051900c44081c04903983c0901781582c4101243e4940412011000e40024182014900d48003580e9241c91300c180240c0794001840e064030581525500540d0320b5050b4441d141c95010f03480100201c08060801c01c030681914900d0044a200b0891014002c0d01c41e0b04000903500c003100c400009078828480b0300c0c090315100780b004001002d00d0400c4091251201524992a4020a0300b60b94507240014201640e60380910700400003045440d1202155040c50074031522441548245041c400039000895042407031a210f8100034207458280da40d039249802d03e240c0203900511580a01401400000144401d10b4022100b409106980d0036140c0100ca81c1d41c07004804e01c1c242d066210388109040419062440002007001c1c1800307840360f603100d1034042c5105002810582086004150400b81001a9154900b00c40e4200001c1803222402d6540c1c0c4000c1d80051010500140c260740c00c0c14000284075044410004003420554203030341030680e1040c00324402c519020392034000b40601c1c60040000c541 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 737488821 1250 737487571 737487587
    0x5120c07060b030d030c09241d1306050f01020606150c0c180f07020a030f141614010605090423120a08010501080906091b0604081c0e03060115 63
    0x4491080090316801d04004285080d4070760704c3d4034010981c0d036101101030760b8100030743c8401424940d103000e110540c41c4440c0d0541820804054052115401e5a841c1c1181310b001601c40081d005813401112518086c414809809a480340345d000d1203c44184150b00c1d4408500e4510490018000c0d100340031041c448002c0c5a840a15941800c3c0200d04441003655030f41c40030f600e50400e05c04024405410203003522200c0e140060305500a561142e240000040e811110a004103816801d01000c544104e0345642c0301c070721900d218a08001d0341d03105914100922070a003884040306100080042c0344c1c07140d051040050055401801c60301d100641c0c0c50000d869420105003003400901074032000c505282c0305180c2354006821180c04165a04014002d5580c41018240e0104508008041a00b0120321007911100b41c00041e8603040b00a40d610340c11916543d0803600100b0805046800c41c411203202c80083c2440e4100d407100041c0c1c6030071140c40b01e250000310107068410b0801c40c8602901c0f500403d440c494 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 737490071 1250 737488821 737488823
    0x1707020c0108150a0b07060b032a0402031008031c05100506120a06052205070f0e0f010e0312030907060c051504020a0e0411010e062106120102040b04031205120c07 72
    0x1310180c001c074180742541c021340718061092101143d25520302d4209800c0981403208814200744840c82070048100418090050f0002030f903005940e41c0304c20303a450010088541094809100000340200e000d2800e4183c8074050303440f6102004075466804400b0345c488000d20444c0d900110501c0086021410320b0100b5401900b50308000038116901c0700030800c0d5003a00d40d04580b11100c450400001e9201e82d004a6910030400d14102c8818040d004020b42094035440340b0f940500c6510034a0b00d0280d0140301701c032003250001000c0392400c0c0a03c1400300582d9100310350b1014540940080040c1030740c06846010010f03940003000c2c25006883c5940c81e515264000c0042e60702c80804c2d0301c0052110030101d01940039038081d001c05d4407801c19900c0098150300801603001e000e014100448103600404440c0078405600392004480307540c54800000314042003034810340d080c9510008000036182c104e08018011a03224034021800c4807420782c07007039542c0d00844840c00520141800001c9910b01c652005280345 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 737491321 1250 737490071 737490079
    0x10507020304050613260c0405060d0f0609080c160503070614030703110703080618190228080907090507021c050d060602010b0114070816021804031707020c010815 72
    0x80d6946e203184c103085000e408041c905098482d80c40400c0880a1041208500060b1410b00c801e061101c080b50902c105034402030300907880340211030200030311034015100341c503041000c0c96100e400000343c46480d8641c02010700021110b1142c0000c60781070101d42c4a044416944880701c14242c0e106c5154140e42c070040c955401c02d03503600b030b02d440004003080207066114001d40d00d80800b4a044000d0200e00b084c41e04070800c90941e45401c00a4611105103d6503130007103400d00258483c5040ba42540d42500c1952000700113400d80003d48080980c400d805910070902141114601985c1c2c20500f41142c0c41500c54100607008034400c021b907180b00400180d116041440d15910300214140c0e0315048410980107240140d44a054075240d960303002012541107811100403600e00385013903852201611420f103288540c03c07040050f5a040d5501d004440c2d404410a4003c40140c7c41e1615000702407842ca009102050074009011640c1d442c0b000035115100b40060311030b01c0054644507010707031a1003401c1101c1944 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 737492571 1250 737491321 737491357
    0x20906060705150a090c051c061107080409092303031b0903060a0f0b19052808070e0f0603061504020f040816120b0103080705070b040608180105070203040506 70
    0xc080d010021441003e001000141d8508603280c1a11116801d5010b6841405030f0354a42112840c02000703d090107500002c001600c81c1d103514030342e0ad00c1c021040c000d008080d001c100003e0280c000e801c200d031190301c04c4401c3c41392102d05503010071009006c840d400c12540d2003800083d10000c2c40004401c012981a1100c13410f01281c100000d16110045608546040d228140c1c1807031030045d0701400c0001002101c1c8410107400c154030f0f0703140c50380c00c501ca07147c4039028003001203941da60380741c032040040c01208103043c0c10a9103940c0d0841d030310600c0b807054036031484d501c5d00000c80c01082c01c25000c2c041d0000402902142e03c907500340301c481c078200c201900d60245c3c0c20024941ea03000c0020051000308518000742200001d070452400e1000342179400529200640f400040010b551040700c0b07819260301042c01605c1d500d01e030030000d2810301d1316009030700b808600080c04107201e90823400e16417103a180075000c48442590070307280d07600b80c071015103164015034018841800b091801d900503142d040302c45419580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 737493821 1250 737492571 737492593
    0x90e0603100504050c010906020304081005130614040c0902031510030b0901080a05121e0f120408042c010521060c0324030303070c0302030903060c09100309020906060705 75
    0x104a800c283c070221025407008484000e0365802a58000060526002460400b8504404a41c480401c103045c104070741d507550700081100391082044941036820181c1081050410b03201e41c1051181a50151039006114100040400190084910807000340d11320120070390044c030034400355120304402a414580c4030b803403040d82e540703610700924020a8044014032103d0b080d030402c1410090311805048490404114403003004000c021010301002c4d5203082203079036070a122444031150180c4d81c081c40190a04034288002d200400c4040d10907100c070324900866103800300380030180341001004085404828400100018502990045641e069841c2c1c042d400b010b51070861070403c14100d5191008400200500c803e1410302c0505650094085c442a00c0b0300040d200042e65070b000041c108420070400c0807241e03042620074016280c6200e03000d811250f00d424041d580c00100e41059410328021100b00442000107840386c0a66000ca80e0007900c0845907132100d40074413131658482c0800b90b80d02d201c0c48203605 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 737495071 1250 737493821 737493853
    0x8040f0614100501140301031410060815060f031203060628020c010203040f15170a061403010c090308071a090a06062c07120e0c040615090e0603 64
    0x41d41d19400c8414249080c6005559014100203e400180c100210000c40c0441e900704c40c5d0480f8107503070b0040c0200c07892218a441141c1f2b080d025001c5007211070b00b40040061141d50028080f01e81d48683c0030002410b030b840200380580e0716691a40e05038903070721003008100060741c02c000035504048060600d528090356529020500e0000844620b40502c946240d035101c15418041031281c84002d1005d14130b01881c04290481100c0c40c0d000d04550f0070700e5040800e0069005042c904048641203000407007600e450300881c80200458412070209450400c0709044500d0103228a50816910745c60340702e41141552100c110903045450304842071010003d0a0191200c003d440d10b109a05041c0107100c1c02401c4d2412101356800d03640036400300304079526000d00c0d044081c0d03080045e0507031490f400080c03641c030404104e9042101c5007000e9002441d00140001034040842c1017449c0001c1503d0501c04e1590720b035041c0002d4440c24628400050950205002107682d600c0300796008031005080b2010170540071040d0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 737496321 1250 737495071 737495081
    0x60120031b03030114011404150c060f0b0312041d0915090a1703040f03050a120c120501151b15141f23030111030a23150108040f06 58
    0x51801ca52000c4010083c8080d1100340d03000300b000030303e8420030007031003420601c506010301e01805011000e08401c942146100300e6030180e00c1504010144810740c0d5000b5403000401e5451074507400785c010f00c0042039100480008403030885d403d400289400c030590400340e26144401416003602030080220382824110401c00b00b90144100303c001e460b510310b5a203041912024441060105198280200808260004100c9241c0e0ba05030a00030740c0d86042d00030440d89400d07141e007104219485c10021032940c80d4045c0341d2608850725844108456604c030784c18000e0905000a4100014403c503269049002c84802100c034107034810f120300403207403015a6200082d80c601d500a041202c800d0030401c4104080c1d2030b10486e4240030f0781c4800c068241005c00d8008154290300b12030307550410910880c50310791001d62201608180010a4a450303052070351004000e015601d10500f03260380e4071440040300f02082d124640c0100c00c48514902484a1f2000650349150010406e884030004035642c00042242c0d80a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 737497571 1250 737496321 737496367
    0x601060302030906010602010b150a0e0409030f020c0102030c06150d050712062405090c0708070813170303190b0d060903030621170702120a0308070806012003 70
    0x56141c3c58100203ca2510700705a10140444e81003420001c1562143c0c81d081c1f40f000c24820300f040e60f03103020f01415035640c1e01490040707400038500740e83c010034158480b03076040c088400c560a4032840c0d4505401260713a40608140c0003d19000b507400700302c1050344441c0d03503003040b80f028000080354007444e290745040c03014651011098100d2503483c202003000501c00d03110025030405000044040c01c00e0b108000b0600d80c004c490060a001000c41d802c1010103081e210f0321940309001a0317031002e4034a00f88440303800088980c00c0310041050042404041e03500c4105204021030011411640c1d481e405c4a440e444030184484060382d40e0940742d1140d00c507510040f1100780a01400301e282030151030300904840c51a03010485c91701e9142c81400341c80c08541d6207644d10720b41003410510312440142c00c2e200d1510032040029480049000180c0f4804004541c0007000c3e40252110401030740e803e00181d174101e80031901580001c40c180030b0420740c1c02811310a2509801860101c81c200340d091020030080c45070710a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 737498821 1250 737497571 737497577
    0x91215010501120606080f090705040606030209090604060b030a0207031b11130b010504121a1311010507080712031d030408100603030c0f0618300e010e12060106 71
    0x100601c03040d6040300800301d0350540c1e220200130301858040f005000d61005130441d000708080a01050407401c08020321b0001c0c0900030820401e0035507501e0068029030144005500a1382c210001445916040c404e5008950349910407603e10340e03d020100d002580031581c100c044c05030400c1c0300d00d070103080303a01081e0901d0710418054680050020811180c0704040380414843d5080c00bc1c020400c0c0d900030305031002c07502ca81200303c000c0e004034904100c00d5180c086000742d250791507400300056255004004100140109054100280c90b100112344034464080701802c8031504002c0100058200c01103000c54072100e103030000341c180348240b8000c05207031181501200c41c4e0000c41c00303106004041c031003400900f012800401c207a9145a8018002a00d01d07031020f06440724004144040c000c05421440c013008510326081e15100407490010310058968842c820040c03400e0503020440c0080190b8400b031030300241c98071900881d41000441d192094543c541d5044140e640204820410411809020b052152 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 737500071 1250 737498821 737498863
    0x408030307031d010606090501140c011a15040f031e0209010321021603030f14070f1103010209150a2c180c07060c03180b060103151404020912 63
    0x81d092003d1000d078040c1d0020070342d1501d10304002d8550445c1400040310b20038200a4000e04200080004034083c5e50f4070407a0035402e0400944454010811140550782c044079002e40004448002c81d04a00907030080c50050820300c01d0a1000c25001e0051040f0b0713000c950b10302c44095250398040350009000b030740203c5805180d84103454524509a054259840081c40140b89200d4086070010301c20100344400742c00d0000d0b041c1001c050b54410414651034880482416a503280c651038035280d203440312038040d08c1c4485200d2030308c0b10b1340c901802240d5020384018005c0e801c040400200400ea680240700207418080400900007500c0e04a100810b8403881e00340c46da00403c0d0011083c40005081c040c042000c0100c0350042040301201101610b40042d0080b41c0007030700260385841580104400c46175030701c146a000351031100704040102d0f400c0c4980b000703980900c6075540e28080c2c088800310500070903807102e6a01c03002004504040e400b5106098006100ea401c1070301c410308490402d2911103a4481b14a048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 737501321 1250 737500071 737500091
    0x9010c141501050a17061b040302100e0a061431090f0b090402010203030c0d0902210c09060a0b03040c090615031404030503040b041502030a0c0e040212040f08040803030703 76
    0xc04c0044006007005e6030003840c2c101e40b10045a031100e400420800300304003004890500108035400390780c06598081c018003c01c10100314003521440e030041c1c005100da8000000850700f00e00c50004102c0310505842c1150414000c1c02908400c09070b00b21403101080c007a00d00140b00c4070100c104040003407a401c2000911a000307c140001955110342000c3e0003085010240401030740c2c00007c80b90300007098144540c40b90304a10401001e42803505020b9440032405104050311100d0388800c50a8070704440032200414003220074842c4200040304c00c254060003490040003511a650001c5078024410f00649011980f07400300701d011103136070740c0041c603104030102c0d10061900d41510405080b04030307524400590f8500307580e00800c03901c0003c0004001c3c900040104007046070000c12104a00b02c07910342551030b80707402219131004000b0703c5854000600c4030585c00b03005007880d00c201c80c400d1103c008220035995858440c2043c803102080100d440720000c2100244035102440903500a00072650049284903030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 737502571 1250 737501321 737501329
    0xd121101021b012324090705030f0a09030e1002030903030d02070b0903070f0807080705010e011b0503040c0603020c100615030b180106110a060612030216060509010c14150105 77
    0xe00003041d01005107016504258a440480045d4007000350920302500d4940003c1007004044040300f400c1d0010900c405005103030f5000405180704402410180300e107682d89001d0f002c180c074070340203001e07000c02c100052200990030032408580740d201d05401201e141083e01c0e4042803079948030240a00c0d600358046224020820280140d68000300c1e440001d500f0301c07145403950310190b030800314002d0542c00001341400c1000210001d807641320790000020070988245035507045c0a8001146090a1515800c031110103240c020070540340503640201c504112107045c82c03c1900258003014005541e8404d032004444001080c1c02084098540c3e807403c01181c0d14511405001d07500315003e001d200312201d8181001d030480d00403515045071000d1604600d01a185030307025042c14100701d4042d122604203074000c40c0b504080303403d94440c980f007682201e002d043e40c40b55546008640740038500000b002004801d403103610908081c002d9600414541c143c031b0104842c00b07480d14401800092904c6c10001c010066483c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 737503821 1250 737502571 737502581
    0x9202106160801060212090a05030303071e0903150b010c0206030403120605010516020f011b05010e1014041106040f0608191109040510030204062306090d121101021b01 74
    0x2240c00d10b40c049504140c0044d40f200c0440d1001032000c0808107001202d580c580e02400000e20024060340e69a003400c400041519017907044031068100d141c040740c1c40251086058004594104000510b4200003440481c040c20841c1c548904000c03040710000e001d40c1c0c0d8017000310300541c801d85407201140220b021a40c184c1d00a030b4003d9050140c180041008104444c0340401c0d015030450300b03804410119001640d51414800c00b111410840c0c0200c4400c00505501003001500705408696046201c1c0350080c2c04c0e91801004010708860804c041400541c03440741c0e15100000c014800d42c102034031145200902a580d500240c0003451640a0003500c07019038502d0100060012030600665101103e514040d2040343c00b010b002e2513a42c00041c400f9502c1d040d01901071135000b0020b02015540b801000d04e001010050228110441d8005410030310702101203a020080243c1640b8892000b5220320003003c080e4900310050100242d13003041681c1d001e100070003001c0d142084480700d5805600841342190 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 737505071 1250 737503821 737503861
    0x715020c150702090702010f0501080714060f07021203043c0503060c0c0115080303060a06093002090403260c12101203091809202106 59
    0x195071800d044000c1030300d03402c662030030b501501e0742820340d16030700001ca0051510703404142819140000100340c201c004540c0c5412910360704a00c00482c0c4034030003040300510403031481c0c100d114010481c0030b0041c2448a00c5280014485050740d040c03d030fa03049000751083c046031032441224140401c0c003a41103941c048482c1803160502d010740f111410070002c00e640b4003014202e85648000483d404e09801c2003500300c4074140200229900806954007141a03480d08195a01032051200a40100d0340d1440341c1054012528030f01c08501303440e00c03200c0d014560000e10580407840d682e030403410203015854a0300d0050103070b8802e54500c1600c429109540c254250312141085440e02d6003018440b0a4041c241500c040045210104e11581c6850305107040d40900740e8400c00070000d010780203005140e04246020215072601e00300c150005800070440e0200c8545080c01040105800c40e010a400682540340c0f0320720368041d011940785d084a003a01d40000d0703420316902d003960348140708020f4001040e2590100342 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 737506321 1250 737505071 737505079
    0x170408040e0a0203160e0f0d080406021504170a0c212604060b0a170106180905031206190806090f0118030c080d050c0703090501052b0e0715020c 64
    0x18201141405100c0c9031102c0380c141082400e14038800d040c0d0b511481c410000382c006020b230440d90223911341191541c026100d0030015001300c04080102e00d41c0385110610482c0e102130940350700c12a540458401c1d800210160301001603801e03020000075190031483c400107445154810b0703c41c4980030004e01e14507980c1210072010400b41d005074000c0307002c1c40045030016842540492130032400c0020900710900c681c03046004000040c1e8103d8a050194000780503110040e1100078041a02034208042d10b550880080c00c81e0b1082001e90a0781c4102000740d600290018007010340d0603072110b44101c0704034490b00304c004540c00041c180890300c481003000d0201002d104000340401c944100c49075070f4003083c654019040c4203000b0380341c504201540b82141c003541d0446d94200103a08085800403816000014200d001c036050b508040b40560240003078a4040017801c100c5080164003031444108030700110340400e4440c0e11000d14101895051041001818000c240b082c40743c200c6890007480d00502d00a00b60207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 737507571 1250 737506321 737506327
    0x18150d1b0507060902120111040f0b09010f030b0301061802040e0a09120c050a050318030c0405100513090204020f09011709060703330f06140a0c03170408040e0a02 72
    0x18154105050780d802e250000c100140c0c11030980042400c9070f1422150074000d510b0082c1c110700c504981e0700500b064500d126901d0b00c07040c2d120301c03128a0601c00c020070300d03000c03820b45013035060100d2094100011220010340007181140e40c0e00c061403e6482c880c0c5c0340400c450b401180510160b842407160561200c502302040c048041d5a40325000844910b038a98010883e00f0440141441010040c20706c0d01c2c0c0d88502140d1b03445003502800071080320081030703451181c024203400c10305031f1416020f41402a03402c3c4480055007840c203420000000302c0d0202c61220035880e00d90001c0540c0d22840905405000c0504450342c460551000400e40a61400c041d404140c1c0382051013020b02002850035800b42c40d5042c00144103000c1e00e104210748140703d180f0000b103e030840c500c1e04032100f05000720007140d5070018140b89140d2074001c01d6520049500d010301050718184041603000d031040521516160281c1048441540003296082036607104403000c2d900d410000600300b28034003612185c0c55012294040840c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 737508821 1250 737507571 737507621
    0x40902221a190b160b010f060e04091a0603070b040f0f050d050d0c0317090f0d022a010c080d2301051e0f0414160207030b01090218150d 60
    0xb80c216154040c05a075000045040c0340704000c1800c1d1034100c00d8126441401942c0d550711010004005400350400140d000c3d58130740d555091034000c21010703070741c4080c0c0600c20000561340d0710b1300040010710103079046c49201d20001e1134516060090000e043c0c42d09a504156040040d0543c0c864000d5000fa4064505204560081080032a01c8a5080c0c2285400041403102d400d0444003c084140101c0c02510944148904d41000181c041c070303948403003015500e20030034040301683c40d403403072050744100344e01c9100c01c0030440400504c240f4542d41c030505084080d0301c0c2980b00c0b82080c0e08080380340030b000341d95640c906041c202c560b113030311210441a11002141c0c2d8180750100e903059103c02c100a1842808041100306540d0304c079008600203401800030000a40c8000b0128804142a298450400c1d08101080883c0780701150071415a074102034480c0d016440e10030280001e501c4034903115180c101340c00c1f00b9030a030364030344001c0d005030b03017100745103a03107801c0b8618034802141c11144420320341521010f8005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 737510071 1250 737508821 737508859
    0x10806040f0618150b041a062b06120506011203120209120f030715090b010b1c090b0610020648070b0c030411040902221a 54
    0x41c94540d0000c404039000780c3c5240081d404140d40300d001040e0883c1e9002e040f640c1c1c80550322580d00748004031820700c501001882ea00c007241d11032a060302d80200d400c1085020109046e5121012101c1d4002c60101641040700032008452803a0050005c0c0d103019264442441402c10043e23000d004075a581100402c425540039254811140d00c00c40a070740c001c10b00090555034008d001d04500050303400e80d045149007c031040e4a0b0750056900701c4452660340c00a82160501d03104462042c0d900480034803281c0d08214128010340c0041c0000c00404102e0b000f140e440382c85030b001d5040d000c0d21034502a142802d00c0c10400207540c00721001d0f1021540818100052035840c4803e1070b2035032074402099081201c03245030380b8211303483c0c00000c80310503080d110152401f520080d0051200c03d01500c080615070701d80030004c070000e11040d980030b0007640c2c10b403102c101385141a5000801c81c901c000c2040040b1110800046a214031002018100c141c0d2048146041c0702140342c940d00c0580b00300c0702c00b101c0d9800e0344800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 737511321 1250 737510071 737510093
    0x606030c0b09100f0e090906190605061626031603090f1b03060219020c0d0b0a050a0e060f0601020d11070b071b030f03180b0712140a0c060501080604 66
    0x10f0400c0110010160f81e0040c01814800309110024000c240e1901c0c2c000340c0180d840d0425600307005110f109400c0011100902e21070801900c0300100041d1078000303002d040086c1c00315541d0301540e0300700c0d004c18031000030704804210f00410780e100c040300741d01c0b171411840c428207544100850f0300c14141000081000603030904200d80416600c18a5007064a01034061603d1641654000414642c40020302c101c04020304081c0c441c440180e6030032265001c910b581800090482850020040800080401c22440140c7c10055000119160010349101003840840c40c0500a440820950490750140011035031306101030002d0640b5418001c1c10741c00f124041a6031380d0024070468520504c04900b0703004004149011802d410285c8590795111a16070414652100c10410124040380c071804500404c0c6a84041410481d07800c0400c06050050f036895801021810340c1070b103010404114250003d032184c01d0040c280c4070484c1d5485108249103490070070221081a00070016a6010104010000d4801412 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 737512571 1250 737511321 737511349
    0x2703020303121f45110d090602180a082a0d050610061407060f0b1e04050f06151e0706020a0810050319031b0606030c0b09 54
    0x140503580c040c0c102d010906a042c1c034070286034000c000000d4103c60364965118a002403c0c030555a0b0040c001044c011142c4c1245690702000405201e100741250303540410300403c0d000060b5441d010008a10741d04540003130904854440e8046001592500404031448496000b0380306800d620741840f00050303035041072004840e0f4048444007224004003030384546600c0c035200908540522415403610a80b203e200726165079500758040c0380041c1c0144a05009011107402d801c010340740402d26182c45006c0e100c0c00b80c1c8000700c142c55034165181a01da0b0003444c410900da28400c906068128410072003503401c080c00c0315803180c1002083c04099034440c1091149041c603000010741d19690242c00880000410414202c001b034089101d00601800b030b00100810034159444804035580d01980386d0002c1118060b5580580c4640101c0b4010034019245403030590080c18903003016100c880e010094103001181c211103440e1901c0b01001000b801c4050301020340800c001e00e608006080b004103d1f104070505e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 737513821 1250 737512571 737512597
    0x706050f0a090302060d09030f0507020a0e061f080603010c140409050612010f0203221a15040e07030209010803031e04020f040905010606140a021011090a03032703020303 75
    0x81d01c64549401080d400c070003190b02401c600d807521005030341c0c20020f0800c0c0b542070340400c040c80d8039400d605225900700e844542d4000c0108800500f003041c0d00781000c40003020140c1040f110441410f402545001c4803141a02d981c1e2100013500d003600515003510400503c2c8014071010310115550701e082402a01c05540800d030300090990b0302d0100241164007a01c511580b40c2d46801c0759888490610b40055105204500034483c0441082d0b00b880d44003c0c15060140410008014a80c5400d41c1c900e9000d400809002c2074180034424000003c088800d4243d482489a01c00c80c0d042045003841c1d0070840c010300c0c103540a1401c524140201030020394180d042031042c101d51400140c1107545252588c032003070001500c00c11a161a034070740140205918021800822119204014055030100c111614074540e2360103084440c01002511020b0202400e0f5404220001d0110001a48030b8042080c0218040d54a074009802e01000190310800e40d21445101d00c42c0c110814000b584000040700d042704410700d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 737515071 1250 737513821 737513827
    0x2040f05040c090f030b0a140408030f36060702010b1e040216060212090309060a110a140318060f0403020d05070b0d090201080108030903060f10090f0e0f0706050f 72
    0x2440403520b402803034200348400700340660080241b00580c402144036040000d0100043c041d0020ba00c280d00000b1140246081c500b0000175141842084405810541038401d10240c1030310407440c204844501d210031724040103500d00d0f00c00c000074200156500074429000030000807010001040d403c8107800b1440780d07141c00c002690011500c4550440e03005058402d03010701d03c9070b00c40c600762002c0e500c40410860b44070790240106a107000d0107c2282c48081d401040c051070070300310000540e0102e180340160002c5008204098000c248801c1c9040c030f811000402641e5501091042c0641d560311060300740780904000c2c09a406601c0c5000c0440701901e4044a5240f05003041d03140680c50010313690481c0c40803400c0401c6490501c10306400c0315682d80e10036260958180e0300c035142aa52070050340784056040d403104005c1000b440b0b40350324080d0014031999007602031f20b0b05c99000c0760641c0d14564800310410b64498040c04c4a14042c4503079102a410034000c1c01440f03117000002800d074002d11083d021140800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 737516321 1250 737515071 737515091
    0x15030f0c0f08070c0b010905040302100e030919030f051c030b0d14010e0a03020c010e0904020a0506030912070f060b060909041407030507171513030819090b1005010302040f0504 78
    0x140f01211820380d008051405d04d42c0c55411080140c0800d56045025101d0008108101c4e1400d00401a80404520040d0304283d2003800308406911071425049441c0321000b00400401c0100401d030b041e01b03020350010302c600155039442000e014000080c1c0d4080615180002446070760700e45000e0000c50300050302d00d0f140420240301e00d004203510201e1400302d10912030b00408241d004070f03c5864015090b00c5c1c815016002105010150b030040714000e510103c200c41c14442460075030091904080820704441ea0240024101c00b100d521801c41a22040e07500b80b0b0400800c2503238010450280700a0312a5802c00c403589001c0f900e0240701400090585d206040ca00181c2078041040a00554001c4221442aa9502d0500100c0c0d4414201c02c40390303016450001805641d0a0003281c002c03040a450028080c0090714101c0e040030000d4000c0610b03410050285800742c54038001c01c0015801280f0940450134503400040c2100b03210b0740300354107240c0103000c10403a81d0001c200d00812510152000b0600e240340d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 737517571 1250 737516321 737516327
    0x60f1b1204080d09151506050f07110a03030e09060d02010c021e030a0f120e0105070f02010e060301090213050102060907290a021608030909040807020f040615030f0c0f0807 76
    0x2002c0c0c59483c15850f01d0304e9801403020400e04ca0f1003c4c0c03010001084100f0340950107400c241744a000d03410209400b00a403030700e00c0c042440203007a25030150b03003000d801c1500f1800040e0380c0e4400754815000110b140360080340324945101900c1d00080200c1d480394581d000d640c000781a0050114019220b000420f40341c07003c01c001e0401003142c04000800b0345450031098945144c0c0202046030556031112000c101c0d04e50907001d041c5010384114140c40781d80c2400c502d540c41d81c00c1d80c03402c80022410482081311000281c1c03a8907016501800c0203100258941200384582050400c45600142c11075200505000c1045400f0410340c2c240d80c4041043c0503840b0b0b80c10f000f5050b460002c0c030000f190f0480061811121540410013810000c2160208000d06a032200a5641ea004682240b0790050310b840c080f400090803000201041351003d07020707020045c140340008088a015501031005c10292102c509003041e8507100f0180f1003071b180c6d20100005190504002c202944258056041c131086902143c12140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 737518821 1250 737517571 737517577
    0xc1c051c06050d02190329010e06010206010b030a020d0c0f02010b19120c0e0702060f1812180301142a070206210901090b070c050616031d060f1b120408 67
    0x14210812402d40800d01c0c0941c0c1182000118050411f41840c0002c100e6008018010340145030590042c00140d09205401c03500c1da00207086030f48015800c06c101694040c040c0642010b40c140e0741c0702c520500840c80006070135940c01201243c4a640028814404e80d0110707120501651400c1c0203e8072110400d240038019518250040d0240c01a0700d41004035503540060154800c4280440d606029125074118a8180411445488042c0c00440c0305403144100c00340074124064400e82001d40e0340100201080c00c613100c1044401007440080c1c01c00c0f0782529110f00c407140100002408910401c070b2020a44258040c00d44001d11070304001038620220680c003d080007400c1641840032105041c1031019600070b0048100813548094800e0000e800c280c0500360740400160840c0c0030b04002d584100d20b000305041202ca007541495035580410522110628100103954501c0300180424202000b03118440c1200402801a4901341c45000030003651900640d00440445424500d003500c035803030300c5104c2b40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 737520071 1250 737518821 737518823
    0x1090c1e02160b0304061b3f050115021f0504020d0209090105010e01060f020a0201030b06130305060118060f090c121112060a050f060c1c051c06050d021903 69
    0x840907140110f4000040da0046000354072986d0100070384055a03900118582005844102244840942d50344540c1c000a4190f40c024401300c0c1c0c041880c890106680814804090551001d0794074001440500480b54400005901c1d0340001c1901403d65207100711203a11500080410030744030404502191914203442128550003070420f80c092030078414041c001d180c04d22076451400580c10000682c18001c814602801074980e0203044400d03c180c00640c003070100100c00580041c000c000c181c0c03d02e20020300300005144554003825855241000a1410343c01d1045100100c0c0d01c0e069040048404807601281185d0302400b01084513488076506480000441c11010025400c0c40106591501c0c0440200101d013a8241450140c2d1101d0003444840500750207415002210a2980720080c40c1c03040c040c1c280c1d0207018003124884602d01c0359410301020324a000e040416800b09080500021100c9000381c0000e107020100902480e01c80002d0320b29140d0754010b4019004540d502c00100c4900400c04051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 737521321 1250 737520071 737520103
    0x11d060610031e09120e0414011205101b0305090303071e052101030201081b09120a0507091d0303092a1206010f1d0c09031e0a0b01090c1e02 62
    0x21541c517041490b0b0301900c00d07560f000081c8484004004610b06032240c0d1880d009044400c260aa0074400b03900c1011001c5e100075101441600d090700032901490141603150b01c90300603001e011821982000d0143c80016200c0c2c1c041c0d40040c0100704483d54001891801c2c1c400c3d00302014098030245905641a00c05c0503c0f10328074078088980d1151104855050364104c0c0d1003030b83e8107000c4d5584c0c610344007100803000d41d49031007085040100691525100c07481c80300042d00744007601c0860419076a003920b009507540c06080b416890b000300d074100907035020901da2801c40400c059441d61400c544005d49506400030411482c61110684030050704958500419103a80603040c0a1003000c28591141c0e070740303000d00c175661030940b42c0b050201e40004622500c10310074042c142e00c18015200d005140700181c1100c0c0300e5030f0301441a904d0403480100003502d20510040381e0300103880c005200c1d0501425143c4141c0044200c03d0401d41c020080300da018602010303030030311101191090b507900c000030ae00300400b06000f2200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 737522571 1250 737521321 737521331
    0x10309020a0807090507120203040f032102070506070201051b0405210a05071503020a0503010902030a0908030c04031709033c1c0f08070e030304050a08011d060610031e 74
    0x740855005c44d004001c40d44031141d900c07403921451401d13407000b210024911017035000d0000c0000d001e0300f00381050002c152019000c0c00c0b40f00303500000303c0e00703c84001d0320a80d1000c82403140060b028451541c2112052681784420300c08450445694400c80c071940b03004241c1401c81c450808811748082c1d50703030a050015100101814184160b40704c1d801c0c0101c0703052111000c0c0e1045050300034422100300f24131584900b801c6a1034244468000c2d0001824002c2064603110503000103a443d100071440340580100103a00c49040d4105282c990300c1800301c2040d510030401c810802c5580010303108048030001c0345400c1464040450a41100c01c0c4060202002d40705140c15a04490000c66920010b0103850003d00c038222070140219110810789108001156181c40841e030f0452243d5803031220010003034101d0340f805555501085104005901030616659a1a503050480640b60075031188241148010003c5003840c17400a6034194860642c1b6080c140d41d9241c0000362000f500003101c010708180c40c1000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 737523821 1250 737522571 737522579
    0x307140901030f020a120b0306100e130203070308190c0807020907020a0203010c0e28051c150c0813080d02090a0f03030c0210030c0210020d021303031e091202010309020a0807 77
    0x1b0381406401c0c06407115051006806003030800142c500c1c40703112501e20400c0454a0030400c004504000f0740034840821102c012100961420080c1d2402540b240f0500380c0e54076001520110f0f107601c1d0001c01010844102c2100021030304620a90b482250129023880f02c940310001d0a034640b00200000030b4040d4280840380045503080000f051100c10705488c818101600d511080007407082c4000b00d880403425052051250b81400b441050324401108091111a0b4054030307003045c0348415000b8221441c0d1031310707101c3e450317141c2c40048160042c44010410401c681e0983d9100391901404140900e903941c040340101495481c0341098000b4a2084540600365880b42801040c01d035a566080c1d000f501400090110342d031182c4140e40341304105a0242940c01030b0a4140c030041c2d4400c01d158060b29800b4400740c40d032103982500d800001d40c803a48604005160008001d1950400b2000c08800e000c444202008001c912a111b481810f60910b000070300d00301c4601c002203100d24680c100c80303003038400c20314042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 737525071 1250 737523821 737523827
    0x31101021b1609023a09050106150c0b060126010f031106120408030a09150605130905060c070c031203022805070308040804080f0c0a0b0307140901030f020a 69
    0xc2d050311001c20002c40064440b18074005911446144c41c0c03021601160404816800e54030403450910b0043c08000c0e1240f05d1044181641d0038098107940d680d41d101c10400107607040b01c2000344081100d042480294169464080b0418002041181404480180c400c1840300965025440030030b80481c072925544c4522001064000d42d0200321403040b9051450400c5150034026186013500c4000040c40e1a075640e540d0703605c550809407290211584800c800000101d1406c801c0381144c0b0301c1240028804d00c0d14041001c248162001602e0345840c090705000850070104189074040091042c01741c0e1a0800d152001882525a00290640b0070044040040316450380081079482001c08114034030301156200351540e04521504400810410080107001074010000d0070743c064080c1d001e80c1d040c207030346203006802c0180912118049404c01350180703141e468003d5440001c0c0c940c01c18800d00754640800d029040d0605401c0880c2201c0002c600394109a100e5002080725042c4c0890540d1540443c3c2805 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 737526321 1250 737525071 737525083
    0x9020c071a030f0a0c0201020906041706311e050607030509030a081f26120a02030427090b06030f060c0a030b01020a05032802010204080703031101021b 67
    0x1d1422007491000c20418480441a42d004042c00c16120b8030a8460b40742c403600030004d10f070703255046d55020701c060001a40d07510060002001800c0180400030644c01ea0b4a007080802400c1c0703a034200d1012540e0140d40f600d010902da1201ca42c1d4a41c0e01070b10858180414030b01070307004010707542501c0441402c0401c80003107100382c042c6a907a1428025a200c08848540300d000303c40c01400016071000c00119000b00c0d0700c01c182d03455840801d1043c0070a48511428541c00d41e0543ca218003c000403040c5283c1000410400e2841d0700e40240d15410203142c88802920b034032540c402c036990003031103107209140d0320440903a400042c00d401108001950080c5441070400c80126000c3e4824051050260850030010641502c5412183d4426203403024440042c2c00401d03566408070f0443c49040440000100308100a01104d030001e01849061810480009423512203510464110f900511007007100c0c8200159a40940b50305d414480800c8140113203041c0240604400c0304881008510381c4540300d00b0200d04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 737527571 1250 737526321 737526329
    0xf0406020d02030a02120d0b0306010b09031501050906061b1f0f0e0a061d060c070615180207150c030f0b0105041211031207030513051c0b1009020c07 66
    0x76500914a21103050341c90340645804040540c002d0080000607180510081c680e403814948001088201079010900d040b409801c410300076880060ba010841c42d0402802504407812030044030150305160118000a80c0a88014000d03800881c0388594210541090201c0740403600c111001c60109005018800010840c102403442c6054a05070f6031448c40d000e0750b052103000100400341078403aa40c4940080c00d03100403408851001d000c1c2e61074105e1090080600984a01c0034581e1210804d0030504100d40c805004903500e0b910708901040309408104004046003552280140c035050203082203005078400c12a805103e034030380300b2607040c0140c150b481a2301041a40104202101ea00401136071079109030302440369142e60070381031080000c240600c810140032029050315000c60781059204183e4000a004501080012800c1400341c989480010300030b2208882c0c8082c2c0a442d800070b80c146845898001d0042d10000c03000400951030a00c075000108419202155644000c410958888000c4d0003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 737528821 1250 737527571 737527573
    0x5010c170106020c13020c191502031314011407080a0c020c031e0a080f18010f2f0304091e090503091309060240050d02060f0f040602 59
    0x40030400c80400060a068036940e07001410748500c9034040200030519444045003a039000c000800361204d040c000240307060002101c40898030540d1030603414060460092a040c1407062040000c4010302c01013641005400100040c01c291000f014075003d0316440c2a0b4203804614841804ac41030350003001180f00b410410b000f0006007001050407600e8408007076a1580c141d00c100c4c0c00510082104c900c1c03085d8082c0243c00c03140c802c8000e0792075206a0308240c020700d5180c540810100c090141c3c0d8912520070020074030340030141c496004400350400b840c3c0491440304200c40c0010740840c40e030245e882c440d2061820700b1a506c407540c60804102420a14003030300e0036034160088081540f203d40c0901101ca984c440d0242d41448101300501502c1302d14000c145154586510006012408510081c480c1d45881e080001c005441d01809242c240c52900b20014061200b080d0808020214030f2490b0682d035003110b10740c40c07003001400000d0350390040c07000300000c040c0000b46601e0803400a01c010002c64072550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 737530071 1250 737528821 737528837
    0x2030403110c010e1530061008060303040303050c0102070b010314010c0c020306010b072103021b030a090513060b031006201005310605060402040b0909090307050a05010c 75
    0x1401100d0181366060015040201d00e0405002030004e4405004081548011061417498801d94034040701c00b13459002440e10034450a0002c241441e6405001c032103441e0911403038074100003000c03a40d244198400a81000400306200900c0042901140c284030b40000c0c03640c6507541c4a040048101c01803054001181d031034045410313451409010120a615001005410580c0c070300300540d40654840c5200b180d03038440207143c4010110030303a070401d0300024040ea0010b0301c59030b001d84024064058000440c000e64014800308603850740c4a0180d0007640c905840c0d41040400d1203ca0340003414113a00829504480030080059640714000c0c00d20444120396240da030000c00398101032030b800c2d03410301850300c95410849013814071010790f8100396000710b600e01c3e210885040c0c80b01c2605100701c0d14800c107446040c0700111032051001c10301415400110486086241c02d02d8001343d01541d1140c8149140686158400688150018400d5401e0a81c01c1415110404040c0ca083d6008101024803280407485030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 737531321 1250 737530071 737530093
    0x30f0712060803070b0601110a030923090a0e0f071205060a23040f020a03060c02150106021e150408031e0f040605060f150a030b0d0206030610050c010203040311 71
    0x780254000c5680210286260580070744540c0304200d001080603050001c614030401e10341004214151140f4020f5441c003205030308019441c00308070442c0141910101c08210130800b680e541c00c040d00c0d0400d48585001600d541010300b03841c04d0806042d1182d444d402003840008201154154840d142c0f44940207035921036880c46230b1311301100d2003a40865015510507540c0724210b200c4020750f80c3c1040c0174240f030300b040d0501c0e58006203101400e0f400488085440d00420105160100140944002c1c400d4200c14198140709000755140e001480c91004101c2140f045800b104051108540703007130500300d0a402618003814400d205910a950035000380440d480c007014002041505540101000c0c0100181c075262a155040074000c09080e059000310f10440400351aa2040130f0f18440a85840c00c0c5e540b80d00d40450040c044840c1c0c0e400c0740e40240850f41c0000d0050342c0d9034048a50000040b20000c15006541034200c8041c041c11140324002d6200005000a040d0400584903035442c4850485509503d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 737532571 1250 737531321 737531357
    0x21203071406281b0f0e090c070b04560a2003090304030312020f040e060102190507090c0908030a03020c0a06090302101109090703050603030f270102160e0c040803030f07 75
    0x41165048c40741101400100d0014003c41c0c09607412038000d19038680c0021072410305102d0143c18856103940d90089850003000c0f000ea8800000c0c001c8a600a80c20802400386008074030440002d01c003080c0140e0303842c0380540728052190000400b107514031b07e03103440b840c0c80c0304034507034a51040c001a8040780341d201e040c000301c02c03041c0200c5185044500b0303481e08052030006484c1c40c8240242080741503006460316400940c4e5005e0141440da800f0703d00410300c1900e418202c00845002ca41c110301004035080f0b043c0105000002100c0c458185880c0040c1d0b10640d500425040888100f80104208e040078100c0091503400152520054100364041101c2c810208804406100d0400c109421501c0c010026004038080e07480654403810103403e8038604100ba03040442039a001480718031410740304040c0d03e1203c5c0036041d40e500d4a90030a000421450b1072022040326003013a240700d1040200c4e240c00000b0f000901e000309407030081c44c0b103004030b0742ca904002c00448500d5804640400015113070b452075004d0076113 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 737533821 1250 737532571 737532589
    0x9271401082e0f06030525080d02060f13021008150402070f03030507020309040f0e100c20120c030909060307050607020409020607021203071406281b0f0e 68
    0x70205482c00e5000550201400281c000302804010040d903461001010900500c0007142c0f560b041d580e500000c51540303009035544409074012884c1c0c0d0340b242860303424403500001c0304c6030419107203000c0c800c241d640c600040d4420718a0b154003d4105a81074004401d0a400c05003060140201c0d040c5030100341c00e24820302089000301c041c01340102040b9072100022900a600194120740144144ca140009080105003622002c1d00f80340b00c010740d034090381502818240403c07006020341c0d04003840340c3d80306a07200504440d42c0d00381c1016210b0100d80140c85c41c140c2000282c00300e1440351030007071b00c400103000059101c1d0000c003241409441500c0c0010f9451a004c42d000c01590300007001c40d810000c0c10b4080c03100411a00d00101d03044602004900056650748150804189040005559030101c80c548401c0790a40100700144903403016050013280c1403610904015441c1d00d00c1c1c0e403036800f4905013244002d0004502e04a00074a41d481295190343d612542c2d8480c540b4042c0c4070710f502c410211051240c014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 737535071 1250 737533821 737533873
    0x206072108040308010504020a020f031303060e01051e0c0418020405010305070c02100311090607110a1e09020322060515030708030f130807141503070927140108 71
    0x6813840005104ea0300e0142d015003520303903091044900346a01c050000d03185a10000ca01003001c003240f1810030800c4180e00440007440303030810080c821800c0c0326a2603030184e031400d140d14603806040300c00210350840740d1701030310b008005001703203603080002d81001741000354400e009483c0003074288000280f4841c09090140c041503405040d52000080f8010708500400c0400545020f002007008581026581c0001802c031840c001d005448141030a8000c00050381c8403648030120b80e001d43c92101c40d40c040e85c260f92a08442c81c410002d43d5981c0c40520346222010316403c1d4038606075000b4840d2003484615401a8030614200d404007244100c10381c10181d61303244c20311482d0220361080003024031440d5581c029107202850180400c110300d44801100c1c1c01d01042d5005580d0401d040a0b040f40103140207121105455590851940707581854040184030301464000e1141000c0c000280710040541616115146540140c0810402c200d560104401040a2240c01d00714400c451b040140e118030881e49101e64 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 737536321 1250 737535071 737535077
    0x11040918050c010807020a081306200c0f04020d090f021e0a0312020a08041d0a020405010f0c02010905060a02010e01150518071e020c031e250302060721080403 70
    0x110780b4480111101e11006042000714024880f200c0001240341c3c002c0d0042400104121182c2410240e0003485130180b25900d8900c02d180c0160038005c01008101c49441a1064500882002c0d80c1400f16002c2c1c0320b0500404001171401580c1402d2191451000129a10803620034842940e50b604c03200500700c0010896a00c2018008104006000d211001881b0340041c015902802c9807600c4031030391600305030310002d50001c01d03018031101c000a01c101154010282e440031401c00b420030b00020035942c4640c010000340038498042d482503a014142400003000010011a075843c4400c43c028080e000001416260f982058000c1d2180107a0400e000c0c01d0b100e0160000c480c10301480589250400081c0005082c0400800803c042010811440e01280101c0c2c005080e01c1ca00c10040c1351500c405a903681048819440c0481c0640390b0118110010400240c6040200c0c40d010039080d5181155500c0250302840004407042000304085003d581c0c204480c0003d80c851a00c90340c00d99080d44210b03001000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 737537571 1250 737536321 737536333
    0x2208010902041b0e0607062a0807140403060b13020c011e1b081306090606030b0604110d0906141513091e0302010b10021e031e09060d1104091805 64
    0x445d0a000010b441000e00500010030410b4550200b04a41021220031141e10b01d520038000701c2c0c5941020b00e80350450a60310307222120162003400c58039140900d0100030302a988134203401c2c003143e032511460304100c441d44504641c1d0781415141c2500a00441b100520194807070382065480c21a24031030b201c80c0c000a234005419801048900311203100d030080042c20070b0740d046000040400c004d0300c00c000c0000e200310b6000407071508506200100403002000c0c2803146080a5105004041c520142c840301c2203081004141d00e5068508032020344014800c410301c0c1003651040048902000c0700014503ca02500c0001940750100304000560300f51140c0030307080c0f034044121036a56001140b0400c8a00b0300900c000500d01200000245612003480c03c40b2f40140d120682250b9070b800309004940401806078029483d02001403d101c40103800400d0a03402e2540200711242c160b100d0004540c001c040c0c5031f0040000500c0079098107115042801811082442d298480002440c11400702034403a03000700007841 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 737538821 1250 737537571 737537597
    0x13e070f0e0408042c010506130e060d15061e0f0b070809040e010f1b1e0302130b030901060504091509060605130b180c0307052208010902041b 63
    0x140c403000c0c0c02181e980300d0420000501000e419034104000c800c2080c0541d0b20b41500d00c1170001d60301e040c0c000038400d4000f00a020b00d241039400c150000c0781c2c10203000f0007082d69072000081c0316454075000503164446c05003002d12030001035400740c0280c6100800c660107044028074410240b4415015000481c0102001403151440f041d014011040c4506031252628070000003103030541d2160111081c07961b4440400b500005070034012482c003024025208050714106880040c004c000c94140c804002450000080704544283c04807458510880ba400b01c450743d5504600405600413234401a0651034030701e0100e46880e25010f0002001c0d00110340d4071824056241150040c00d006d04101c070f109642d008001015103ca458803094516407000005801e4808014000006c809940d420401c050f8502004603a11301030341aa90404210b1600036110942502070604074820200482d0400c01107600c00181581c054000395000351080d18103101c0c8801c804940e2102e88010030000700818070800001c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 737540071 1250 737538821 737538839
    0x5040c060203070c1a0702120109050d03110a03021606020403030914060403030807030b0a0e1e0f010302011e0210061715060108160207030f03030221190902013e070f 73
    0xc00988071010000d0b280900a500003078a040a04011003d00c9e51102c108200740202417121082075520342c20140f140c4200003030501c40c00e02c1080701c05400c3c507a0103e8030761303407030f600f14800f00505036030114046650303036100d0401502c104014413035881296000450000c0038202001524101da516458240345511121001e0780900f0a0500c3c03d60015980c01002440c80e9425108501a0f40d00c8001d920708002e402c40789800b20380f0001c020420410340f9000400050360300c41c0041180d8004016055102078028408031300749170b5003403a45c002d038a00f8aa000b10300c1d0f00308076050300c061100c2c9600321403151001d8804840c5440c012501c490100300c0500011341e0402c1034061003040380120744141c602c00364076540d54500c000c4046600341c000903400b190300c009054240341d000340c82020300d031511141490074916001c1080e10041d024003a140d240d09105085902500030311903103140c4016209003181c080352021a0026810081d171081903003888030b203001e907035012544109454002803041d0100381458014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 737541321 1250 737540071 737540099
    0x90403050c06160e0402071106091f02010204050906030c0109140310050a0c0f14070623150324130503190210050f060105031302030c1305040c060203070c 68
    0x25014000c04106a6211200c140105403040c1900040f000c01c40411620041ca03014140034002c0c06540f0400c03c0710042600c405005801210469034103035580e0740f041c0849ca86045090051032108028229481140e4041d00a40f003a2070054800190980d5180d0405941c0c0b101d040d140340c082018500180720130000c4520001d801c000290441b2148192210304070205c0c0c50858020755019600d0001208256200b13201a801400c2460002d40bc00c02e00c0304560007d101c0c041d0000c00559490740020100c00c44144810740340143c401e10b10031146401000c1c01c0d1401c600034401813007400f8520742701c4800a086c00c0403e81800c0e840c00c162207599240c00070359118680c070300825100d0f40b005220108031203081c168045035814041c3d0141520351021008001a03d601a0808541c0c000110402000d6607010f0b054a5001070280d00f0400400458004170303040450f10504581c000703000760b1010040a10b5900501d028901c98800802926030314103007280c6034001c810340180424042c000c1007045420000b05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 737542571 1250 737541321 737541323
    0x20907020309030307230102030c0a050307020a0804090b090108011b12020904110d050a110708180a060e03190302060610021615020105090c0619020102161a0a1a0904 73
    0x101d928020490000903d90741011000b240d408180b01ca0700954450341225404070b40103a04025400d40c24500600c038440e00481c4900c004204012002850b01482003081c000c005800c80300e0a5070b80e1361201946009030013440403080c007914082c0e00010b2101014401c5c0307072031f000711244841e0080c14020030032242d408008417200c0ca041e8003070115000b5a5100d00c82c0c20513144503441ca40d640d407082d43c0342420035600020b0844c00064642880000600780c450202d030004c0d9445945641d4580018207a4001550148100c541104c03102e003000c0b0b070340c0342c20911a0f000e107441141105c1e50110003102a00b1030380c0d050f07003004005805c00350203e0344c40c1c100860010301080d024016501c140682119030030802c076260303200c50003040c0c6407100520b2090b020310403950000c9180d00544946442d9074042803483c8101104103409204111611000b64801e5054482c01d10701040d02c50282d800c00d081248100c9500300c80050342100f8079000c10788880443c46440010790780d50360601e840010000403c0b0840b0b40c0244 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 737543821 1250 737542571 737542573
    0x5070f090b130503030c0105040209180a02280b04170714150d09030509010314060924040e010902010906050406090315020d020324030c130c03020721081e0402090702 73
    0x840403e1951303084c800b60040701c1e1901c000091a150500402ca18220050001e40c1000940d112282461340046155809a6019905001c0480c0b0900280035410b021540141500190100214500d455400104122100842402081c00e110050141c482203144285018841c44054038002801c0005081e151141c0d41f1071901d040c20034100d456429203c80003021000036a0000f000210383d80c2521601c407800c00043d1812805181100c0803592402c40602046c0c01480c88115124040042045103035001c000070b08244103108503440c540e4044c01103400100c0c0828250300c4080784051040d015034040ba1080d82e5031424551840d160588c600402c41401070455800700b01601e00c00700140011030181101d0018018944690004503070040c05094060b8807d42181c03023a03070b1440d940c003400d41d000740d500c04100041140b00d204040e4000c0c810294010309060400415081c031031440840c9203480b12898841c0942d640e50107054121360b6942480c1180c018081c80041005801c204461507402200c2d80 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 737545071 1250 737543821 737543857
    0x2011d01230a06180f110f0306010c05031605031c02090108040312020405090c070b0c0c0a03082502031305040903050a081b0f0d0617060403081504020301030303060905070f090b 78
    0x1080040820000a4140d00d020703121070500780000c10b684141240381e142820741c141005074000d09148144000b030325007070403c090394008bd42032050510440c4c0040270041040740f603040082c03600c0ca8994212000d01c0646005548503030744015040e008845028405a44403405996543c0c1d0543d4010b040c0942d031110036170f0901000c1016200c04036054025009110500d03100d500c03d02e010207100c8401444250849401e0005c000c2ca100f0002d40c02c10706a5045c2042c5403e941c44180000241c0050300c0c00c90650084110002c0c04036401000400343d403103d8001070800c5980700c0007840140c8029a80040000700c0401c040e07804a40b184250b02e07045441700c0d010165035000702c00750035078076006840b2034031401d1000109020640ca80d446400d005002c141011050b0303002c00c14100c0e807980030081010f428040ca6400282e06492002a500100c80300100110348035612400e00800504040c041c0200040c90000801c841301d00501070354400c0481640c0b43c00329241011400780c4143c000c0d90201d06000022 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 737546321 1250 737545071 737545079
    0x60423150711010e0c0a05060c0c0604090c0816050a0507060e0d031509050402150a02030d021602040b1917010f0f1a2e12020a02011d01230a06 63
    0x480034601880342603403404148100350700b49908540c3d048a2a0b24103074130448602d00300f80c544a415000f214000c844070f5843e0441e16440e207080c208044c44250f0302c924001800300c0c41012941c8120080c0c041c51f41d48210369643c0c0d01062070803182d1020300101080c01404a8403009101c0c0005003100303841100042920407200b00150700e0422000f8201001c0707500e40420404544a42e0380b824001e2036292818802418903802261180300c2012140b00c591300d0014081c24400d0080046481c0d04032018401c44d69103900e000303003c1403003007944807c9200314200514424030f0b1806c1304840f440000e80c0e8000011451400d0b1102141c0401000c0c0e500403035491740c8028045100e14411703050092600380b03000c41c17003400200d0308d0000d0000b1100c001e48110700401c1d1242481420203041c03000320044100c2016160b0755844140ea0f908010a110b00000303000280d041f191690641041d800300d0090a12122141011303107126080e41c030601140424084c031226041000401c032040160420200c150008402d521 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 737547571 1250 737546321 737546353
    0x50d06020702100206071814060702031c181d060d0227010801060b0f0a1407060615030c0503060f1c021f0f091a0d0b03100617060423 59
    0x909103e90050303048942040348442c1c212502250f911381c1d00905000181c2050110311060600700383c454003801d8003103088011034808020505442d4071040c51101d00c141e23110f100401c207881d490741000354102090303000902c03640c83c0304040480e40c044109400c1f480e5165801d11400c60322400c4185d074800e80407a003500c0746042d0710650035010003c4140544482d81016203450079079115a01c00305444000f0007401c030640c44080151070b910a05890a903070101d0800d645480075008414000e0013451038080002608140655040c440c1d0f40d20303850611144034120420380304c0b400201d98158001985400281041c44c080c501802400508103101001281c1c0b50085400c0105000c003444a40e0079840610151640050030203c0d0140240b804082503070504040d401745024a6203c40c00640003c01c084000e01c80c1904003000901703024040340c54003031007280303401e028002c00d02c1245400002d0320400c030301404000c01c80798880e0b60001d5500b42c3c00382ca207a084903801080d41950310401d002d03200b20003e042c84 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 737548821 1250 737547571 737547589
    0xa060914150c010b0f1c030503181606020d02060c16022808190f0311030d0e0102030a110c03030f130b01121202210a030b0d320601050d06020702 64
    0xa020000010b00050b0401489020222045410704c13030215041c107800c0c0903098086d1002016070601d0310b40d441382c4507581c0412203d001001c010403d402810540603030601c80c0110401243c45075400c584c039034030030310701c0a031b856078429101d80d00002e070204031860220002000c1d41d0001407024241d0354805c4031410180e803400e6000e200d081c0e011840640c0401000800308801e0249502c0c060b180704207119140e845070030300e000c501c41c01418009030041e6044a9101881559510103080206002003204080c00d18000d5204440da507070442d03d002c141c003000515103004d0302d02c01315901008514540b114030020701001c0000301400c891000c1280007000240f600c11119008107442588182003240034680034441010800d0303050110742c480c00d0b80241c2240c03d0300c05000c01c0e016100e40140d407007421310411005080d0441103182c1013040915880300704070440403000e072110744500c0b5100b64a030107580e81d4503140c6640c01c40301c0c0d5150300c60b40c014401842e04580564007d480ac51006103440e5281c2d0108004507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 737550071 1250 737548821 737548837
    0x16030e0f0712060b1e0409030327060c18290f040602010b0f011d030f250504090804060513090c0e090a062d0812180a06091415 56
    0x290109098001c10140c0c3c040c49008a130304940b82511400c882120000071055900c416228076161000c200c1810700a03401a00c24a04000d100c8030071720501000b80c0000f1403205400c60b4624905106c500680e48503001d2048040b030b0140d51012100d1030321051480e65a07940800403001e076800700c10002c00c0d000c24001001060110202c0c5901c0d507152800c040d00316403403820313803e00852072a503d4100f0340c0e9010004200c2c4112002c1d40300740100790030000c03910301817240703001041a1284409500c02d408034007604600e640800858440543d48076001c2c40203481a140c0c0080900354144024059103001c0c0004c0c050100382111481e40141d0307150040000e98080760b40b4500860345051401d000d5080c00300c4010345c420350190061000c5460080611603008400001c0724800c0c0500451481408004559034000c00c0b60204903100d20401d4900003e40d40d210b600b00c40e07050700f04401c501706107013040715071341046405903122030207694633061011880e890a070b5140c0342d010303180309101401e40d29141e01400070a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 737551321 1250 737550071 737550089
    0x30405151b07091413021e06030a060f0f060207180e0331031e140709050106090603050103030e120c041109150f031b0c010e031e0316030e0f07 63
    0xd03180601000c101d44400d044c1104840c00d00d410001c0f1894929039402d1400c3d4142c5000300c16400e243d520064032080300d0303a0540d0121f0000148543c1420300d800400688606414030b5155035602d0903403861202c2148078550258200d02e004005100c6a502c80011848d04428003007068050b4405103401e40d80003440400810703600b8092602d010520750f0002c100440d020340e49120750350540d2103a580138050700c0f4090121011008007c1d080000420000c4c0003071004008555030b82d5290303000803000d48001d0260b4170001c1d8040d4000074000d8480c4c0034081c1205d405490300780709100c8480921040d46020240e03040c180c89601007082d01900c4511134624001c5c3e0440c2c030b00c1c0d101c040c031604020890150314041c8c0003459052100f0303508840c82c0750460303400a50081c81d1400001241c5207101c81401031045140055107020091160100c011009040700103105c40d200a4a0800c1e002c2c0d409a40800d80c1c4442685841040c6a20954040d9021050000c4283c0803110045da09800c1e1070710780301594000c1110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 737552571 1250 737551321 737551333
    0x703020304030b07080615030603010906020d020309010b031b0108070504120b060a080f03161e0b1e0412081f080a020f010e1521010305010c020c030d02030405151b 72
    0x5000c3e5924181e0f810010700d1030509280e08204000862940c890302401090031800000714850759025403080e22082d6000c0802e54903211104070610003034000b221500421750910b019a0f5540c500403075001d810202007980008105020350044801c440003c20180074401c003004041002903001e540031543e00d204480356981441c00400f401009500d80c0d20070003a5510041c0040400076001c01903580211039a601050240b480d41424400220100c15489807950609551418480c0210240c0c2c80b90406400d107030f02021219008909141044901038480f92900303024038407851103409034542001644840501486c5e900d081c98040112560150440303034481c414032011810702d03402c840042c490908007080c0354010b44011a03094079140c0a80d4840b02e00000c1c860746100703000b15059020344040310b03c0901e07035170312840c1150003425401c146101621401c140301c101850001a102c80d10200390740075608081ca000305000c00e52800c1d1200380c5281e4000c1c0301501e00c040590f0405001c081084009040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 737553821 1250 737552571 737552573
    0x1e02070312110a0921080c0307020a0b0406020c19060e0111060a0e12040e0c0a0903050106270b01050a03020c2b17100311030109050d030f0c0e13050714070302030403 73
    0x2c84c0300c9040c0c0c400b41344071070b062a030f01400c0038034140003c1030a40c0210b41c5565513800c20441a095110f8104001d521010198000c2140b84801002e081502e2140e0200d8030404401c008001040c110400702e060b00d00880c201c24407025100d50406425403006041c02c1080642003402d43d8105503044030441c01060747d4105a442c90076003005004a2400810326603446c082c1015082540914003c1c41000404400120b6080d51440741392020002c503084002000700725200c1001007841d42220501d0362005400468003a4140218803c181d4180d01c140c49862420403404000e6020f900980c030544403c1c05809038903019804aa41c2e044c040c800514008502031045000241c20410030007003440308100d80310100001480754141d5401070b20f4104450007146a03640300040e000d8581390600501d280a094402840700c1c2d050307080100040c40d50310f0140300c01110342c0000c0350704103c448101c943c00000011010612401540300542141c40c0c0c2ca06901041442c1384403803040d50060104400507170000030100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 737555071 1250 737553821 737553827
    0xb010c060e01020c0c09040c090b01050f0309060a050a0c09030b0a02071b0602011b08041e120e040b010201020a0212070f14030304030905121e0708070807090b041e02070312110a 78
    0x1111005c040303620400e03500709600e40c814409024012040340c566900a9124107a000d4421307101c0407102c1d18041c1d41d585c6000b0001c552036050603116030320060300384030109044108500840000c1c0240b556644c2207285036403109030603158050034a08a41e40d08001d5913000c5a90341c0102c00f032542c5040c0c100c1d0000b03494510007d085900c011850203c0610300981c005003a54030410040d0410b07000000c111100a154040b4040e600d003d41e00213000c030b281000088040c4c0d4000306158101a400c480030070072601070400690907481001007071801030308a60f510b021039108180c00340070064007074003100c125100c1c5e40e034490a40d1254024215501e5201104000415074403082c0503001c0d0105075808080500b91102c02543c072040c024000a0410b035156540041d000200800c05c003c08580c805c8550b807a564105840d11150107000307144e425800c08c2900152802d250103064800000d00000c4003101071000e00c5c0314001d410500d03003281004240c0c00c042c5000703800c0b401100f000403082422650365208000000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 737556321 1250 737555071 737555083
    0xc061f061e183c0305030d09050c040504050d080106020601080c0603130803040503220f03030302030a0e190b0a0c050306150903060a0f150e07030b1f021e07050a090b010c060e01020c 80
    0x1003102d030f500c4003010301c0096070100c01d803194160261400315200b035940c03400340d0802d2182c10b100e5410503d2b100400040c4180042d03c84494201c0741c8a1207400e90321a98200c0e140d030824051403d040d1f005509040da10b0800000950744441259048822204255035144080c0d006560a4403282d0010034ad0803400c1ca80103299100d04006070401c0c041c141d00d000680c210308145440013509060f03020001501e01e128603001348401d49405020749404064034588144040100002581d5200d10440050b1102149120f102100c08032a1a198110354030b80c41009440000c103c0440c20780c0200344121b848a45007002401d000c0c030b1400c3d002003801310360031101e031040300d0030202c10b400001100f21080100075918a280c50b003044283c5408138165443c0b80210300300c0356580860b152404103410b0b00703010b015404034642c540310842a4240038040e00c5441c0d01c507590030090180c03030b0f4082d8060100b0411980d0030340c001042c01c2810b06180c08a1001c94a0312001c0303440002c48041700d0394000414940d070031024044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 737557571 1250 737556321 737556419
    0x5030c01020f1209030720061b060a0c1718070b030c03071134030b040f0201090e150405070e040504150f020f041a0c061f061e18 57
    0x85080c8501c5403200038001c21448292800c1c1c0f5040143c045c520f07110342c41103c494069282c09c05444400d4045501e60b1807400711801c901c0b5501c1c003040c0b800000d00c59400030350014820760941c00313517442c3c01140d100e081c41c400c0c0c507200252151107000180480e5440245200700b1683c202d241e200d140a6401400b06500c101c503000ba02e0b00042d1034140d211281404403100740701501000d010f020034100c0041503803401e0b40c00c051f02c440e40500170441040348001c0a200c026100ba83e84851940e6159030703c20440406031081e4040c070b148940a00600e007001d62003d580244603182000880c000c3c41c010400304e400c01d45060321401c1030b580414044050601030313030b02c451a03500c0c401c51034503034010a842280c3c01540600003850100d507448014401c002419140032148090a80c1c1c1c0d51308003a10030307541e00d10681d50010652134031080001503c90050640c00c003600b0030018118a41201a482240e050302201010460751221000100e054408040e80042000b44401003c01112000810003d2080d880d4a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 737558821 1250 737557571 737557573
    0x1312030f090617091204030c1d130303020306040603020904030503061f050414030709020307080117030325090807080f0106051009050d030309060212040210030b010203090d05030c01020f1209 84
    0x710801c100c9600040c032482c16180d400898543c3e40b80c50b40c0442c04e001c10b4000b02010004042404003c0c031000445280455110118807079101404c060f036100d0243c2d04903019440d0719034200a03840401d00a4008562200c030040c00010b1951316a80040c19500041c1c07800d03400504040100a001c0c1000f00c01d40c002d040d81c06065100100a035003004016101d64041c580f0200d12556101860b5101040b0001c082c3c456003000355224500000000c00103d02480780d1406640c0c0b43d210200c01c00720100450307018601c02280090014440a40400030701010007010080040c0750300009a206010301912018001ba0741c05400c0d9645600c030010b0030360342d440e0041441010340440003202d00f17800c60404003c8a40c00d880f8154000042d050560081102c3d090242880d400000d0281491030b01010b070314416072085035200300103401030004030308030392090384100d0259004021800e450302d403003445010b20905c103108a80c50410006442030a9030400d60740206001008150b461540e042042800c0e0710552400c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 737560071 1250 737558821 737558837
    0xa0609031e050616050c0106090213170d0806030f0604050c0102161206090312051317090901090f060b07060603050715050a050a0e040e0a0b060a080a020f03031312030f 74
    0xb4890648441c8060416920896000005000580108203807480e40e10b0500003040b41070303601d0300032030040d6024000d049200ca0100744085075003c01c2541c0710200c07514140042c02c1c1c810302400d00f40d031808009400030b40d040c480c08440441741d20b000c01c029486a4840da02403c4062680d10000e0301d0300411907207642603120100c0050202240c1922070140e005c2d00020081840b021509050350100107102c04a8007441c2040100650400400811013005102c0c80203441303104880100111a4003400e01c10941c030510f540010400564250405842c0010b40d0800042055440c08221410b610119003200d0f0251619020818002c05111a000130b200190300c0c40c0002d04e24100c0100035206960841c4107200001c2200034165110f01990070305110090401c00c00c260b900b501c860398444039414100c81c1c24805e00b00041050402c1c1040398221007100004081e180079070303805c01403051051b030b612035050b1005000180c101856210482c0043c015101103081c00b88032820010704d211050f41400702409140c2e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 737561321 1250 737560071 737560073
    0xb0406050609060915070b09060108070b0901020a060b0a05060711040b03030304030206190914061b0a0504030f0501110304121409060a080402011e021f06082104050a0609031e 77
    0x400f040b250284400c640c01c1ca580d00350400115a103010b4030f00b020b0000c0106c0d2003041000394000502070f058403c240c0858000654400c0f007031029119151600340103800880e0b07140c00041803038100c1e524030307140100300c12255a100c0e0302007580758000f50030541d87e140d4884403002850416206004903030b54207402030f40c514502502d010b5954440501000240310b880c42ca09001564107070b0228540d940e025081d090034214881d030540d40e400d020385d5a42201110425103582e05403e56040320050079840d10360300e0400c0c0c0745490741c40124100080036030349035403070b0310405a2000c00c0f200114800d5220308903000081756032101c018a00800d220015012590801c01d140d240c1e51020b098619084103840c0442055036180b00480301181c03014403010100202c1ca18180d0075a4000c2014000c0000c3c144a014060182040c94000c1c2e86a0f4410f0303521540006440058604c2807007030031a031824150080c1d82c9080c3e510008580302c0700307696100c007000800085d01401000b10086031a6582c0c084418103071010465 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 737562571 1250 737561321 737561329
    0x30915051b010510061416030503060102102a1b0c031407050105092106040803150d08030f10080d120c050702090f0718080a0b10180203040201050c100b0406050609 72
    0x11074001c507170a00c09080700b8002c070308042c01c04644010320005003212803013036030b803802030100d410079103249015005421240902175102e12501040800d410200b48000c80b0364100600505c0c20750200b8003c00a0301554011800d030721500f403080305d510039007d907041c0da440c40c1002480480250b40c85102500102c10421590303078064180c99100e08101c071003c00b0b0341c400440358040604410305000c05030155038100400e01c90120051071203610322100b01d03450034100c1d1040008a0804520003803c1c11403c1c8041114050030340c0c5856888040706012001c000c0c1c172108400d140017a059060380c00a03480d80d100d4040550140200e098172902418464203140716a8005800c00e00010242114081f0340e40006031001e12030309850f8005141d14030190b803429141c000b211784a801043c8195601003408004c0749003c2d80c190180401c07140c1d00c541801c009501504008080d50004d00141c2c1044000e1064542c85074003400700c2c94110071541c50015000b001101401b040d10034507444548200030520801c115a11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 737563821 1250 737562571 737562601
    0x908090901061e0e040902100c0b06030c180603150406232502100e0106050307170706030c1e02030310090c0e13020403140a0302010e0703031704030915051b0105 71
    0x2404c0c20a07201d01c3c00710001050080800d10000395004980703c0ca1110000d070801170b40140e1902070000485565240800d0556584d407032180513400c036500300a0394281c0c5003442da0f2039070481c00c0101552945103150700c02011889050300e082c1c584590380c4444a1003850000c141a02035158180b01ea14589001c0700b1801d022441182041074561014507074510451007401118040c560500080100100c401d00090003002c0c5806014001c5c8921785010a04090074120f44e6041140c1000600034541415800c134043c0c05645540f10038018040006640d04080e02c0403118114960782c02952686010105222444031650001a0242c43e00c00d070855069800410380501c00740503540028860b450228810007881158806490621740f45013082c0c0b000004100c0b0301d00c42d40258021301032540305080030b0340c0341c400920001300400c05110001188044010202d0f61140c0030b41440d1418a03500c81180d4503001c8007010100015400182d01902840700e0b50211200c8918107008114618011000c00c20b048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 737565071 1250 737563821 737563877
    0x1030506010905090a060b030106030c0e0409080405100c0803250804080a05181f080703023405371104090203030d020a02030918090d08060f0301090809090106 70
    0xf04c1d6900081d00f000c11a03040301c4010025110000d95070f603541c1c04010018602010013400050780114182c01520301801100c43d4075130803054080c50a40f0340030030800d00c0000704089409005003090700c1d078045a496030145200f00004c0c081d600d01c8800401402c2e0120101854031f00c2030202d07810a10002c20541015903485102c0703403e0203039460044103103507181043e02620315607100a03004000c1209000340055040e03200c1403511005611307110800180c0c180e0103407149403526580340c024032040c1070b403001090b180f9902c0100804101c3c01505d49655087c445400210541034038900840440b4000c040c131400c1e840a81409981381c0c0c001195101d04e410075420901c0c520540c0c44031101d41c107640c2c0c18000c840f12024040c1c41150380704429800651241c20021260344030741808101d000c0c1095104c460103200b02d881c1e03c0a0160110074440903a10100007800181d040364650451000940b0300f44a44031809004407105501c4845200030403a034080140c01c60403c0202d90a050f50603100480a812519 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 737566321 1250 737565071 737565079
    0x1a091804051203181e0613030507023a0308090d0504030605061203030708100909120c1506030c080d0c0c0b0a020a0b0109021b010216030c14010504080c060601030506010905 76
    0x1940b24038600400b40b038448035001304e26014042c00f01407544041c903a038a040200c0c0b94140ca00c80e5640c00c1e411002442244070103404503604004500061601030400c00ca20a03074100c00d070200c00070340d1142d20100b15540c001c094484400c1100346091507045807007941d100e0f440d40000e00c408000d40c17a00525130b014a110040c181c3e51554081051955460382200c80b500c2283d08490310303407030101c4000b0011082600c01100c0c001c1c0790500400d144c0b250340200001c02c0c0e0803814001d1f69868001080303e081ba03006a060b90640c078101700e018100e503660300819008601a03a140b000d090b0410340b01c0342c20401d0101c42c090a01c481a00c0380800209141d00b503400f01d1b024548443c3e00ca81400c7c00580c00c00030031000c02030142c41150000300f10880740e030340900031902645c3c44014145101d00d0b0f00c03500700e00c030399101c4484200c5080c100c2c41c00a8822015200351602c29003940411261403112603080d200c0c191401c8507008004288656456010800142e20032320920b81440301c0d061000020300612001d00482d802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 737567571 1250 737566321 737566327
    0x40b06090913020d030507030305010815241207030302122a01090b0708070e090106051e0f070803180307020906040906230108012f131a0918040512 65
    0x10302104861141e03040d40c3c000c3c24440c0e09640c0b81c030740200190f00c40801140401d18100001c2100c0c2400140f056581292034100c0c5941d03180c0c2c146c10f00c00c1e0124032101d02040320303158118409a840e502c4490b2201c080c10002032140c03d0561602074142400941148805082031042c0007441c004a05140b403c814071f031514007800403e4101282c09040c07070210182400184000b880724a60744021424828482c5035142c901001203441009031681081c4100800100309200042d107074400c000c2d80109008006186510b000001340c81d84191f500490380944100e40c0110800c0300c0400d0544000d0904061407002c0e41ca481540c0d80040e100140c094000c83c061951101e002082040c9680014005450084500030002055841d0012120b013405900020350815080212001c0b46d00480d28910f180e4070741c20195500030090314042d40e00b0140c40400c0301d58111100040329002800380c1090a500e0002d00da034ac504210b030a02c6864800c0020300b0100106000c03c00c8045800402d140701d00c10034401c012a9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 737568821 1250 737567571 737567581
    0xf0d150c03111902161202011e0c1e050f0606040c020304030503030109090c091401080f15040b060a0b0f21010b070f320105060a08100e011d0109050c040b060909 71
    0x1c45e05154402c40b106a05100c003020821000e85a0700c026114400d03a103032001550008404910610101caa00c000f03d0b692115980000d210b1104d8847e0008040c0c1800a071400e81d612180d20b014028a1844069000f060502c001e81c00d00d4018809101c0d564001585414903694506030340e4441403140c10100359441400d101041011070034540107040010003800000c021080b0325441c0c040078415800c4511404408407078070000441d040e094881490180070556466844803982c105004143c154054000d50000c280501c0301d80181c4140210f91489075100c81c00441900e44000000c0e408400300c0361071030010890040004121140c942d40b00d030b240c803840031040c582107200c619182d1050810b2800d901c81e22405135201741890340001d410300b00034006522444140b00e40341c4105c3c0200d207010780000100790f000417040d8014980c0c030340801c000003c00003d2002d288103290713200d6082c0c07122a510346691005108007088100c00d0b21004803020090203941c000000c006100d84100325020301e035508000742c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 737570071 1250 737568821 737568823
    0xa0f06030e03130b2a1005061c050a171206041e060b180a0e06060f040807030305030402120c010f110102090a060810060305010302010e09060f0d150c03111902 70
    0x1001100048005054141c035180540207903040842d068500d08034800c4041c2140020f0710000d82d044d12154042c06c000404042200b0203400d00a003690341200c40d03c0054840078a002805030596800b031009000c1725000d600d0012022000e00c40d9103013a17000240941110784d28003c0b00d07142c01400407500021240c0a011008901920984144107014600039000400c904d8030b20052500c0f440320801c1900c0c03d01c232182006102000b50090700d410b204c80000081d418200303140201045026081c15a0400384d68800c41e038a40710081d0802c4002a002000b40421820650700300300c01211090050710b810090540002e06040c1d106005800304161180c030106114021b50403103448a03005040c0315a06612040040c0c2005000c0e14403030910120102d000881600c2031107113a050b264140c1d28070030303903040160411640c03010203403c4660080720813110304603035500c00c141003030020310460f030482c1d4090b5182c40507403c45800ea501c9909150031301209032910942501201c1d04046240040810504e50031012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 737571321 1250 737570071 737570077
    0x90d0f120801080c1903030503040c12030203180f2202040b030f1005030d0806150d02073210050903040803030c0403061a0d0f03120f020403020a050a0f06030e03 71
    0x2400d05500011503800280d885090941a103e1a001315000285010140403070341c01060010b44c2ea01c007440704140002840707240191340260040001180198541d1620b6440341d00341041140942c0c4005001d8460090f030503810360f210b200c1180d001c400c41c80d9030404102d1000c4034120108008000b840311200b20601c80e03068034041d20380448030030b403a4582540b8000861740b0655005c034286450301c40000e114500000d0000500240d5940c074000c5803220340a01401c4840d0003003001070481c0511005030301013214405442141d020b0b0362107110406a030f0308a001150b003072141560341c1c10300c0c4503001103032503500040b580c01000c0c503490000740030390351400d406007107014540000c0c0399030100105004941d818a4007410607240541d03030411000c2a10740c102154500542942c40d00240380211420200340060100501e490003800d0202140b1200c5030043e00701c0d0f1a03044521411360307000c1030038425414a11101c030042d0800303403807081c280c40c1004000c42c55a40c0c1442204c08040e02c40181002114050051b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 737572571 1250 737571321 737571323
    0x6090f070311040f08060903030103080f1303120e01080912090d0c090914010c1e050a020703060c1206050a050312220906140a2102041416021c05090d0f 67
    0x203140c3c90341d480b08204120745800d40b00e03496252003508080381038464080200c1e41220303404000245046404d81445002d03820030006000c402c034810800001140c5c55180003103801605980b0f040d440304007400050088403000c0c054210580c49a0f010401506407001254594001242c07c0c0340181c105141c2070080c1c80705500501c090a00380340200e4100054240c800ea5484201c2009020908030b20a044405d080780c010160800361310a042d4070030060081c1c000700203110040c8140c9041d10303101d4803600c06848051025000041501c0e0000c1c1340d103002c81c450f0f10090803049815066542c43e082c0080d5407011951000e501480e4001100f40c0a040c030943c0c20146140c042c002c0c884a0ba94900865001340440e20820b1440c0fa0080d004440c2403402c008810b041d0780f8403200315010b4103440c0749003145d60b13010803c0c00c0f0b07042941c844030310347c07080b80e40c0110611554601e40d0b407142c138901c0c10500a043c14281c030007100d0301c1c41e40390300d0400b2613170340040603a566180150741d01001c91a2030304041d0520503510f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 737573821 1250 737572571 737572601
    0xb040209060a03060e0903090a0302092d010f06090332070b12090105060a0b0309030f0403121e170c1204031e0e03060114030a020a060c020906010806090f0703 70
    0x114102c1c800d805402141c100d5130742c000c0880b1241c0d14000c90b261607100b8800d210f80c0c841e000e018240018079041d007075103411000000704a1582902003409013400c280c40100810406a0100100700b44481307400b001014000925001000c40d10716074a000b030303170059541040d81034203414108000c0e41e0740040b002140014014100d41c4070035034445581c41c4035809039207005039404129000074403d11050143c0380c0100345c080c0101c8490703803901f0600e885c070750000b03401d07000140020010460700007800c00140003d0742c020718003079240c180c1e1840081c0025207032680d01030312070315128191280a0307000031099004000001e0001070646c1c42c80310300d001c10b124490041c0c0c600c42ca00b106000906601803030440f00c0440c0e000c5401c41c0142d0108080d42c08200c085030341030303050303002c80010b001d075907401407150198000190885000100f10b03400030340c0c0e250940e04000006202100310304203500c0d11034000c94020344207007004100c50600340003155482034020200220030070840e0109242521130392200c080b88803210 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 737575071 1250 737573821 737573827
    0x60703021519061a031504020409141017071a0702060d020d0b0102010b100309062d0612021315180906050f151011060708070206071d040b04020906 65
    0x9070b0b110b20072401d8001072041d243c070401041030811032214079884800da0f4a400e0039580e9022000c40c141150121180d00107400740f000044a04c120300412003007144a507a210403a203800598011035010750340c40481c421054095034120528089500c40942c1c001c40d5664030003d041d40300300c0b840b0744942c0c03100a420260010360540c2d03051441d400ba25203601510320601c42c00c5103e01c012402d80b100405099031141c1144910b01005001c1c1c0d00000f0503a120722000b1555102071801c1a49000b65840b40d01c40101182c071504922044038030035035000e04841c288440d80b00c00b20340c0110f4a20200610150004d07075482d943d40d407003c4440b030200d40040410f013140c40c1e28651040c8546010749401c51048900905110104a445501a5481d03200301c0d07070a8a044030801141c1c0810001c012045641c4007800181d140c0f908040030300b841064800c0905031100800f50500000003841d10200034003490402101ca522098021591911341585140450b4085440013544c2e00080081c403507020050750000d800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 737576321 1250 737575071 737575081
    0x806240705011e0603020f0f03100f15080309030d11060103120e0a240c0f0b0601090e27030316030c030b0301090c0801051e071b0209090c13020f090607030215 70
    0x260000800d9030710a541141c01c000050b814862030071041238400f82d0640081a011440c1c100036807000080450200c00801c0c0b646001c0c0b80c003880c0c4142608020041d0b0000280c0c0b443e2401d007000018901c0b405441c0c0400242c02c011041030311010180001004800f02241c0010311034410202c5286099005000c040f0880d6254030b6001c40000c05110021200181d00300140580e010310350b00e2040b69000041840705520603600d40c900c00d0303801010301d81806044000400d071020001042032241035885103044202d00360b2070920042e018400002103c6601c2001088050080c10741d03802d51040a5050104010f4203c0406901802c2001d1903035030550310745441c00041c00400d409440496100c0c0008104644510b40081400400741c0f2004c89071035008004a0307041c1d07110b8113501c045591503203a4400d4a40302c036070008218182c15500a0302c1507005c400409c2c0140740a54411b290603003800400c5243480c060005480550040c03440c2c180c840e400c0403580600b0300d4000c0c044424104c0308109000d060303141c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 737577571 1250 737576321 737576381
    0xc090f1410030c06050c120a021f0e010f02041214010b0d050a11010801080a0b06060403021c0b0a02031012020607060903170105030c01051c060b031501080624070501 73
    0x49100688180260f100d00149080c0610101e0700f009111a0280ca074070781040c1910310741a0300c012141401c51040e441641c0240019844081081151010210f034004520001034203407444c100b0700005040c810841000b911a40903000501c1c07a07030101150340c9400704540054010f000842100780c200350011200030400801142d91400c082c03007240c1d900c990103191001124101d409008540b45640882000310104185000080e844a40109014038080d201e80c00300e80c3c245101c5040f003092035180140c480c20000072040c042d0b4040c0c0620011815440c0c45507040c1c41251091040344200c00d1010116400d54903004100e890040d00440e05102c0210a0701d40104440d5544900c0c079802032203500089540d2501041c40c18401e80c05179141401c0525600c02032069182c0170032010041d647c0c91800103181100080514490801c1500b00d82d00d45400d0700014040c0f08005003110b100d001ca451084a89040a045a40141f209400800d03180d20107490210300400305461025082140d1144440350008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 737578821 1250 737577571 737577601
    0x414190312050103020d0818060d020a110c1c030302070609030c05150c1206030f0d02010b041a0603010b2101031b0506031005010302090d080d0b0108130c090f14 71
    0x4401d81c0c40215400e2520740201c102d4200303000083d1301582401300b010114204002600410100c1030003d41d04000c0c500002e0210f1740100c0c00c40030382c10b4020038262050b54106044515000d124170103006204c00a10005211400c1c90340004030400f0844032800c103051090b810707110001e0780b181080240d0030341c0d4100136001901558080390184540f12800180f070400011250180341100c10b03030f60030124078240030758100d60010041a09032040c1e507018603400c10100700d8281501c0003900000350091030380b814041901c00c01202089100d0150048180300d4880c1d404030f030304540d45400303040e2325030440845d07903510941c0018541456213030610000c8140038003480300ca80c0c5000d00450708824180d4607000d201c0b0340e0004a8100e0804482c0031000c00855000740c009050300e0800600c001031000850351020b0b0039401650100741d00d582d5a82c020740003542c01c06115908810302c00f401002c11000c940e24001a94143d020302403400d82c4070070300606a00000e802003100407107002182d100700e280000700303509694 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 737580071 1250 737578821 737578823
    0x14040902120412090312081510030e01050105040915020c1501090b0315160e01110706080919020a1a070c0303030b040c1805010c050f030a08010306230f041419 70
    0x8588980405800f9004100c1c4004513607024072144c4c81c182c44242d00307403942d0a00600000c100754403001806071a03036810b084e10100f008603450015030004c10300d00540c21a101600808d004034a0710b9040700200d16003101c6038403c4c10b6084030240e600c0350200031660500e0000b080018141d116034001092612003500f0407510304000341e04594006003541c1c9480c00540b01a12030350080e0742c0101c5880003da10401c0e6440c01c211040c1040c0140700620960356203400070035071115000400b01303400c0c0b00b40100c2c140100b10b0042c508030044880c40d2002e4000030401441c52092511503103400942d50041003100040e65141500b0a6001c00c0e5250780e410f0140181102c40f00f814030451038030001100144c0101e14660340301c0c820a101c0300b60b140c2440010356038002c0c90502076074039100e20210281a59004c00007000340d01c1c2c880d41e6001007940b6526105050382e40c0e1441001d00908907403200303800a0349404115501ca610b030320442c241911241012201c00c10b0500c08528180508a07016614001d1000b461500c0b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 737581321 1250 737580071 737580083
    0x1e3f050f030a120b01020f030d0c080c03010503070605180d0624150c0807020a032a080c0d031e03061a07050c190f0e0a1b0c03140409021204 62
    0x15a4a035400e03160301c1450290000b04016145291807100e19510442d080f840c10300448100410341540c003891034020a0002ca1660f4940d00390a950942c80100140c1011500011a04550402000a44444043c041d01c4c0400c0004260604c10b42150f17289540181c1d4042c200c40c0e001216410a040a40501e028847d004040c0013000c2080111005124080700e401100e00300c001102940e007219040b05010080d0b4694605100a1015035100130441005503c00c1054640941120440c020000c111074004005a40740b040c0400542d500803441410480080352250060762152030190303884100c40c0350185440c103584420010140c0c0650203032056034080e450b000061040410501814422008018036a4011052a0703c80303007050f003a015030010b001a41d110380c068907070500034030415081d481405050846800e10045d82d86a10410303041a200c8844403890720700c41c40010341151a50344000301000005420554402d2080040c0e0300a061010720655540e1000c0704203c0c010401901c090b102 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 737582571 1250 737581321 737581333
    0x7030c0807151a10030b0a0317070b01060525030c06050906070e0d260c0307060501091d0d080711070605040f06030509120c070512010f05011e3f05 65
    0x3c4030345000c03030520520005010f01c0600c08a5601100030300b88500200b50015851a00071000484803d90b5010224030300d16625101d100d28141041080010790202c814040c00300000028003280701c004141e1030010441184101d840380c07804850102c0611000b4040f0340c0390000f4005038010218030742c0e02440c42507a0b59854901003108004a0b071040000042001e44000c1d0510417a10f0030030041c00b8086110503000741403210b081000e50039580400400c030351403a61140188103240d1207120301d500d48966070740101c40029105054680d10154101442e052244e0f04c400074008510820b42c40510b20310328400d0320301180d540c22001c2c029402c2405062064511200c0104086100e17101d16489100d0304001000f050b6685400c51103a6030010a5400860141e080c2c086250341f2000582247c88010034000104044801d09100c02c4802c11781140c0340002e01101241180800304250405850684450354441d01d007060320201c3c54100710100389080700003d07540364840e9041440030001e15015070241c0301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 737583821 1250 737582571 737582591
    0x50c0d050a02031c0608160e0a110a0305040213020a0c050c0d110d0f06021206040e0105010f060e0d050d0203070b0c0a0804110d230f0102030105090c07030c080715 72
    0x4841c0141c6034a000103a10501407059041401540c1d244824202c010000303c0d1600d400c0501e0070002d040c40b4801e001c0c2030300c100c100704c01c3c000400441d911065000301044802604001006d6034441c88003501c04064444000c02c06540d00c040409411202081c000c540d2450385030300103000782c54243c10503581806010b06814860038130044440045a004140700f403070b00c41030f008121401d09107030010740d48031410b0003080b4005180d5200400b00417010b501c541e500780c41e01200300000c1c1e0f1a07100c00e100b40359043c0b00040043c640c142900405444290514003816840500440c04144012802401500c10643c44030701543e00480100742e0103024000c1e48109903180d03001c20805200b050000400501d002d0001800705480006010998030300529901984142e5268007603034018140b40b40a910310150f810074107201d02049003a00c540c415100a50031580f41c400000c3c1402d2000b40001200440014072004152048159013213190b48150400c2d01c5084070700b020004162131400c210011403805c81000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 737585071 1250 737583821 737583827
    0x5030d080f06090c1c1b05071a0a02091c0201030506180f070311030a050106020709061202120703080c030702090106090819030e13020d0c0503040308010308090d0210050c0d 76
    0xe22909840e01c0101c0d850701c5960034070800c00c8005045a034143d070140240c2c02c0090500c3c640c0742291058140c0440c440405c03100c1c02205010352a8003000744207041040e1300c005140459008003d40f5503420754883d80c2d031815487d00c042d205140c070032540300240658a070074021000c803103245001e0007a80c0c2045241d8a41080c0b00301d41580c400c6d0a00c1000000000030060610200166407000030307403901052120101c054809503801c203035501d80a898403080140003003a0304101440040005140512002c0d00c0c0c0300712591800c006c0c44000c0d000b10180104403902682c108007580003113a1258881e50755121208106850746c20030f5401328441c4110900002e4003d10914189080d94141005031800039942d4910207a1400003403411003e214440614106941d109002251a5620060056a1504950b14420031140c0240c1200d091240500912000c2544000380c0d9044d03c0d40030403005da840d00680000380150b146150003d44c840b9121602054035640301c4060b280c8181c261086446040803d0401c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 737586321 1250 737585071 737585087
    0x70f0c05090c0415020c042306090c0901052a07090623190801110d11040e16030e160302090a0603020603131103061e0903040f060c030509090901050105030d 69
    0x2c86805106000900841c5108022406007100da030048404524072200403d00f034070101c61540030a05601c640c10440c030310607a02c10950080e41200e0b03036615840c00958048132030041c000300c94100807001c1182e026142104a03a480c01d405015001105d0340c0c41c00318010754072007981c01001405400c01100140801c91940f01e00040f400c003050341c552100d150810f00403c0f01c507901c500096034180e9100040c2080c0c084c840e02010b40c85a07901c15a076007804046c0714050303a0b590040c0100c0038000300010440d4641d0300c11510b400842e08035100314841018002203024010140014800f40254034900c2c13040f0322001f0135807045920a40b441c04850340c0c0c002054045404c03621020303400000800c00a10322041380c00c0c64603651841404002810040c3c100401e207041d00490f640703800d080c0c1c1901011100c0e000c5a140030f500c08140f200461070581040103000e5590740ea48100014000c0d807070381d000c04060040742650310128016040e100c05240180c5a28041c04003882a00d020380110302018500c640f24245c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 737587571 1250 737586321 737586331
    0x3020703020c04050c19030c141905130330030c08061318060f05010e041a0406110703090501080702030f16050a0f080901090b0408061501090b070f0c0509 68
    0x41c1c41070b1100d120a000141c60003c154a08400c3c0030000b81d00c83d100310484c99071017011a070b900042c04800c1114007501c2c60303814613206c000151082c0310010000480350120740c281111441c040d600c40c070814160303c000c03810681008080904c003214000348080000310016200380c49500032403020080860a408941981e540d0100003868480021301506240405403103c21421070001120000103c208941403075200007250010f88603070008800241c039004182c050300c001c08006025080560312140cae01c440d014641000c0590700c20015090141070b9210b9038605004c6503117640d6820036032900401107904d40c000c0c140890f4003000031805c0d182c400810f40d809100001c1c000c501d4865030343e503400011b8511410403111817240c03850560000c0c98407200700907010711600c9250303152881540050305141c0c2a80140000c603200780f00800807003a00290007500550003043d08240c012160004944805840d0043d28960341e0010b842d030200081061900400d5004a40c640891a03c64080000325a01038070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 737588821 1250 737587571 737587573
    0x2190b1605030f070b010e061207150e09010e160905030c01140f0f07060515130c021501081f05070921151b02010c30090c080d0302070302 61
    0x300c8a400c403410200303044541401002264108401c06120381019484460201e481000f403600401115004040c0c20b50002002c542c1e088c610154841199524202845a8100056000441080c00740541c04e096842c00d0080c01001443da1a540080c010003002e80d4150f101c05d11603600000c0444c4560745c8102a9000100a0308003050400700441e43c005080f54080d58250302013102880b05920000104103051003070003807984545683c00c14500301d58009216221114540c03c00d401d5680e1a03c0c04001c40c0604c660000524010070b5104910307244e00384440e00031060500c0d0012076640e1000820000340e00c00303d02d01140c0e84030340c070b41d405080e036000340e03038000c080385480f0424007402d070200702e081801f074010000b0f0601c50091912204650109400642d104990704d482c019045543c000a015026455000920050742d03420802024414202081c050421f004485070407540140d010350410305200210500046815052502c0c2c0544503220744c00041c402e80504400e03032070083c0240c42e90160150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 737589928 1107 737588821 737588827
    0xa08011a010207060c2d06050403052a12071a040c060f210c09030204050c030f060d0309210f0c180b0a12020d08031302190b 55
    0x68005100304400c0d0f050314004116440304528010503106c1400c1744240f01030b50301d500c6980c0030610090903103080c1001d1005055018001d0005403040243c00142c2003001c0c83c0b428100050440c0008054100360b004c1c0c4080e596a00184c004180180507449409116090070b00c8000000c684c11148207010681c14841164031078404203203104a414901c803003111405040c0503070517038089401440d80c1c403008a40c07042441840c44000545d80039009104038205241d0180150300200c5801e1341d400d42200000b4640c1ca403001c0d9418055405450341000e590501c211925159046c001e9050b041c1040c5101000040400b030840b0043ca0180000300b15007410030b42140344030301d4106004141e041c01c00c22000c1c01c5540340c2c12940125021080501e0051f0b50718408195404814440030b04005004406c10952414102011034101e1084409581440042012001a81e8a8001c0c40d00c421018 = true := by decide +kernel

theorem cover : BRFrame.Cov 737410071 737589928 := by
  have h0 := BRFrame.cov_init 737410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 737410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 737410071 ≤ n) (h2 : n < 737589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
