-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1523
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:23:39.609585+00:00
-- url     : https://prove2.me/submissions/d174a74c-52bd-4046-a0d8-c099d4704b25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 273741007 ≤ n < 273920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 273742257 1250 273741007 273741023
    0x5090c0d12051603030e0d0804030e040209030c031e060c040b0409020c1501080d020f0c030d0c03170f010504060902070b040803062404051002033430030c0c 69
    0x114004900c542c084803c0140080c05440400d002842c1c000c005082118a1504a01039495a8502240b0072116103000341d4040c0d403403401c80e030744540030840250f005c1000c0c59814401e0403503030652a02c1c2440000141e00364590a1a80e400d650a903441c14040002d00961850700b003000140000008003043c1d8054230001c01005840300003007060b40c0d20b4102c0d0070b5650141c14502400006805200140d102c102c000643d0a541440962501c070700c0d5550002b4134072580c907820075454000054860f0f1000c4000c1030192a00d02d0201003100d02c1403001d0300040d00c03100c8500443c14014810b6041500a031001400c505000314505405500c0c1c00b00c0201e40035100528402000000c01e001380d4800e8a002e240e00c000c1125a01c5494140349154180d40c0075200e92030103840300002d940141c41c00031050b14000c00012000c0440400700905d43c0013000859459684400100807030100412484841440041046a070031044558444c695207065880002c5220806040640d207500f855031245004d20482d03400041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 273743507 1250 273742257 273742283
    0xb0a09080405061b1b0f040c1b12090b070201021e01020405030f0703060c0302161203090c06020f0c030d02031608070204050f041515050d02010c0b091005090c0d 71
    0x301085104a03402a41e20000214a0b46440c1400740e01d03401609000c08101c0304062101c0c081020070801070340c0301640c0110000390f6000b4604190300111650011403030320681c801d030130b40c0820990760402c4006484d80d03040e56610300d201c19000143c00740a00f580410030307801d00007240c5c0001e54506000304009104d44038500c0b4111902001d4054901804c0e00078195084540c3c40844540d0f03448140c88107690582c280784020010a00070300c21100220718669900e000302c4c401d5210030600484d00d43300302c2c0800d917603002660007040d82d04031210041d01c0654050240c40c0c0d0703c003018a03c4c1c600b1a103542e44c031a4000340c401400316a0004101c0b424010042c40b50f07414140c003400d0171840d40c0038085001c0d41241c02c01d0100f2081107510310145120710703c10301c1c8107021000c07a45103020442d210481603500000603002c0c2403000d841c0010b120904e052051614044000a1399070b902c010324403d65254040d03522242c1041070315800b41c065254410410402000032400300030028424000c0c0701400341c015901c03404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 273744757 1250 273743507 273743513
    0x81906090f0510020c060a0b010509121207060902040f0b1e0109080a03050405010f020a030504030f060207050f06061e0306150303040f06121a0904140705120309011b0b0a09 76
    0x50140700281c01c0070981d200800c80d9a0f141000e580000e03d6803040f401006c00085c0700313090750f219141802e117060756036070300b05035603141030010150003004521028482c01c101d00e40304031840c500418513103108240115030442144140401c0d07400b83c207007503100181000b4801103543c4880c1d076070400000b5004480203124503203000503941c12420740c00404c40e6004800e02c003024950008001c04c125142a650009401c102410813601c1d000303440802800030364104001c0021960b0300310b030f007030b001030046000600d0292140d480e40d1420000351100401900b2081c00c01560b4a441e025a0403005290101d5480c0e410900e0300090b120000244020348140c100d0010324843d032002c1044d64050240c0e1103e0b007083c1a1203000c040d00201c05403810141e0581400d1076880143c01b101c44611001201901240e420384039641c52440c0d0621071007180b03505200b170180000d000e030381d040c540404400d180b41c0a540c0e110200c2d4001411103810a041c054406a84c2c14031900180e40c2100c402e910a541c1c0030000344181d5507203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 273746007 1250 273744757 273744773
    0x70f080d06050d06021806030f010b030a0b120a02010905060909162c03191e080d14010906120c0b070f0c03031701081609180602040f0e0108190609 65
    0xd0415a040032403459010f04021076070380140300c000340c0640c10002e1400c092042003018031048600d40c0d40e034100c00004001c04440e00303020716000702c80103201040748065080480e0307445e00b510b03016040a920801e60b000555070000990710140c00203941107461303d1045400302d8403444c00a000780f0820900250150383d070b107200e448a11000038004d060740f4810349a80d4101070032621684086c074840c2c01115404860140d1801a80b0581640030b160185800000184405840d42001c02500c0002c01040440d0500055100d80c00c115444007921400075414441880c08072a859000010203540800c1814040703600c18007143c040710044c16140b070791480c451070036102c90128050700606802c0003800200c10150852403000d121003610540900ca607a032901010341e00e070b400c0c410700011022000c1d000c0c083c40c0b2050700120b8440010550501c01d002d01da40c0c0356000c9030b11552000c43c1c80c40c16500203005060292003c40d004094a000030030840303903240107049404555000c01840103580345010002c01901c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 273747257 1250 273746007 273746009
    0xd0f1116061512060b010302030601121a0a081b03030403080906032e17010c081911030a05190501060219061d0f010b03070308040302010f1119020411070f080d06 71
    0x71202c842c080582e075440d52441c5034450001114144c0c18070304000d102c0d5119100f620310441059540d60f555078101031181c0c2c000d0030282001d0340c450030040d05110107030700c4607540700300140710000040c190a0180003c40c075800c1408018248244c104000c100042107030030041c0c8020b80401c54031182d485c1c0307581d40b503c0058400315500301c498440c0310210001c11080360001380c1c216100d1803020b004010030102550b0032a101c85210402107554103000c118011644403c0c114822120310000840b1180d0041e2207001d50000c07554001000d032120104407410340c800c40c440c04120618501403000e5410088065103801c048036514410001c007030014414090190040c201d000703690034001c0703050074802c040076880c5c6003600001c10701c1f90b081c500448030318280090700d84c040780e401011960401d410b590045445008d5560500100030100302806105171040c0105c000540400100d8900c01070944148020b450003c51000043e141c00d1141d10b020410b61045111840e50041d91940e450644401450003850a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 273748507 1250 273747257 273747281
    0x409060e0103030801090e10110903010e0604050d0f05030a0f0f0e010b040b030703020306010b0a0207170a02031506060d0c090f030305090918030a0e0d0b07050d0f111606 75
    0x90000014410303540c20300190503039000360360760503003030ba2500c91920541d4440012400140e20a804280d1200083e078000020740c002106141d01d80f1031060002400d54400001030070b8103030816800d100401004010107108403031103041c520600d4181110151182c0801800c04c1d038035903120b41003d090384000742d21500402c3d00c65170003041058803e0709000d00a01d00b501040c0e0040e45444039100c00d07440e00180c030008503980280108002c0e070038201010030640000c0c011400b0340c810810007148001007000ca00c3c010000d150000c00c0c0410603801003614101214400c4984001c6007414440241c031a5400c81c2c3d8809420310b40440c20110810044500f9852035120618000ca800004410543d104000301007040c4221111500340d00c03585851030140401016140003a401084400f0510340030b00110310961070b00802404e5051020f40b5500350704201203481c10006000081c10030120282c80c465503890103001c0c401017240c0700601c0b41030009071081101d007800e03070f0815034000d008112031030700009403200c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 273749757 1250 273748507 273748511
    0xa090309050411090a08010218130e0d0c03020d17010605130312020a11040c05030f0a0b0307090506030f0714060d0f06091506020a210507051605190b07080f0409 71
    0x7030f56034112850340c1054403d0f40c41025030b1100018040303814000d81c1c5440003241541d0780510b1a181c2001020210350703010754585519103001004a403020711642d8500c0c0503e856841088040c3d2600070300305020601c0b5001800104480d4002c0d460101c400380d4190b030311030f080c113583c2c805018030b4030b410711541ca510080464101143d40f601840c3e000c00d0500a0718800d5000060542c9480c04000a03114004c0c3d45c0c50000c0d50078000640d622605107072294024201d001c0c00940d115000c0c000c24280718040d08400d07402030301c07003041c05040c9c2400c124848200c0c1d5180d018000140c1441020840c0c40c0c140306000f480f40b5004602c0303064400325a88a9440211011030803c07002c2e68907582c5070050001403002c030800d0030b5a10030000c0c1c614008134802002540c080d06201d80f8036030b0040b042d00800d407051100c1c4100b00080c0018170018001b00000f081c61040341c13844006542c40c000400400d0b1f160004000140e80f8036550420640ca180010f503186580d10240c840c1d101d90006507a01c40600499200d214000c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 273751007 1250 273749757 273749771
    0x90a020c070321090b12180f01090b090c1e06040905091006061d1003320105040c020c1201180f060b010e010e01030c0917010f1407080a0903090504 65
    0x182044450a003c540707010003000c900415006a03040410f40c070803540403400801078022045040040c90b54040a14480da400300e40d04d5007003080c03424000c04038651030340e907484180000380000803000d607a111503102c000700120303803103036003c500d9020400c121925180750101c3c5550b001e035516400e450151150303440400242c6017100031141d0b00d000188044160524080012900c2440780d144440e10310103041c00c88440d40e0440c41880b80c22095400c2844c20540c0d035101c2d401c401240f036001030708001c201a041c40c4000025081014415070103034003951040d458035154854064000c00c1b80051020700b1a100c001c590004062140909601c09425004060030a0540c080141c140010142940a0f10b01003106110080041d11071f02e04042e50f00c0d02040d0f00c01d0b8242801c2d840303500120810009483d20080d840d5031080d4011000b00030300041d241994442004422410481c4036402103a45089013550403401d11500180201c0d402030307e01c2076615250f050410516004010a800501e40640200184 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 273752257 1250 273751007 273751013
    0xf0112140f0c030621070306060801020c0c01021b090c12010e090f01050f0105041e0509030c100902090c0f0f03130b060904031d0d0f081c05010311090a020c0703 71
    0x1510031200391801c0c40d442008100c00340099029280303d0b000152a0150100d10403004d44840c8480744601c0416110309040400003500902407500180207410004da00c0780307112550b007800c28010803101030465001c0c400100d13040304000d002c9501241e065032a80a10b444d041c0028406114104510f0740701c54480c00001405510070100505c03c0309518207803030255040d01d000e682600c2c402d50302c2820800c440b03130061160f49001d078004040309055200400d040c80a010348042658070803281101e240d08041260200c0b00406e00000c010f51020389801c208100b81540040c1d003200d00981641440e41021554101c540c00303403c2142c0e413410702101e8041d12840d00c41d4800354175095080089030895a0742022446074188038000e00e000390345c035443e01d4242075103c680a0085c4030300780700301c143c0c410400d00c031101c0070a0100c0c1000d139129005520342690740840100c01c4240f03c003152110601149004010000304d00700114004001c002150410885d0301c840e000000a402140c020143c68005c000d800010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 273753507 1250 273752257 273752291
    0x1c0203030a090e1003020d120201200a0f031103041101020a060614040b030606100302090f0904060501140d03050409050411060d0b01200a02040914031207140a020c0f0112 75
    0x1110f0081000030020b603500b0810040d810703018400203410801d21201407000400900500c484007071a0b1000007480c0c504000c1b80100d101240100480480300000e00d04011075002c051b0100b00609030a05000407080c0340da01302d5071407100270000341039849152810303c42a8800d1240902003900b160080c030040b40c81c0c0307848403911382203884103500c2540351074000702c014180400c12a1051800030540103024a40e03079010360103548800c000c20b5010031803880b0001c840e6030704820a801b0b2805040001011360420301007118514081081610401c0240308040000c0c3e40f21048500b55183c02c90003150320340715886d02c01c201c0c4081e021750030f41c0300001040c82c5419046540c003081c1609426a50801da44001d01e00c0510629100100d408194200d000703a0405804c2981200d40d0903841410010b00070300381c0e00d118a06540007001e80c0540c01b004c034028402080e0b802070583c3c0b200600c980107580b80907890304001e5650722a99080e14080d81440001d10402d03801800c0b088aa0100c015007444482c0b8042d01d0701d09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 273754757 1250 273753507 273753509
    0x120a02010b0315041a04020f060f031006030e0d0c0c051c1104060b0409110705011418150f130203120a17060607080d0e0307061d06070e1c0203030a09 66
    0x30103446500ca01c806203e50704884540070f40d8200300714400d4042030740120031030040d00800603600083e003d40e00084a481e03040050002200141d40140c6908243d4000f1600c0440d59219208041c1050345c9001c0d1307481c010a08501c403250328101118100c01a1405046081803a44902d40c0008200e0484e61003001012030203442512400540845104410800049407514040c1c50718902082c0300c1400206403e501c101c002031440c446482c2090000c0d5503060a450310b030301c1210404020007040c491095011880582517040000141c801c0d80c20310f032401510038000903da68224140903000c00c2c0c40144042c4401150303a00901aa090400310304540002d0354800c1039190005150040304444001e0728600b59401031800401e0070340f0305415500d1b45a080e420950f003000011381e4070280c1800100040004100701885808089524428000103d6050301070403525011a0051020400015885601441c0c1c04008403150b0010540b500303400604108101d800030740600c40040c2c01c1d2192504030000300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 273756007 1250 273754757 273754759
    0x10f05010207060f2f0d1e050f120408123301030b10090816080309010e18010305010603060b060c060106230d050a05061e010f0302160b01031101091d060102120a02010b 74
    0x2541d030000c2040100e034201c0c25183c0520902d001c7c40300b03298070a07104070010b15401000300070f858103000b00c110348902000c0e000e0b101118003010005280c0400c02580340860b030303c5902481d40b580101c40b4104040e9814140785040c52200c0c1031611842650781c042d0b07104800084014010091100304810040c240901d94052001544581e011035101d0842030301000d000d41e104100135500b010f5201d4019210240c50b04031140d4004043c250b4591202c08000d04107000b18029000031902ea031542c100001102c1918001c03901400041244403000c600001341141180d05a03d041001080c20403d5196546441c2c40401e04109000440103000010303030300030341d0244e41580020032440d15a04c00b0000c0c803c5500103400740140c1c0c800066407040d806401ca00c1e40c1518a810090f207841d03420096042038800700b40381125105400c2c001807041c040740d6401e0b40381c4143d00382000501d1508200950020618503c010107513807540c2c000049050f4400c0c0007110380c02000d0084c207502c2d01085103029000c0c000d45d81c40b036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 273757257 1250 273756007 273756013
    0x50f0712060501020a02120106180c0f050301060e0f01030605040207030309021c0515070905060403080d1a060417011805281703040606030c120b010f05010207060f2f 73
    0x68090521612422080b258142c00404c80d4801c42e500788505845e1400361038040303550320f07803001801c00c0c0d014015043d030f8030720342000150004407000040c1501001680f0b83d0100301c1c061005101d099040004460000c204440260b0241c049200482c080e00c0c0c3c0d50489504680041016400c15170182c204401d640e208036810041411010b00340c101081102c0e001130417540c4600542302e4034449a0700a82c1c0c0143e440d18084945c0d81d2998082011039005902c01c541d44480058002c010910910070b0a002469040c0ba00d280c0c05203034000206c86005502079080742002a08003100b0341c2c8001d6108840c48050750130480c851885030b0605684030a10381c18110400045041024a502095003c44120a0744084824100820800c6901c25070704001c0003251030580e035080120216441c0c4907038a0040900083d445a0209946000b50748404103038840d80c16800e10782002d122680e008204442604c0703907407421400030030603000c041342ccc250101c5524a40302c81d580ca40f03440301041c403130500401c260004411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 273758507 1250 273757257 273757277
    0xa0b0a0302090a0e13080307020106050307120b060108091e01141005030f03070b01060c1505010b0a02070b180904020d0c081e0f070b0a0c1704090b090403020c01051b01050f07 77
    0x81c004409421680b000750717501c020624800203114240515013110843c03000184072611180464501449500039400030300045810408000803075460682c0000b007880c0c0910302c2e0400c00561076640d1006400c0e04001418002e4400110109600c0300d1400c00e01482c524141e400c041c130000384d12040c00d02410303000e405050030700305001c040001107511550340850080302a03860604111500c45410101701c0c1e00f079074a1041801415400d0107443e020341b411701606940c0741c5480c400a49402c40305c7e4051001c119003400025000c1c005089040c4030f02c2400d071034010700c0b5030342c40c4000f44803003e18100c01088840008004101100c0002e079400f4141100306008100e0036050000e56522480a2900307501540035100c24012a1121400b40185100c14101003803407408941e99115103464400724526802404103040080140d14011540302030b80a4401c07207524245070700d0080d2114078a180043c103103e8000f40c40c00300305405862206100019200800c00c038100b5030320480962109542c20703000951800380c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 273759757 1250 273758507 273758519
    0x41a1504030309090203061f030b091003020a260a0302150112020904062703020606100302030907060315050a0311041512030e04020702190f090b100e0a0b0a0302090a 73
    0x4100c0303040d42e070141c9030b00f000c49152841c69400383d40020507407a00712507180d018400c0c0010b8420726101840d031644010450009043c188500c0d0523004044896100c1084000c001503264010381c03e080d5941d5083d075015400904a124100c17114603c040581c0348100081402030541c0814909943c41c60b00c0d460440e542d07a40c1c04040400a20f00308080d61203060b01e4042800941d890303201801500760358410b1f0b0108004400e840024403c80300c01039005d600070108124480c81c0413100c005505001d130034114107605100d9507803642c48400d0b020303440070b050361030341a00c220b03c40c0441c05000526004101461f210b48900e40000302900701038506008508109a003814007001e000780401781d40e50384a61408017100340d24202e0340b40c03402e05002508290b003007050101688510022000824035a026001251b25080081d1800b0280b03034000b0300d40c10320b0413600d06004d0340ca058401121070202e02c0c044005600100002e00c1c1c0149680c808103400c200068020009905074024080c0b144044600e04182c0d6a601 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 273761007 1250 273759757 273759799
    0x181e0a081b06032215020f09090c030f041b051f02160303020607030f0e06070206070f0305090a0201050a1806020c030706020105010503071e030c0806041e02010e060f09041a 76
    0x5110040301c1a003045500e03404640401a06248900401c10760940841d901005e000726030084551342e1b00f5240005141c4561700b00b803000c1d55088801c0d039182900d14036002d0b03070003000c003900500000d1100c42d070030040307500405070000410098180180b424091012020000004107900c85542e400350041c44814003100a684254204076030301600a040300740d645003011402001c0052900000d19980c0343c1680344503e04101c06886003030341c0d40042100707051595014041d611140d14142c20113040508201c2c00d01341c0400d10030329581d42824642d07119418210250380000c01c1e003012226000045000080b244d5001407a0700080c2802e4080d2288a0b80741c0c04124280c5a09014094243d4030041c2c0c20484190441040c0e00c400303d00340040c500b03540e1a0354503107101c0309007544000701070350007902444103100d1140450041c41b078888442d074691301c1c0c403035001030b120640007846075104e40380100f0421207961420048543c5024001c108100d040c01032650130134080c0c42c10203024010621508040d40c558040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 273762257 1250 273761007 273761011
    0x309200310050601020307080705060405060f190c051c060e06060414090703140f1b0a0e12010b10020610060305090601031e120804021005181e0a081b0603 68
    0x50301a18034200c032500740d0000340201900650440c0300c1080804045601880500312062081c00600300070704081c20710034541381b400ba198800324903540e0140200070503018569007099034646008107941e1510312041d03589000d416000950700c0924100110102d08551104064403c1e8001e0007001b0307201c071810300083d4001c0b40190900c4071003094861400d86001e00f100c032b42c00352040c074000c110340300200e00e0000d4480040e180b4400c140c00030414805a10310068400b000305145c8a0114207140b6440e900410850070b04100c140107032941e110190440c242900982c1d0704200160221042210089000b9503800c3c0440303001c248511081c0c07010400320b00c68002d1340c6c021030310140100050390279a00d0355521b46014030480c503001c0460b030030450300148400100c6440300510b601ca8203101e2819005101860b10303491444000c000b0100a0703280920070341840503540c07030004e403104c01c1344502c160072840d0140d80b8120460761009a0742400102d150700000d1090100c0c030b109030841c54a440407418041035000c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 273763507 1250 273762257 273762259
    0xa1d0c030c070215040f030c150e0f0d150218120c150c0a0b0a0605010210090c120f06020c010203041209030b07030504050313032102060417091f030920 67
    0x8200701c00409450000c1e07001e401403840c40100703890281c0e5150011a06c03c440e5008503440f89404030104481c00c1000768691807060141070101910148000203407492a03c0f95109206400c0700c03d00c00144041e07240c00d0032058810311011540d0317810b07402d500703103250140c6045c0701e22371440c0b450b2500b040c000100b8441c600e0200a4540c050b11030026104640070781141610401030b1281e02106804164030b0141a4080c0d0240040010020b040c0400241070078903d84146035070b0b40c240286200000c50340740d03000c0100c1d00182c2e080c280007049440d000720700704500da0004c0c00490010070384580341d080640c000c5004174491b422680d1480154407069401402520000c1c01400480c03002550b6540617800c0160300c28810410b5a203403882900d400807504049420654030320110709500c00981c020000e54801e02843c03400109480c1c0b4140d41c0d48080c40101800705071038640c0205040c202600d541007034000015400300d112610010114004004103007610040e1107180080b1440b016411010070403a000d450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 273764757 1250 273763507 273763531
    0xb01180b191511070e091507091409040b061003061d010501030e0607020604020f061210080d020111090418020904060f050106110309010807201006080d2703020a1d0c03 74
    0x12074580017031038880004144050a020305010b180000311914040f034032034420f40d101e1005d03035414400070462881150075150301503084031702480081521300c0c0026502c50070403207102d0000e15000c40114081c2a0b507501c80b034045040c040b9000c109160804015058a80c01e03079040010b40302a01080340da580d0300b9900344001d43c010b0f002180150414504031050140050145494040f03802c20344050618200c1d8002e541d22200c04040c420120140900a054543c0b440244a60840c8000d1402c440c420201c1980c4240e030707107416600d5600103a4440d0408550000d007201d009140a0510a01604030b99a014010318508000406c015026440240744000481700940c24034550500554025a01510303200c1417003405040403e4410042d458071140c80c203040e001c1c2040070000340c81c1005603070350341e001500f058008540603a00d0591100d585400e60303d162400d2007511840213000703003c1c040580c0001e50020149000403035085041c1c8400c0d00417819182c00c1d15059500c2c824140840d01007074401c0001c000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 273766007 1250 273764757 273764759
    0xc0b01030f080909070309051e07050906041b050403050709050f0f130203030c0c1306050d1203020c0a03050c0d020105151908030c0f060c070b01180b19151107 70
    0x50412003600344502d10904105180218100000311010b20803101c010000f41c0350060101088800e04c204000308840040200d000c0e0060750a960f200d04007801107600903648480094065039072a0408070554664100428240c0401c403802049030703210780000e0750740b8450094000f91000240c800c442c17141c803002e40e581c4c44039218020502e01003000036220303982d554580282c542c0540d405100801c07085181d5002066100f0000301070011420344a21010903c070b1500a04100a844020040b0045507002503029200c0d516280c09800a02a40340851900d2050090303510030950003c000b802c0c0d00007050300b190040072844c1012826240304131503031b001405502140c86200d06144e051020143c180700914000140c441807c207107103812104144003658070056035200710100500505402650140b4100e103410425260001807010621503803a8503194503940f0238500c0810b50222028001c01820001c064402450205265109001d0030300c104010680c200e0615000300b079213201602042014114031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 273767257 1250 273766007 273766013
    0x203161809050f06010e07031a0a030b0c070507063b010e011202030a0605040c170408030621010507021903140f0708040b0301080d05030702031207091706090d0c0b0103 74
    0x90041c41100300c0c0c8610840280710411903060200e28040e00b2290702d044400c1c603050100400303450f071300c04100721080d90300e4a9803403650300c0f4000c0b8081520b80019030500280c8401c4000d142c02c4c03083e0350300030700710340a050710116500e5030045100410541c900404904400c00d01a0b04030707081c0000000e205075036600802c05030036500a4803140408001410800c402c002014065000c1c1d910403109420345603500c98041c4281e240c140719a11404401c4d18003034265000b000c410340340e1610003800141c0507c41c0440054126641d46550040051102d002c011010880c250954082c040c20b450b440e016001d08002c019049c800c6445030f100d8541c056544100184a40a442403e907000e00240f98401104220f180041020380c0d005000400e014007640f50780358036000c2e41c2810800b80c04104810440d042043c071014603800800c1d6010f4510f030800d2200c080d16003103419105241d00f9480300404185e81400100c41c401f000c14050b20800003201903d182c045c222100f11080c4091180c003c1007030500c04010f0002c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 273768507 1250 273767257 273767261
    0x606010806042714030d06030c0902090a0612060306020703080a06080d02030912010216121209020906040209120609030d060e06061b0c03030d0204060e040605030618010f020301080a02031618 84
    0x40c040c020505491303500d25200707070540d4407200d51024a01d460744004c00401800c0880c00004124035801107041c44810000241d80200c54490f09007081030545044100b0303051644460000d40e408107045644141b149030140030308204403001d800c2d0030b141c1000084d6101003c20071410003841d6601552a01c8040f4040200607003400030301e614507650034464031b030740001401c141c00b41180c0902d08030011603681f04001004100a442c4030418542413044040044e12092201038104c042210b015031610b254030082400283d44001e004518480d58051025208002c00145a4072210300c0003482221f4480601909104007540c80580050b001c2140407a42a0705480c142d0400307006209545200800c00c00081c95034110704441600346a001508008098001c042e090001000780e60070300646140500181c1c072a00c00070003010b9005800c1030022490729007940404061044031034115240d58446564559668504000324020304c034242d00c0c48250611000680203d46103012a0b4164081c0003c0c1640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 273769757 1250 273768507 273768581
    0x7030512190216140d08010915080f07080f010212060d0510110c070f12020603071403041a070e01140c0102070c08060610080907050427060f23040803100302060705060601080604 78
    0x220409c030598021403071000a006060401d04500020103151307003005202410001841316a1021303070310401c0b0150b07031114201078441c0e120100302c40343c11090480e0b040c454280080b07248800800ca00d00b1200080415a65000e0320800e21a04111401251540d10006440c0d03043d020340740840e44207070118001850100011341c0e004825203044a2440d010840c0030361107030020b17a0125400031102c21010040e00c00500c2c0968000b0251030030b100048984400a88060820760a5030310300c43c1c0005000b03160070301c00d4040328140c0d80d20900842c803e030b944001c81c64403000c0548009100d01e81c1b00c0380d010151882100264003801820010303100c0d00d072406040000030440b080404081e100105a0400030307103c3d804240403541d00800c808a0f041d40c8403c034440807941d414244034503c0d06000500b24607140e02840c4254801c0c1c2c09180c050382c0e07881e070b1100c980c100e2901e940002d61001001800508000001c243e89010780f00a80b200c0c03c003038947d00c04010a4908407008245010507403225406c1101d13942d14bc1036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 273771007 1250 273769757 273769781
    0xf06050d0b0406021b030403080a020d09050603070c170a030605040608060712020c011107060c0e030d090e09010b0a0b070c061b0b0a0b0603010906060e03010207030512190216140d080109 82
    0x2241645000348450440c0c115034001d9600309c0e804201d010031260181310345c4038241c1c814540480c9403410400010510b0001619000c00c0041500d40c000030008080040200184c00c1e060180e1a04c00c80900100034140a00800d8065070408030001a05a000610580aa0b09035101c0c0c410411046d000c1038020b4200180780d80309507480d445101c200090800040400a00400010038003082400010386140c01804e40701c0c1c0280e10000c1f661501c1c85c1e00c18851005d84091150303000f115140c1782c0f400c0d40034050803440030398001c81d2441c00286900b013400c02070841c40d106411055109540305802d80e02003032041828041c150103002741000280d900c4c03401a0b4044000400084c1501940c404140350303401c06d07009003800c140d60340c40a0000c2c0da08140002aa1041100254a0301040d40da00404502944003e000f0340040040405e150003c84416061461050a002c64492403001e1480514600403034096030864410712030f00e1180500400c0f00781d2521442c2d11840030991a15041100501c0c400c0401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 273772257 1250 273771007 273771037
    0x11d37031809060e0405060f09061f0e0c040f0603020f04060507050a1a1012080711031924090203120d0905010e07140901030b07140d050a0f06050d0b040602 69
    0x440c0b01200c82c842c000180c101c1c00700000c40d42c42c1c940340035440c1003005172504002c000c4842c1080300303240c0e0010710583c0c0300012014821300711603c1e0341da140c00342925810190b03501c16890308110032006c0d00da02034003c0f01ca28902c03410391503585210940480c4100c0740d40f032080e202c00304000d1007924000c00052043e640f1900850b140c402058481c0c4541c448212044030710b400526080c005100d584094220103000c52220102e65031441da525020030748185503005010211450500300142d80074040c6200061600c2001d1805289603d00300860000707120b1203403048120140707042560081740c480c1c0c540d890360240040900081070043d039016034211804070100c6686420030706c00042d80038002d100c00143c2c09402803c80c5400c0403450403203980506201c90050508000401c085090210415000109424046000ea469412000d070b00c0c032802041ca10050304000070b20411040c16804610f920b5111402000501d880d081000540c1c600120040c110454150104004c9122680100703080e41d240700d50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 273773507 1250 273772257 273772259
    0x61d041211030a0903050d031103151804050307020102121611060409060920070f15090c030b0910290334050409020105031602011d370318 61
    0x145881c1da030003c80a040020820302d0100104102004140f9074043c1c1c0f410140038052a40d0350094850100600d0b0480300220070040001e84d4541c07040850040701c0d041407804080c60300382080c640d01c1d403101808a00500c03a0801d55940d01244900f039490b42e411107011000400d980d070311044108040c1840741e0340d000100b04030010b49401c840c81a00d008001e84200400c0e41d80440c0c07026a19642141e0600c68180010010b41c40010f2480c030001c5500c0c0d9110141c10002849480b02c0c070003c0880714001000c1c51025103022092101c1c40c1c4220344502403990458440614100308442901e5041c0c40319881c100d1040c400c0c1c0001d00103070328201642c04000d000c85050010f00003154000c41c1301d01d25446140c010307500440c50701c0d04040c08ca00c0b02030b040070758003070003000703503d0b40020a5444010280b08440600d4085016424800e402c0103428007246101d414005420404031501c0707a031005440404480003002c10380c00c40100c050320300312913091855440203a05560303c05490340031881c0240f40c5007030b4440760 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 273774757 1250 273773507 273773537
    0x1a100e0a060303090e1501110703170711030d051801171e01060302090f060906130e06040b0301060f06080720060411010519030b030c030304080102030a061d0412 71
    0x1101911402002002090701403441c1006000c4000710f40154030002030903003c1210030740b4000048902c0b1030080c40c0c04219149400c0c8000d003400c00c6500002d1640041035602e1040d0150f13007024208540c0218210700c0202c2d0308808242e618604c91007441c0200d10144540b9900740200d8180516461041c10014102c81d10242d602c0c16900c0c0841d200018946d00304020071009404100c41400f4000c0e0741000c6162040880000704464001036180340314880009061190303488040540d940001180f584150300703030702c0305030801d4078010449400340036601c0c080075010700b40b805000d00310485454201c850712a03400c1c040c040f103031031600078803140a1000924010381c46418001014055294041c041c044c6410949007214900380185100381c1080403d001070160355080070780e040c038149540e0400142c912040310100b81491405162140d140c0008203002540441c10340056215582d1403508000301c64031200c07450340c0e0706100c0740341c800c0800f20440020002401d844280031803410a0a1542003007a0305c00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 273776007 1250 273774757 273774779
    0x304050301020c0607090b0406080c1308010e01141f0302040b1207091a060406120f2004030c1703030a0905030904051603050c090102031c0908160b01090501031a10 72
    0x30400c03a0b030202c1d080005050f80f002020000d031014109131f0f0315140c64070384000d08098002d002c06669840c0095084c118080046c140340085c440c0100074009445150f0b101c500809511000c5030055450300009040c69580408051030031440150030aa054295002d00008000c4545200c4c0c00c1103000c02400a541e5041210400070b1806130310210703856100b0901e504050092200d51070048005010a202d00da400005001000048a20000c5c583c1528a000c1d80a04a00707080030315084034044616038140b00b54030040082e40c0c000c14002988035560f26030315a41560b03a1142a03103c0c0c2007400030500d1980300e034000c5c0502c5070141d030889080016440019045410a4404200e42084035103200707100d0303800d0b000341c59205000d00704050401c219400081d40300e105618122040560f60008003e02200a51012140f141c01c254a507456001041d44407070a00161070068446039411000003545108034010320b8140d0b40d1024031807040f1030a060000c05c441d40c02078555010229002c81c003140e0490700c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 273777257 1250 273776007 273776017
    0x30d03050a0f1803030b060a05120402030c10090501020c030d02070510090305060a06031401060509011202030703080d0504031b03091701021620090610140d0f0207060513020906060c030405030102 86
    0x10b03900f50540c00e0f442c60003130b0444450310300c120301a0341c040c0b00760b000f2a9009400d40b140170034070700e8241c1d00a58841c40001c1c00c16403031340c60b9540e000c5090f50424600305e034801540b40503290280c00303c403105400c0400b01035898900c1c42070400140d00040f014001c90070030340040c05210482d4100101d0036a101c2d0317202810000202e1b42002c410342c1d10b11081052004113540c81014111030002007183c981010b01140075840140100400030200c42612811503d0420000c00256000441c03d502c4580100002c00a02410f88054000400ca01a507007801003010100d000e00c0381d8982c480c010114500506815074000750460700c10103550030f020b8000c0070030150b8110300e40c03740705083d0703402001ca007894003541340800700c130060f800b94003105c041112a444001015048511905110b43d0720005c0300c07204005031203019402c080c41400c01c0103a051400898010740301a40c0705000c02d0140340d541104031041d00300720a4010390b00450b400c001c10030b58280310340104032100c920806d981c64640c0328000700e1b082ea446 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 273778507 1250 273777257 273777281
    0xc02010903030c0302070c030b07120905010608060105220b0a0e1e1b070609082a1b030607030914030a2007150509010905120604030f080105030d03050a0f 68
    0x1205590030070140d1510803d00440721a0074214101441a2240070303003d2464080200344d032000002117907041e80280681642201244d506101508051900d203010302211710408505100e5240013007078510740800352071075a60380e800f655003168491030300304001f420b03814145a4200076503804c04103000c19100314083c42850401c00401c403107505103044042003500202020f5903a8440c410140c1001001421511010b822050200340c4818a0400b80458403403c6103900d0b85a0712a020880303544002170310b403000d001d5007406980c000107011030225612403c440c180c0740d2581140000540c2a0b000340d010242c058041e1400ca400e880c83c0c8030f0410b00d198010002440402c0d480291807811406080f507a0030300d500801d000d4403040c2d20305581c0c10602c02c080c8000388140100801d20924503445081148001c003c0108502a00f016100e461611050140c44c00d40020b134508040b03003040d81c05411024102c400c0903000300012080d003c4101c0c001d1902600c1c260545441e020300c81c00ea0300e910701802c058004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 273779757 1250 273778507 273778511
    0x9060303110607180302011d0a080708060a0501030b040807051002040603150f0b0909041104060303081e04020a05100219051c030506060304060507020f1506040b0a080604060e030d0c0201 82
    0x41d00c03994051500900a014004101010b0070080300509030140410031242c0c203003071a03a001d080c0714090050b0030036002c4011f074001e1f180c0100060741c101e00244141c1194206004d84115448507042241520360074040034012940c8400410300180303181c1e0003441168001e80a8400300755400c00032209036481503001d600041d49030301c0c00c0e404400c404186500141901d40c40352030214540030700d5640c94090064818404da8483c4000f606101900440102151005100308030494407460098610b04058441111510b598507000e00001e0890031490b0160380c0051050840a19200821156001c0c07089420700314083e0b551030041642c041d04208c1811441b8102401d0b1205840e10642d8420130109042800c050401c003c0c04220345416040301e8000790814004100c60b5103a200036842c2c1a031548441d1400c2c0700700c03143c0c050a2810420071714015402114180682d2401d8003c10103480c8842c01000c040e0741103038020030000b47d038950082d0040e1010409603801c240c0c207244120100c44d107190000c400b5035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 273781007 1250 273779757 273779777
    0x80714071127060a050a080709020a0507050316060b030105040c030605100f14240d0b0111060403030f0b0103020703120213051002010203070f2105060301200405030c04230c0409060303 81
    0x80b500c0d0f2074004c064041940c85030a60741c54030920594030000c1c0c5c428a00506e500240300074410b40b050f402c5540e84c1d5001411a50399050314640c48503070204404060f42c0e1a0315000b803000044c5418024240180d411180c11000203085442e0f6400131720000c2c14030160580c6001c400212544d0040c0d181c0010004140b09017105018901480030786050810100b20b42e01c4000d0013940311035650000d441e01c607034610341c00003180115a401660a103280d1820a0100e104010400c01010790541244405058441041c0800005480103409a00030180028042600c40084952403042503010303080c101e010350644a40310390303a04040f982280191003540d0050750000100701c0140e0300014808120301c541d01d043c6200800b100250051440030020a401c419241d8010a2581e03400b500034030310030b242a412506004c0380c140708603807151340b0921800f07000780a1409840c0440c581482500100414000300e4a6500400d4800d80440c0c0c00003420402c0640090001060f2a0440d2007410081c502c81d0300e035a8015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 273782257 1250 273781007 273781009
    0xb150a03080301090c020303011211030a08040905090f010209100804170c1b0316032004050703091703010506031306090b0703050702010b1909021303080a0e0108071407112706 77
    0x17070f620a0320706000390340c400c00041152105c1c58415445194012003494500804840040c2c1171a54207203003e00315800109006c10503031180d030301140c05440316404031030001e080d1040d454287e000c4c240c401c0d039100e0781700b500400205015043c41503000d4420040c20010600707841040030140c10242d41541c1e1507010000d0b64400c00e6001c8240002c3d10011001004441460700040e40780d4145400014030440d0000004444025503101321218198010010703c114a0011402401440a40000d0750740580c00040c2c05194150b4508480c1607400140106240d40e0b01c801c40c80080400d0b00c2c004840a41c0d58196030804100080c281ca4010081075401044a00b00380c0c01c02425100180c0c486071241c0540b04000d118004605d00441c11982c0c0c40342d026032940909023040d03240114550024114540015825220b039a22201441a044090321100515126608200d400940076801600101d4040240b0800300d25803402d11141c2000041840300d8205c0d41e0203e10b00c44c071a42403075280381920481c0034040c031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 273783507 1250 273782257 273782261
    0x70506010803071406010807031707020d1b0b0906070f14010603081c050702063705090d0203031003060207060902040f06031509030818030f030f010f0b040806040b150a0308030109 79
    0x3d00d504c124010300d459414900c130300f6140c00041c44000c007420800f0894180040100b01620622034005048401ca881103080c242e80c980560a4024610f00c4281c601140b46c1e03400d00f0540b0560080075000e10300745820f6585290003119410810b98075000314980441404009004440145114100e8941c966500e4200322501d218050040c040a03400d110810804560008101e03034005070100350200404041407214188541c2d1042c3c40c805900d48119541c00d0101c9500924002c081c20401ca84520201d0b0604a0700d0340415507444840400d00b14040010071115006031050501410340050080c015a00140445007800d02c00701d07005445004c10010700000c0c42510440c030343c0c92502403042e412103031780042070180000d0030030361050755860348600c8005003082075a00d485c0d0860751307042e07403414051608052058248143c40003c3d60b000da000c50280c10003015501100d4044004003171703d8465070744548110328003c001040b1200030000c4006103640f1038980b800214054449107640e941050740e0801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 273784757 1250 273783507 273783533
    0x106030b01030b0a0602032a0a0f2102060a09060f0e010902040506061303020904060f140109050c0a09060503070e1f0201050c0f09010c05100c0f2d0e01030207050601080307 76
    0x121030784d28520704001c101c0d0040202c170598240704581c4c1d869100e100d1043e00d680d01d40d100c02d00202d840b403010a82c0c200f00d004017031040603038081e00410128044140308103840d0340b255012030006130080000b041e2065415000350700314512032000400c05062000800040354154040c441141e07454940840a6050600c250b5030452001c0d126141b0740b000e900080079800b55a40300003801840604000341c28885183d004202c2000c55503018010b20100304003059031007800303014201c05d0614241c042450034801c041242c00003000d0743c880c9981e46160000135102c90700024555400c2c4004d20300107414998a810003070346000d540c803000405070fa41100e002402c680d402445040f280200b08403a0060703207245c030b0940b282d015003442c2ca001303114820b1404508107002259070410700740c00d01b10400f0b00e00d41c00416052003800580d5035403164601c41e00b84e1016042ea01d600207080040038091104071a441801404540003060402500d030403195551186000000d82c454900c640001c2514003c2105c0d82c06040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 273786007 1250 273784757 273784759
    0x90c081e01210c05040624080106080402060901020c0306090609010b0906130e0a060911010806180105102c010801050114030c160221010f0c091502150106030b01030b 73
    0x801d6040c001c0001c41c00240c0240d00c00500710714004481004400280600036040c0580f05100080c0c0e10178019110281c405064191900f00e20352140d105c601c070740900d03030407100999220346041d2030369000c0c00207540c4031682240c114003403840e00700f500d40c80c1040172a000e01c1460009000d00e1a0a031843c03401c4501e581581e034410401034007440283e542e0402a481403c0642900081c103246240a151402e004000c00800407428200440144003201100101180c82a210918580e480d24100410788544070701109249650300300522071424995002030320b820940c10104001e0314101140900b0b41c0c566491070902c801320101c0c036805568056035190042000f800d048000c0101000001c1c0c0500006080000341100825008c0440c49420b41c4030501a4000e4140724000301800c9800d510841084203102980d03007001d20f25030810074148505911030942342d860901c00e0b410074032018511800302c503080c411803281e0315414686c0154081414020201c07a01d0000d4030721010030000d810350b081c082a003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 273787257 1250 273786007 273786061
    0x40602071e060b010f02031209031201090902010f14031f05030f010203010f0e040b01030b06060405132405061b15013b06190306021303060b040e0c060d0204090c08 72
    0x40700703080c0e0000103541d80285140032001c081d6850380b0301503286000b40101c1e6040bc8501100006401246030321902515000fa07880b5503591015400c1610800024002102d820004100003002034110240c645070103d0280041da010959540c00a8601701d507208528400703942c00001080b0580080c0d00c200c00414075000901903500d00f03500caa400e007110520001d01001402e4001a500d941c0360401c072006880c0c000c01c0030300900c517030720300a4004001c3c0304442250b1030209864000c2e456100b00c040d03400c40304024840c0c1d1501c039400c0006c4441c1908243c3c01c64451041c43d0828100540c21030009006e04481044103048015403031010442c025010b03074002c4004210701c044008450185070441c0d2268094510404030381803c80301c1540d02d0055400078102d98400314007046410301204051341186c0c01050207100c030580010030001200d0481060140d02d620106171901c40d41003050103401c401c82200801802e29540d6103007902a6150311805000040d0a04104402d0010380d00926625030505005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 273788507 1250 273787257 273787277
    0x605030105011712070501060806010303030501031203151505091201090308011d0a1d0703200a0e070c0c03050106060f080f150f060d151715060405040602071e060b01 73
    0xb20130707101c090131a40c501c040200068040103011003500050002c000c1c1c8011101c03e580e480c11300a00030102800121103514140c1e0107040b41d148a4058100c0302c03002104a5850245400707408490040c40342e00034820b0041c01c4c07044d80c07095038a0310f0b40340501c0713094800049010381e4a840d0081c107584050300103007507200240080303400040c2c44254080e8040d101680c0041c150344141e07000481c4060074a800043d13031047c0340012081000c48080b61000c402d0480d03450030001083c50422003c02064000c09601071080400111220b208481844c142070086542e191780985a4581c2400d603922600500080341d000c0302d00781010ba80c04205243c0c0800d840301c00402d54144002035481c00c02300915440e00c1608110078900c0640c1d284011034441c1030280c5003c00043c1009268081c070351540d0710070100c039100b041107002503852000c9030314941c064442c0581c00c2d05590b4a42000000d0bd030140040d51115828800c060000d0b100b220000311100c01c4100d040002c1945250200075540d456040c90b041120200c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 273789757 1250 273788507 273788549
    0x403030905040f02190c0c060203040b1210030503070506060108010902040b0d0c1e08010e0906070206010e07030216030e120c0d03051803071d090c1c0c051003060503010501 76
    0x306520684004030780100b0520450484600680107002c0140c0f03040b280158550081600170454180262190b11282480c3c1d41d00e0750240d85070301503845140c3d090f41003001028010200c444100d60f009000c1401070140355200e0700c40510703603000018104c41980c41002400340d00d40c0c00c402d6082c01000e140400f54031305400c00c8660388060140c11002000c494a415500d41068052400e821400d0303001180c107502810f1b42d8000030b120380c0d42845074070700b8003241c6c3c07002c940088030118500b031045100c4e40050003980d01e041c42d10300300c6d40e4008018504043c1d0a01c099280480d2150160716004c2c081c5e610407900d00000810809000141c0b074034034a840e03010b800503500d15207032007016940c81030305400c050b6124000242000c1c11b0344800c0700c0ca140d15004030100801c40c0041c0848587c00060700c02142a040ea55426034281d070b2780407564040b40c0c42800340a8240c0041f0485078070000061154110b40c001c030740c1d03480108001c48040d000301c00c0800d4032445c091203d806c00f44242401050290b1b911200c00345150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 273791007 1250 273789757 273789767
    0x31e030c0f070501060e15040608030705070312050705011125050d03020a03060504050c0301150801121e0c0621061d09150a05180109170d14161103040303 68
    0x603500c4140940205030003003801400c1d48045c0c010b00c0503881c0f900303003882d01940c0a4180c88240d642e140c4074920b822804500c07172a0020503030b204158068003c19565095454184161060041e400c0802400300b04100004901380a401d003615581003503107803a00d6031008886e801000186204848140c4c54804802144000a0030711808405050040e41da41061400b1005860980c00c0705804c1410314040c40a9150b074040110f04075840140701c040c03184800300d002c42d032421080c46903888041c41300881e00042001101c03404107140940316003c0c0c0300c1205513915072012446520030740c049184031084104110300400d5800d82882c81c080104001406c00100d030a0a480000320307c050740410200049215404120380c205d040c0c4559007280661500c40400350152104681281c180175405071b92400f40d007014000ea20116904c40386205c501d045ca038411400700c0d002400025941910340c1b02c2013008141240420380078022000ba001303260000c03424058050007180d200485154401c11040007c02d03402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 273792257 1250 273791007 273791017
    0xf150a1e020c010c030e0a0308040311031213060e061c0504140f120c03120405010b0411031611100e0a0b010f0b07030c0510020d0e06070503010b0a110f0f031e030c 72
    0x10308041b01618501408a40c0310a11a08010680400010084144450f141e034101c0c00c454210700316607124440c8204507a4501074058001d04400108078240003c90003410740c0030704010041d00480c00c00742102402c90108402c070b03240214250303640052005109812030b240d00e41820240081003d5244280c105a85866100390030140c45800728803200001001e0080719100324200148401d44e00b4542003072030003009850034203449030b880d0041c0c000305001703104103032440f4010b01050111300058012040e1007007151802091054065141d11211400c8035126259095070500010302d018002c6142540484006030000c1550111418040100303012034012610300c2581441c0104000c030b603a2070034514201041e540c40706541e0002ca5010406190b60340b1600740107000c3c0c02160f269848604060324988070a02500aa0780003c00400f68824050222501d085051100325500c00c41e0f404010f1307051131321005104400d03030000107403031028002000d5a955860304120140b40385082c01c00080340c46100d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 273793507 1250 273792257 273792263
    0x705100c0f020a0b030c03010602100b010905060a090806090304081b22020c07150f090302030606040216021008090f0606010503072607050c070905040c050f150a1e020c010c 76
    0xc100901021500c41c03d988030001c10031803c085403241041c040050068009003c1c000052043e18507170940320b8264024401e0348281a120001400d007441d041c084254032007a00c85060144000f40021000d60800c040c500c6154104095074442e407c1050083c180209039007a0700e0000000300292026680340324000c6403900c4400500700704001d0800c403882c00385c0202c0c0c4007009140a0080005884902610545815861607803400007201240b10191822241804080d401d0307882280050a14149507005080e81085241310f0b003aa1100c95000030318001604030b400000640c06418031108007410040310010802e5031001d070100c0c1c40d00c40300080041c0002000c1c00200b100503c2425070510b2001060700c0414080c0110062902e0300c584081e0003035000200c8040d0b244522200056500504c8c400c9070300943c1e0028180a103203140804100c08010b10505883c0d10007049500c1038182100d00d0001d000301c00d900d40356250945a0000d403280840301a15550040d90041c3c81c29428a80c0d0007000c030203645034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 273794757 1250 273793507 273793523
    0x121a130c230301120f0b0106020715031a011805040e030706060b0403243210060504031103070f060c060507050304080a0c05070b0f030f0723071703010e07020705100c 73
    0x76901741411000b0641c000507041e82400030011880a90204501c8261030010f180340410a05142081f01103a03000042908100106c20b2a05800d42c411140d000d515990b8500c110b000781c1d281c030005000c590a0030300d5401103071300c00104102041120700484008164240d109810a8031319120344c0c802400d01e0010800074142c003284e112020300b895004568012014699086240c01106840e1220448150200441404100040d8441d80130f030030300301c00d50744156140742c00e080c51582c910451007001c14881d0381c0f42c0180d4101155504a041c1c1540040840760344944810410381800800ca4038060513005c2080000c20070000030031314040031200b03a111240341a0341e424915042181c2000450780084802c0c240c00681c5040601c58180610701484041e03004110320f0b1600c00c8282e4004440c52860a49014460020301110309903001500d0b66030700514100b0420300c2088868120369100342c020000028a090912040070340c10465135001e4801a980c0003804004054040d1076204003040060000d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 273796007 1250 273794757 273794789
    0x3140a02030c0d05040f05100606021207020427140c0105040506090d0501110c190201091a041206020a030b0f09060d030e0603092b121a130c230301 65
    0x101c18011107000d042d440f001002503040c5864601400d8418280a581300d102d500070450f4449502d2140108464440c5c00030007031041e21800300000d94000c00002d90b0311030fa13506550020b18a119081e950384da0004544100c0c00c0700e10f468a24401141d00700d4240c4154041e102c181040e0342c12208880540702c0c2140c1d400c0d00c80e149031002582007110088028015400c190400507200d07510006001005440e82c2524866140f109080c0700c00541d00001a0019000300383c03c00c603001c0911200300342c1d4102c003964240790030340b40d074a40b01861104000c1100c0302d13540041c04102203030f890300c07500c52185c40c111202480c01d51014006850102c011346803604c50122007000c41c5c10540501204e40040d2000b50580e40c5070301d40400400d440d05110111140030324a0f5110030100d42000100c0e01c0d044020b5600e072040200e000c950310500074495645a0001d01c2c95544401040c1d2b5a410b000003c0407554040219540000990040500c16100324070003001c40381e088150020320004090341c0c1528000720400c4426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 273797257 1250 273796007 273796021
    0x9090603080f090d050a05060a1d030702042f04150203030907061b020a0b1308030a021c0c0506040f1707021e030102040e0901060e0c07050318060d0f0203011503140a0203 75
    0x307a21100b000520900c03031800f51b50204a8040f880b244500ca00c010208048030f2050f2410440341c4402d001600b094100b00240401454103901c419003001e40e04100900208441522200107203010810f039075040e10100b02049902d5584401c0f43c00070f04548003131410760900c091620f5032003640e8002c0d0b2040c41402845a50105c49504200c0f5016800401d001c00159070f03020241d0161b031000c0840901c3c08030b6814040b5409000004655010a1950051541d4606412507100c3c114001c10f4101c1041507030905440841c1080086a005a01441401243d10400d14080d00a08410b5851a101410034861140503071340304504a491009000303010160300d450800000d009206941044814155100501103140c40560144060302e95094410b112522410071030511401040d4005010368010030040c4035401002d4140314860304041c10640c140000361a600c0f0031384034040d14070041d0070360100041240322400400888440303610305041207407040c0c21401009403030b0000d100c0c0360203d80010105420f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 273798507 1250 273797257 273797269
    0xc04140411041b1e030212070804080d05040b16030608070612060f08070303020105070314040212071701140f06060712050c0d031a090c04150215040506060109090603080f09 76
    0x19034956020105090405582c0035003551140c503100180c420500581d2281d0901038421221000c06d87c021010740e03640c501f036007210a1754000f4022203200009002028070182d1030300615004030700c5085844024904005000f01901a050003203003014144a0100056003000c0b0b2245c0c183c840320310f040c00240907100710207070280c5210381c8100c961303c50f00710000a01000100d0b000c4196403180c0e000703101507105c0d0b0400724180c1d950102c40003502c40c0c006010800500d003841e46011586120383c26900d41d29525100104600008200d0044903515a141c184410504400c00756004080003c410124100180458041e000c0c8040003860b1200d42a91b940c2007030300400948410512030400c452024807060300050181101b5207100c03020804103540d10010b4908038540710321518041d041300781007904e0504000311104501d101d00d0154010a00100c0322400307854070151081c0d004100804450406400041c0458130703e0748641e5505150500510000d0440422542e000719283d9080751203400c640000f441c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 273799757 1250 273798507 273798521
    0x30b010f03031101140133020303071106010e22020a0b09030d0912110a15090e01060305160f210507110307110415230901060c17160219080c0414041104 67
    0x1030291387c030400c5107410398008011817103640e15a4a0741d805c54020406550741d00401e025541142da4070100240303054007080940c0306008001c0b0a0001c1c0301c010b54011600e100b9043d0030426400345d000810405d18101000010000c480c245080d10804c1e150081602e1044140071004042c60240d16640003560f4072242031300d001e8070102c800c807108103000100240c5134441d40c3c41410080140e83d000021400e010b4400c1911642c0c0070301d1920b400280c80c1b41c0c12605d140403449280d0030f000299035014501500c004007800c42d00b0a08000040c1810101e00113090702c4d80d1680c0f03041c00d5602c00c12801002600301003804031800800e54011075502106000d05150f4001500581004e816440c1c580c1d003500c01d000c7c1d480356448016144649680d0300c1c3c4208a80c0900d07684806808a1404441c00c1203007031207000106200200c00004103d036002550018640107004000360440c101c10340028058982d041c81032200c1024111010000703244c940c0c842043d4880003d001405c0000c144445694940b6131360001c171 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 273801007 1250 273799757 273799829
    0xd021e0a0f021e0c2404030f0c1424070f20030706020706120608011b020105010b07150207020409061517060f01150504030b010f030311011401 63
    0x40d8440364106001885001c0007451080144101008041d0041c21441e01141d4008508080d214141000f401d02021821242160901000c0e0a00310015640004040c0c0080c5200b10603441e0840301030b040100a00b106501301e003441361803224400c11140d440103c200301c203510141d50b914031600c0e0b00d00d19004900640a000d4040c10301143c1d22000c00c400c440800c4243c20712549000003407030084050503aa5800e5005c5c07000541e0051030140400350103013180c4008018400c03800314105407110303121030039941000c1400282c0390950000d9a4059028001c00d40501441108181030000c9521441e149110116108482e50b50004044066446503004440041d1b0000030912034590300b10340b54a1460030902c02d003d5080504002000300f00f1002c2404c0d406081203956800840c1d007003044138a001d89400ea000e100b8030004100000019243e0010b10340245142100a8031061031402d024004420803032a5010036494091544084044d403c1d0242c1552001c42d18103903109401c1c1e40c0320920306540500c0c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 273802257 1250 273801007 273801067
    0x206070c08090406090b04051303050a030f0e0a0309060809010c0212070f14030d0c080c04050411070c080d031a0a03060c09080109121b030e01050904020f0318011a060d02 75
    0x1007a011704c550042c0d1101c03501610b00300481d644018401e00d50403841b101c02000100c0400070812030030710039049000b50302450303800022452036150b4aa0315000703403c03c0480c04241180b800f00041500b180702d0a5000840d00024000800b010030025201c041a102190144801194944c14050090034400015901c0b1150403407101d0004541592030b04600d50007400282001c008012035271140c2441030082003040581d0b400e0074201410040544030114102520907424080040440c01c0740000e02d004000000c0a0310070345040110003010340764180c0c51a001880080c0c00150075032602814801201e40080c000984050200d42c1103a010b401e079800240c2941c05e142d0320030203002400326511120602501d4104030542c584001c03540b01104807401401103880d1000c071009950048008044d003110043c0f0040c80d060303014080c10490341040e10081c1000c10500c418008001c030900c904440136844002e40360b007800722040026940c0c8290300c2000da0545d004209110344024041d07102155131070500b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 273803507 1250 273802257 273802259
    0x302010c1106210606040f03060b040b090406020a200a2402070602040e060a08061b070f0f2a170c040203130606150f030b03100e0a05070807060206070c08090406 71
    0x250341c40f003505801c40b0900120101044c481e1030400110750895602c00c00801c2e03c40d245840d042d000b0850ba04500d5000341e12001444000c0d2f8841d411948614030421005031249100c06001300503401c0386030002c9144000f030441c5041d8a10008001000992240382e1009840303c81c54008040400b4174251922240082002800c04c4016000f030310684410022500032a9a6482000300f12415442886425040038002c1000020b221507440c00d0041e125200c42d103006e46581d90340d503404c840f81d80b05845a41c01034450001f08900160360702c0d000c0440c1765400b04500200c015404208205118654040c045030300030501504061295030794400f40104119108c0c42c005101c0c1690310304544040b5400745c03401001140d8860800d081e046611126612190706040c004001d03002410740c03a10380741e458480e40000b5820291203002d030100245603100a0240c540b41880c0c582c0c03070078403aa000b4401caa0050ba07814040360b540011b5249c0c0c400c4491400d107110301c00a04200304d0300c0c880c01511035013017810214 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 273804757 1250 273803507 273803527
    0x3050609341106250c0f020a1508240f010e030304060206160f050f03041110021c0503060315130b090601050a06050702090c0903070e04050a020a0e0f010302010c1106 73
    0x4142c04903500c0a0058401603540c40c07404a18010040124201100d01c0d0b0312a000614440d04100e014a0310601c0398846c1d0302c1580e00040d034a1402c9600202000d034075000c2e13180c41ca40d8000105a08002c8040d0a80c070040b244d80f24400071007080280e228059030a080c1d420348a03038814042040346110190959584a07211040252519002c80d09035020400701c03038501c0c004d079206000c0c1346802c01d42c581d034603070410200f100900d0580d80050b000f5940019400c05026459403080604d404a0500740c004120200500c0c90340c1180c0c1d0310003410401805400c0c0100011902c000c154650611740910044000d0b0340c4a20030fa0008403080c08002d403101610501308598030000041c3c460581e6021500001c9042d170341c1e0170485c2c940c0709661000790840c010f100824007032107291015001d1000c0c024241c652154480d050342100c580100c80907107a17940010310000031740c00c0c040c6101000d844000010f00b01460590f110200700d98044c84001d04020941c40000b060002d041d50f04500c402c4010301103030340d80601c10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 273806007 1250 273804757 273804767
    0x3070212030f010617192012070212090a0b09061b010504050c06034804031a0402010207031b1a0307080c13090f0603060903051206010305060934 64
    0x1001e081e000c10421074500c0030701c0f0700c035070041742c8243d050604140584070a840c40d04040c2965060440c00324092120a0400f00f40440142c1000c00b8613800410046c41d0400c8000e142c9115030f2406160769000300315617031f01611010521819a080e186005544408200c0031070614410248004060f50010703140e041001c134103400040c0180d014108a0785041d00150405c4214441980e000c0500074000d00c00c14a4000c1446c0b044660340e1907044241c00001c85481d5030072810044290b014007402d0000b805000f000046d00200c1211440c4094000c818605640041d41da06214000a0070900d01e03e01c040114440f101410b01c050950040c090f80d0110030901407070880d800640302c44010540c03001c00101d200180030296405802503100c4201654640030700c01c401402500c1a80d0790440d202c2c40080040f50850143c40407851007603503255070b950100361070780c2c40c01039014001a04044c10582803150300e03a1250105600014002c0034130764481c141e8080b410300d101010b03101c1000c01039605441c224242d009 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 273807257 1250 273806007 273806009
    0x3090906240a090506270d1b180e0604171612030e0f0c130e12070309080706201c080a06050102011103040b100909080d0608010b0a030803070212030f01 67
    0x2d600d644168035200d504110860241e16201c201c0c441d0b4000072150b003510070203641803504001808140e161241915540c004a60000841041c04501c2c01c00b0030113012010400070300c50611311000c00c240031822401a859407000780c4041e00b820b030113550303010b8850aa101140c40810701004610070103411403802c0301c141d0441200e0032012030f1038074142c441c003402c020035001b88115a0340041d02ea11501d050821404104d19151044400c0d82c610900c2420740b41004142c240990200d021900c0e40780628005101e40c0003604102c0307003500311680402c206da40005086003040704100302d0400144179003500610b0700e01c114554160000010f00d0624040e034000410034064142c0c007070148152504c0c0c0307005900343c0b805080034004443c0b00b00300080100300302134003c070380002c00210140e0b0b006075141d01107010b48000c10030030b8803624400690401c1c403c4281c0700e00340080151100a018008001c00014450100d611010b0240400017001440c2c65200f803110460244c00700c514180ca07814480c030f5011480100b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 273808507 1250 273807257 273807277
    0x12010e0a09050c01030e030904061202100f02030a0c0218150a0f0501021506010e03070e09061006120c180303120b0301050c0a03020a090f060810050a05030309090624 73
    0x2541000c218010824080c001045400c0002020b80c0359004004400510780c0100030700c40c03070109100089082d540c50040a00401ca01001d01c0e0b210740d070741d0041000d4142c1c807003c450107001d22007414a00d1940c010056501c10907890801c8020504180007007490301d0224031007030500444034000c00540c0100500811307441002620070151881d19100d030021070349854016580980e000b14480c80304503490802150780701d1410324102c1c0c40c1c90380003000300c3d182c10f545801c00c030300d07007010b0b441001141c0707000300000351380503012000c030244940c81c0001c050420060108060300701501c0d40050303114103000701000100c007001c15884040300c030781e02c0c03c00400489181080380d138910304210346c64255150500a0500503031036030184914203c0c03e494107400940c446a000810b1000541d4001842c40f20f5030604c40007000640c03151100391500b030100000d44405900b09505c01c001c2000b003840300343c4000003560a030b0f072001d8074503003500d88130300000a07c0700210038800046c40c0c40072203220f619155018080c100e40f0300c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 273809757 1250 273808507 273808529
    0x2040c030e0c0102070f0513020c060106020a120219030806151605010f02031012050709020406050304021216090911120c01020f010204030f08090f040f020301061107030203060703020901050f1201 86
    0x20b00007004a031034100f40d114541c80ca4007103030030510007442c00503000655007407070a02c01890405240c05050404609034405800342e0084002d05083c030199071704500c0300901d2403000c1c15072580d40075154a21107400f01c00281c104250b181c00501d0541742c513403440500d1041d108559441d03000c0440700103851041d42000700c50a500300362140a01080c2070080e607000b01b0380d00031900c3d51181000408002c02c25603000039a1507100354100041e205003184000c101419003039950303581c1c0f072a1600611880d07607014021107403503500080900c004200c1c2104208243c0d8400d0102241e034130403e050070700c550060383c84126403103040c020b10490010b00000b5600030f215030a0b002d4604e5440f42504540c00c0780102d1101401d5006107003e03040002d4140c46c002e01c8900001031030800c6266001010404803140e041d03606121a500100520000d500714007442d503880345100c010301841d420f65020a458020242c003150a141d0042520411030703011381c0c2a1111031414015850700c40c0400311200007601e0742131040240c422 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 273811007 1250 273809757 273809773
    0xb0d0b060f011e0c080f0301030c170f07030615030605010b0c01060e07120b0d12112a130e060406021206040e0d0f1b0b0411010e0913020d02040c030e 66
    0x540a420000f0109000d00c03001c90000341c101ea4169006407010b6004c54690104003d890504c9454101440c080c6000b10081011281000d1074099046401c0c100000141d215210750040c00c1030011740c520507070350311410204405112030340c0750001640340e410052600b820800003042c00b10701d160180510310b40080003805882c5d41ca0000200096003698070500150070300781010040f5103581c2203d2041c617406040f45948001d10f4840c074510450100e001030016160841101512008104900c0c0303128620062403109e1b00548140c0d965864030508250040c0c82500050920088070b40c0008181d0b640d203801e0f18070070301c0c180c509440254000c43d036000800c285400400e10700e040a11a00e91108840001450345189449003520b00342a0310300c403c2d041001e80c0b1071031601c4050f14a42c172100c2e180b181c55008e80b641060320b012000d5110055005040002200001e1155500d840401e0b800101c190803119000e0350900100d43c00001c4014040e40081c146140c052542c0e0340369010301641104881503031040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 273812257 1250 273811007 273811009
    0x30b0f04060e04022133010b030414010507050405040e100203090307150b0604380c060a0c0c02060a03060e15120c06030a0209190b1e040e18010b0d0b060f 68
    0x141502d1041d02e46a030020090702c0c007a010b0b0324017410700401b540c040d5648101c02e0000f803400d01072090b0420701410030044144020452184d6044490301c0500700284064506464014428000ea10900344600e8a44105800303050092040c40b8002c0705c41c0205664a107041882c6607035903402034108803020f45400c0318a005078000c0303115640188900034403e6161628010700d040c3c1079010903c0850440303080d81c952030188582d28103402d280d4903041d42c8098862402c111101e040a20041601e51201e0409601c20407081d400002500c3c50703070b4105c6800d9280c402001c1c049000301030715008451007160b031000b8000d2149000501000190088862030150315542d281c05850301c0000a40f40d800c60f00500224907a241d0b1600a00b048a1020b0135031504403101d900481440c8032179074084402d48000290f06480440001c2c0461035a210700101c40f480e041c44c114650044080c004c3c81c00b101241050990216005c080d080800c0d4a00000c154030a488464245000d078003000740d480741d100f05841c0606c2802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 273813507 1250 273812257 273812299
    0x3050a0b250507020f030c030a110112020412121e090f05030321060102011104030803010e010e1b0a0c0f201207030b0405030c0706050306030c040b060a030b0f04060e0402 75
    0x140072810b82e541400d01080e0307800d2040c45800c1040b21a40340c00b40d2400810682c500b00500d9442602030304030b0701c061203010000034084a2090402c02c01150040000340800b140b0030001d4600d440d0301240c4446030301c0f03884404607014040802050b8460194030007101c8072650002c3e820b0181c84004811100c07881c1c1c3d03182007680e00e102da01080c0007110320f20444603030049110b0781200d40c0300c032041c000030801100c00100b020059000b84c00407a0b505c00c012005100c1c3c060343c1803e90b40586a0340c070015802d03041202c0c040906003401c41c0301c140d4075000005d03a006064460107405c40e01581c081043c0380b40200615150703c0241d40c5a101540e500500084aa92072401d081c001e2090540d0002a02d80075045441702e00100100400c203540c548010040e001441c40c0412014000f80165070301c1ca6105d007401c0342014104251a40380c20b21860070124491060f0342c400303088038010903143c240090a240004046000f0f0010000c81c0f81d805031a1040002d1700080104484c0d0ac030347c2c422200f641c8240600e500c241c40c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 273814757 1250 273813507 273813571
    0x6081606170f19110a050c0c180a0504230a02152508070b100f060804081b0c270a02070503040509131b0303110601060f030c0903050a0b 60
    0x340d441040b00803450312108414040c102c201d00074008107030030000c00b2420a4070740c807400c07500340000d40000e640c000350002400303010aa034130200c40b600350200803141604280311004d017428240300c0d42c40c2c02003000c2001c0705014030449148185c601d088010b90030301403a19a200c01d00280d0142c80700040200c41a80c10b2421546074030040c0844000741165982d18a4a111321034204a40c0b05104105140101e024091410700c03401d880c04080410340e04004d0984850300c9a640064180403042d000e0000250a22003540c0b503141140880e10b40c04054035820505c2e10686904882d00a8220f9811180748030740d45185001c2c00b104207100c1d15507501c030945148100d02c90f0001c003618542042c40203000ca8900080d511ba00840d211f486c00501042540354443d510a85544611300c02940c000c040081542105030b164080710020007804071580742c44406001c001c070880b650820981d8404000d1500b030701880402c03000d50b07046000c5880c10001e0746005c461440c4181c6e00c4d031503200b40d414400482810302854108e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 273816007 1250 273814757 273814771
    0x6030c020c130e0c0901090e070803040305030306130912050a0e0307050d02010e0d0b0108070e07030b0f0909030c0102071a13050c1c02060a02010506150703021f0608160617 76
    0x804000c4007480c600c001c103071450101c0d90f18007420307400300b00c2552600d2800740179110812001454250f0a003c4501e84100e40c0d12016261300103000401c00b04001000740c075032180c0203845c451070f1403040034000c000030101c42400509a02c5502e200c2c81041d94080098003010b94141c880e035005440e840c040540e108100d200d50b0341d100140650920055100710400e160640010b80341d110641c80c2580ca1400801c026000080264403440f0100b0440000f072410780d812030403505041203050b840f6004161002e034503c610342e008610ba1004500c0300c1e10100205d03800c21490740000c54840c4844c2c54614100700002072121503e549234004114510050303420800c501d035000e40100485820401400361b072150700c088510311044007500c04405611803c2c020030781c070100ca600010b45854120304221600700c410800782d007510001d201d0b0000080e00040c04080e6115001004a00400401421400381c55103030046610380c019000714206122010201070150b66003520f941c40c660708104001941c010f0f085903c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 273817257 1250 273816007 273816019
    0x6280e091e0a0905070b04080d0201050601030b09060f0307150914030d0c060f02041206051b13031e0204090b2a190e030111040608130c0501080c07020a0b030106030c020c 75
    0x214402c0c50303850f030002440a1182d82502c2c4441d50b98000c00c5240c1e0416030200050703800c410019411140d0a114081c4c1c03140d001d09003005003881b801e0104400380c900400441c0641942818010340d50f4040103198002c010898941200e000c014400512003400b0348106400100180f6116556140200d04080307204526038030f1822400881c2c4441000e000480d0300c0000caa542000b0209500000c0d03100c03250040e0007908040f03642e08084100f0007456096101d10700035100207000341164150f40344109421030b0b130004079040c1824441540b6055400407660000e6221b45086400010054216907441c40b604942a00400401d009800c1215090481005015542080051540b064100c51070785121030074a03e000c4d014a255200441e003140c040400245a525000c5410003200f070f0300c0039410768490018829100c494203151742f0344084441c0da00515051094010015086c100c4110071703039910355002440918082d507a405103204035407081c010180000e08040d005052240001020307611031b032010f408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 273818507 1250 273817257 273817261
    0x1208030402060d0b1504080d09060504060c05100510030b070201090206190219061d01150b070201170a05040b0c070f0b09011103090105010504060515040506280e091e 73
    0xc0280e683c1c0164641c8080b96510824a40b0686501c000c21840748008108155110b04000d80c0b0351a240e403203c0e482d02001409402881440d50081c15034003100c0403414004510320551802e1401c240001d01403031030030740c035000402c00c0080682268000300d07030092036075101c00d40752000304900340e8250290180d000a810404550445c1c07458035440440a9684156220414800d28814640d91441000e0f82d8803520340c011100300518901000f682018085c00810895a0038982c0100c13441d06849032100640c8085440d00a5900036070307250741403640c4000c020b03030301c2d25044581400030102943d055440d40f005000242030741c05254229681c0300e8120b400402000c1c40d0b0307a90100e036074000421206195480d01690000b8401580c042c40c003031a41140046000d60401081c0320854413141d20052040c0c00e404000b0410422003002c80d025150140e48030f66480049100081103219051070500b105135080000904c1141d00040110b4024412540d00b000c03a22403410b10584000403980c01518000c4c0c3d100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 273819757 1250 273818507 273818509
    0x515010b0a090e1806190507020d0c17160c060e0411120c0d0f0b0319030504060e01020c09240f03120309010e070303050c0f0616050a020705031f061208030402 70
    0x2650b42e0100e4403031411650302002241050410000340ca1b000d41d683c0c20f21605100101e034a004440d440b0000b80700410894042030401004000510005010b40c207019034096002c1140400b03c031420029222140d108042510300456094514441d07a000074100f0166242c061902e80100d44000320a1844141026214130790914404001380c20076071061030401201d821002c080c090240c0039034003004001080030340981450705001103203c9103081000f1540310100040e030410700740d07800d64202c0c3c5040f2400039038110061789040b03403100c0c070b0300d51041c10f003001c021540d910030602c95021900c001d0310030354034150315040c413000c0c0042c011000e606030010102615800041400795910030f0640001240710905010101e0410180c2e800070f40001c0c10004000040c03a00c200841e5100c8080100104000e00c0c0658510302c3c1603001d880d0840800c50009a56550b00e84200210805800e00405654242c40010f084660500003801040300da582840f10010340f03448004e9070b07a00010340103580d051840d903c40d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 273821007 1250 273819757 273819779
    0x70308070507020a0e0702100e0c0306010b091f0203040b18210715090302040609020408060f04051902011205010f05030c090f0105011412090d09140d03080a0204050303070515010b0a09 81
    0x10881000c48c461540c90031408522400340c0302c03c00c3c0104001e450041c10905c2030604042058010710050390080020a6098071780c44045c103e0003040c4504032140c0b034019082203040d4070996000281c0c3d0040403900014000505820520030401201d10002100c0308502031604011500030141d02074119900401c003030740700e0800a2180520502d0b0042c410341c0c9075800201201d91540081c1802980424148180c4000f0401650032802503925202545000e5a5141c0da8841d103000403140348100c0040c543c11640695511000041e40c0c2001303004940c0c440700d03145842c0055118640c82881108200300d654200900d03401d0096a2011020307003142c6c280001950317000c81c2c074081c8001d039100c204180035000c480d9108060050042c0000b808071403e885000030000c0c0f003da0800b095007004080c40000696800308054006607050409002555a00176001c001b03000e40c3c3d101d0394050100140f1042042400305001c0c0814000480410040c0d803600e4400000d8003030f51000002080c015107061100c00255 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 273822257 1250 273821007 273821011
    0x6080f0c0a02010e100b0f0901030807061805010e0105060f04020f0d0513020d03320d0504020316031110031b3005040b0612030a080414030f070308070507020a0e 71
    0x5000104000241d04d00700c1d8030740080300101d8400c03281c1d038040d4a0074a1030f2058410602c402c04071920b41940d4155110110644140640182075a03030f9a9a10700c000803025034a80203407900400200281c50316100000e001c2c003001c880781d07482254100707507481d00f83c070b413510960312960f070640381c4182824800d0440c8401884081c0502014040c2c0204100050360366052400c902c0340b081d5690380a000c582e41c4081445680e0b4000004025510b10104607070884190513174042c480702e9003020409884034008203003011045c00301c005610400100100c01d0004180d044d0007080001e46401c80e0300c200c650011005c032000c003901c290344e00070101c80c9502590700c501107100d1040e0001e80b4042d0000d6820100c080046034240a03681035076142c10410040c0010906a964004000d65030b0743c40080c0c0d103040080e00c0340310700100b0380203200030710001c6800e11564911461003041210100da0785d5010307060b407884ea141c1100308100e001544c0000011807162188040c1d0b20850703400750140301c02a0505013003000020300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 273823507 1250 273822257 273822277
    0xc0c030c020f030703051b0d031b020d0c06051216020606130f021602040e0f030901110307050307050f07060c120305041b140a140d02060a0203070602030703020d0606080f0c 76
    0x1070011481d80d0703550301388030080c0114864001405609544424a0014403100c00924440c4807600c0031613001c43d41200c0c012407a0080144c003070a0a6060740300044a13091440000303400b00d901e03401c0c0405d4803604078005001c1843c0100d50056643d4440010461010880d0804130060700150302080c068100458400f800340c01101c4040390b0302d454156804200d17004084000f00006000038088207504152040c00165480000a00041004074411568a03c14410283e04118205080d201020b5061040c0d0f500640d00600b0b4079035911081c00c0095844988120344003003030294110000b80140904001c00d1a96405813014402652414080d401020000c00640b5003045e00388a4a00c20f0341000800d9000d41040300440d4401c00c1ea86060001c0300ea540e0f000401044140311003454207580d48c426090055a0480315580d45034070b80e4004a0842c099948014000fa001200740308000d5050b4015141501c2c083d60100306041d6914012164030700159102c5441c07150400c00726200d40d080600510140721 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 273824757 1250 273823507 273823519
    0x150103020a030201200d030903141e0a020307020904080702040e0d0903110a1e0602010c020f0309060f0708040b03010312050301050f01080a0b0d0803090606010906090905360f010c0c030c02 83
    0x42992005041c0700c42d01c0b40b0600080d030323180d400070304040e040144481360440c499099400c1082c440203000ca80c1000f16480344a8900200d0810b90b190300c00c0046500a9034060300041c41c83c2800d2601d042540c21002c400c034851400d2201c0f0301c8241c940026a00050b422a907181040321b45580c0320400b2412045400c1504661091408101c010064010b440c2ca40281603605131580e20741440242120080003a100454001d42d1070200035080001c1941d440c40303401c5454664554540f01301c40308a00c101f4030001d00c01c039008680054065192030145048a018066440018071503a8040318648800d02601d9404202071a9150003548507026140c0e100000300305c0003407a8882c58002807a8001c0c1104101d40f00a030000400c40180b00a000c8150094020308101c041d59003000c41c00342c150a82c50044010851380d5000141d00700244643c44030751940c401c40201034042d410044005194950000c1c2c0c02180300f010f07011510031505204e0707409070007800e6403004482c000c03940d0211402d80c500350701641d00c19 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 273826007 1250 273824757 273824807
    0x9100b0d1b090515041104231915030b190b1e0309240c03060108100506030411100e01201509030901090803040f030816060c03050108150103020a030201 67
    0x38143c41450302400f46100407055100b01d01c82000150b508440c0200c0ca001c10a020400420b0000c044149540110a42c459210301c030305c070003060560442c0c1a9201403884d40344000a82c07100d280e40c15140b825803603a01030280c0061401803102d013411a074000103c0141c01002005002224400f41c2201d45280d000e054002042d6001d4081c15041135030000642c0d0000e03600c501180149108041038955400d000884074540360f1911368641c00000d00311418000c3c181c2c00108504000d1000c017010f000010810b0b500c904050070300901070005921081e0080901004015615005945007600200140d4521095040d0041980c11815804580401038411254052400c100071455a441000d00000454551000310300042c100a5650300140c510b4108010501c029240b0650300760076030750000c10b03039a5154840301c00c3e28a1610300c0607028200318075000b80182519499044181200c40c2e070000c4443c0c00a0701e00300c401c40c84d0340a00c0003d40c0001812420001035000d0700c0209503244028444072121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 273827257 1250 273826007 273826019
    0x90206070c06180906030c12020d0606030b1803130504180b0c0c06060109030f0b280504150b063a1506080c071704051003020309100b0d1b 61
    0x3030840c2c0c1c1002c40810a107000040da0407a288800900401084105201c45461611038080c200814041c610070341d60710302010429500d82c80c4420700210340c0710004104040d0b40b418007003c1e5000c20340751604807204422422604d45400002c3d1502c1018140c924821076242204020060000310a0080b81c0111300110402240344001114031504905001a0392695141e0240d8103225005000d00d05000d04104140080f503485031804000c142e01c607401d044a6111614180d81d1002e412006000700008805076200c9003103550400340c0500c0c800c503c000c0c2c5420505c104230060710002c0000d2504000c05200002c1031b020010301e449a2000c1031800c0c414914144a24140c95248101c10b10124070380300c910841c048664281c11000520884c5881c2e445401c00c1d504200f141c0c401c214020b8041001244050740e00c4410400702c80007400001d0604441c2c08443c813001d406900100c074100c03810300030120003440c1d65000e0302070000d5104c401405d13420407101c156102e40302d104901c00c020281c070103040e0011840c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 273828507 1250 273827257 273827273
    0x20709020409050a0608060403080106140904020a0203090f1c06090c050907050406080a0b01050d050403030b0613060e03150f070306180b0316140103020a02030c100e0601060504061209020607 84
    0xb401820001060910300b540004065880c50780c07080d0071a41c888010032000c0780d80601418152000e5180007928403549410016541c01001100c90780548002100324225800100401c510351055400001c804140801c01000e140e1000c03043c0039404c1000710142c0001d0726540503c0d840ca00c030308148590103880c1d201142115a04660b04404164005024041742e07400409056100328600800d1000d5006100000d05a004a00031110703c56180e1020908050180d089007121010150105840d50420080c40001604600c82c00011a072022505402c5040100d220404c0c80f6081c28039541c140c6445103501d0038403c000303000c2020141d4900c0c0c0030411031054945c0c400580b80b48100410a902e1500816041690b0326542c2d21008006250170040b008071001c000300e00003c2400e0041c2c8683c501c103410703421803141c4e05005d809801020140001d10b2003640c03141d504003100c0000c4442917038a40750181c545100358001c0c80d0104440421007004125960000750f100351010b8541400e240542d602d00310 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 273829757 1250 273828507 273828509
    0x301020c01060806390702040b030a080306100305060306040b090f0d02100b010e0a0504200301030c0305011409071a040302040c0806090a0204060c08031506070c03060b0a05100c02010207090204 85
    0x4804e412280500c100c00302e2200c0000c0c51039041c03500041051700090580748042501441e83c03000030304046403100c00e550311395028503a2a40090140c1300040c40d5441c0801c0103905c1164140e10808485000154030381c420302c0f0f00c1c1e00c582c0380640184060b4540303490340020050020610f201070320607101c0d1310f1111582403007441104c000c107400078821032940015210035201e117101918100f00f000c06403c0c41c0d990fa040c410900b2a0402c1e20000b90200a082c02c10310202040180d0841102c00000000704002c86500782108a0b070059008000d40300f8258140442c509c8152a00e40480e4054082030000d1040451482e03091214207444524050352940840d042d160400801404103044204120340e500300800256441031307e0303030800c51a05003010009080c0c0b000b84a809421401e02000280c0103660405030848403080c010a11a2502d84920303061101c01518003081b00e03820b00308400324805051414006c4c05454000b404460389036092841220382c044103030010b07811441401350014400d201840104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 273831007 1250 273829757 273829769
    0x90612040303181a0408130803071407030c140409120c02090f090d080903040302040912030b09010f140315011e0b0a1403070507050304060314090109030f05090301020c0106 76
    0x801500d0103080180444610101e03600b040c4600724011000030b090041d14024103ca46404e0121a4665003070104803070151100088060011550100e00c0080000c05050103030320500300d41c54400c0300c50700300c5c40c0c5a84140c4802000307244801c0061101040c550740301664280040d10000c0e2007441d42c0c58a45a1131412003021000c1080c103c0d201c415800c051820310380c000ca003245684050b0600200d0a81d030390b444001480100302c0e05201182203250244100c400440c4c0041c0f0074405401241010304120a03c0004030000c649030040030466410300410050484912124001d0240e2802c5020340300c0740006000254940100c0c5c03050003402210a0702c042c0a0142c00c1400c02940c0d4114400c3d00ca0840150042c4a60140038060000004d52010410350100b4a60780030342d40700e440f60081503940c0e0040c2c8200410707600010501103109503060b440a064000c04c0c03c0d480c5071549403550501e08a40c192076018001482c1c000800781c0080c00740008101002024000600d00070b071025001e82104c400350008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 273832257 1250 273831007 273831037
    0x20d05031e07060c03050903030a020d09050303090102040612050705070f0203010902151b030c031b1e0102281d0d0219061e0c022e0c140705060417030906 68
    0x10034003c0030702c68440300080038101084242031500d078243d502d0100405e04448140c00080c410500310464201541c42c2e640305c01129103c0c200140594040c1d003040c0511000258144802c22954400340207840c019401c40c0c03140c2d8903140b21501c41c0000400e070158203030b8043d0348810512005850350032020440c400f2051026071a0740035890145640e03501075400240c242d0040c40038582a038400f00c12a0032001c40e410340042c0700d90540c0441400c21101566500e28480505042c41c14401d040d00180089444030414070801780030f4107403110390010301c80701c2c00001400c1000300c000b80b01c5807528501c11003a0b000740380700254240303603000882e40c15018202d03a84032041d100c02040319503042100140400b000441d8400314900803c0000c00310030f850b1401902c289844034a50685070480d014041100001080148030300000d01d030044c01d9109038440c1110100c02c0b2280c04000100b02240031000d464008100780e15140c41d00ca0350b80c400350351840741c102a070300003002980c0d11640c0c0c4200501d030946011103c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 273833507 1250 273832257 273832267
    0x20f040b07060c0f03061d220f06050601050f070b091e030c01110c0a1e0210020f06010501080123181006030b04091502180901060207050406091404020d05031e 70
    0x8014061320364445900c05242c1428000c2c030411448421411080e50600c4001041390780341031804071312400354580c594030f480c241c0051809020f0b00001c09001d40e401000300384502d48810b001112a40f140c80f5a648002d00d0a000f810001140640d209811951007022200c914103a42130306180301912111032020ba03400014a490604801e0040c80311300c0120060aa040403008080c1c2034540b5088030340140203600303001404488001560f81c5202c1240c020304464882400c100000e50fa0740d54003511140300d4440e050002600750308c50180c480c169500c9076542030804446200818411000c1245540c1c410106880038101aa0694240303124483c41d00244a41074604100034084441150a2074052400e040e051004124102d4844580032410480142d0311412130800303003c00139654074000d07808005a800010b000f40e00081c2901607841c02c840402c8036580d54000d01048800300240b0031404660040082c01502d0300c00340c0c1e104013900038803c1e08d103040c01d80381259903101c001100d001002000802e03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 273834757 1250 273833507 273833531
    0xc05160b0c01050a020f0a081009050a140603060403020c22020d06050a091802060901110709020903010e03070507060f020a1506150c03080a0f0609231b030109020f040b0706 76
    0x1603d50010302d880b00840c501040071001c40a2440780b24840411302208502007919040d802c10100c00800c0301a0040020b401c000c004c034400b034483c541d54001e00940c2a00460700ca4600801c00030702895044d00280b01c1615428107201e08100c62042400ea020314180e0044a8500300d8001800038007101180090564100750800c05603c600790004a040b40c81d01031241d0301c00300f0010085610540498440c1d80715242800101c46030360018003004c4050040c0c85002030001140c3c0c01510451a044000740004500004082d5407400f0701035000c0c00b01e1b8804030b0b08120349070160310480d90b001a03070301c141e603450b44030f54480d401984100e100c00d2640743c3c0c0d41c1c1d800f04a661642e40501702c01e00c220b46001c2c0c0f00701e10a510014248031025021f40300159503510001021010341c1e01203401401080000c3c000c0c500500b0988880c9201a2130b40a0485141000110030081d0364403002ca0071250411914110303400c2090600094000704a007800c02e0f1010400442c13200c01c00805027842511440e00030640b03c6600d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 273836007 1250 273834757 273834761
    0xe0a060902130302041515030b060405041a0915060d09080702030d080403081303170c0d0e03070b0109110f030a0207140a06060603020c071208070b04031206051806010c05160b0c01 79
    0x3d9600140c06039010824061040400c1f000b490807090380c5004a800d01c00c140005a00740308980c001c0d5030061a000d0b0103008440e10030202c0c0d040b00000c94400250b503840034036160701c2c0110310503090307070015003048200030741c81c41c0d13038400303504030b4024800b06c1e08040b010782c0428506003d007188400481c101900300010158052b84040d0700c8428091021500529647d0107070010480342e002a007410301402c0065102003920050b1980800c4c01c0506200100320010104d444e41e00661003929490901030010800814a0041d6203250344005c3c101484c114001e550700e1305039040600f1660089400704141c20111300c0e140e07418103618101c10003400312420fa0385044e500b00c030a15030106043c10300501542d0304c042ca02103150001ca5400e14495070418130940340c441010310032940c2c010f00300040c5009000616034000c881c1030001d140100300700a825220b4040000044940346003803900351400001503140d502c10030704403190364459021103541220320300c2150010311083d040002c5010002c42d003642d400000b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 273837257 1250 273836007 273836021
    0x100905011a0a110f2a24030a0b1005030f13030207060c0215030703020901020706020a080a0e1906030507030b0409081e04080a0501061802130e0a06090213030204 71
    0x1121105901040c41c54a540369801035911030003d00075100c215508420040c4200100c3c80d000c00c041e51040075080c030800210b80d40c1e81c2414121354034030704103101180c1419049440c442d1449421156403071081060309a0682c0010300050501d52240c08240864a429044c1c0e20320741081d4650075200c3c81c10f81c0f481d8050300030003058401c5140308030f0f1913000400c0c1c0111350300e41034540d54075202c00310250307a00100d01848800c3d000c440c0c01c9500001041000ca1b4941d020384401c900903820381d0800b0303075520012a0f80f02003441c00a89880c9040040b000c0823800341e0900988820050f04103290850741061750303601410640d0200010a4441c0c080001080d070501c24000385040c121070400c09031440745c4440c0e00310b02510b814120101d049007400c0d10882001810782e030043c0038400032551044200c0c500240079000500c2440d00c0c01420101d070038420740e214000c3d02c40e06040d0308020501c5601d41452407550356806440c44440c159035004c085008a440c0c0000c107a00803c2104030040240b0f0351051000b12849 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 273838507 1250 273837257 273837269
    0xc020307081306032901030c02190f03080f0702070b130504050420060408070e060301021614060c03060609010e040b04090c291b150f190203060f22020310090501 71
    0x864004603101020181003171000d400380780008811010410a81c9429646c0024031646d6224107010000c1202030880003c84178072a5540c0111500d40303002c04104514213030349480143e00405028401c00c0d14103405807000d903110681109060f0360301c5000c2800c6a5044d60181c69148a01050190511301d14002c241a003909503051860980b03400d000f01c1d2211041d0242c41094031714000841c486035000d4041d640c445090b00400906000180b41004000d0300c0c001b0380c0314143c080d040020312400d103d0710a0320301c111009131000d0300d8851164011941001e02391807040e4401da03030304c884c3d48558589220301c2540c6440ba4594a456a0400e212581e690003003156031103901c4100310038480b06544aa058580c2289800c05066070400e681c150981408200e07070f60000e400b101d4504012404070758541c0c150044030502c0170750825041008190090344000c460f4150440110490404079003801500035200c0c10104900d8548070914104c0402640e0060b681c01c0407032440c1c0503090012408621170540141b43c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 273839757 1250 273838507 273838541
    0x210f0e030c031c02120108030714070510080403120e0c1207030f240c0f030b0307080304261006030c0906140d080714030c0c0306010b030a0c02030708130603 69
    0x902100034650301d100b070b0b0390704000c43c44070038401c20610810b80e0180c07407480301641d0000d459581c48445003a920b0700555000d403a541041e0040c40050070001c90240c080d904050100010074040950540d11010b024000310100001e801003622031079401c1c850502c044107004080c01c00e08040c041000010a00345d480c0360015000071508000040c0108072a48ea142e078442014481d201c645000781100180340e12140b055a402c4c003120b4184c060f8407801c410380900c09500c08001c2040c904040c540d40e06024040e031a840d600401c028000e070241c010000c0c006a40e028440003603800c2201c01c560400c0c0988000008681c0c40b01e070309208000c4002240341c0941803042d41080068907080f00040008092003c0b40e003e5210b6030300410900c6005c1046400f850b80000c0380c45401581d84130b0705956503000742050119801981c00c580200d1501040440c121408104a00d0840d00c500c02c101009108040002040d8401000f00d00d00040008002d04806440d07041c40300d102a1600302c018007610305000200c47c1c44c02d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 273841007 1250 273839757 273839767
    0x40b011409090c090c040902130603051f09022203140607110601090c09090c12060f1a0a020c0a1514093a050303100803160f03210f0e03 60
    0x60002509030300f08581201c1160458584400c4011588501e400c2081c00c103000080064040e848945c81340210350380e994080003c3c0e618004d00d00c240c40040f00300400c80d100004005c20000c0d0164001d0580c070f0720b28070701110001400d1084e60311020034980c81264189040030b0416403003078081c080705520003183d0406440103d0720950064440d01c05004d1088010b54805405548502c40c2c2c580c075010781005281003041d90036506014080001c3c3d0302c00c00742c0c03990805401140c1d0706180c0760482d04071001e01017060511104080c8891854100b101c01c0310031032045200008940e07850f040590010305240c40e4603041494401001011900c0c101d81120a19401300000740c483e072607140c04d00702d0403002140c100e00142450543c0340410055500000230781d005180c00300f414400040021802420480c1407403210f60303036030384245889000d03080c03403044520744050401b40801c014490f0800114480d2920480841b041c01e04000d600500c15501c1c408103565030380c0380b814502079205043d1484000401036080c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 273842257 1250 273841007 273841021
    0x3110c0303130b07061103070c050c060a1d0613030f06050f01030f06050a060e01060201060f140108041709100c020103150510111e0303040302100e03031b070605040b011409 76
    0x490b1262080942c50400000c44200348882580000c42e80a102d90109990b0b040c40c003002001c1b402894000d031007602580d09941c026103040821680383e10041c1c0c4484994044e84240f000c80d543c140c07180241c0199041061304545540f0001b040044d6120303102412149005041044c105d138402092040064038460050020030581d00b00b280109038010008940c640e50300103404083d14280d80018008018000086005134040d001081525103402c5001072003680d81001301c881e03c0a03060050b0200e6502d4001c640400c0c080c201d4003103030b501020030940c6418408400300c0c1381c40655209100016020140c0b035011503a05004540c03408404c806001001814800010308034860b01d02c1560a002c00e02c566400c1b03c000920a120300c8104410b01c05400c000907001641c0ca91f4022141200140910300d0781041c0000244650b00301c3c0d071081e0000b982140d49080c01a60080c6801001e1041d4040500c40d00c4000391890140340e21a502c1009610959454260040d00d4910300b40030452280ea2058100000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 273843507 1250 273842257 273842287
    0x1404090c06081e0c12041b030b011703190c080f070f020406080c220b060309010f050c040308070305070c21050c04020702091501050903160e130b040204050601050f040303110c0303 79
    0x15a1040724001c0d101506e503484c000941030040a0030440140c10010004140104032030880c0c101d450f001003821451910f4030905849116141c9a03601d0003a480030503e8105200c2c42d031200410348580c0d4514900380c0007001e074011542200c0d404580321480c460706041181131502030b08008250b418024a038021018002801041c07025a901270fa202550000707031001542ca800440c0e403e40c0181c4220703503e081000115018107001025000c055003490081080700d40c2100031202100d411440c03003401c180190390300b110980c2c05110f00b41d5003c0c040035400b140c90940410a100e144901070740c0b9035484810740c90301713508150015014510417407050007580d0158030340c25140c40e4803c42c0158003040d030140a90058030280913920b5081d4041c858114104e482500c030324508020f850a5800079150303030350b854030035030100d440c006401411030840a001c41c0050034140c120720303009041410114249140d10b203020b02c960704268401d41c00103041c8550000b40d00000d000d85640d44400ba0003a40c5000d034520078400d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 273844757 1250 273843507 273843517
    0x806040506061312060b10090306020f09150a0206010b3a0c050c0714014a0a0b040806070c1103152e1404090c06081e0c 53
    0x2019a80303490009107141e41d85400c03203032110300401c1481e951a44400c10302d01040e10300d182c2100e03018603051951042d0320703100d4510785403203c85542c0ca5040c1400d55032080042d4100c03840d1002006410b10160b4155540c04003c05c9285018803099511103185040091a0640680c071080d04441e042100748030881006803d68500d203401840760311000c8501124845034608500424030b003525205000c080c20380d03c0002000401081d008407580b46803108081c55040868021043c00b04800442c5251210b42d0442c4640510614400c00c00ca903400c040e05440707880c8641020b40f03000c44801c0261401c245001e01d2984040c0100840982c10142004130300b0b81c0d20302014040c5002c0c81801c2441404016060010308101d000240540700500310800e07900440400c1a0343c80060750480c00c000380101103090b900d803500340b089080345030642d030319082000d08000b02042c45150410348070040c1c0c10205180b2156880103006076504c52140b440c00b680d03881c000c40ea9400042140c0c0d0013a5003444424003403003064070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 273846007 1250 273844757 273844759
    0x20d0305090915060414011404170d03050c072003070e0106030c1103070f021c0606150e0f1002070902031008070f03050a0227040c03060e01020a14070501020c15010609050108070806 80
    0x200c540186140140e41d0780908c00e07100c030310050000802155440e6420100f8400075149400c40700c641011034026020741c2c1044034040320301e130006e0000d0b0002c125441c05007080306560007817600d0072141c86008242010344503000f0003400604d207001000166030502c40d001e224922450f00361100e0441400031600d80c41075590142444442c5009041503541d01ca40420a0002000c40c0780c107101e00928160f400381495224665203120070012024820380145210803507120018500003161002008204010b04d04d0500403085201d100000701c0c44007414030046004a070002446035201d8a014855484d0564640100e4180ca000302d10800c0040c0d40061901195035045940030468400303690307803100b04402070920085003e4058240b00501c40c2d51040e403000e40b4041d4409000d509508803a0071300741e01c10b024046000a50700078100c1805200030020f485001e00c10f100152031314a034005007614104110050b52078042c02c240040288582100341c0c2002401e0a00305610140f80840c3d02408441c0f0040c489 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 273847257 1250 273846007 273846029
    0xe0304170705060307030e0d090e0402042f0306041b0f030203072f07091a040b15030115080601021c050703030b060d090b180601061407020d03050909150604 69
    0x30302455081409144080d05003c0d05843d120728001100070003808030034200d480f1900642040d411900e01c03c0307108500b6101428210942a26a0382c00d001c0141403011001241c01c1c0d10f01c2c2d45044a5100526000821061406090700ca04040c0200710071100307003460300d030f07074091980003005403440d00450380700f5079201541401a02ca41e5800000d079558003018007280c50541e80307202290b404480c2d11904003035010141048607886a01e801c1d44100701d52090001240300a2100d040103010700e030507080340d0500302c0c001d041c1c09a03191802d0020310081d00b0070382280101d12119045802d04c1903001400039403111091000308072205020f042c001d40080401140301c10030400080003003d150083c2c011900c00341001c0c001c59a0b40d1440410301b0004c1117540000c60340f1002001c049000f514800c2014170841491802400300c1e80d10f07281c4103580b01503e061b09001d11030000d0110700003503501c42d40d451031b15902a8903041d64039442003003005420540101985501550074a480170b042d11002e007510181ea4401c0c6407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 273848507 1250 273847257 273847289
    0x40e0408030907030f0f050f0601060203040b0c031c0204150c030f030b1f2a050607031508030706050114120c010e0607050618150106080a0f020c01090b07020607030e0304 75
    0x8441d040881c030340c10140417140c0c43c111480030480d041405004050040080d00e0182c42d0003061292541c03000e00c01c8030010b0780140400d0109403660130040034a20700e440103d91610390068000244580c0b0070300c03214011540450204034100e00d0304048200b2030424501200c0005460340e000d060350840c01d5100c001c2581da104d01d44078940320b03c54410000084212442046804900010175100300784401c00d401e1041111a41c44e590001d80285240b44d9101e40685101c1da628a001c40041c5140000518250100c00c8000740c80e400030310082108a00480010a003503041105001580c50922007a41c01510a1501d9440c11030703021521003400d08007460842c45829030303a0300080450290082c040d18601803d0148002003513007852a4020300c0048040e100b611003030608114103d03100740f144401090f072a000003055444540d002c485000c0745080018100860310700c02d46d0858141d0070b021034010343c41034107210900c0c0d010001c040d80b0040b580f606010310081e00c8081500ca001d580f161090024a22003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 273849757 1250 273848507 273848521
    0x60b090c0301261c0207050607050a080c031308071e080303040b070323010807120b0c030403030f02040b0702010306090605010e130e010e0303010e070f090302010507050a02130218030102040e040803 87
    0x39083e0f00c0d656810481d80500503041c85a15240c50080c40c500141c401e12030009920304021043e00e0340300750800046c000862031a2261440d079030000120061034001042040e50742c0c4007035060341001d071070104028402a410031b1450380d010b0708015840000c620000700100051200002242d520175802016008152a45881640503010302c01c1e00100150112043c0e0b0000b0010009d494120741c503a8048802607035503110110300c00c2c2e030080409410807075180000b1325071202040045801511900d000240b0781101d01601041b600302d0b030048444450002100c0d01503607030500481014010100c800c00405160030000b9141100c10616140500102c103181e1000d004154448c40000c5075100082c03112110700c03028141c07030758000d002c0c00c00d01c214104080b981c11841346401020081d12500d038201041c0c00d40c1c0046d00c0c036400841045070140700d20351010006854100381481c60202c0204c0158aa54280000785d42c140045074903070f80aa8410f1000f04000c96024140c1600103070460a01940c5e900c81d05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 273851007 1250 273849757 273849809
    0x403120c060e03091e0307030f1b090209031b03190c03050105091e0a032313080601050f04020c0303071b06050405160e0702070302010f0905041503060b090c0301 71
    0x502030402031414040020b2210048000d1200310411513501150200203c107400600d15081242500355004500900008407041402030000c0c0c0641d080103034a0010f5441e0004140d2542c12a50703030356801003070901c000d007070412500036009100400b20b02d1600000c0c002c00d0f5075621030342042811140c260281824094143e500c0409035030418005d01582c42c10660322991036006e250250110b1101080a880c40d0101003070803612140e0540c6c410141007104039501a00e204418002c89641d40100f11201600c01c0da40048030040104031f024040c29850711041104101c07101c81a20700803401009101c01c0a100402182d520580c00c0c00c1005100700341046d850380008124100401c403d25010602040c00800a115600910021081c0e0032941c1c03038240007288440e0642d0684090b0380050814001503001d018030b08100c414520740071816565950000c0d068030007427608100702c024809804d1080c04058050b5aa84410944000040d820089407411043c881441080f907034007410082c0d0242c0b0780e84d01c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 273852257 1250 273851007 273851027
    0x3090306041214040e010602240f0403050c030705010b01122003040c0513090b0a06060f210c0806100f120c092d0501020d050d021e0708130b03010b040312 68
    0x142c58058486468050178034103048280600d10252040450303c503840c0e03400520407061b02107042d4840040e0740351564800b6031001301030021000e102003400500c8500c1c0d0208080c0030f92500410010414040f848005040080221270350f2000a0a2005040078420004a100d04518052641030b80c0d130b54481c1070240d80800c03180c10141e0b00c030794880445503e644407130b00003240450155170061090303210401c202040700c0c640d00c40c1e040400e009044071303074005025078a0442e80400d8a0341d0880301000d988546411511041e4850000c10894410b0100700d0410884d810417100b01da0901008841c0e502402a000030900050445800d4480100d50081d1388280b02c10380050000c40e03200b00c2c0c018074800488400e5011441500354031000f031400061950310009000800040648400303261003030b10b82c44040a5071210458400301683c01c820031003080e81c41801010341a015401c1b0075240e03070b443c2c03600800800300d0f640300026444060005105803503030344c01101d0842c2d9100302c0080c03a032210318400365050224 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 273853507 1250 273852257 273852287
    0x204050106020601170309100f0324092306190308041502010b010e060d090503090a031202070e0603100c120c09050415030f140708010e1e030903060412 67
    0x82400004481d5000202d0905036141107403403011401044da1300316520300400c81c20f903512025064082480c1c1d4015241c111801c0018034002c900d000c00d9103a02100c13041c0c007459424104c41070030400c21252000d88652404002030250050044d511560032412403c00602403500c9411a030f4003845807420750b414210025507001415a4a65580e04000262200c58203040c101550805042891541c0b041d0b0459900c3d850003041d4500b00302e8520000f400805202c0c034100d0740343c407041103500340d181da90651150041d44242030a03000200c201200a040c40c030385901402c00303050303d1414071440e9680030840003801c074135614001488094850302101c0a0820082c614046450b04500f505601e62040b1101e06480003620700380101d8600758403800074442c15100190804140c0c00000e40060448007007081a01c40443c126038040d900d07454000d00312414088244202d40c06200a40c0e07044041c5071b1045103c1d41284007840c180036030100440d031290310040c0003c0101a1052915003ca802494240598a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 273854757 1250 273853507 273853511
    0x8030105060318151501050c070b030903130e181b0112090614070809070f15050702060a090815010303020c10030e0718050f010605070b040203070b16060b1f0e0d0204 73
    0x820f8211540e42144c1524013882940700b0b011582020b501840032a0b003a56220310050194528240040007180c2000e091410341d400100000d9400b00d0308003540c0d4001c0e2544003050b01c3c880c103000c0d00d40040d00c0030800c04810207030001168036948c04c1c0f0781c01e00c000c0001020b003001c04007000d00d082244020500c0600c020002464452024140b80021106900c40c10007a00d41380d010341c46211000c5d0341d41c0c03210702ca41c4290502d540c02c18020100400301074070f07018096041c0141401d001d41d00051094120511050000380340b250200b140c20020010160b4455400d4000302055045490003912441e000e00018011442c42207042c054078425484840101d11480c2969400c544481840301d0104880713a00003103650410b40482c440d001d001c2101412035843d6111103103040119034a000c00308200810a070f0f03060140c0d080c0024001d030301d10000d01c505030b094044c8408441c0940b030003404545e00b1001880c0210041c813400319600101d00160a2040143d090210001c5804000240c01c0d02c00c41c40c0c001c0d0014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 273856007 1250 273854757 273854773
    0x40602040b030c09100206100b1c141902090a060804111e0102010b0a211110200115051c0f11030601080a0201091505070501060e2208030105060318 65
    0x403243c2c004e024800b60442e21158070741d146140480c1c0d180c000b03903140300b01103031508000c200c0c05a50f08010404000018100952990481c010101316803117001442800d04100081000416084003c00c0c021502c0803021410801d8050200d0507402a0303002c0c0b4428090580b000c0340500c20121030320482902c5c028144500e840340c1e40c03138003004000002c030720358090760038007501d0401441d001e401d010544400105080a1120390102901d00414409040c0c1c2c050000d51000c0e141d50311095021024502c1548610003008640368403403201d52100401b100309031f40340003003019180000c0c4880074210f03031007110200c0c141c507025140c1402401b0300d00c07402444e081090403080100070b417440b40c165640c0011800e0318500c1e03a8942c585c545503a407015000b03000400088081c040d5141f0545944060501c0b403030418180303401030b0b448070300310f03941354000c00c050301c10080c20821405107001401c8480b007110142140c0e50611036642d070099001c1801820310542000c00010b500c8100301420302c46403000001299001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 273857257 1250 273856007 273856021
    0x2090d05060405100b061810170906010303122901030b0402070c09230c070609050a0606090b0604081b18040b0106020105060f0904240207150c030c0504030803040602040b03 76
    0x1030741e0b84c0850b441d000d810700c0500816854400182c4000c007010203246a1a01c601d4002c010040e08440074480c1804004403041582d214020a0b05105000d00d000a0510354114280504107208690809130540c1c102210364004000140d5942c036480da1110805032110b40031030059000d07040d041c078840c0c2c02c644042008800d101200641c0700864071800010000b0300130480401c02e140c840304203240400f0101030041031045100200030f0990742d00440001400e9900c5a44c4c0034180800000180c032850740b588400d1222143c02c0c4100944108103c0c1c3c2180340c545000b40e555100d00f030b11407000d0003c1c0960819031100e40c0350303200e11b034440c1e440009500c20b41d4503040c0740a5000300c01c01c0c021380b8010f40c40d00e800100b15052800c42d60684200c01002e164480d80d80365074000040c0c400341c003200042180c2214000e28165603001604449214103a01100740000143c1c602c02c651584404000301030418103031102d8690400111000d0300d405c0359045650390b88606182001c1c2c8241d80c1310a62400e00001005a0303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 273858507 1250 273857257 273857263
    0xc190201020301140406050907081b0f030430050f09030f070906080102210702010e01020a1d060901080f070c05100f0b0f2209020d112e0302090d05060405 68
    0x59620501004c00c46040107810b00080350003070301400d5004100c00012580d03c50080782c9c8564403a0103519501000842251402e00c1508002140605c040c8040306100402000002800c1414104241503801d550700300781155007030b00c05607449014050005945141802040100d55620300050b0465103001d00543c0d0305656200b140c403a4032800c0345412350102c0c3c420818021501580c0d1051002c1310b041412074001601500c02034028020341d03583d80b9030703580420020300280c8455141511082d802409070408100040300c00030080c1c0c49904204003044e080c0e80c209480d190070050502c003140190381e03032020a0b22201c1c1c1050014046114580403d5108452500440e4190713440000500804a8030001e0040d614046208075034010680c01440c0c3c00040c9070314461030300070148200031811481607004110202c42c4004141c904500d0704004808c00d041c0104810320203c4011394000c514008a00140206851400a4410141c0000b10701d94aa951004001d41007900801502c94504103498401c2e5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 273859757 1250 273858507 273858509
    0x120318012304030f0509030d0f0e030d110706020a0b0a0e0a0506040804061d01090e0c1e09010206061002030d05060f04141501030204050d0b1b0f0702090a06120b0c190201020301 78
    0x20035984c621200944140142c412860029000340202842c6a10545517007401584003800c209495210120381d541c10411740b050303820307607440c0c080300003401130341250410003035402c410255071004e800c100c002144040310990040072034400083d030844425040341480c40b10400170301580b2030102804240084134004100b228180c0d10340e004146201e40d0402d55552400e6945408500785100420000310000d10550780001c08242e51458507240d0700003c00304e103031003141e000c0c41c524000c600d0540301d50b01040001e4100008031102100888281c3d002547c92042682e1000c25945903000f2680b142c45805400c10b440c10010424050080310812503250300d081180d525480c0c0c0c00c2e021880840394044d10807107055440149c25200d03160140d8403019002c0d40d018110b60070100065a0800080c5c4041000e42982c1d40801010783d9200c0c0140100510b42c60050701c164a01842d14038100982a18084525501d5600c603601180c19625025814818000c203280800c50006005540c041c156065000714 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 273861007 1250 273859757 273859763
    0x2040e0103111305092e02040b0d0c050304020901031403041503050708010f05030709051003081b16050609010f02010e0303070306030201090e090607140405100e12120318012304 78
    0x1000b91030b030039034543e0030703210305540004d039640007030020304c4105980000b40c646200d5401c8809240180c2070f01410101e0740b099000307420800300802c031003000c05220b000b080038000d1149042c9046003000d400103800c8403410321000f00b00316154907102d031b030455062040e1001070940c0c01281c407611001c0f0b94050060401140d41900140c0c1030000441c080083c1f010034016120301500502406003041928002003c0c050148001031020b1080000010300910040c0019850806050702200d664001e040c82e1240760000281068400d203030030711160f101e40c0c060b44c1045c0000d1030b020b184a007000d4002c1e4018002c1c2c00f000c03401c50000104101c401c64064014404580c802ea990703c5442d6502c1d400351b01c00000a945021840e0041408901d0317417807154280400340b00743c032500685031076035030700004402481543c803402c04210800c4980030b951920302e607003082105418019024460014031024481c4c071004000e1001c41c2041050030341d088100351b01c40c981081c440744040603c000103806002004204072070072 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 273862257 1250 273861007 273861019
    0x503090609010c0e06130b0c0717070303020c09070507151e02091c021c03030518030c0a02011b080d200a0e10210f06090908090409050102040e010311 66
    0x106254420512a440403460340781d0702c4e04100d5040c4420800c060303221403500300c42584800004110501c0360001020802d4541c0d0041440914099444001c083d02007543e40c1a90040c1e8000c10110f5008200000b40c2542122036004035581d41c40c050301d403400f488202821000c0c1240581c0c2d04248503070301a02e240e48218842014007212002140260700c0b41e8400180c011001829031803114682003440b010301440104250101301100e03440715481c0101007001c0e00080e44500074001d981e080f50480180d42c0101c40080e6190150041906645031007824009040000d03541d540c0440b21144445a038ac00741e8414125a600c03666942c02e1000340c040c0100310b800240109102915140b00c4904848101c0125221170000501d41c50410405c10f20001842d402d21500b07e1242d085028000d54000040341620b0000444040e02c02d040802c62341103404c1944198034007003c0c0ca011070f0f080800d0340d0000b807046501140c81802840c1107806802194010305414070920008810403141c00d118100c141801c1e140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 273863507 1250 273862257 273862261
    0xc0e04030e09010b130b07030e0d03170c030103200a090e0a02091e041101020102070c0815090105011d09010608241b181906020304090509010608030a180e0705030906 73
    0x2e444d100b446142841e207140c0d10b800404015001902000d0074405000e420410a54801036010890810100b041180052005400f60b0164035070b10300403e4000181103941815503055558408680600007a0034840c8040c50f0021a51b5030b8600c00880d02908d40c1c5c42c3c0500c0055841070115603200300b5031a089205165510014003000f100040410384044009032044042d01c503a02c2d6030850031080000c1c58115502008400003003004480041c0061507440c0c000c0628240040d8142d90303040340900440090f90504004100c81c1c004441511200018000000415242c199045004120580c4000b5a500070880b011a00c131809001c154650b10398008422440e84d02d031051230b45611b201c5101410340344400e00c0385005100e02000596000d4002408078400c80205646502d000a0150300041c0140d1000605000c0c0a07014000c064115840000a000e2907003000041c94881c0100d03606072081208007650700f01c0040c40702c40b14000030140b0490040309420040e900500691040322041040d100f4400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 273864757 1250 273863507 273863519
    0x8100b0301051b180414060102010c020d050307140d0f14010906060503190f0f020408010f0905190c0e0a0c20060601050903070b1902061f09090c0e04030e0901 70
    0x5052241010903a0b03000300348668603500d01d480d00401d40d04060100740c188600513607210741c820035a180d10030b280302c098903181c007000081c2510480c2ca100c404541006401c11092030300007042e2500300c078560030140280b4001c51400301480c0a8100c00000c1603050010b4900781000d164814041c00c101c08600c0c0905a0321414030300d05a500b03511901000410030400111480010b24000b9010b0030748840105a100e060b80c440b03c191031941c0c0740d140315540d000504100e031000910441c80610520032051001691546a0984560b0040420014244426000340c1000f0b049500c08010b00b00903c01c1d21100d00f030490a502c01041d5107910344010600c0705480c040101c0c005000c5c4005245454028002581c80d0030045645800c5102c1e081e4040c0710303095000c0354219140c40075150511309040103611003c0200c0d4003e04d0242c0c0908480140207100b4003080d0080c1960650500740c585418001c904401d103481c010307001e0607190384022400242e28003030000705a441f82d01c04000c49400c80e46003c9507601c6403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 273866007 1250 273864757 273864761
    0x100504110d050d03110403060f0606030b15120606070c0e16110d11010609020a051c0209090103030f1715010305070306080a0f060f11071203021204020603130c08100b0301 75
    0x1c500034040783e000e02d06200c00c0d03e200e900038104264501d00520f00301607483d40d888058034121860344050513200e0606104944e850310980c0d0340c403036086840e0484400311a6120760580b00d005502000500180002401c130340f00c910454040903401240f03c850750b580d442202e0007520060700c90a00449000f0115070307229216659400801c403801001d0110300000c603805030b580c908224000d440c5075490310000504000103201070314401c4603588850360740c0c403a01e942c414030501e030311985885901c0c03040c850381000da1203071031030030303041d40e615040c01c40c6500c1c43c0708820740d00c41892600e020754600c1202c0801420f051320514004112100b82c030141325584030706400b9401e0300d0035405006815808080320b0710129510000c440412400303418001100b925050b9624140e9219544030714822500180250030011108040602ca01141c0b600f1414400c070550a141c03145006400a480f920740800400c030b20a43c0c03501202010303035000e8100044a56a402010788a24019512071250340c0b401c040030340d29003018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 273867257 1250 273866007 273866029
    0x40b0403200105211803040609060207050402070b01030b0c07020a12020f030d02120706020c1203090d08061c15050106120e1219020712030201021206010314010b0f0c10050411 77
    0x110095018503e13120b07040441e40140100300040b00030041194189402d014802030001d42203135618503c5641c00e1207000380c6070504651205020310310400c20340e00820403000e0b0080c15641e2000c0d114505444e070040352440c50052240107580800c14a2000505110300440111454400c1d02c284215800140c01c141d241c012024031031004d0380107020300d07a007009800c400806400b4401c2c2001401c00382c00c8402075107401e03500690021494030002c144041c400003080200040f160f1032070f00c0300003490701c01d000c60559001884a0b050111103142400100107c0ca054015800303c0b80008000c1903a5076a00148180c41c1c00101c1c05180f840c103541484080b9012800005840340c00c03440516014a039252040300c42e030003080720011805004001325404c0650443d180b901030081e8005a140c09041c4803034200840080e0410341407615014403006502c0c510085130f411122080100c0ba121480c40b03001700e80521a68880c2130703803802202c41c0c61f040c5c5c04040d030115000c1e90280700e0080c034040c4502d003403003100c01e40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 273868507 1250 273867257 273867277
    0xc0204060e0402130b01050c0601030501050601090e040809130e0f1b030109030c0b0c0c06090a0c0609053102040e0f0105030304052b0f060507020d020601051014040b0403200105 78
    0x5a11310046085071550802d139808141031500b607140041c9140324134207011080c0c100311080c0c0d46a0052010700d47c0d00c5092400a04011540307041d0a00701a42e60701d20a00c0303014141030258555464560080216502c581003400c400300a40c5d0b455042a060721f516480c071a04064401f0058260080503804e05101e80314005506459075100c0902d252034082029100802c1165040f000704961030704075406001e030368050400c0a00a100e2100c061a01566840c07140c0c0100c02000340c090801c000d20303a9001000b20100e20900c00e074440008072a00a00e200003142d2003426200f600009002a00e00500c024851091907208a0052940d072038908240d00ca101d28402d540e03100320500e80c1c0b0a881300b16445c4004200d0340000700c4205081c41541d8904801310090000d80f4500e40e20030410038255014003170005401c01501c003a055030741c10000001c00903a640c214800821014402400c04083ca96040394085e10100e80c02c0f0352141e90701d1400f222510880c00d05c640301100d41784181c2c02c565000e0360940700d036022 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 273869757 1250 273868507 273868519
    0x1206060903030e0a0512210a09030b040f0b010609081204061403250c0b0f0702030a0c0312060b041e0612090201031803020c1008090a03050318030a0c0204060e0402 72
    0x71950b1011a100c0c06402c0c8121391199494200103829543c501000e2a0204080b000e400c1c110340320200050198000012860042400c002800703c482d480010b50701500e03030000c00c2d403006846900b028215041100e90060140701c001001150b01500000454101c50043d02111215030b9001038008540c01540701e0040070030b04d0036900415414038500510b5000b11488165005880a000040001542c460703024021400e550848005e00074045c04141d0301519104110682d8101844029580d203d0b0400100800c070b003c1100e40101845007619101c94005000103200682d1120a900c03040c1d4410302c214081c0b0781080c0c401141c0b28021003030b004c00300d9010742c5030204040212800c54015050406040341015a103d01003400050244500402517000780d0050600c0a44503060020540b03005030310740140305101c001c00c40f03260700024070442d040d075042c9441a2a52148141411807c0091042d021180804148540060303800340c52141a03a0003190144400390342c44c807925490101c00d07980a50021 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 273871007 1250 273869757 273869759
    0x80f120d0c02030c010c120e010b030604030f17160306170601030615090c0e0f030109110d0314032d0112030c11040e0606030c061c15090c0e0112060609 67
    0xc60554004009100c0d64015a8500004610003c0c03c4500719003800010441c0400780392030742c1003a1312030801d4001c0300800800400e51280c000903954000200b000f070400c94001c91282d04544a4003a021411240c46600b1000d4146039104810b80b0240301c0083e000a8640600040d8040480500104000c0044050100f99080d6210386010b401405400d5103214260708001800c80214410344440411a6440c22150f014035800c0010206001508a11030b070304040107807002c11042000c528a401044485024089113444c007038440d48080084114250f00102c2084040b0840c0801086800d6551404002d00500c0c9544822a22000c0c010364070420400482c1f200044d0141c4204a030a5001e0f401c19004c0003803030400103040d5110300c0701206e00c035040360040c00383c00e0400300211044280c086407402d06150600c4c05485514141e02600c0c003a03151500020350b05a02001c641c2005429407102c18040c2c07000700f41015091450f188020785c001a026004d031201e0191074030030030b0301f621125a1071200c09 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 273872257 1250 273871007 273871027
    0x3080a020106150507061d070902070606050301050f041506211103010e0703020103060812030c0f0705011109090f07120e070503010c2601080303061e030f0106080f12 73
    0x1a4000542240656503111804500b0901c1d08521004916240e65465501c3d0250b10b04403055031411446641011146800702c150b4142c081101801d452506600585400441c10700c0c1014101e80d034041c5d5019483c00c020310690098241103140321740d01a1300803020060165100e58102c4009100f6852481190f10070403600c0c0c00400c0721002414000c000c6441d050b8030520010f421a04241e50941d40307030703000490400443d6018000c40b0001e0940a02406003500c800321031010920005080d8520b0b40d1000404c000385411840644100907040802003012881c480d03441d081caa444070702d80c2441450903d0016500c403040c1500c00e032154820303603a0308242d00302c0416984050b0080844154041c094401c011800351024851900300304280d40d00c252020113000f80c40e10840101034070124062004000600c0300c0c0000100b01e075041641584c10000703115018040c030542c045106071043d0705003d039a00d001c4038040150007900c10f403002d0f0800e035051700740c080d003000b942c900c91100e40041440e01132044d8800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 273873507 1250 273872257 273872273
    0x1090203041b080c030f031206040207020a030f03050315060901020a020126040804030308010602070b12060a090e01140a15050409050c0307030803160908100b1201020a09090e061003 80
    0x428480d60b441244a01d04048440c80302c0d0460300452043e5022605041c1c1c1e518040054403010344c3c020014501e441d407400041d0031074500c010321007400f503600068410115192003450800441d0819154000e07001e83e498014401da10559003100000a41444d114072403030b20400712110b2600503001009c540720180d006450926000c9012500480300d03803210354020403840c4600d4462442204a203682e1811480d01071700cc1c5a040c0c101e441150711000b03060080c0740014040720381035407540d90a180e007075a030a800181d061204d0b80040c1c201d9401e0101d20840d02c801500f00b6406a440e074003880c49a43d032610414406c40794140c0d580e10b17148026031010080c40c1010b9100103039081c001c03400d44060400d1200440d05c0c2c10034650044900300000404c02c00c036400180119043d80086241c1081c0080c540542160396600c113580c143c0d01c203551100f996403540c4c0c44017a10041060088000d64582040c4400a080c0020900c55004094107040401d81210740208426119215060020700b11909644038001c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 273874757 1250 273873507 273873511
    0x30c06080915150303180301060e090a14120c0d030e011112041703162d0509012708070b07020d080a1b061d06040c18020d0c020102040f0b0f0301090203 67
    0x300c0038100c6009200351020720007011b005c04921807044d81101d00c01d080c542100c2c442d0740071030078480da20018030824800109003802202d41000700601450340e014625400d00190b40311440000382c0002e0028070301e050100300b0510f54500c6071001c00c20100541d15035802d840340725081c030185040400212000828403400250014001d4040d070040306054401041e0540c001c0c1c0f420307140900360307902e070600450f40f251004031054440070030500e414070364100c0c0780c1c1a5414228200c090203400314512009034030480038144480070b00804003001740c2c290f081c00c0104a110780203501090182c83c2001c20a49402d4085a0702158050300c03405800c211070721040c88607001203510504200709014290801408104141002d40c000c0f04001490910351483c420f4020580f0030500040c3c021408100100e40380080f2401110b2500340160301c9202003180b860020300c201030700700312700c0ca00d000e00c4c90020b0f03a070541c058419a419100220a400d44800a070700d5030740104900a8581036040005100b0900c05c0d80180da = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 273876007 1250 273874757 273874771
    0x51e010501050a030b15091207050306040305030a0e0703080c010c05070503090d0f06050f060a060816080c0706020f040807060c050c01030b04090609211119030c0b10030c06080915 79
    0x20400c410300c001488101351b903424008900e4001c1a400c140313103006e10740b0843c080010002800c2c05817800c1d001c2619150014005018890040000b540c01c010f035400644001800340103440c1030305c3c0c4914204125800000c3c040d0003540ca00082080704a0103941210201600000158202402c90081001041141604885204401000388009500da008583c00b0b00c9101c81400482e00e0b0000c244494ec980360f0384201c00b000a600c00b44a405e404480010400c480c2c40d180c0124540c0c2d412035034561030721070400002d000910000d50361000d10280d0002e44240d81c40303402640e40c010347d10b0f10308843c0c171580303440040d01d190040d2016089560003070388010313520100a440400d110440342c882c0000c8503082c190a44229102025072482903203200c20706200b000c0c05003000c40f00d011288840543d44c9421284400119500c50100000d160041c081c2e06809a40701d100d10b4450b00c0e0911100300364504a01c01202c10700c440400c08034025000780e030014401e804090050140030101031103c03400d880040c22030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 273877257 1250 273876007 273876011
    0x206040b09010b03060403030e011b0e040b0103020f13030c05150f03060a03020a03060c0e010503221a070f08010b190e011110021b0109050309060705240901051e010501050a03 77
    0x6403c0d850600a080c030540c001e460005a0b01e2a5003049402d640120804a0f403c1006425080c0e4003a0025040810340200341c9001403840d41c1a001a8000d10503d440d40daa040004602c152103500d03030300624800c0e2031007007204d00c60f020394072400d002d840d591018040403507103400d002401c1701d440700740701a50744030800401c2180c00664a0300032401044044d042038031075a40390892540a590480c001003400c045c20302e003091a5150065040c0c004102580300c2c010501c40e00f5851809010902c0c46825101a0105200455081024015280801d0f07030120501180000c800090b0800d02c4900f5207908405428040d50300e2869004119140c03211501614184070340c0d8942e080ca560010455200450381880005030348a11688580481024000030410340b60f04003d00c2c1e900045011091300c49070355042d240f607901c9051a01e4640c0c100701400c0f40c02c005800207401c2c10750381441c0601c0020302039100c010003000f40d51200720541101400d205080203002c60000c00401480d48201c0081120040500e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 273878507 1250 273877257 273877271
    0x60b0405272e05060d02100c050c12071a03040f0b04150903050d0b1f03051b0a0e120604030804140304090f0c020c010203160201211409010b100206040b0901 69
    0xc00d50440704112010241051031908544902c0c600707108031030f000384c411a4041c00001041d03001800002c40c9003221010014290034030010003004001444401a005100550402c806121076030f58448a218050048565184401c0f880040f00c044a01941d04800c5400c45114240c540c450f41c2200940700300c40e48400c101007034807072070014840c1240701d91003540ea4075591060000700e43c098500800040e440b510130003400c0d00d8001c1d505100594241d41508011400d9903800000c030a0f40582d4125040c106000000d150064692101512071100801c4403040c50060884030f646565002c01c03140100483c000d000070502003054181c16000706104503003240c2c0ba041e16803031060305403011418050b42080e11501507082158042c403443c0d9000301c0c20310055003070001c0341c41d207517050007807221000e418000400305660705002000d5096114005095083c80340005a17070320135201c020304840e8000c095103040d8403044249408011100101c51940c000c000e542c5031611440310350310700901008625035032841c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 273879757 1250 273878507 273878533
    0xc0803090c030c01050a17090f0a030503070216140f0411041d0901021e030415020a26190e030c070e07090f0509040f03020a1707060b040527 62
    0x46208441100281c480948048141441c00040341e5065040c018103019044845511010090f0015494500b616046d11030554450174407401c0c2d0301c02e1846020703031802da034181a00a0f0017903018018550840e074082c030402030044070a54803406201d200c80902100c0004518046281ca600400002c0000070034400c5500c02c0700710b03507009900c11094000c4411054007024600001e050348442c24034000e40c507080340070150072503241ca04220684041380102c089018800e021511503190224100704640c1c030300032a1409006102400b00d0b08048641281d20818500c0100100c5801022009001c0801e005483e0700200a45110200b19a40f03110500c0900c0700c82c882009694001c0c81011040030180c01d118200600c20030b40e03078109038668052000d00304550344801e44800c0e801900080ba00880e00121700d0101d080002e05500034280402030740c4510082140400180b1110780310340400c10100303a1010a00c81600d504441003041c81903403030041100010040380924001e80c690b0291168074500309 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 273881007 1250 273879757 273879773
    0x3180905130201020708030a0e0d030c05030a09050f181501120c0f110a05060103080702060705010c02010203091e0c0409081b0105070801080a020d02060d1404060e1603080412030c 79
    0x461550346240c0c4281a80150f507014000c40c2c0103002d4810240d031070300d80c019001400ca01340d490b90540c010141c03404402c052510422301310b140150710a041c3c903030b2210f20200c0140001c00c140038652103a134600074966141c0c9060407503078a60344030f44c0c0f841c0e62132907451001048040c41008056410f10810202511036545070340704024040c0916200c038004e000003070340001c045040c2c01c0c01224043e80320742c40c0940810b070b00195040c1140c0c0e010b90810795031042440803c0150050180050056007031a00c20400a40c040d009188110b1700c0754125804c8400c4683c1c0302d10601400b0b41d588905070841e8464403001d0030982c002c904058098101c6500d0140c50021080c20040d50f4660800f20340d540e9400e0124240e40602e01c0c500411501005050007001c5800140b0010440d01d4000e02c0f5080c00180d400108803d81c1150410184100c403101343c624003403c0100187c014148001e1490041e20151003030340c00c84a503854242d82e0030000380b5040505103880e41d0081c0c00d07580c006078144040789418400041c008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 273882257 1250 273881007 273881011
    0xa0f030f0c0b0309030711010302210906071d1002070e09060402150408101d0d021c0203030c07061109091302030c040203060d030e04110a0f1704020d03180905 70
    0x40d500c104400405401d2402118150742c1109404070701c10014041010750000541c2c4045400001c44048a030303085c1c005074001d200700420034100f005412620403200b00c00107141449004401c0503078125554681046a450341892507403a4801542410f0000070704046455440c3c0712010300444004a0f2074109240c5503400403601035401da0b00c403000300000c50400c1c14041c40406602c40c8214105400c00e00502d0701d50010181c680070181c0e5540c0c0c0100816450000030034210851002c1ea20a40e24500b0000c4d02c4048984a8151940380101540f04c03140c0b0010807613100d400590461410642e4543d5018098201c90b0b130300c42c0c0900d0082c0011082030f91400701e114058030440c905003030114903c0c8181400d10071000390785480b03a407042c03041005544a0006a140380d507030603e441c00705040c6e04000100180040000e001c62502c020844c01d0b00c894004001c09000340681e22280c1c188101c809400085074400c803402904070b42d011010500090280d807a03440f48200e0807284100a0342c5500d010f008035041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 273883507 1250 273882257 273882263
    0x60a03060501230109030c05010305040f0213060e060907090501110f0607030e010c0305090d0e030f030703051b010c12051e101a03101505120f01051c1a060a0f03 71
    0x10f894145603941c5119180b00300c1c02d030421309089118520b1511103a401d0000c07031150505144c0c44a00050800002d660003a46495009041d4250440c43c00240b1008144a0044803507038013900d8045801454242e82c0644912410703a90088501d08080044808200840c2820968481c138103a0425407001070100500c9070120395030001d00700c001030408500391109d0803412024585000d09129541d0303004140500755910714200004008000d5011a20f40b104410403403156010114244081540c090004c111880e4000300c241460010307900e5442c201e8000030004004906480249102c0e5426074101e05e0b840010f1443d411002c2c1c0444002c4003440c04119644e8901f48a1840184000c1d02c00301160060b0091101c1c1036421890000038000c105134450144110303100845014000680c4207030700300d40c906400020440c940e0f08015003254403001081c09001d20640410201407144034000c8641405190091442d000c9800c0410403010000c5001d1b102d244c015802090104280c3d034090150002544 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 273884757 1250 273883507 273883529
    0xd1d0106150806060c07170304050307090f05090712062a09030b010801060605270a03140106090e0c040c09080a03090e0c0309030717040e040f020306060f1305060a03060501 76
    0x81d4410024a1020000c0010f0310a0744184078881080000040081c00e0f1484d03000034456a034100130f90301d89140205d610140d8144516800483d03020010380003038183c5a404801400f1903224a190396898407141e000340101040c002c00080d012034999004440c03295604d01d12102c040743c2c0d4403c15108118118030040c0426900c4804004004601d50001d0060240704020805a410180010b19a00c14101e0090301c0090164810000310900040e40403100c00080c101700b1015500d06c1c2c41c601000e6505019112540780c03600c0043c441403140980300c0c54500c0c0d2009040d01000c440204401818000d03000d404000c04000302140c40d00c010440085185c0c02034485207011031030b20401800d405002812030720320600c10300070701c2006e050000c1514489076110300d21414a0703144840540b641d00951380001c46260540040c07000380030078126050f403510300940546034a6030301c601c2444000405542c080707401106401004c0d11001d8141d003d9500004018510907026681c0c1e20303000c0503140c003030b001003441c12 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 273886007 1250 273884757 273884789
    0x30403050f1605101a0603101e061b030905120c060c0a0c0f080304150512040c0302030c1813050a020409030302130f050105030408220e090c0103020f0d1d0106 70
    0x4401080703951305102c0344040c140005414906460130b40000c891070640102e4021001c0340b2552000c06804002c0e20313041004400240041e620340c1c0142950b80324800c041111010080034032251805c42070010b0b505901c4001c900d41c5841c052120800d110744204805001d24190208190f8451004100e0444140000d01000c500340c1040c0c2e1010b101355009151070340c41620100088940441654100e1f40b8581c0d084e1095020349030700303035014428200080442c10840d0100010001c2da540e10f0000d80380241c4c103c811848815051100d2000a07000a43e10071040f0000510701c0480b440b08100080d2090b0203645141c01164042001d8036210b203001c60100b5000720301c2c03241e604051801c01c001802c2d40700441407410b1038500068181e110182002d442c807030340000d0b42c2c40b00c02000720b6603809a401101844006903926043d80e81d1a520940c2c4190039400313200343c24042d540c030034002d4902c0052191103491074401411904401091030140c0001c541110101d685840d138000c3c0f040000904810340445001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 273887257 1250 273886007 273886013
    0x60306060e0402120403030506030f0712200915060c01020d050a15030807030305040f050607120509121c06180b182a0f0403060b0a0501050717030403050f16 69
    0x81608941c00e00e000350700c140a20705103c0f4101c0800ca4000d60113040014994036880301081c140038030490315a2a07803017805400100c803c0d1485452450900030003410201080404d0b5450785401c4003030380145d010041e140850a0b40446403c1c1002007540280354918082e405080c071400c0e41c010a034403048003039540d020840040e08034010011a152840d41c03c3e01002d09517505c91050b0301a1a00140c01c05595800007810407081a82c8000017075004002c840492038440d00082001100c2c84c482000300341001c0c0469203603000040d0b2807141100005041d41070000b591404003e220350b501c51a1071041d1501c00c0068045c4a0754480700c500b1620740004500d908400c0c041c0a10080e1160010b62484001790420414166100d00c1510995a580319104000000c040200550148840038003038804000307000000c21005501c4035070810704c141c1c0c0301340f80c00d0b507140300545140c092018050444d9800951903a0054514001181e0181c40f0b800e10b14186011855a50320940041600a4869004c6200301040c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 273888507 1250 273887257 273887267
    0x2502030f01090209010902030606120c0310050a0b04050d0602090d080d050c03040b01090b040b03030a09170a080703080a020d090b040204051018020901020a051c18030308280606030606 81
    0x10600034080203002da2442540840c80300f981c144a8006030030f0f03003c0081480b59884134101d8103003411100b10031303c941c02c1800660f1b2035984103a680703100d0f004400100080c1030502d003145c1402c40340140640740c203207850002030081d0409458000ca858a070b08128001071561404800b0341443d000d00c0ca445e8032000600032040c1240c01c040c0035458100b030b00740708000010b16150481380c1554561500824010703002004100a4500340c80340310350500000c180041d4031540481e40380c1c1101c83c50200020351104001c812900c5c1c007000000174040200c2000801e0109000700b650079080810400c0040c0b030320461014820032105500d20456403103910000707007c2540b5082c000c6075003000c65410903814481c946146801000801c0c44e210703030040d402082005640c0e000b445420505038115050350824241002030307070100381507100c2a9020a41942c00703c83c400c2400e0000b601504c3e407584950301d40b03446d041088000c405015001e1500c031040c48100341800b031722900443d4020182a200800e983d42070100241c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 273889757 1250 273888507 273888523
    0x1c081c14011401110c0a0510050724200d0e070e090a060605040216021201061802030708010e090d230703170c090604140f030706050913050f0f0705250203 68
    0x1003985c0c0601000e08059842865100c2183d000700c4100750800e080e943d003614030b40030f00780e006007607510313034603509901024190761242003225079240801500100b080450001642d070101c902402c50306102c400040c0c1429400040c8806c40c0004440c45590346040ca5000814115101d02003030700004811020824180101d1000c0c010071134003581010340701c002c051654103021a0280c401c01407036402c400307101000e600890140006903e48031181d4803400c1c02401940c0280c03044000a040c0100002c3e050a1400c5418011003d4070007a0000f94111401181d042e1410b0541480e12846540c1c1c026000e1000d0006240b401d00c03d0300d03031910207101c03019460359540c00100441e9080c8810000581555244412507040e00c0203041050f2900c0103071000b0903050818071602903090321034080b01142050b0054090444454215452030f2400250114a029920140c48441002c0050700200700d5040c0d0105a8991009551030900c1c1046100b0103400000c0a05058000658200c9a503050541c06d00780210b403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 273891007 1250 273889757 273889787
    0xa050a05030901030f0b06090d11060d020721140c1f0b0a0501020c150f1b030301090b010912020108060f06030106110717060609040f020d08091c081c14011401 70
    0x1b0000341d1031404914a4411408110721400020902404100812602d03004136a4050510b50325014801d414000960080101741c0d03818041d00c81c1141d413a64200b410401968032540d8a0000c84540c00410606802c441c054030024018042003200525082d51030740c10301e5803100004101e441340c02d030600c502d501321904041e04541080e40541207a494a8000384000c10240305880c2da109440340700500f060040090388200030070359500d110303a403600000195050341c0300068100302035591100196040c18461240c038400c40030b00410540958001c04840754081405050314180480d05030000b0115070090300905c0c080b07a80d490100d1070f4440c00b0045036000c0c0c0750030880701401501210a00340c0c0e42c000140410f11511982c4001030800c441980c1a4400c0740d40070340004404015454121a6901b00c58a0140200d0441c2c008043d000b4042801d0059950030080f5185040074410409079403100c1501d800c5211612155500514540042c20500030090318840c2c5840301e6843c4001001c5500e01041a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 273892257 1250 273891007 273891011
    0xa06030b060306160e01020c060c0d080109020c0d0305071803060c03180c0512070f032315010905130c030b06120d08012105010c0905011e05040e04050a050a05030901030f 75
    0x4c0388a0101040034078844030340c1070152500b040749004074940540c15103070302d80281002c20380311300c03e520003c1d0142c1b00c80c0c0f81e42c40c0c50440d61780341c00c1882c080380508084008164411401c104000c1d020341c0c032494200c1c02c0c1d49454061400000c503422010500c6030300880c2c0046d0ba41c0100d865440c0e0601c210798003103100301c10070701208145e9241c91342d15000342d000c4caa1003401003020800251600304000c1d0018110282c00303203a10782e56820000c0c04141c18240030450740c102c4440035540e156010440d819040407406070140681d09280c441d400074007004001c0d44d0440880901c0c00c01150400f200301008511420b010299441c240041c82010b003c0350016100d142e11401442d000c0c25044551b044c10b652061700982c1d14005404001c1c0021801400068000c1d444c00c01c0d10600386502a44800c00d8400c203803a0381512a40182c10092922201d225110004100344014841c12640840298016000f041103030707040d1380d040e103405003003d9016404640c65480003a04141070350b0140039250269050b0582 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 273893507 1250 273892257 273892261
    0x609100605010e010e0907050702030f0714090115122405150403050307060504060f0207050604020a0b0408190602040f0b03070311070b04030f03141003050f07050d080a0c0b0a06030b060306 83
    0x20300380031760000d003052143e41d8000004030294070440c10380300000d0300101155103104d40c80d9025901c07581c2d1801000c142d03254801c102c4009040540b440c40c100da130b4114070310042d2682c0910481d82c04108458804006854503100c0c3c003481c0880010b01a000400c0788542909032070501002030084420020051150040c0410800f00d10080180c039900d40c0c0040c0e0100d0300f540c9a01c0c000000b4620074151219891000c0350351814043c00040b000c0c4201d00c01c0d52003012441c0c03650710650650240b4407940072541c0c4007440800b0400b0f540c82600a0341c622505c07002d42095150801c881c803080c001e811426000e1004030800802d070f81d0600410f25007841428100c0e00e4a801034951861400c40140081c0c02c1c094403182250700c0328825407040d10b8115121480390041c3c1072039070710440700e002e0342d01c000e2f20703684200c1101c00408500420564100c80d40240300782c160304495500e1500c1c9400c54407080c0140703d2140e8210340410010548144903980c9050b001400740c1c1145040c201941028103414020390000007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 273894757 1250 273893507 273893509
    0x50306010609030210090509250305060a1703040b030a05090d030c050703030b01120905010209011106131211060a02130b07020d060515041a18090303010506070c05030609100605010e 80
    0x4024030030340741c043c0c6134040c40341071a0000740ca0212007a80041d40181200040002e0640f500400b00003009c000e40d5a03c05188402c08200c05803103041c2c138041c2d40054940b404003e003840c01602d1180801155090781c1c01d160b582c1201f00700300c0c0c00407100140304948035020015101c5080c0710605810740c45081c00c0205130b0a5080080280c0201c242c010b080c136650b990000b0f0726a009500300900c07404a00c009008524140c6030442c080c0d000604c4150118800701442c0c540d034030300414440c1c1b043c02415100c40205059032600f40300307030b100285c1e09028041c3c1c00c020822480d500703024441c89410f0380711000da82c610301c0024160359000c1a6000600c649001d1142c0b600690743e00e02d0780411160407020100c2e9603111000d1400003c8954400540c0c458600341503024144507040601c2402d01c400c903238100880180300601900b60310122111607281e00201300502c002c0c9003802c040e2401074015424004201d4560700401d1409106803a040c05950040c9205403541080d405800040d02d020310b030455052540d18 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 273896007 1250 273894757 273894767
    0x606030921160302010b03010606090e0f0a09050715020c120d0809010605040c0c1a06060403080d061a07120f020c041a06070c090b0307030803070f0309080406180503060106 76
    0x1150000c1d40100c00410700311440892416645411080c1644810311600303468007034020003125601d00c1c0a942424000580c0d5402002018112190b00e5828503090751120089800d011000709801311456440e2084000308104009201c040c043e1100c030000080c82d07501000e8540548951024819416044030707a0042c400405c6c4006d40d04014203042460f07480e003c0d541c60142c038064021a03002890440b554501960101120b100d8600070b000211601c1800420154001d400701c645a4118004000420006402d00c004044070720604400141b400d441e1801f92000e03401c610302e0641c91950114041c0c0a000300e2034020b00314410203007440c0b5030701c80b41103502941380d1070204010f51040b80d840310050000055501000c0740041d00504895840029240070b5107030351054050880c0062400c5080c03003007400c0c0054624280c1e030b00700644134119a14032100f00d8a0784500c6c0349800425480b95110310001d400440134102a141c00d4460071881141202340300d50040c05640042d00c2031344401c0041280c40e07001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 273897257 1250 273896007 273896023
    0x308070b01183c1e060504060602030313030302130b03090c01030510120303021b0723031b0301140103060b0f010c020604030311120a030c110604200406051c050606060309 75
    0x815100f26a4041110041c001c4104070120541018186000d07280740c00d401c288000c0003500000f1081065a844000780001c0f50349070b00500c400350b441003002c0382c0c628821440b81441203103e4a40035151005031b4001100c40340340c5078806058410040240b00204a040c0001403040e070b02840e040100745480c0e08411803020745403140240701a108004a17081c144244c0442c0d980e60740d2143c04911140c4445070440e0345690724480d010289130061400c21052071401c50800311484001c004004890400e1103080f120b05124441a07419940c0703000805004100d41032300d500840c000c4c2c0c80041c00710324900034000801e0f2206507407070401580d10004030042c3d0300c0c2d200307440940740c05150264007400885100340c5044d0420080070501c96010503c100800c1c1d054210502c00c01142d510100320031800700300255582c3c400c0c1c800405209072500123500c2c50000d4080400400001400816800c0d550804900118250340d82e5102900340204040d0074072074100030a43c1c02140564040c2d196141c206025502c1c1c15503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 273898507 1250 273897257 273897311
    0x1205100902090402070c0e04110307150807050409050709090506030102070c181524110d1103041d06091302090c2209020c0d051608070203070308070b0118 68
    0x4080365410183c0c60703903030603900350301c0d408028421107507210018881e401c0800c6030b00b120020201520f01c41d040c200420484110354842013000c540701c400240583d940340c002000601000024030000944000c0c601442d401072680c1e88a80b03c01c10304004190041c0c4400134901c0e0b020368010455200001e082c030b007d402c111000f41c11110001c400c00507090001d09035195042c584803c94420200300c1c07100c00740d443c484c400210207900402404041081e102c60040c040341300f0712078100c641031a507950700504038503403a911641e094925050311506038040da446624403c1a030803214104000b00e5007050740c605c1e500801c0d400850356001625030300298568030002d012100703900010400480050710980000c000c000034039210b551958580b8001070003034000103400034080c443d5680e2801001d0040d0200e440700320b01016002ca03021981e84940201d035110440880c1c1600c101e500000100d000080070340402c5209191124031035241184d0040c0e440711041903a140c9518081407c02c0b41d50f41312100d0007420300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 273899757 1250 273898507 273898511
    0x201020f120a0e0616030b0427050a151d060f0714070f031d04090b010911040b040b090a0b040b07060c05161b0e1603021b0a06050712051009 62
    0x5102501e20010300343c4899600018440c4c0c00074016a141c1d0f0a5080c0441d0b001a541005811020002c10081d99880305108449c090102c10103a1006c6081c000000304a00500840f01c06010350381d20984211402c3c0902094181d40310702114614080112881003541004024080b40c20014005100084042d0414061088500d44400c0d18000441510601e40d048080c00340344440310305015010041d034802c0c5031300c2031300c000c013915401f071509115110380140c100440700642d030300340000d42d8010b11012501618180e400d00000a00c0242d1900600c040d00c9007122003502c2d410504c0510420000707607085030a02c1c1c4404d00003401014001e0301031b604841d40100002c03c025888150503206e5202e02d02c0c2a04000c2a83303c4d00300240481c0d0300c215564074a4035a0f030b25000d6940c03400c4000e0680341c280c401c000b80350742000c2183c0c00a4800d0b005050810141c0c80c074000203141c540c2801d0316000440000700c4185440d0810491a940c100c0351180d00640d0400003409117182002d10700300d0150460182c1180c0c95 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 273901007 1250 273899757 273899761
    0x150f010e060315010602070e09030a170a0e0106080c01140c0c040b0f04020a03050115030b0936071a0c0a060905071806090e0a020a121110120c0201020f12 68
    0x40c0d8100142d6030010704555035000f6550b141c241c020b407651384c98007419146041220204e2840300c0b000085424900ca1503503440910781e5a0720041d804c0c0c0d42d000c0c0140d010107031102c1c44007440e980203100d1a0000c000400003400701482800003d01120112588aa80c4c40c4046c00302144500d008100a01307202021a0001441c4412a0020751114040700300541c2091004c9800c011f050b40650005041c3c07503008803a070030034540b0040c0807806e441e0070b4489681c110304a1707000b082001d0003038200302209842c04a1882c03109843c48400e0704004449811035040341d44a401c003008455885082040555000b4444514094182808940e50401044018000c50350740c513026007441424825900600504007403020507600c1001120041e14050243c500b8161602080b00c07890480080c8401c41c499010380b9118a5038684070a400c4c103420012815140c1110318500c095840c2d441a80034800c1303d00c0e54540300e41c42607512250070f08a903ca1001d0005584c4100300c1081088095070581e415072001c0300f0318aa0503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 273902257 1250 273901007 273901009
    0x101a091b07240c020c15070311030712080a05070305010f05061c0518011407080408071104090c0e1e010b09120106030308010518130201030507031b02070503150f010e06 74
    0x5030b902442090341d2004a20b50300900d4141c0248442214907400c0b203030030780905001c020302070b80c0404045040d40c804000c8000001c0c020400705405106c80d4041c1c90034000300c0c1c1c6804071804c2c20402e40c0b03400903520300c003000029161482041e8000c4102d24041009605243c103902041140340a028031594010401c01c2180d5812507880c000b51103103017024481c1d42401d00c51060f8243c140710f512107065007801000c0303c040d1500140700d071251003039540d4405039403100c0c0c4400030719602484050342c44036154001642151100d01030000c045200f0103240c102e4030300d01103002080c100083c1c0010005a02c01300500e8030707034504140da6415900c0141816a0b82c0000c070300002c80000000300e6100040d400c10b80000141a0044c810700d0485a0580d0112a40d00c00d50800d4041c5400469940c40041d51a41003080075511039031016600080900700040d51b00561007090721440d520184d0f40006030700031141071102c1d00341808105000080720b00300000d241009a88181e50103014080d060342d50451500103842 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 273903507 1250 273902257 273902273
    0x140c1b130606180e06060304170d02120105180f0a0f0617070326250209131101030908030103020415030b1e01060509031906060503101a091b07 63
    0x481080d0040241c0c1d5991200a04200c000c0450550160b4120300005104960201c44601c5084000c0c109031030340d81c0e07655601300c0c0052600c042c08014202031100880808451004000d421411002e050507580741008000e070340031078510078100c149603e10a014051050000302a080700b030030240070401c104070450400007040c407030340b00c0a164800a01070301c6440d440070403a102520b00920040c402240301101020b40380e10f04105a661100040144184844d5071003035000c0307290070b8071041580414058000600c0080c05885032030100f094284403000300807510200c070105481c01e0900b4030805480342c8036560140014400a805070382ca800d04040140d10031000c80c0095075102640d0b00395030604d00c1c1034080398410000549540e40076900003007002406842900d046000040092001603501e500c03000c101404484100c0f042911000702003050b90f824071807001800210701c00010700300058403120700b00c100d01194450041c240d40e018411907505549514500440e1a4482c6589d0112072a00f010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 273904757 1250 273903507 273903529
    0x110c040915091b050103060501020709050a18030e04050f07050f16020402160b011406031612180501060902090a05091f0303111c1b03090305010203040503040501140c1b 74
    0x58001d01d0075800b50100900702d18070940031191101030010180e1200e0064044541600905015034000c2004102d002065044698007104076200804c0003080000d2020500b02580422070209001192851441c1031034030406d90700000c1003149a501d82401c0101030110310828952030119100003800c24601f14219484142296001c0e0017150b507a542203c000185144511003180c22110100000034180d1041d007505010440c010030252071501d500c81404006210840c0140601c003200d0804001761101d4410032030400d00700c0f0103c01c118416454440c0c2100d0841c0c02ca1440d852040c0000081c46e1034130312002007918000d4440c1803680d1035032044907035903000214602e412500325642c003000b01940325810030202d580d0842100c140300c850860b4002410342405900000442111441141140c0040340d232055074020305140c00401d4030303906d94a0030780c2d20841c0e00365281e9100103010011546d001108803462181407400e10b0400130b841c43c005403182c01d1940d00d0a610850061905200d0b41c0ba038807201c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 273906007 1250 273904757 273904793
    0x8010f15090b070b1602070311040e010b0910320f06070804030c3002041d060c0c0c03030406050306090402040f05071d19150c08040605040f06110c0409 67
    0x20389690680c03510284591301201c103240d40514400603082164000107041041e603a200c404540e041034588184802050850002c031003a6489448000b81c640720409102e003d95140c0803000c8a29051036051000400703420600c4a80b0f120707425a10b240b0001d80310320410400d80848029400883e50340002d8050b004d20b14014001050008000040181505d2000102c881c044110580205840725815081e01c4075848540c0551040108000620f8030380c1c801448100301600c4500b540191080b1149080c1d800c68000010000c00603020300c0401c0304105221683c0c0086005603d441e003000e10062540c00003a000d580101c01c203601180455646400403030000700d021900308114542075030b004042000c00c001501030290b080008000c54102540d14110108040c40d5408080c1d2070307d0800301081d4544104401040f1446e4241c20000c0c1b01341c0e00510040c0b2107641d65903125810b00e103034204a00c4140e4482e1090088071502d066a031080801c20054101d0203c0740015000750b00d041880000030030b80c81c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 273907257 1250 273906007 273906029
    0x2060d020304051e07030201090e06130b040f020a11060f04231207050105100905060d02060c0c0d0f110603220204090c0602010f0b03060402031207030c06230708010f1509 75
    0x7513a00c8480001c40c0c0040700d00036a969a0169901c9000030b103200c100761586e90300190b4905c400080c0b180c0940041c0c0c5521005000040c115034510400c400300e17002070150b60001600c01038000402002008043e421800d083d22011180c2002c1d0360398501e6400088113070040d209640321000103511f0a0100d5841032140c0d403070083d40c454440c584607000300780485040d406109054400315250080d4440c0c00e12620019000703082d078859a408101c002d4005c07014400c0640b0914852403e50340785c1c94509445c4a100d42900340400340c1605d4102d181030055511540140c40900800403401c50f038858441800c98515030b0047c038069180003240c098a000c0d00058111010b00c02c0c005016a4154026a08500102c40c2040b000e0300620030117403100c0303003a00c0182d4035512400e950800803680342c004100c80c03442400c280d10181c074590b61f01402e58a100b25075203c41840309501c144d140c00c070b000302c080d07010305e6620f001d20041d03040c00013011035041e090141d0b00440c011b00354543c644e54043e54102020340810070b04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 273908507 1250 273907257 273907303
    0xe130e0a03030c02060a06060f0c02030a06090606180c0203070215130303081602010b0d02010e120105040317150915060706020c070f05030703080a08100e130c080a02060d02030405 79
    0x40a0040d15001103d600107100706800565264014405c20707058401c1a92401c0a19400d8503040300c200000795416a4035005444418000807864804c6101c1c1030710500c1e0100f4a2441c103c03c120050801000d84451b041c1007480941d940341e80442207551071076044540084020040404842c42d001740f91540842151015003c000d05820030400b07807103011441044401d0400f4600124243c801c5204c2e03141d0410070b00c4031758400560081602940070140035204800c01c9000c6142142520021340e8160040340c1d40c1038190404040c00321a6662081e8580004903155030700102040c0e940100504558501e641c140c00ca4020303949034411580c06d141c11074015074130f4010590b0002e880b1040340c815403c01ca00740402c005050305010130070710200d03600411003506010100e10142d5241900820496403202c1410300401c0782101e00c440c150007140d0b028201d5400d050180303800d11000d40160420900c4d0b80c0a5207200c40141e640c002140c0321000031410158807038665141951400600304400f410181401c04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 273909757 1250 273908507 273908513
    0x70203010207060b040b1207140f0604030b04110603091504211d040c082a0c010203060103150f030f020a0e010303052809120203070f1d10060e130e0a 66
    0x300c91940c81c000c907401c02207102c00c8400c0240e07c1d1741042d4080802d4110307000070400802006a1483c040c0070141400c04628003a000081d44c0d64019081191444402414030060000c034441000c0c0c01d03003082c1c4440389541040940c450303403401d40e12005000900c00800003005c22202c031185d04184a649411200303d25140740c800381080301c00300b0101d82102d805a540324114074060007414000c0c5401c0c0c861031540e44035661610842c0c81020045804000341c03012500607401d24200502c113601d00c143c001a181d0818000060a07110b10361249002082c1000c02401980c08040340002180e90180c20012401e00e0341c8049602c1c1045c43d44800055640c210000040c5034100000384015290440154812104c403007483c204800094102c10004072894420b1060304198454003465500040464040e641d8403241c680b941c543e40d42068010707000c085100e00011090340c4c0c4103a0040300381803d00400f50300740700e001009420b210840c60300c81ca210350140b0500750b00540c0000003154807042502c10110840c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 273911007 1250 273909757 273909761
    0x20705040903270b0c030c10020a08060108040827041a060307120603020907020717070311010f020307061b0e030601050f01180f03050d110613200d050c0405011512020d0207020301020706 82
    0x200c02c01d07c4a020f83e180e0150389820034401c6030f40151307141d01c03020301940742c0a004440010004000f10341e5001c007081080d4280092003071514034001440684520366040c5800e120664201158503950b540356098081c20350703564481541c1d881145850120307130080c0d04517610000303060180d00280d041300e810b10a02040740c1d4049401c1c4191003094090030b5000a80e49207150f510a01031102500030040b419210b0040d6204150354600d4040b03510450742040c010703451700400c550001c880141f48414803400032908a80001c1700b0701201c00c0850240005601d4100410380b09502080e025040145140d074031442c4070b020504135070145c003040f0712403e042170b102d00d0180d0b0360b420010b42c41000324181088400b001900010482c2c825031888440907504070950f507800305503605d680c80b10780840c8840d04044003d03469040440d2640303070040c802040030742000c0c014402140d5040c0c0003e01c00f102042506c40d05560400d403e01c003d000600401a036440707a1000d400c00a004040c002580b550000032114240803182d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 273912257 1250 273911007 273911017
    0x7091716030b010302010305011e0311150a030501050906040e0309101e020a0b0c04050f0405061c05073f0303090c1d060102030406120906180b07020705040903270b0c03 74
    0x3e8a0400090b602c66184214038070666140c900407041d00d940c01d0001178101330fa10801d07040302411700301980300d0710904d0050780e811a62246001a0395103004104d43e1030600205030300308a041d64100060300b055846180c0b644510146140254005141401d10714482d1082c1200c05003480c1d0090301e41c1000e590001c0d19000c9001090b11203040400104018580d807008580803640c0062a40c1c0519078038200380070140c400144403540c442d000190401c4000701056400901c984110041e00303149082c0703402c503010f907500800f003820548403841c4051501d0041c01c200c580002c0c402050300440780018034040b4003030910600c004040b64010040001c40c0103050400c0c448045c2c00c60400c00c0342e170341c0341001203980f8021441001c0000d40e04e140c541201d180c00760303c03a4042500482010502c0e5418042c10224501e640800701c81c41044603080102084d03041c840306001c0c0074120740920141806450080403401c40c0c2c4000c803071490910310300744502c088030112907000b00f41052035542c0320510340100d80e0710f82d004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 273913507 1250 273912257 273912259
    0x31b080708060f16080406051504020a05041a0a09063c0e180a0e1014040203060907060806100219060b2701120c09090c03030e030607091716030b010302 67
    0x850f0301052480301100c0d540080305046540e00702480e82d82c2c2e200d84003d8500604204400000f000c206e00c4035480c1ca00040005071303820386645036074914001040004070140800312040000c10f10444807802d40c06043d00e4200d9949240c042c030b80c02d49602c03012040c4800b0314400500c2607809810001c4500d40c24aa40050f03941076101c0340301c81031988051002c0302a82c84080741c003041502c400076100c0c1055512035640c0030500812114480c441078041c07022288402800d120581605041104514042145a0384208140040d251561500340f01030036024010707180c103110700c2074189060b199a1082004944100b154965540000606e0a01000401144c50064007a03400341d504000d800cad440d00448000d26001c41c81098039030386072507131140c0980900941140d001440060004d40c45c0032901412080b140207407c840040ca295140c060300c1341c20034000301402030f0000c030204034005410804990807100101d19140c445000c0c1480749081910403480d03056a901c41c0d0704003206100c6625550f40c1038a00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 273914757 1250 273913507 273913531
    0x80f0115110a3009050418020303040b041406281710030b070f0e0d1703010e0a050709140d0204110c03030114060702030703031b0618150c020304031b08070806 70
    0x20700d801d4010b4503c014105000c000c1000d07181c0400071400d0681c01454401300314a102801c0303000d01e80c00a41164001e42c01001801d60100b014008161410a4004000d004130303000c510b0465130b4000042d42c44041520040c550f4502c500d15101103008642d0300300c588071240c0c409105403520341a814204a001d00040d1210403042c00041d60450003480c000d80019240d8a5058090300c0301c004118985001d000c048480c07202010b08050301d00005005180a8030203070301d0412552a103a5400800c442000300300e44104807007004208100007100e900310400c04000c1c2c480e415503038001d0010a001c2d0081c240d842c0c90800c400240b0f83c2d5014008800785050318001680c0c1d220303413903010b01040707154010240007a42c0b641051008000090280b07401c1d01c0c1c03440244148446c0a84107440d01ca048030b43c20040001440f024101d00010041100300c1030f1480101200c041040305003110b4000d540c2d00441c00002c000514514106940032884000c86000f400003008480c101521084c1103a240c44040e152003884503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 273916007 1250 273914757 273914813
    0x406030308160e181e07080a0c0906080406020c1216030801050a030b06091008060109091104050f06060c0106080307030504152303061207060e010f080f0115110a 71
    0xe2282400442903030000340b0700502c4662003568444045030240c100c040402d502030001030111600c90f003003841b4608070340b91a03040e80303004501601540c0401c5103070420850003000c2401141d4001c0c061a8110790048401a00e41002001692400b410b641801c3d96080b804250060b101d1000b00301d6200440c803a030740d180003c0e41d0700d40501280300c980b03010007850843e4440006900d8140b10b003030141d1008030007031210703002680c07803840f1410902d0a030014100f0035180e1a2280c1404466440f500341c402041d40c0400062805a82c41881d541c0040c0186218800000345214004000d42100002d0100d03401580d64406c92403501a00702e078030520078400040380304556205010302407124011107034505c5541f1510070b80c0303000500c951a80018102540030644075042069081c0400c64007001c1c04994a07170580099140d8000352107030740e1408119080010b00020010440c181d0804a0f0446402d100c0203407525284140548407a2048822402c2c90300c10761054100340602015040303243c0c8041482900c0c56 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 273917257 1250 273916007 273916051
    0xa1101020301240233010b1204122f15070e0918160f05060c190303020708030a050f0604050c190e060c06100504020408060a0b0a050406030308 63
    0x10740003d10420b004076140316460310b8141d10038031151074883c00301e1050b52001c110b1a58141d508404012a20b100d1642d9025032040c2d0350f840600c150301400e00c1d01d10355402d10841c805a40c0e41804002c00040a0041d608681400720f4040c03103a81c410000c074174100c4000c00c02403806507a440031008488040c944140d0fa0a05080b001418a40c1d00450003a80d404102d01144000c2c0b121405010308140640c0701c41c03d04d4141a60710034401d400041c0c0105c1000905103140c038038602e182040c260082403140c4810003d80c04404400100003605400c40060045d0034441ca08003580203000c1c1c80c1001c0c0c40010000b0800002d00305951045214810215550903030340c48030014032040f11012a0425104442004410190700c8d001d8007102040b0f6451520308a0b80b01c0100100d03605400040c4101241e9021100f0300028a8080700144050074098800b103080074030b032264559603180041e1080d08455980d841907102519003035103802c083c4c14060003e200c210ba80b45001030883c1000c4074840c000c001e0100c204884 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 273918507 1250 273917257 273917261
    0x8041101110a0b04020a090501060507030e030f10050a020d020a020f1504172d07060518070612020c0d0c03020610050a050f03010e0a06050f010e0103170d0212010b0a1101 75
    0x180444002412000c02c039a8420320540c80c0504141c0c0d000c1803548000401c00b0880c007480e4041d285582d0f8080d21143e291a014058010304500740d0b219420403203007130b400c6c0b01c40001c4140b5034440f014000310b1a070711004912002031190000079560729000040940c2c440d41c001a0940444003128215030b054200442c0c0481d043d4415600185000d07842400d403c02c00040d038000d4244c000f01003c1c40c18508011940c865100c5800a4040c042e5074000715182d003d1205030303c6000d5000079031036004407925841113602615010740b4020181446960729611010350010750580b101403824074100c07242c5005842d405403214901e00300850040c41441d0000f6081c1012042440c1201da001d0b103d00130690811080040d1f0307803283c0400c00c1d0150b50f99070340031403640b004000c002c00301809907070000b6242c1800444010300e908140c21420000c0400f1004000148040741c0d60444502c4001055403030f80d10703c6e1031070006442180c2e00c0c4520300000720008624140b0344002841725155503200d088199030a030f0800d82c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 273919757 1250 273918507 273918527
    0x71e0c02030a12080108061003080906090a1403011d03090415270b040218040b0301021201030b101a1e07140f071a120a0b0a1d07080f16031b08041101 66
    0x341c04032040d01040050307456030140203290401059907080c1211400410073b00707002980300e07411092418800c02e60a04003889030244464090b400700c6003c03403e003218141d50784a1201e44034001d03a03842040d0010031140460700801380860203000045101e80da035000440002c21811850f5582ca8034040422a10381442110050b28030340c0540e00040380f8820810001b0308105219540654080021070040600420842d0181d4401c4504075060306010402c000e104442d84c006a514080355035603c1d104000003003d4944882c80315103503256540b444180c40149006900d00240340310202180c42c0803503007001c50309034600003a1004440c0d480eaa00e4903142c0e0385013a896a03640101c1810420000c0740c3d18000e01c0158004114040401c03409445000f00300701c5811a8045040c0034030641c0060000c4c000c0703214082d080010b5141201d080d00300310558041c003c034003500392001c0001420b01408054080e4000c83c203c104035043d9001050132068024004407400c0301e0886000400b101200c40a601071200c40b8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 273920863 1106 273919757 273919771
    0x12050f0406180e010509010306091e0b060f0603101703220905060108040c060e031c0309020f03030a020c01050c010f0908040603050f071e0c02030a1208010806 70
    0x581103115a0448000f9031440e80042005580300c580307850640b034008900050040702c502d0043e50034a12070740b0111080781d8501201c024401c1c16910325110b40010703034140d80d001048100304107a502c0211008020401e440d007082c00799480c00c40d00216030381000e408403407070240c40010200644103011190f200c1a155800c051040c2101400b4054000c00c0a0810403242d0400b60307250802c01e80b03a0b028140030408041c13500d60117682c00f002607820701c0b151136070340041250035907100070050045a541039001b6803180d04110b00f103003400011144007074030f03d40c090040705d44000d0045030b0951042a0818041d920303800b40800e00b0840d44100c1901038030070720312503a440d441c158000d01030340e0b0000d28003116103516004004140c2c1d00050569011038185d1650000c40810310400e80d225038500030003070741500c07560320310303d00b04550b64506920f080c00c0c41d01d540140d680e0b5404070550b40c4408603911 = true := by decide +kernel

theorem cover : BRFrame.Cov 273741007 273920863 := by
  have h0 := BRFrame.cov_init 273741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 273741007 ≤ n) (h2 : n < 273920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
