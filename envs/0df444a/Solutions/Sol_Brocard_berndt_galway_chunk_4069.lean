-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:03.297851+00:00
-- url     : https://prove2.me/submissions/38f70eb7-412d-4987-93bf-010d9804fa90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 731654676 ≤ n < 731834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 731655926 1250 731654676 731654681
    0x1050405060306070c0c0e040c030311121603020a08070f1208060306070c03110615010e03164a0708070212030702120c0d030c02070e0f060621060f04 66
    0x100d9094042d0043c0e00080e4009000d0b007030240da42c40c0301e0107010454a98039502084000001d65017103c004005140410515911080400510071084040d00913040000328908462044485103c0448000b00c03010701450300a0040c08907540c1c100b90003d981c1ca640d85030043d00d0b010302403070465454940f48003580c0081d100b0004944206400b41c01011a82c0391041d0a031307522001c0e8002282040482da01006440e1f070240080d502510705003203101e032655403880014005181800c06039000b13038445262440381d41f41a1100c00100d0b07280c0502031900e411028070321010400e441c550007906140039805e5004246410306052030f81d4090340122003041c1c42d41c050842f81a81c040e5856001a4001559202501039038001140c00400b6801111401104019000d2698010b10030340007243c2c204041c824005601805184240c001e02e20150a0803800c0c26801c4080c158007806c02c03980a0003100004009403290305c1202c420320201e00400303003840a25045800700d08812200300d4003501e000e0340040c51505050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 731657176 1250 731655926 731655931
    0x1201121a040b0c0f090402070303050901180201050f090307050a030803090c0402180411091e180f0106030203100b0304150e1f2316090807120f03031116050601050405 73
    0x4100300b500741c80d04282410030380c0016120141042d4200102d0b159561584020209948030307440100d01d92038440295401c54145001120300003101040220050380c1c000212151415818021601d4640c8423000c2450003880d600b1150f04003e105801000f03004004d000345204881c8542120100b02c417031800d200c103130b01030a81d0b8003040000b1040300140c0b0746000c2c0c000070030b0400030401f00350501204400282111140d11000403d243ca0501d07031624606000b0020015039180a241c60710505141031900b42000052003880109680400402d205ca40741000382802405210001c0d0b480e41001d0034628410100c02c06802407152030f260701c1700040d80c00441c880c001c9820f50715420483c2d0910560780e0f8040c250107203485018003940f094001c50080b0f06580d56000c0c00d54902c0c00d1040005407000a054004903421802403035000401c204504640304110100b85a8020700081001d4a1481c1c184c02800c00320940c4200302c2c0b0040340314030540482c00303051a0203902890846045907611070912045032400d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 731658426 1250 731657176 731657183
    0x60b0432011d190f0905090313031b03080406050426070501030914010f020a02161a0c011b020303060102070f080601260d0e090105010e03060105151201121a04 70
    0x3402c03181444a03400c1d0078802d1800d003e0031003000d01000c1c440f141d14a1000740c11005108082000c20301c0021100d00c2255403040d032040056240c40010141e000800741603110080c0140c3e004e8440800c046400c000c200c0046600c10811900c03282c807040c026180340c2041c002c020800c0d14275905090304204a00d1000114110f180c081c280700c40c10440110090008000185c82d500326181da13151400700709109200080610076801a200d01036036000034242401070b120003100e201c10240c11b0200500201c0c6203400c804502c3c10300b03984d40440111003070140c41c00380c90b41200541003041802045070040011407180340c0903825140b0b0541c491007810300c100307a20701030104580c0c003080040c030003014448030289a5000164402d09500c8011419920f0f14509080328000910242c01d0b00d2078034108490075601401003400e00d85140001840440e0340d9a40501c034880c800d0704a500000b490054280840c0c0101c0c0104660f04490340c0c440806410580c0b0f0014101d503801418805036080008411000d0300441c1d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 731659676 1250 731658426 731658437
    0x6020c070918031211091c0c06050310180915140a0207080f21130b0f0f04120302040f0f08100e0a1410090f02030f0d02030715060b043201 61
    0x101c0740351a4020000c041741d140c1c621000300a001c90700e9851181d80000b400c03814040c12000060384c0303008164202c8581c880344c2400410702c240191110001804001d551a4580d0081c44481070260200500003404c0301405410781d0600070400c144541c7c00000e03009600340704101d42e50f03c40c49081d00c100e20510380c0241041a081c00881c400c5c01e8013200610030440e4600080d5888060710710302070086801034484801846a2540c810108440380f01c4507075000082007102c108600c0d107500c8508841c1402400101058254205071071554040c0e07050310080c00b00d84100c10705080d11003191b40c04102c00350042c240c15202d1010480c3d40205240a0081541c4800001d81000d0429941c3e03600c4011082420000c1e0b07028103e16003201164901c200e0802d580980300d4690884270b81e005040c18100d02c10760380d042d16000300d98440c40c0c0315000421241c0195011400342e4259405810300300023400c0350f8006c2d02c041c03000010000b0302000800c0800c031540026980e01c0500744e03105100c4244901d02c4c4c1c0030180c046603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 731660926 1250 731659676 731659697
    0x70b030103140f0d0c0314040e010b0408101109010e12010c0203121609060c15050a02180d201807031e0504031b03030b1914030304030b150a0306020c07091803 70
    0x3440b54040c00e1400304140251428549c86004041e40200c098115902401000c40d0030404a9010416080c1200440904110314400301c2c411340101d104030100c1038140124000784d43d44031784440300034208040b1020002c000f1100440c000948075800f007038050749060803010108a0403207818800d44204100e5480d280a01c81c034200301a100c5900c8154107a40100c281a498801c07403421707024440c8204054800140e4a010801050b0342c552202a0128040c401c806a01c0d00001c10f000031165603140f8800408982007200d000185807001c034041d0081c1012591002c1c0482140c05400c01154880e0a0361150444d10b840350980003290400c9a014002134000c02840070000032224010050901074500400c8040c40240450f401112120784804c01d007020800802110320358a200800456044001d14501031071502c41d030302e4106029015015520203005a0041c03566210b843c0710007164880ca095440d801c2d107e00036900d07881780e07200d00e1086a05043d80782d0035120056040888080d4942c40e411400d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 731662176 1250 731660926 731660933
    0x9050f010c021c0605070906020d02070e0603010914060f060907050d02030a0603050f2d03070602180a0605180f1c061e090507080c060417070b030103140f0d0c 70
    0x850300760500380e0708480210704652040150f4421103401a0003030401064a0600c102c004001d811b01e64010003c5401228800041550218500c0d04803940785d04510034940316900024010300d800c080060440302070720410000100c011413034600c01e001083e101d440d140d48001c18049a90003c503a001c0000e0000c008050070802990301840d080000140b001807266141d65a042c54100c0072030590720a84d019080c00d9150140c07100c403002d00a40340c0c000320704c110000c1a00d0369a0724061100700800e959008503890400c400030420fa103400610060603110681c0d59040050b1082d40220140744440e02029904403040c20010700581c0301040160411849a000c803403143c2d884210110b04551050303c1e81c418140180d481c11f04601010aa01d9001400810070f103003680c9006210b9100072034a420080c107036400c40d90380009907022152928a0515201c82c0480c80506110319500010084c24000c400481402000203213901000c48076000c40d200700c0b000b01c0032655607032b600c50741c1c410002d02d98040c40b4000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 731663426 1250 731662176 731662187
    0x70302071725060b0f03030405100c050109050102121006020a08030601030f110f1c0e0601050904320d0306181d0a030c170a1403063106050109050f01 66
    0x1c480404540c42d4450491030080702000356200400e485480d100e0001142ea0302d0414100181d85004900030b502c1e051a181c04134100e90615a40c8a09000340325085070103000303080d006050181d51080007117648854140100d08000003d84003100b6140ca03441d030118140380001826090517400c16801400c5a54400044000d02030078582003c1483c1c0740c00b00c203804048203501400c07400444000040e1520144a0340d4200b0908a10240e02c00c1420010b85000802003c121281540d5042d600b844040d910384c1000300c1e80c8000e046081401c0c80040e0b01201c00008940a040400e440e5001a1080078103e130000320141c811500070b0b40e1100707104103885240c0385141d40c0000b450b2111105241e2550842807259070a10503245000c0c3d000c114403c0864041001d0110140d1984000d09421420410111001807601d82d4038140e044507010300201242840d981c0c911001c03080525104908208079003a01d200c43c04103402d0720b0a240c00d60801c94007113050341c001c421201c141c89004e4452580c000c5880f004403007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 731664676 1250 731663426 731663437
    0x70c0905061201050906073c180b07020405070e03070506221701050106090b0306060a0905091e061c02060d180501150614031602240f0703020717 64
    0x2407010007541d080c0507802d000c3c0551485550008040c20561a1110010382000a40080404e8108030b0303801100d01d225800110f485981c0420481d5400d4203020907060b075100c0107254000040145405000410101c5000101200391096505001c5611100d00503982c0110703030710000ea495000f6a1083c8045d08154029040822000008610031003940b100e58001d01016000f00040000a090b83c0d07202d540c00f401081c0c010961460401c00c0145000b4600400e4000503248501c200000a10141601e200c0c1c4821070103003000030b0000c2da160406204040c0d07500308420000516049400c00283c00d49400ea01c81034840c2d444c00c3c043c8030074890030350030401c15511100e20904110b9844901070f510122849540004500ca0740c0001111b00003c5100c484192941e4005d004109080a4241900d100502503980101e00f50300352000c2000301c580242d0030024049c200105000c850703842c1d0500a10000c1445010380703601d0043c000c82c0d8455810071004e80c0300d40c44010b0324030142e2450303403074451a5120003802d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 731665926 1250 731664676 731664679
    0xb1002060415061503020c0d0c17030603030d050c03090705010207080a2307030311070e0717091c030902010e030a080403030807020a05010f050103020f09060f010c080d092303070c090506 82
    0x100c3c1034450140000c0c2c00c188402031400070354007042d40c02e13000400b0000300081c0507603810b04411161007990380c1c20007220319845900a0200200c08212244c408000359180000c03180c20900252505103681c0041d900210350403095842507810004041d40085080700948001c0d20242c402410540c03964401c0c10700c845403d034010031589822581e030321402d11981010b10b10039540c100c00303410400c080601e040915082074070307040c0018051003183d0b508017400c450040590780219000d952400c0c02c0b20705100806400064031806c00304400022540355100c1c281c8280700362114002c4000c031005155440000100060504000304428008680201c1c42682d10803001d10488030b00d46584d07a5030b54251074007030104c3c890040d110300041c411454801e68014254900341e40580740d6107000303400110614580800305050003e20f40d64501801140400c032400d11064100621507000f403450131086680020084800c101507a03d041600c08902000320b030003280e044104460b141d8200460308008140241030305 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 731667176 1250 731665926 731665931
    0xf0605071112061f0e0906060108010e070503060d110405040b061201090803071107031b0311012c01030b091003030806180a0b0105091002011a010e0307090b0415030c0501030b1002060415 82
    0x60743c5c00f807003100140f1413500000641302c9424844009820904180c00603411014400200040554040d043c0d0f030303111320115600c135508200e508090450503c43e41090303401500703020401060040341c0300403500800c419a1714550100741045010700702c070803e890041600c0000c0005c20305440c030803020178248210550a481416669540703420a80d4500c2115502d0008214002c200340070318240f642018610030b090584140307009a03a40e43c1c111134005000024103c0400b40003140d40d10a501502c01d006000e407480342142400c4480c0840b41081d072108130002045080011907604040e0350399804a09040c606800b1602c885100f00f01800a00325840d0400005100407115640c031042480d440d4462900000750004e69550011800f0714004d5103141800f581e4001002d01d510300040c484105c9202d40000520214840e0000d030240984040a518030010301e0341c0402401050903001c0e04441090b00d04000c0f442c3c49505101071035503514038040150b081f150004011940c000c3c2c1c2d404040310080c100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 731668426 1250 731667176 731667179
    0x8060f2401080f1005120a0b10050906090c0c1b03060a0c05040e07140f070506010b04050d11120a080a0305070e0627030f010b0f1221040f0605071112061f 68
    0x81541c0190035450a10140d000c91f41c0c0b4030601075202000d40d00505048001143c9500b404003241e28400080d0bd460f0140002e00d00246d41c2c1582c0f0400c0e03507182900b0302c00780e0300d041c0d0003040d80c021180c03851131800d40f083c081c0101158001c00b442c481c404c0803030a41c0d1242800d0031300e082c01114008200525407010301c4a80c0d1444d05010340c0400050031b502001400c843d0720761940d800c2c4a442c1400581203082607940810041c44143e68440840c401c80341e00c41e0305928820303c21004220100a44003540141e44255038008042013049000b8003282112550700b0011a0f9491004490401c0d02070740a5070410400c11a885040120620f0301040c003221020354030042842c01c0c0030074a8516031811010880e5515450341e9054a46902c0000c0c4035502140c0c2c4886001c25200c06039194406801d070b80707020300d80b00c0320814810500300040c0e50080112554004400e541d80c00003510380c0e844000f040b9000c01180800070f403989070241c00c1c000b100a0400c0100029580d403807000c800408104004004d40301304090 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 731669676 1250 731668426 731668429
    0x30703170f032403010b06031801150f1706060f01030504020f0d140c300a0b0103030f1b03080601030b041104030c090c0809121308060f2401080f1005 66
    0xa42c003401d41d200302030603500f55025608941c080303040c0303241e4401c0c1d0500f00d0340c02040c2d0358141130b01e801802c00151010140000c0030100c3c01401000c000003901410314000203401c0141c441c6d00e07012101007a10b0443e4400d1800384c0c0e2500c4000890b441e40d840510b80c12234565a5202e83c3c031440d80548043c1c00c0340107800841001030454281246c00701c510702ca0306198034602d000305003c94042c046043c0c0d5503448001041c11503c0c800c0348081c4032109003807100e4010004043c1d08000e04021a40c1011102019503124100200101c1415491501041e5030310f91881c40b600024946503580d5400d0b660b01c1d0815214440110054074601d02d06039171003512201d10b50f80d4030b0104801400154801c0c81102030741850f0400c0003040d41c0e01c078406003050200c01c0c010040d861a02103500010188025156503840b41001c403132852003001508100782a201d0740c4100b20082d844d00442501406030310401074071405800f10f050801c4007803a4003140c0054440d00c04184040e80d54000247c100741491645013a850700c0760b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 731670926 1250 731669676 731669707
    0x7120915050a0b040c03060b0906032e0503070e091515041a09070302030f01150c080a0309030e030610050d060605040c02061e130803070201090b100603060e010503070317 75
    0x76500b48034180d41d00007075102c5140920a41c1c544400c281402d001c0ca038503001405405000c1c1400b854024080000014054441030112081101107000e00c00c40040310310341c0061504a140c01014000c1c41030080100700302c200800c49500c00d890050080c81c1a070084104a464001e01a10301a2040d08004159025540c0c43c02000e0343c805600303041d072640e002501d0400803402c40162002007850320401c14425500b4100450030306488403521190000813540c8421103c0c80c0340ba24025002040c003042c00140c83c0e6054100c400b909010707645600b09200c3d04410140c50b4601030342d4901c29082d1000f0204481e08100a84121b00d900850001902ca51b481012031309840d050301528005812003000c01c94062401541c07a24691100e00c03c0003014034022003030031800740c141ca401074071f11100840010f0640c1d1003500705039042a80808203c0181c107005050200e007441e05c0c09600701080c1082d80c01705540e41e524188504070746000300100001c51468660100550300d0a0203103000f403c00300700d200002c1c02000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 731672176 1250 731670926 731670931
    0x312200708150c090a03201518101d0303041e051f081b070f0c14010815012304080c2e1101090203010f230712091505 52
    0x180050807031440207245851500304001e00e20035481c2d07018440b20704c5680f90040c0b200c0a60ba80404c2c000c0da0a103e409a486900390f840f0780c1c00b80d0142245c0391840c40c040c1d0f110090310742000301100d101044c445007000c200012100d010130300005a1100e0144402007501c50815800c004050156403070706807620844040c0410b013440c0c80400080c0c0e8841001a410030004880e95000b00311a801d8a400190400400d00007000d0300c460040c1170b80703c0e40b60009c110800101d8500036841400303104240700d1407900c0025030302c0300d219001c40d030101c0c442584880c0d401195034500c40c81c6031880c648499541c0400565200c400c61100350145820707101015602060200100041c1c21034400905840c81148104082ca40c00348950391100800b00a200701e2641070724007620080c48560401c5224890b820381d5590041c826954080e5040d1f08003489400c0b4070115501406510101c4c404452a02c03800011010000340155031150004884030031000301c4120a91000d4001c80c030481d80032a0703402582240300282e4106 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 731673426 1250 731672176 731672189
    0xb040603062c07060f05030a061d010503070b1e0a0c051501050a0b040b2a010c0504030c120b0103030305060612010b130f141201090611030405070501050403122007 72
    0x440c40040d0381012060403448041c018200100f990301d090260080c1200c2d200140756091210100100f405807000b90803d5019007400f1000d5510003c130080c000401c20000c0c42401d00038050b0000c00b103602815031003114803000001d55021210f6a62a06405243c0e0105c1c80110801200c030303030b25000042c02488031500b80301d0b4005c2101a29410542000b11303e60b030b254010300350101c0800003040504149411381c0e0903c03419a8118002080d61381d0058030800d5501e0446216529060240005941280240040d240120019000c46440380544c1120754071040c000b41c11603030b2070801000068440e07000240c1c04a4054030250400e444694400c1c1510f0007a040146065804100e81031455132008100e8024000c841c16040b000d0318103c2c4013501c0070152810103000302004000080c521200750040010707168801c01c01c0140e003a580c4110071607a001968206c401d40241ca4002540c2d46c81401070340d0a40c1e40158000306100c42040e4251607820200300d540e5100e5200c68001000302a0911086008042 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 731674676 1250 731673426 731673461
    0x603021e07060b0d0f0515040f110d05161707031e0311060c0406020d0f2015010902040f1e05040b030a06140a18050a030f05040b0703050423130b04060306 68
    0x200d16020341040300c900784144045030003404008c04110b0220f254000150003240c80750603084420007003040e001d03d841d0043c10b180305402040d07910348070114294088500c1829404104c080c0320500c00c1c1c03a104280320141c40b0294038402d442140840d5900c03010614400e081c1040e0344800034542d01d041c8a070860710504080c401240802c440d5405000e615004100e52038451010714000c40058282110301580c16510001c482c0c04003030f4214104180e40e4000341440340c8008940e559080507000c0e40c094040e800174030840c40c4000070319803042e110416480210412546c0910309120501000703000e0002001d925200307404a00010032036030320034800103150707170948004d031842e140c40e0103002e90307541e0b80144102c0b4400e01300d440040750010600480309613061805840003080b00300708980a0103070750006a011880081d05101300354001000700220388110030b01c0c04100741074140c0145600c1e101400c44e030300a084850301c1039100d6850b901c80780d070a0000800008013140c07a03846000c100d41144802182101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 731675926 1250 731674676 731674703
    0xd0801050a050415030803150316170304061b080d020703030506040e07030201052a0f06040b07030b13110f0a0e0915150315091f0603021e07060b0d 65
    0x348202074001400c42510140805070001c00507008444680c030010780f02290102c0400c4001420249181c401c040007811108500504401c00102c04000d01c1241d0702d00420b160058006000803096608641031900c8220a848000f40841c0c84552650011258080c04100200c2030b140c4038070281c00b4040c0280c0d400101c41c41d00005000841d803410243c03c503607030b000a23010001030380d201e03040720b218010500345d0101d005400411505200b410340088640340c060b0809010a02e580052098401c502850034240140c0b81d44600342c2c225940340d121070b44c100d41c0e050040c4682d03040e076800941740f818138801681c0c0382002e04d001c030034515004204d8103800202c51182c6409c46140080c2001d42203d031514a000841100c100020002c041410500c0d40c2c081d00480000d4242120b181c1030461454064a03201306880c0c0082e107820400101c0124144c1e410401601245040c03182c82a100388081025499900186c1c04215055640103110304407452500d0b1200c6011a4031100300421150384144401003444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 731677176 1250 731675926 731675929
    0x5100e07151e03060b0f160c0303020a0611040f1e0f1401110c0105120c04080d0302030613060f1806080307050309090916150507020405090d02010b0613090e0f0d080105 74
    0x10702c80a0801c008060601d1014010094900308407003c0c24064040207030745180d4046011203100b520320703019264002c07011002040c10740204440e43c007a07110340310400c2190015003108200380280e001d41c2c0f410380105030040c0815842e50040307104400c800500791200300c3d9240451110b424050304a41c0f003526a19103980c1165804c410b94940380303414440640304c90742c0c0e1100024881d00460f0f00c800c01c0d8400060204014550b850116006001c0c0c02d01610010081e010010703002c0d41c4141da036940a4041c01c0c0c505c040400300c0d4424070040e18582d0060911040c03031303c4080064a0050380715000360a90310400060030b424104003c1403080e1203500510b03180c0000074104040d4000040000e6030907008140a409464400c1a94200b034441b00f8000341542c17140b024080b51140507030440250400e29140a101e1007902c001000510b07151154000d11050380360a0a00025014040fa5014a01aa0740d42440b158490760000c0102d40c010000300d8040340d10303c11005d40b609200d50614030226800340e0051015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 731678426 1250 731677176 731677217
    0x7021207080d020f03030f071e020109031106041505180a0b061906020304060c1502070308061507080304020f04111210060504081b040b0a090203011404050405100e0715 74
    0x80b210350002c0d0640c00c0c00c001c030541c1c0341c2c4001010282e0032101c000c00664242c3c09458800d1007440903034842c0c0140013900c080a070081601c0c21065012801040c040c200300c0c1c1000030018429580310031b089088820681c0600007500c03001d00401242118880c1d26034401d4000c01c011500c0341e0082e5007007006414200140a12808900040e4980709220041480491740020444040b038143d0320b0158212031a40c00d1039101c110000c242c070000140001824028580c1c040c0c0d40300d02031f9404462851141c401e012140c2c546118a400081030079101b48000b4000d4641140e00400890001d840401d504011145241c0c207540044110001800c5103800c2c0444412941303038001c0035001d2410158500340c00c01e030415035074070800c2040101040300825031280325191a0080800b0000141c03075080402d0300c8100314000b0303400074068100d0100d80502c82ca00c49207000c0c0640da004a801801034407059010440100140400c03c102420034440e01d0300001e548030340c010306150400800c0c1ea40104400350002c11180307 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 731679676 1250 731678426 731678443
    0x50a11030d080f0a151401090f08100905150f09160302060d0207051e0a1401060b072907030b0306060109030b0c090f04060305011b050c0a0305090301020702120708 72
    0x10740d020400300045290010300d01908030f00d03550310103450f641da05006440940003080030700e00803461007140061210780b8180845003001e000d8840002c2252100c40d23140c00d551b182c0c41005d003e40e009403020304409ea00c0d54400e40d05c440c02503095503120304540d040c1c1000014280d500c6296981d0380410400700500622500890038044200544c950f455a0001207050240c1c06a001000364001101410407904100da0045410760100000280341c40f200c140380c03900c403400003d0f1030340644801401400401840b4410558580d0302041342000000c0d101c1c0149040ca0a5a11408000945840c012003060444403803007441c803954081482c440d8141418202136000d04401d042c40115481440000d040007415680400c44c0c4c190130343c561a4183c0007500385108a6040c80c2c00510745a400310a010701904621000b40d00d8444111010340e13280b40858540c17040743d5054803150809180000082d1050b0014000705000400160030f01c1c80300d070006120480c0040c4c584e02d25620001d0100202141409400e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 731680926 1250 731679676 731679679
    0x12f09031c080a110d0e10110408010c0516080901050d02031003120f020604120c1401090302010b1027180c02060603032d041805010503070f14042007050a11 69
    0x7290200000e1134201a000f625000301c80c0729210300a021500304100000071144140c84030901c542d007064200e6071081e0303100d4000e40c035055091000c241351441c00740c4100c800c1c3c0f9000340d14401c24100145c4506421f82c0242412604125041040580c456864000f070740c0940c0502e800e0300784c0345166142c00044490b10b80300040900c400903034143c504a0300428080d0340260020b4103021000b203100000c483c6a500403a0040030054849080c003144581540810b0f2101d2103500204910a01030041002d01380304c1240f01c0380040c40c00d81013003030660000340204440919541e52610b160f51260381d101e000c42c00740030021201c1e6545404c0003a12640c104900c940106046c3e01540c54442200c03041d220405800e81e04103881030107800304500f00300600048030300404100c50301240c40380000c0b0086018010a1180754420320440e800816009564403803242100c90781918085820940b500b400003500f90303003000f05800e0741c0c1c54000e0922508514001c1104920078030207010f18000b80c3c5002e41c0c0c104c00702010035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 731682176 1250 731680926 731680931
    0x503150d02010f1107090603030e10020105060a3f110913110a031a0a1a012a1b0f0b0c0c010c060e03071211012f09031c080a 55
    0x30340150b40c001902e00a12070051803c40320490460240510302522644004c41061900b0400414190711110785002900200d80200740402803100490a0b64002e0716146c3c0d10250b030110400084524540032401c600f0104c05500740d02d4205001e01c1030220000706401041454891003404026100c0c000b07a521103811910318469091001160b4211581a00000d108182d01e8034034000c956a0900c07410019070b80010490b051450030020020b980c031045e6101d00c2c04034101000c2e84901c4c0000c04000044080c10f80d5082101c00c0b5070708110030b4540c0d03e00c00910a2030a02003c1d503010031281900d02c03211800c02045140100d2502c10706c41c0500b4040d40c80a549001c081c04400481903004c5007035007001e002440c0128140f84c403810000300420091300b200c0c900d40710000d141303c10000b030705071600c400400c503032224180c1d80701c601c0c1042d0a880c03802010b040840808881d0b804843c0d211001031002420340f58940f4100b038880c4002c42d15290301200242c07840380c6901c0c1405882d541c0424419846103900105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 731683426 1250 731682176 731682199
    0x109090905151e0f040210090e0c161e05060a0b060d09030c0507082d0309010804020307120b06010e18010302091905010b0d0612050a06180f030917160b0c010204080607050315 77
    0x3089e03000907001c0c0c1150040b400003e090840b03135800b0348540c52829044100c8000620441c24080c0008080180480f001d0061100050b00381d0801d120b11640e54034081c0000d03103002100304100006049480e0218140f040078035807400850000c00106004c0d1803410020842000009000348144048107800410310100c400158000b500110030f132740203c1c80a0a140c0002c0d140c074800242085401e800c1141d10081c200e8800e006d01410300307640b5002c1c110031303202c042050182d6018021003142890100302c0c070b150780c0030040005040902c0020360188000c00081e02410b040141e60b415528283d06c81c054103400441e1030728855a07544551001003d101494619020007a81e41a407100045100a480c0c0c6640d642c92035145064076125884895200c0d00316511a07840e0303d0003034004002c42c050013101d24152404280c80c41c1c3c0025841d41d140d2003508240032810f181104071045507115509245440d5000d100000300c0c03501c05c2041d14024142511203e490307140030200c004050140000701846050818031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 731684676 1250 731683426 731683439
    0x140f0309010c1b11042a03060e0714030415020d0212011e03022d040f1505090105060706270507080d02060f06040b030a0506070e0109090905151e0f04021009 69
    0x2c0b0138800c1481a01c021985001e00c045c0442903180038480b0350441690060000c1d48280e050f40030900b500c024916100054503240742c1200d54041c8140008030400c800c01c0402e011403404118502d90b0031031800007600d004507403440ea0041c1d8001290b00e645040307203031005200c025840000c2804c2c8641300b4200c901083e107103400180141c110740030b06500d142c803840594441c80305483c16520304607501400c00d1008440c41d11704280100000244140751124480c8013240b14a44030040f14103c60000709034509011031074503000010425506081c004400d0911801420400007076101c5901d800340000d082e2092403e035000341800442003419007190840d03000c0040d100d041e1090280c03c040d05036000200c0b981d40c503010a1405100b40406001d80c0310741800c210304641d203c2c406a11500e000c1c0c1e92600c50b280e64054020a6501018004203aa00450b0741044407042c2170024a0340300094102c00c48905d40309109250102d82c0076907400318860300da00200420350808180e401402c13141c0380b0380010030740c1c82c001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 731685926 1250 731684676 731684693
    0xd060321020307032d171005010e040c0909060b0408070902070305310801050a0b0105041410050f04090506120303041a0c0403050f0a06200307140f0309010c1b 70
    0x10010180010340a4141c14128a00d20030142c45c81d00900713042d070b02c1d80c81510180401500c169540783e64030b98400003412404400c4ca0b481c2c04c82d041a1100411002440100300141c40280030890800000f083d0000c6c1083c4580600002482d88202896035241840852030401448c0e4100c007181c1401000854002a4031208440c0c50701400c40b0310b0340c07001040c01c582441c07171540c1320941c2d01c01ca036400e60003181540042d4030041c0100610002002000c1d0311360010354080c001da0cc9030042c48040f003071900b0440d0404501e18230383c0003001c5c6841071800c20000c1d0304402503081500003610165a840401c00d960421030442001090550021800c1d441c0654440d481c0400e400b0039440240485ca01042918200c24151f801469010041c0c8540d04240100e09903103003404035068400d181401c074080c40a0161156072405880c1c000252031541e9581c0005445518031510b16070401c440c00c01212460303245010266029080540c004513460454250040c040313002c1d05030303400041c4405003905c40092a004c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 731687176 1250 731685926 731685937
    0x17041404110405030d080108010c110a060b04180c060201141302150c010906140601030203071205070207050d030f11060717061801060f022506030b03010609020d0603210203 76
    0x125004298214480c070503081e81d000743c0d481243c05116014111414541201c1024180c420a00c001c0001d10340c8079204460018031a440503240360400ea14007404070300030f90131219070003c0150000c602816050710003580324030851815075024162980a000040d42801030003200c403080102c20800703080041060a4500000800030310035801c102d0511000c5901d8401d840c07103801000000c10801115003060f002a0002044802d12194004c0018030150300031f00c03e0300e00445655492003200c60280000070000c21000c0c0c0f025041d40701d154030018256a40c07400082c24a4803941c2d40542c5c4822072180503082404980c0c44d011130390402e5040000940c0d2201201c4241519414065915100c28001c40d400803000040c4091140e071090001c070b4150b412200340f0040c0203003a0300721250000d80c1a90544c0ea0035400d6000001e144103200304000c164071907000785882c150010000500030340d540080900300e900900c490600c0d0b40d181c8608000380103040302d03007403001e81310484441c15510b82c18000a4492061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 731688426 1250 731687176 731687179
    0x40e090d0509010807030605040531080412241a0a050f0f060903060408040315140c0304050f07080c030c01080105100c082104020406150f0f2a170414 66
    0x401000606040c847d0701305100500000d00100b01c5810710f00004000f8034901d41102c1700c21920480b2075204040000001d0281d19080700c001ca003800e09003503d0741886403181000750360039170000f40c8079032141000344007503e14041c2d20840059450140310418400000300b402080c0b007600c00d5041000035403280103504000042c12070716500480c0c01c10700082c0719405120141e42d054403444040000f040504001041660300807400e4050800402c0f15490644401d02070042421a05802081a1003400400386400501c0f4406541c0c42080c00319404d481c004075503001c8201a4420001b49a035410203101c515603050702840c11295a41c18400803401000041290000700300541038003000b41b0001c402520a405d4180c62181c5904841da114132141e050140c2c1e0581c42286071042c000307003a181907183c4407050030154031008204041244144c0b00011f1800d584400c1c460190002051040001110b20710f070401e1911480014009040144056880c41c505100001c1c0421044c01400007010b07503444030400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 731689676 1250 731688426 731688437
    0x2010e0f01021222080304031e08040504020d0b10031a04150e13080f1e090907081008190501140906240a14030d02030f0f030a090c0b040e090d050901 66
    0x3042e44080c502c0805135000d140c203081e07980c000843e103540d0200042048900401c456007400c51080c000d080b126001440080440130100010045030034103402400c8002a60f00001407034084000100d00203407003101420001945c2d070001880804048110801d48070f405880811116041c00101c1c002d03e00c40c0e014010b0b80000d0140024074403000b10741400d420039803210075103440d8141540200d590b504600b04120461716009000501351041c00c2c01d680103218010030b02d00702c0c0d0700d0301035069074000070280c5200500c0d0074000c0c002c02c10040c20800c00080c1207141041d80c4000c146818202c0c21508400002c103a02c1c3c21550510960900000b0115000120f81e4140e251202a071901003084804000340f0581084c034015000070b00801703034045120303841c0003901514009449041300b2a1244106044011602802d014810480078a070001d1540b0440f040c100080c2801c8d0303904c807103c184215500200c0f041d14005024400c0c440981000b581000031840100340d4410000000707071880c007920001604000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 731690926 1250 731689676 731689687
    0x5060d0605191e0b1912061407050405120307020d02060a0c0614040201110a03050a0e040906020d0e0d0801030506041217040c1514030103080918070c02010e0f010212 73
    0xc0400301c03400ca01c08504104025500215030341d000003e644250144540303140034500005820003e45892001d482201c01030303e07030b40c04c1c05210107403465900c800b69006c0d66220401c0c50000b000d048010b004440315181c0da44c46518120810140000142101d09150018028040182c443e84640c0d00c2407a41100c001e604d070705a0f01c1040b00c2500780540040c042d142002410740304000342c104594003c900030303a17400c4100a031109085a0301c0da9a90070003400281e0400401c0c030064131540d802031301c0ca0001000444c4440d2541c80321000e031b81196041c030200c150780b04420915a0010020000c00d6040e50070400b2a540c55501c8241d01e54000800181030b0441c1e100c42c4800943c8201c0119010b2801e64102d044c050030141458001c03022280038500079030640c44110208180600300c43c0e14608803007000f151960382169608003558121000c1c281d0000100c812041001c0141c10b040782c810a0a03a40b030b0003035400c850000600c0d660700c0c80080d078020000030300d0028241c0d0380400c1151444080719601541e40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 731692176 1250 731690926 731690941
    0x906040203071101180c1d070e030705030a200a0305070302300f0d02010b0f100c12170606160201110f030406020307120801081e01090804080c04050a05060d0605 71
    0x2c0c0300007064076003a940b07010309045000e4201003408548a002d1b0030f40000b40f9407603040c3d070320102e215209100c1a40c07600f01c0c00289014070440146040200c041c007610003481d0366001007440d1010107002282e00c191445403041e0815001d017040c245010045808002c03051560721216103511803404068003071100c91425600320580b403c50742041a0000d4200204086140e1045443d1843d00001c0c0b0381038002c10742c1215005105005050200d0002468228042e0425003007091b0b600d20940c200e81400560304160001c206010131300c400038940c1d83c40341f148c0d05200c0140310401203c02040d00788211400d009030500f48810803012080107a0a00344041141a0303000f030140303400542204501c00e480001000700d0a168044060805140300f2100f114040d07402d40302c181c40245003406241e0803a4050105a003070441d68084007041140c1d1000002180301e42d64a4508642d401600312050541c00700e8403a48150400c1e03c1402d5020146000403c603078140803000034852001060041d004075107540c0810942c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 731693426 1250 731692176 731692187
    0x111c290406030f051b03031908060a090203100623070b060a09050109150f03050a021e150a08130201050f0a11030307020604050d09060c060c050d0e06061509090604020307 75
    0x2941e008207103400e00c2d58803440c01303a64540d80840100c038120205840411103081c0001a10108500141d030f02060140942c800c45a0041c02098154003501d90740c0000f40048082c802940075412840403220f03403a00701800036024580941007207011032440b0425090882d00c0c43c090ba079000ba40a482c061240c0c03103400002c4e1411403282c0000c0b03011450078000081801d00c40e4810445408484280741605580301c00041140100b48406051034000342107030300040c5040a40f0312049140c516040000d80d80f840041036030f091090185036801140050484503d039000024150320240046150352903a103030b41d000900e240140c01c40b0140300351b008514000c046005c1d54005210706003840490351a8981300c00020355600054505552074020010038260041c41100b2010550320b06858140c0c0700c0100d5a645001404019440800c00a00f40100c2d804048035002d603a80328006d100c0148a582040020480c0410070a1504810600308005103031860b10368410700caa002d8030032940107840340d56004042d02c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 731694676 1250 731693426 731693429
    0xf05030c0f07060236120a0210090815040605090d0f18090f1a1c0b0621070315060f030b1b0c0706031808090906060d111c290406 57
    0x3100c05c420254062030340f1207220140b50000582d5903c44200b030409002403130009034115001504403070500805400c000c41d00d445048000e281c1001b40a40e90f0546074141503c220300000041810400d0000b07001075401502e406c0141100500030803d000400500015184071210082c0410014080c000500d5010610700508d0718000510841200c0500c80c0c004120f0801c40c031199462a5a8103c100d00307000000b6440d500b90f82c00720540c1c4481944410348801c400501007503200c42030020800341e03185031440811041e00c65030f00521280381186000001002d1251010015038a090400c10044154005207403c807600201a812580c4643e8004110b0380d01c074800c90035603220001a401c1c0000310000c0c0791421101580d070700700709800e55004628036200030030a014041e050180302d10360203442c101b601daa4121100401e40703850a5216924602510b1140c4804800c7e440e01240750101405402440e001d00310400b4020050020030000e07600401280044652040401c019080060b8407954060720 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 731695926 1250 731694676 731694697
    0xb0f010e240a0206160e0612040c05041802010201060e090c090c090901030c0303030b03010c09031b0e07020d020c030c09010312021216030201180b070f1b030f0f05030c0f070602 78
    0x1c1c2d8031805a034029540e0042a60f5003040c02c05407501c050030980c803440c8810080d800041c000e52400a50031010300314440c001d8070680320780071000030001e00355440c1d01c0742c400c131503406c800400d41c0904540006421200b89a0211001440020800262000200360140850001c440710041134441a10b00ca8030380c0079500300103800c5940140080284007070b40410305d00700c03440780c2e405100c040d4070b4800341030a883c04040c540000c102d0a84041c8000f90203c140c1c0392003129089980c18505581e200e100b02100070940f01100560000400248110f9060003410000c1c442500200707601590f04000c40d80c051414400079000140b0501e0201a80384280500d60140c180100380039210328030030b81d90780e0200000c2c2c0ca00710302540c1382190b495030304509a41080a2290000754050381303036446200130b54220081c42d000604003d0100c5103c500281c3e103400300c4040d1402a9507804000d8021071029080d10340b88050601407000c140208244160103408440310043e00f0801c05451f42c10f50310b096406806000c4120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 731697176 1250 731695926 731695999
    0x62205100c0507050d050a2307060519060f0509040201030e070e1609080615220f05040b010b030906221a19020403020306340203030405010b0f010e 65
    0x40603140c2c04030140444a0007002514030030b4502c21000d0700d640c0b10700c40304140030440d0309400201442c100c1c8648031804000404803454030b00d407550fa080444d00c040b100050008030030780403400110303001c1c4030f03a07409003100c04d0708280740c01c0c101400a2004840104024101911984c244800800c01c0c0005002015504031810040c200072148851590407184482c0c006000c6880c00600c0e04800510140038210369121501454100d030103010840261250210100480403c8241c40512030700c103064602c40061800561070800c0d20b0804441c40040e401848026018005e02240b00c4000c2159900310b0718003100038402d0712a0a20710859108218400b6040303518071980c9040e10074140403000c2c42102071202265528442c4c40002e4100d004032302010b50103034869000103190354a000001c00200c495544045140380700c20840d4411101c2c900c0701c03440144c102100380000c1080c240144200803c084a0b094a811180400200b008620620321445a507500d0045580c100b0f440c60f02031903c80343c10345803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 731698426 1250 731697176 731697191
    0x190305030721080f0708041b090e070b0306130b0a0504020a030905010c020d0903110301061715240d14011802120303071707051306091706220510 64
    0x2c1000408404000c00d50300b9020082c041540c481e2100318481e1221400200e11510f400c4000c581c4010010002c80d007440c0c401416441c82940400c611004000151000c40e96105100c141c6044c40b44d503500200c0c4108084c0240002541c5203124440581c9200d100082c0c60601400003400300042a8086ca800610004018507401e0707040d08a03140c4540907100900c0f00007800c95040340d60f41521100c0ca000158040400e1002800c0b04c000e50402c03000050000c109280c503a403c24120300b8041c10807521550040d0400c0c031800000000d402d50010b849202005640c1d90403058507001c603074034481c5038482c51402840304200030000420301d00c03001810008210800c50340c414509882c020700741c164460924050f12090200c6c00104072403159a15a0311317800700d0451001c03d040c0011000c1c000d01c0c2441801c1c06034000b903902085109004243c199518401c2501d0300504403200d0308194044400e50308280208100050315406801030010001031041022001381015801c02201d249125034481c1010f04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 731699676 1250 731698426 731698433
    0x3071d06040617060108070516020f1302030711010b0a05040e03220501090911070605040215030f0a05150108070509060403061404030305130f0f0201030e011503141b1903050307 78
    0x70090f40009030100c441c0c8094885000644425008841c5500042e104100302041c444450f09003910b402d20180030f000d03d80302e138040050044107005516041080d8080b007004075942c1d01048049207100004000c01480340d1601c0440e00f03061842c0552809581c032040c940c02075440400484820121000c4400760711500b0000d4262015040d104213400111104c0b40401c22103c248100c181aa0520040310315042031035444201901c1c00078411b80c1d200c954030a140f0100e22402d4015441848018950005891b18001c03040440380c000c0d03d000014403060003800c115036044041d003a04104641006074a4400320710000d1664444c9400c020300440c1401110b0206076401d004003400395100751000e00c0341b99203500c1c01d1420b1741d92054010f0320385c90740d441d0340e0408949141c0207889a940189404240c1c000c40180d52400d4032440400304903c2005490f04005000d0021043c4485544950150040030505070030421810060400307a44141d150a5404000700c00b080d0107100196409418ae0340c84070b80608 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 731700926 1250 731699676 731699687
    0x8040902072f030601270b010219060e01050c090d03030b06040b04080a02090a09020310020a0c08040e1801110d0e150f101202060304030513051e0a081203071d060406 73
    0xc4a80c044d00c0f84034004511240c038000000c058000100c1000b540c02d480d000204064403c1d20002c5e41076004100041212400b49241c0c0c841c0680203081c00306070b54402c80034031401c4840003800e9640c0181e050000b11805c1d0b0310700785100c274095018507003c15100000c00c001001880360b503000c00710024000a001035010800314011620a00071100d003401e44d03550703c0c030758419640348a100a40c5034100307144443c2a28a41c2c3d0180187d40c1291a241920045c250b90b03c229940c090380109940d03951900400c4110f0200600031130540d4050b00082c0100d13031400c3d1051000b0300410b820099242d0b103410310300450b80c000b0000d100800c0035500c0d540407503040584c49804100c800b540e4080428141c84030104082c411000c8130440584d01902c000d265584540301150142c0084000000114600c0400140c5560707072003080e0074445420300f01600e2103150038100900f0706004e50104845e60070441c8164035451614080e240d01c51141c3c10004480c004030380354400040100c0c06031540c4400b011801080c0a0b5020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 731702176 1250 731700926 731701013
    0x1306030302010e0604020a0501050307022d010c0f0206130f0813050a090e0d0c0f0b01030b0106021005041a09121207031109100518030a06050a0501120804090207 71
    0xd400801101d28943c2c04039403544012100650030407520b5008000ea0b51003080150b07030042540c4140d90700c1d41e4141000c03410300241c00c6000d207d030b284180e146000c140428441c04001e140c440c104190790b4900d40b82c3c043d40b640001000c89150319818501700040c03044d03403d241020240d014104c10fa5a445081070034541e0700c018082e0311300a220007040403d1885552251132180d807004c0004107004030b5001d40846684804201c00c44805450f202e203000007601c030f9034906001c1d511900001c0301d1507050a00081c905400b06a4000d245414007052101290840c400c00d4040100c00941c00e800741c1c0c86800c00c1d80f40c44170103102c0305009400090030280c00041c001035180202c0e00d0303580c00c2c0842140d0440e00341850040519a44d0b001500d0346c121503900d8084c0740140b024400c822a580d1981110300b001a040c41000e00041e0303602c5e0388460410804c1d1049100341c0b0302400042c550518858050b071505181c90181c2d026031406e01d540000c012003481242b416504180b55804500d0390403009282c96104121320380c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 731703426 1250 731702176 731702183
    0x2505100f1211070b0901020d0606050705070312030b060c0606011d09010302130b091321020d0f0315030b0414030301230f121f0605060a050f070206030f09060a0204151d130603 77
    0x50400101e24038bc8180c084500c0303550400001c00440d401e41c2c85a2294625040c00c0400381075503410501510b84841026083c42074a0310302501d100d00e40b40c400500821a07880c0c1fa900c2000c81d202c1c90255039a6805046c0341540c1d0140c580c6940001030314410402002011001507002402c0d20401c12803200e007d0104070010311a503400d225030200c40090020f81241d00c00740a0150704100180d1031802c1c455500f0500c10041403030086260412505001c0d0604416002541e100425000b0401802020000300308540e51a00c000c614561406a8010722990100300440f201c000c5540c45800319030392541003041d05940280265521208088516582c80d030a0b0000034011581080c04c1280c0c01007423041071708440000d004580341c4038000038100d505034005819078940c2c01c418400880136803101c0005d107100340303229510b4015500b41440f40340c1c60f22000408003003801d80100010b1109580e070562140d108103d1381090298507500162840c000000c17008056084603484412804080c40f130340060044030f00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 731704676 1250 731703426 731703431
    0x100c060f021c0b09040f0219030804170609031908040c0315141312110102040e070309050f01020901091a0c010c0518010c232505100f1211070b0901020d 67
    0x1441001e00444d4441102c02405022801920802600304070700966090201c08032650754241e00c990f5024400d8010340c00c291165010f00302d501440e40001c00c4207a4200715440b00950401c550700c45d0501d4520003241103041080300c840e000c6420003c19002d208095980b090303100c02a04e0482c02c00d04018103014860700078801e00380d4080307003414200001468400c1c0c1c0010404007034038428502a1040140720354404c01c5990708003c00194000c0035002c940c01011280c0d40411410100d0070401d25020340520f8045069204103c101450303030b0040e81c10811a0701031a1030150230440801c041d0030743e01400c100c070b206550a0041c8904000e500030000c140c80c0b0007161059500d44210001180c0c90703a00c0e21001003040780380354440351168448820071121a070506007101d0f03124400c00a05080f406c2340c0b0b800c0700030107000c2007018000c2c1c0c40c007501c007429105094600030301c3c420000000140704e03248220302e9108071a92101f40380402d240c0c9608840943d60441d11003102402d000c84c01c54001c0d4842c2c2403c03c585072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 731705926 1250 731704676 731704691
    0x1306200f0109030905040e15091906050f0609151017041203060b04080604060b0a12030f030c050c0c01030902030115030803010305010c090312030506030705090a05100e06100c060f021c 81
    0x541b0744a10169068018002c1004050492210076107200140c080540b600c100740d004006071035001012034402d840740801141c941415542d41d81d8200011340700c0342c415202c040c02c10070396a80781040d040b41c084003200c2c641480071910909448075559250042140c2030480c0c10002800804890701840151566042001660b141031901a9000f107003d42e035400c0d000900131801042c0c59802400b8141802480102e0707240d07580032056692420101c0403408203030042811112660144201d180820f6142065407070081da0000d0242c0718090790850300d06043d9180e620f082507440940c000c0a400300c06070302c0f41100780c0d180e0a0503403080d00309100448540d0709120070309a000e48103c91550840c2d500c01444807100b002c1c02070a4000c4c040080409416206100700012959200d0038203502a4a44100001d99414401c56240c034809154000d20003582c50141800741070340f285035201d552100d0914202401d5020740c80c103680a0114a1000324080c0d001042c10a800315040c6004d0070004082c1c142080f050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 731707176 1250 731705926 731705929
    0x40b07080c0c1e09041406101502061b071b290406050412110303040e0405010b0109080d030f02090405090f1506060904050702010e1f0b061306200f0109030905 70
    0x52040342c0a42180001003c903050300b410b00244960b0000d2180186d180140c030021030a501c2c1030f070700310b80d20000720a07100010400c810a28802401c001403d10140c1410320b800d441800009900210314501040006104014008010002000070040022803640d03140d540da11106640d94842008000c140c034400d08400003112070301260f04a0b005d81c2ca80c9420203141c00c04101131003594110664556000032848007080c1e42c1400184040c0c01085642100c0c0d05041c00d1032030842d5051f60a1505000c10245c05200707445000402800345001454081030071a4581c5419000e0700904030b866070458204020b100b8030b1200401c8500c582650038085a9a00c0c1c01c0000c03a4900090a4494540101d002c000760030113414036800c0b2590241860002080f00c0c0d01000c10217103042c0c9041e0f8402d1800b07080c600380401c1924680128018114110740250500c004100c0d4400d9034912071180c00c003403081800ca40483c040e0b10b1200c02c1d442d184481c00b981c1144034482c062070701820f5a02421070001c0c10030b00010425 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 731708426 1250 731707176 731707189
    0x606310806091905030c030d06090e0a1a18010e0c190b1801050403320c03120705160f0e010f061d03010f0f09110d05031608040b07080c0c 61
    0x14844802c002d10500102030000f065021482e003040e00c49000070007081e9500e00301000103007a8503042c0704000540c07c0c40c2249100889021010800072a0000306000c2d01103420349a00d41190001140020b400741c0f58182107000c01500200055155402d080170014503a901054140d90340105441409001c04540c480300e65024a0703015240c80700c007040c00703082140c4070002143c240100040c100240b80c20340342d49850f1400242c0741e8044076403510b900c12003413a4440d10108150504404d400905000e0b050b100013a80740c0d03002258038a007152010400c0c0082c403800b04226041e1299401108941e641c0b65065042d00d40f4260003204100e003201000019540c0c4001510f404554140d556036050029008607011030100b80907082d0780c550740719240c0200000e01807084200c807000d564400030300c81d082341ca001140103040c10003507441034401541960209602000f20740342c001c03900746000407800d0940303803000450140750040417544401003282c4040025131030040856028000880b0031000441003040203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 731709676 1250 731708426 731708431
    0xe011101090c1e030b04080a12052a0310030204050402030139020604110d1103030a1d040203010f0b0a02190605010518040510021305030a0b0712020c03120606310806 73
    0x1180190301c001b0340421450702c040e0000d10300c0e0307240807020880480311040940f1010340d01c06255808441080044940401c0b840303413000400c0c2125819480c0c40c4084105408161201034052915280007804664081d401500da00301c0400103031444034000100e440002c00c0d1503130242c0c0390300c40c8050021202800000d03541d1041d80d0001c0000c610f80e030004207100441f401517104440b00e5040a0100d5803540c2d050002d003000c400301355124580561050a240030314804240994022031040005000052403440181c00303803040082d90740c3e524501400300328501410f85003401851030001c44800d0800c4155040f00f4122481281c0104c5d03003140e2981c1454101030117440042c91980300d0542ca14841e4079503005040c1030408000001c162a03521030200b1f0a001880404860b582e0b803030701c00c000070302ea00301562410040c900302085040142c1c4d00015644e83c4076800e518803071400d4040c00900203030380d070608440882012203030850b801d030300300e0030b03000050413031282800715992004030040307003000d80040e800d803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 731710926 1250 731709676 731709683
    0x51317030703121a0d0213050c03090d03150501110304030f03030203160e010c12090e180115140d0c0512070303030e03090a050405090c220b1c030e011101090c1e03 72
    0x150b260503002c2c1080600351540d4412a004401c0047e0045010414801d4500c9850201801c0c0e07960701d01002c1250400009940080515145c0801d0158030b04007410400140c1d1070030b0a00c810308000c500a140d00e075000f6039100800c2c1c000401c1c03000d0b0030540e01d500558058410350924007074a221914059035807a0303003240c04074002104201054040f540124408960319200d0a02c44003007a22809c40b6030a4040449070011200041c5043d444661000d2050f0640845000d0221100034145401000d015440ca00d5461150a0844401c82400180a015001040024080c9540400c18200325407a00d01d03501c4160701203481c2c5941d1618081c404800c440600c1d00042005480724145030400005181c007400c0c0c0c0c566882040c070034040c0703a11100110400c02180ca201c0240041801d111081071307c041070341190040500640d445801c500d0328101c844069894203000000100041c0103c1d801c1c40c8040b001610fa608101e40d0005010790605240180c4041da0945111405103000f4680804030f01e10004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 731712176 1250 731710926 731710961
    0xa270f060f02100f0f0f150f0509070f031103041a01080105100302060c0f2515080127060605090120060601080a1103100806060d1205131703070312 65
    0x9810f40d4407507500c0300c5115002040c0008203054440c290004592150a140d244d1650716040c207100401c0d200340c0240205450503119102c0d07418607000c00d0681c04007a02c00410f0010075045184410f019400c02081408a24103854503807400d81082090000401c0ea0000c0303048006d40082100201800784d0b43c4101f0701d020503d03818901e1030f400e1003aa98801102540d075070081010300c120018051101103034154000826502c26001407094001383c001d00c2d07010f10241c80e07401c08403c80ca650807684460450f54120071043c1403101e050b012a40c0301d84440105200f00c0d2800c0707808500203400101030400c4040c213a03140c88100b080800000042910700c0411001c07944400c0000e01c45600c604507907940322680701004101c000111402c05207580003034030304004850110009000c4c40d41d0802c81d250b0710000845440319814955180d1000040d42c200d110010404000382c2c0d503c07911071074064a0003d1000c42c1080703403400c011006454603900240000c45c00141c01440d02d410140307540c000e86444403e043c1c0ca4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 731713426 1250 731712176 731712193
    0x50910111c020708070905011a0711010e0d020307060816020a020d0b0628030611191409030307080a0806061e070309030f063303080a270f060f02 64
    0x1040071042240c20000114414694041070707a8a091180340010045c400c000f148a5051910044c012080010000000f00d014003005012a8041401102c400001e003016050110b1150108810081e0b00c1400307501482120000190183d01c0343c4070310310900006110b000d0446500504a03120303c41c07240003075030144d501d07014200412950044160405c0c4000d0a4903c480d4035451410709803902d5030302d0803403611342c1c07150304005104403400f410400ca10010501d901c0c4c080036184a042100117180a00104030310341c907013404c481801604842c01c0010040490b070f1107588510300182c8590101b00c49400160181d00400c0c0903082c00c0c0c041e50b50038401e8045825500411134402d080035040b1890036410003c0205002003c1002c0355050401c140c080c2501180019004081100c800c1b182c00b08000f002440c00f003441303070a03d281075611003601e5000481c11f030b5522501e1000c90342d004164403142003c1547e401e1040e000004042c0d540102c4001048c0103d030213a5070901928024454007281015800001381d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 731714676 1250 731713426 731713453
    0x4030305060a0620010e06010801020c0714330c011b050408151003060f0c031a031509010b0901121a010b12040c030506090a0c050402030c040501051b01050705091011 73
    0x3605101000c84c1c4000194000221034014035241082c0e001001e141d60009034024402801d204142c06800290790100b03440601502156800c2000d500e4482c10040035240503000341c0003881c04040c43c0035048525901c511901820034020904800251072010741e00038200039050181040d20201c0d410342c1c000c0c200090110301c840300e00e620010070401c0100b020000110001e001e512074040c19040d4001c00144414044001a080781c110f00d060b0580742c1400c0704a0102a54005050490030030b1401d440171072a06c0304540351780509440130740f5030b034408906d030004603800b512401c1036091240614408185144a40c40b0542080c2082c00340304418801009503452040d4058916074012344964509802e09070340341c072010700300360341500c0c1030902ba04881c0075002405140c42c4084043e010440d411481c40c02c1ca4804c00e40c0d40d1245104150500902044032548004113200d2490f00703c441400078401440e1104c1d005091381e1040800c50300c54a038890480740b45501c11b041d444a2400c8910060071500c80550 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 731715926 1250 731714676 731714717
    0x9150603090a0b010608010305390312070f022803060903360515030402040c0507080f0a12021e2d03010305010e0d0804030503060402160b04030305060a06 68
    0x10503180c11445000b04490004442c1c82c0e00c0c900038500360b640d8448550440c42d040d07017011895400d0314074101252440701130101041044401a9141190540808407480042402c18104980b0340740642000704040d0244203c082d01403000c1803003210640c6410319020404e007031211110400d0308a26036140018000121503602c041c1c0c9150080c281103841d0742e81107400108891040b440e0486540300d4044c20041c80c100d80c1300c150b010f080200c03044821500100e07020400c174000200041d128070344492003021414040c0007112880e0f0b40101c2100e5950a0f00c14003c8501e0b881001000001412140d41c410350f00358501c01d880701d40000100a42e6105000d403441c0e840e0740c20461030403024055503020582c80300710f1b400340c0040f01d11450300820785035031450501508585400c0b407241c219030410b0604503000b942c010003c0d5403041c2c2c54141682c03a42c881d0b00101f4002e008000d103800302040400d00d268203100c054110284903038401d503002e01c040d036200402d02c07058a4052207030358081000e41a03c44100341c10310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 731717176 1250 731715926 731715931
    0xf0807060e100c0618060e0c06030406020a140412031409061605030d020d0e0607080c0a030c0c061e05010906080a031202090d260f0409020a09080d030f0b09150603 72
    0x20f00d003a0403042c0d219200d1404490310101c00c02962000e519070301c410041603020726a500c1c034400f00500b81117201304010440d070740300080001b807030160f000484240c501e01075000454000410104d0680311511141901d03005202e210086d00410039010b40a12100001070887d6980d6001030800d0b400e0640001c14000085419282141c07a40401e00030f200052103580302034045415040c0c000706505102100031400c0940160a84040018175000c00140940100c11104401030702c1c500043c2d41c00d581402100c500030b032074a000f44071a0400040041110501c1e200001c0b6a08142080000d40d0766544840100d0303c1d1449021429040f96515402190060f441140719440e0050007601d0310040c10000f945008240000320364489407021300c541103001c10007088054403120900302d45040e05142d56400300d0f0040b8801d03d0003550300000c2602d00a4402c406100040844004440e44400350860103005414440d912150140c43d021440640e8a008031085001c0c10100c4440d0502c2030801045c81841da000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 731718426 1250 731717176 731717209
    0xd1e0b04113c061606050901020a050301062d09080607170a09020406050d0521030601020712060905010c1e05040f030f0512210106110c1e13060f0807060e 68
    0x12451809902d481004205459800c4c88002d001010391405c40300311034010b400c00e030142c0c0c818003d2a960b10780220407241902c5240c200580510000c1180c1d01c01601104110000d64034006000c0703402c030350025140d005803551502030301c100d59141001142c100360001c0c0396104030000d20380840c05004180d4003401c0c010340081c0c00030078882d494a0100d81071032041302d021243d9600a6006002001b038400088640b00044e400180c514240790700000e56805c0075001d50000068800700410030400950302606025074840c000b0b00c0486650040941a4640f41c900415030401d608010f00c42d517449102220203440c3c41102c50003501d030440d2a1810600c4c1c0c00340f400c94061040ca0f19410112002d030014043c0e43da961901c2480140c840010000c03100c0341071b03000c80c06200001d40c042c00041ca000c83d80c1c0c941110150b60916001c88400e4404840d241046015600181401d00620b9003d02e15002607003070324142950203640f40c2d5102c40e010b699031075622481d4000b5250860104442c50300f0002c03003904164 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 731719676 1250 731718426 731718529
    0xf1003020906090621130b0f060105120a15060c080d09111906140c0c04050903130b090a08120d1104030c060e030c0303180d1e0b0411 59
    0x140b120200740340b980021400040b00c1508201c01c5c080322041035003945e008410141244142c481c950318290748a80192428040c080172a00154031039201d8030540311031140d115903a00c1c46041c81c80b210402400846c90200b180e43e95050046203544c040c5415500e180c0d07010034614507181800c9090b000912888408886208103101242903507901d0f03150700940c00c00c80424200e401468440c01401c0003804003140140c1140c1071109090300c40340461408004d11040e1004245691210a0300d170940c4200c0988909140010340049007644151015115014041c2c60f4403a8240d241c0144ca03548a4095003040011141000540041005504030619440e4030f5070b940c1e42007980302d9a4083e140c001e190441e00004081c1c505000140c9401c100c070281421080e00603600e4100c0035002003000c03480d5140d0342c074012440400e0f0341c01003020019104080700241340700c588403200300e4130f801641000240c0302500c180911401c003c0c40c034074101903910f03058220140d50790000f80e20781d4038940d17201c40e035000d08090504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 731720926 1250 731719676 731719687
    0x90606011b0c030209041b05031204090207031101051006030509030309120f3f06031b0a03060e0a03090f0b0405010c03210c020f06040b0c13080109080a09050f1003020906 75
    0x7120114030031b00452041010740003681a03828030622a6032140d000c01c0c4642d1242c516001702c0b01d074100445059510300c08001d80d0301c104034181501c41241072180c01e10507600e0081001003680c1da4860100540d500ba5500703001c0c949a40812550b6400f040e00c80c00b036603030042010402c1583c820300003003407844074264400c7c2c00c000c080040341c010a90b42c484150703450781d45055001c01400f111010030722442481d07482d0821904119002c641d981000303410000381071a044012480c03039565080c8072001035034000018420461905610b945440c80d0100071004620311403404110310039200044e0007907400e8601c000741032520346801115034810381c81c8290305000144007540110400c0e00c440300e01450f4900000705400d0b00c0d60100901d029040e0381c4000c6a60400350602000600001003250083c102c1c603d86502d840785201062046011030b03220308069803802515a0400990f81d0280082030703030031385508040a03640c02c1030280711851020340c69445009641c0281020b8041d81c003a00c40c4d10009815941440b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 731722176 1250 731720926 731720929
    0x100e04030c050106080717030a0225050402130f051e06160605040b1603111603090806280203010503101a060a050c011a1c05010f061d090606011b0c0302 67
    0x103443c140c01c40c520540110500348000c4400d008220400881d10004514040d201c0c132700203444640340b5000d10355804002c040851444140102000540401841103690700c8011401d40c02e40c81d00c41c4940e00d040051402300107507501d4802030300082d14510944040c0c1c0b40d607106003080300d5030f403140c06203145034a020107507000816a00e1043d031f44140d1043c0c006445a0034160074011005d034120f1202c008141c00e10101c0604818104141c0700914115480200180b400740380070340c5c0b0295150448a918491f0340b003044003603440350103e503103d03000c00559004c3c0341ca00c00e40f040f026440b0034003a071505640200304a10b207510055010780b410b0b0321980d8115070101c00c107100040c1c26900804082000590124441d81d1f14102072280580200c440e10740391100ca8140340c04500400c0089985899060b140800e80c420b001c000c0d04080804001048100405625184c4511080a0302c40b180004a920400010614000002c007140900d20503141c152070441d044244203244400302c48226040744a1b1030f80000103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 731723426 1250 731722176 731722181
    0x11060d06060210050c0327010e06090a0c12080a050c01090c09090308161709120d06170d080c0d0f020706020304210c030f0201020c0f01060503010b09100e04030c0501 73
    0xe807803607030702421100040307036036034001d41e90042c0203480340b80010814009190420031002001e4010b15441c02103090361115024010004003509604c179001e12010019050f502182441e0403903c00e02e810398007242c1314044019482d0017504011300301c1c0010007960104d41d0286000e0040b900f46840045840c0d0350a03994080010040c0c0d0010b40b03115141e000b41400c143c3c009030b03000c0c1c1c0f00171144440f0402001e0620300404405596421030035070180d4030080f80f80c55030f050000d192421002c0b0020760303881c00301c11680e500801c1c180c8504030105610b080048202c80c004503c0041c030000d1599110288c0d210403644800c1944240d5058412643e90a0210020800c0c0d0020307003166802090016282d28041c2048104100c00c1007450700c46e03240302e40b901c41030b55400c140e556041580500c0e10740c80d0f02d940344c03005a00a12590020f240248501e0116074510401504050b055a00c281c3c000c4c0f0101019000344000824181c0720b4010070808607500b400b90244528a050340036000b454028189201500d1301400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 731724676 1250 731723426 731723429
    0x10218061c060305011e1404020d0f12050301050a090506010207061b02190807150f05250f03030e01020f0f09030a020934020d03050c0d0c02030d0c140711060d06 71
    0x415035151603811b03002c0340c180d81c081c0c1828001503606001d012400e444081c07502c0c00c001c000070302c10145231414900340070244540301e5515a01c000c6202da40c4d5a034140103405604240700b42c40c030840401c1c401140228150041c14000d440603001418020708100064a28455400000314049128070200002d662099001c00c0451006034141589504012005051003a90740003013241d07284041903420302a510603010300c6000c19502d80f8640700d8010701400350340c18903188200041c49200038140c40510446000301d034880c5100380c0303080001c2c0f400f100c1541d090340548075040c0c02e0f0742c0c002d0008001404000c0024124854000c0c1680d214004550004000744003d45100c0c00c02554040078028154181c040c0c0903289180c000c1c500d0752209a5040295201c0004607084c007015103860104d9084c1e1089010340b031022144181c01e025013030358070100a5480d040200420380140c1015102c100a9006036802c0445800100f229450b002c82c4d0f4070340c03007006500c2680e5203400c281c04010041c1d980032503105410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 731725926 1250 731724676 731724683
    0x31b14100302190309020406050108010e042d06020d0c14040509040510020403051b0402120606090a090f0b010e090f0121051227102109050105070809010218061c0603 73
    0xb0310540721b0040c0000c41d07001e1780026050004080040c480f000e07031401c0c001cad0f006900ca503031303403004c01c01038901d0306501c01d4040a030b00c45800410008508111658015080b82d885070321081041c901010f404481c400c0c840702205000060400080c811818401c0a150780980503d00f150082e8bc04264501c00301d0740103500079101c60300110004e110380b94001807506080c3d80d04540a42c189814a020904403100107040e81d446400006071010700e0307442d07100d029001061240c208112080e409003009014000440744140010300e4401d04036114500003a40314054441802c0e40c82d1681c2c28414007440b4001c001c1c007024034000030f80035005e0016408210b400e03070101c003425080b81c5521500c842a004071540c0c4030780e4682005682080d40c8240c660405040104500340b900c0c1c59407200951514107444a54082030100e241015010360901030705400203030042010b603584100c02d0b91155071250807070207400c1c034207030035441201c5a0988500e0810301030b0215003a4440240444034408400c0c00460b0305e6544100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 731727176 1250 731725926 731725931
    0x51504080a032309030c2e030e0c12030f0702030a15140703020a020a080d0209060d0516111b0f120d18030b0103022403040309031b141003021903 64
    0xc00c821124421862040c005507510b05044c18109030000c4e480da441104110b00860300c0c440c4500c8401038a41241108109101c0da02002009010004000c0d101c891808002c510500c1d0000e00c0500304075042d03812070128280907605124042c00d02448651014409030384c03500c5640491000304e014554008101c107d030010001c2c0042080d0306c68520b41303800600b000c00749807040c0a0208016004150740c040251300c030341810340d161400034509000b80107405100d6003240010130480c4c8084035039803010f400b6006044001014090503401110340300c500d522842100d41000104502d0502c0403103001c1c01d01400240803060303400102001c01c607102d2030291110000d03407108421240301d076040210b0a01c01c0601c05103111100c0d0564941c0b1030b046c1c5040c0700c000e0155120b4400e41070070112441c0c62400d0002c05481943d07031781c142405d00600d090128082920040b0381103408801d00e0b265103d081c003c50310100e41000d00c0e030302107100f04590450150107202c1416020030007400083d0383d0040b031002c02245904d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 731728426 1250 731727176 731727197
    0x614090c0a06090b0a0804061503060209040e0a08040902070f020d200901050a0b0c01060b0406050c0c0103060e04030c110a0f0608100e0118021c02040303080907030c051504080a03 79
    0x10003945240ca030b40000c0603c030ba00107040c402030f0280400ca644411450a03d00c0e03c03a1502d10b1301c070000705200e900307080140c40314140c003004004180d0010044c0c2e14040f2014010381c03400c4d02440761200302041d801061140100002c00140c00943c018102a81c020107200c60241c03019000f1a110001c461740c110392000c40001c00c421082d001c0300c541d035003005054036244900d41c113000c080743c02242140900d070340c08480850881d402c0d180035004000030702109030141782c85940d81d0070046c10582080c05400c3c0780c0d0140c440114507035480fa00c285400c45500013109202074175652401c0c0c40751640751205035040c220b46240c9c2e410b82d4541a00480091001e0990020040d2412400802103c009130500541030a6444200a480018901d25040d40c0140012020602c6545c0c4180001d100d5905660f48c1d801c0c0045c60b4030b40c1d03886558060000c81e0b02a40313540c0a00d0351045c0260391a6001408002c00f00e200411041c015800d007454000743c02c0c001040524a0180c030f500045181802c4114120005185e003040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 731729676 1250 731728426 731728429
    0x6200903010f0911040902040e0a05030403030906051305040216060603050f0f1f0b0a0e07030b0f0d02090406050618090105090c101e050d140603011109011b0614090c 73
    0x80d00407402c04440200310288075540c0b030300c41d800c0c0440d000a00c81e540310444601550340380c2e800940810303049422a180e61f0345925080c1d803260002d20064000c070310400400189240240c04441c407003043e07406501081c5040c0000c0200035044064440d40c40350781c80d8007050028a16102d04400b450040004099035022981401d01d4070348141101e040b9908402c1e5602623144020380380b2440c240d800c0e8070115145660001080c644d81080c1d11001d0001e51070700c00e0020721505544000103a0350296002000c40b1680410701124070b51070f24000703402c43c161400040201d00700390f2049400c203100810007094013070b05081644405405440b031079003995507801400900102001849100b0304152010f05440f5010746000d000c8081c00941d003804812060301c6018040d102c3c1c1d007118440e48140808020100703a20010030031003001160100d0080d0700e0095106003a07000300341901d03d00381059484480c64840040401d441884124040319200c1e100c4075001111074141e10304d00d20402c03585000b410713440170500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 731730926 1250 731729676 731729681
    0xe030309010603060f09080702150f03070807081003120e01051b0102041d13060b0f0607030c03020f01020c0d0c02040609050c0d060b091509010e090c070201020111040806070c0620090301 82
    0x201d076004484d282c1b1000c8000250088261100d868040300c0140c00b00c01d440030303541094411510035104100c0d00000704044a41c0200d001802801035a5540c40b040e590605481000d500b0b0f40405080c9458030021192100c0c400c01c5204401b80040c50070300e0800a5800604240c0c1c40082c0e03401900f070b5004a004d211111550a0901913010000c484400a090a040380d180c4c070440100050700b0140c45e00d030303030030346a8a40450031560110090000c1d603542e40c890034024030980032040d00b18014010840d4031103540300c0500a0b142030300c0c1c11030054852010058016030701d04441580803604140c840500150b120f05034801c0138170501061110b00e55030040ca4059604662039900041400b0800f801031081c0361700c410f000c441c158295508056540d16022005840c1c02002407482175020000380100020401102c0151801078800c1c2c00070700c81000500b6000b08180143c2c0624041544820001804548035103441c041c158010107001030082014818001e140d0110f5008401900c0c0020f4903025500302407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 731732176 1250 731730926 731730941
    0x15140c040b04060c0305070f0605060306160503060d05070b03090c091b070b13020a0b0a030f09050606150c01050708040c05010512190e0307320a03120e03030901060306 74
    0x8224240341604000e00030007603010324000d10080004808101e8200340c056400c4400107074000003580c81c4e0890318034101000d0141101c40d0b900a01071031011404441080c001020b2404560702c070f140c11070740d82000f0300c42c0c07008644d83d00351124400e00600044802400340110b004526480240002040e02810b0089005010b4443c041c445407070302c6c4041103070070070780c054603c8150701c10203030f851a0701e540d28240355941c22141c010b944104006000624011080d005201d43c80c5207480078030242c2c1805001c0012540d0034030014090340c0100b17002074030500e41241c3e1300c00c00c00d0101480e01d0806100540060071210300f1207085020610001c248024006400d094900034502440c01c586000c01c90b601c5032894100c040d000081107003c4043e003c40c0605503070803141080e00a041103130384070484d03400d040d8151071443c40341d011111480c4e003600742c2ea184d907c100050708800c600c0050010f8a00c555045030065103072080c08100c50340e40d94a003416080c05100135402105184000301d02c003401d5041080807201178 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 731733426 1250 731732176 731732191
    0x3010b030d0212030a1d0c01020115030209010306020304060e0d1133250314090307030503040f020f10020c01021c020703030318080412053007020d1514 67
    0xa00755003080782e400125010070b90030020446851340c6510007801c02800e0813519180310280d02003101c0c28000400a10410100c800743d009005158601070050480a07440c000070b034001700500700510201d030640c1c00a6400c80d00c40c00e4002220074003c0c903540d0034141e504100d8030002c0c00c8080c01641c1c11008020640c02e00a0402c00f03030070301140d586d0000c03c0030340001c00c40c072040d042c0c4800001d046100380020328085c1c031804003181c50142c44408000380140511300c00e81c070003e6500408622540740c004203455038103a00d034441606c1c50311070741c41d501c004815154040740d1105a940303030a43c0301d8568485401001c08560010300040c1d031001300290416036100170305010341c00c401501c1c6269070303800114841104c2c0c02d4207001510b01e00c0841642c1d0755000c0e40401800c007010020f0005815414000ca092400d80100281c40c0841815040801201303809281d181036502c2204a08404002660007404002c0c40142880c0c552103841d9614a2120701004020b00d03059035078201c03444444070000031a584203c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 731734676 1250 731733426 731733433
    0x23070204182406081204050d1704090e061015081005060a080105100c050601050f0117070f09080303070503191404060515090c03040b040302070e0c04050f09060d061e090c0503010b03 80
    0x48101200b0580100e07c03d60784610b624a1131042844042d01c411000940502c1c8007603520b5480340d10f5100584244018140c80c3c0c480c51000445500e01c0081c0c00043d90101259001c0501042ca0122440d80001e460500440f444880000c0c03a80c3e5210001c0042c800c103a1288016903260a04103c6003c104007005410310040406071740010350042406410740c0c42c202c03486241c1c1790703101c40101d0340209c014003400306404424040c0302d942c98114204128a0340203581d4a030072942c030b500040c1e8a0b8001900c000d4082901800072410000600e0611100000307001800110080080c4000810310007d4a082d070b919650b0324103100104c198210007000e00042591441a2800d121308000e070070307100c01000602810001c1c8003060405200744039003001440e81700c04100f240e0421591811150f4410b03c10144205010913803c6040d0030940c04081c4504401403207078a04501da922440d000d480600552400c0e00008080300c42008206d00c0765000c0c0501039a184c417103803030070881810300f1101c1d000500c038425030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 731735926 1250 731734676 731734693
    0x11814010e0103050f061c0501060807051005180d020f06030a0c030e0a020604050907030905060f070f1d1005040b070f1403030405190501060f152307020418240608 72
    0x251084c1707140d500700b542912070090324081c000c01501c2418200304c00070304035402e2050000d8045400900c1a098482c04c9600d2000a01400d0b070507038503403082c0d0700f806040304042040c9002a03d4045c3c6405503050000d04003007c0d45076100d0008045a10454102c0384a80d5500900c601a6506104d00070880703e0800c02012403039080d40014180b80a0762180521500c00c5600040d0300c44c1c400d800415495602008542150a19440f00303400c08800f2140a1b0000d035840ba46402d002c0c0c0b08800072003100784081c5144580107001401d02448000485090081c00000c00001420004a50040c03200783e000310520b101c9840b40e4500042c005001d1a890313082070740280280070210380040340842901414040c21000001c01e80740283c0540343d90b5114844850340d8400014070000b40440703400118074541c0d2503a441c4540403000c02c14111540709107001e110400d004900c01070a09a0007041d000300003030107019004106940d582c0d80c00707014804130001d140507000510404000c03409005c0c09802a98050921074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 731737176 1250 731735926 731735941
    0x9091d011a0a05090a0605060301170d020a0c030b130506010b0417010614010c06061206140609070e061b0a050c010f030c08061e0405090624130209011814010e010305 73
    0x1001c02e01543e8400c41c404c0c2c021440f01c0079542d10100c0145005040d0907140c0d81d50b00e0048401780c0003815070b0b40c0f040c0960020b0b4500c8620100e121008075500c1041c0e11406820f40d1101110500003c1180341c4220f07590580d403000c51f0b0b08101d01c50003051204035099a842c1001d081c0106181c10141d401140c0c1e05240f0140100543d110010b2401c010a1a05331241d4400d0309101c00034140366803041c120381078401d0320a0306100d410340120b00780c0c1c1e441203001d113a207845103824012419003c40c0c000c1d00003001e1200700103840c81e100c0020000119030380c0e1070601c03003c49010424101041e5110485040d44201c03004a11960080000724200c03583e8141005180d040c00009400f0801c0280802d02c207094600c0c034040341d088803c4141000140c0944200200d107040804d90365905000d80e00084070680c0710152b20b10100301040d9038603e155000d0300440c001c00d00d000840c0c01a402040d001414401c610500e450300b6500360001e5801804508030308007010140c14005060f140f4003420540c1014181070400c0b00c0c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 731738426 1250 731737176 731737189
    0x1715090f070b0f12130f0f03080c19112509061a07230a060b040f0e0a081305030a050d080106030c1d031204140307050609091609091d011a 61
    0x150b40141d10154083d85c41c031a202e0164081c1103001025140500460000e0000c0030b00002e20241c4640c60b07015503a221403201c0012030041c4003511541408890004005603c40e000504442c0170140032034001d0340062400503220f000200d03134002c1d100aa160300300401403450140100070880c2c05050307501030305c400c50710901503c40e0341c801030411031020181808500341c006402e40130b90052400d5401000031440e104010f0240100340c00d109031300b0300040f1000420648640d42e00402a01d004105d10302c61030752401d46a4120308525071420680010015041e1020b01502075800d2281c0007520402c4991100a0880d50040e00603c0403d032400c280c00840700d0308081028031000c084007102590185903c006481c0900003c1b14400c0000c3c0480d00240402a003102060b40c0d1030110140d907001c0d42c480060062600502c60496803042180c00440c0c42e45210110302994401d9924025914517120b101c600c0c1992000590700030403d05a00e0f204600c40303028403030404a0600107201249000845002455 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 731739676 1250 731738426 731738437
    0x9020c1b0f0a030b19020d1509050c07030309060b0301063015150b04060e0310110301181b0509040c09180c05091306061205010b041715090f070b0f 65
    0x620b0713419030007040d000b100c028034030300c54400089020b6503200c0036140302c080a45070041c0300c0c01007044103070000314414015018a9101c2c05d181140c50742891581d0700c0c210b01404859109461155440e01000c040e41c40c01c1c011400544021143e12074960100f004950022810300541105405c10419600000d03603035807440c00080140c1031004c204140c105183d1400b00c510343c0d201c400314050015001840340e8000301140d501c202c0c100d0548041301c220808803c159040e03030f0440d4004900400051204400820b03035881594007442c40000c848210032801c0c8030a400c0e82c0301c4000816004212040b180c645802046505030f40b0385081030303a1901d440010511940c40d0020f072807107281c5800078068003c0c82601503e0914030000c20307900c9041d0794500c20100401b00f40c042e000024586501803c5120090f0080d01d04071201d60307500300e140c503280086801201916071044000c2c0d004850b99040d103415030494042c005c0324988090030007004503403885882c0400c41d074410407120300140502e140c8521001c040d00e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 731740926 1250 731739676 731739683
    0xe010908010c1e1106150307090608030904090804080a0f140a11090703091a0103141605040b010e04020d0e0105011a1206060c0601030605310303090c09020c1b0f0a03 73
    0x618202c841544e00c168840c5880000c1d115540400c004910003019100200a082d41942d444070340f51030318603054600c0b60080d00b450b03030b108009032800c5040c25801171318814000d140d01c5003486d464280c41e50031f01a0010054502e085094510f6050100c2c448010848001c0b00340145003101e4142e841400f042d546c144010300c188000740001e40a240030b07801c50259158020301400c44152420742d03000c0d0f1504280810b4035085d200d10742d4520a02c0000554504000b80381f08405141c40c6030400300310281100501075410488140000701c1c0c0d0342c9481c006400010000303e00802d11507951169682115030591101041c0c1e00285801041c04001768202c40d0305800030723030103050155501e03000b161180c41840e10744852071041780300000a004159102900400c0404085070304100010000041c0c000b070340c0c80084a440b030030100400001d0080e400b90820f035100340007020f440d41e55561b5003412600301703405c0d01c22240c2110403881c1810510402000d00c15000f158803401e6001e800d00800d000d8425404004e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 731742176 1250 731740926 731740967
    0x80d0f0e040e0f030708030f06030706120c021005090d0e0105090109050409061d060403030b010503010302010914040906110a030605041119020307062901030e0d1206030b070e010908010c 82
    0x321002d2a06209000345843c0c03110480b5540c40d1035103410f1740f041c1d2085030302150509250012802c43e01d40802d10800700e49030390743c0b40f00d0340d00000d0000c00000c108511600040d4410002410344021a90140d94800ca0100003e840d05080203480940349070307501c00c40c0504200c0100b007802050380e00010007200b980d60a45d0001250a89880c0920041144100c08890341083d4180e0008144000076503e111700d00c01e40d13041c0282c500f4480151001d0200313000c004d01248880506000c2d480d01d40c1d210b0b031200c080041003c1b400700c042d511781d0400c88a00c5d140d00c0c119034600040503101c0942502130f003002844c0c151010042c4040c411034540140c02804a401c1030301e03010040c1000c00754820820345001c3c5170040410402c0100c48038940381c4114410458120346060401900035540c000d100d54030003002130101070320204510401c00c0301da04449440d061299a540e90001c80400c1000c001188251081c3d102c40c00061108070014042c40707101d901000ca00e80c104420b603148140e011000e9004608842c108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 731743426 1250 731742176 731742191
    0x603071a1e03180c030616031407030e0d020a050d05070215130509060d05061b041208130f060c080904090b0f04060b0109050a050f0d05100501080d0f0e04 68
    0xc1910407080340404181c4018101040300302454002c5004103500320749819a189800e11003602c0340e030300021059154200500003030380c002c50550b1010711403089240c0020903252440d0b070fa0038940c1381a18880d00083d503410000e1085007040200c108180e01c1c0c0c2c00102001d07030950352041d0b9520b42d4074041008000000c02c0c410210b480b91240c19451501500d0784545442d20a0079884405040340309162180345000045401070600c100e65030180c0740c200300605113950b946c440e8102003400501d009203154004010024188095500310505248508003050703960a00901c0c0030800d8280380c000c80c1101c2a0803030308003c1c140d0841d079035400c02a4081c58440d107038100c01000070004c1000d020050081d94181c0308000c40e001001045a00c524030070340c0b0800480303a40340011254840301d8042e17079402010710032041c4264170300300403440305a980c0202401c00300c6942c0da035124107050701c1c0001e0307168494541c00103020400c1e007400000c1c410603003454280410b404a040041002c6164900d041c0103c0e07030b5929 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 731744676 1250 731743426 731743469
    0x120608030d0c09120f0606120b15011b0303020d060b0906040608100f030b0a0c11070e04210206040314072406030537030e01050f0c011a18060307 64
    0x40f1400030034640d50800e149015906020100c5008010f084510364541803022480101c500507007104580c0001000e411681c43c250050300d04d204030449a810f10482c440202c0c04100c6024941c5040391290740e000da100c0f401540054103444007034000c010503403000c0c4640a801d49444040d1000c4809500d851511504c0d111901e04540606030003681c03d1000c2c08501105100380c4282407400741ca00d5490030480c48880070380846410f510704603044600d0b0803544d0200a19114400700320303000740c0500a202145030b240c40258099112010070540540c00002c100000d16400c01094400005200d41042c90880075035a003000700715141c0110908140e000314a0308003800298049009581d02404840070346030191484650400f2484400001621402c0d519006007a10081d4510896160b02d4115900c0c0ea05001940c141d00701001c02c0306040c1003400b420b80016024007500c4000d45100400000c1c075403201081c0504000d0380c08010794100990410300c103544d00d0020711181224621805002005440030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 731745926 1250 731744676 731744687
    0x12080f0a0e1801080f0105160c1707051f230702210904061d040f080c01110a030f1404030f0221041d0906040f0807150c120608030d0c 59
    0x10856000003440c0c0740003480101c8040b0040c107943c4404111448010100b421a007641c4084910000ca01d540000c0080c0041c040e10040403400d11034010034014440180540100382c114050503140d0354030401000103c0604c0804100e100b0006d880c081c042c441441c0940058001c24200c0b10b64103021002c00030300d040d4400e1003a44105500c0e00415482d6a01d00d40c104c01d1310341c00c030010141c440e914003007001440c0720480d0b029104001c0d80906290b51541d5589030619296400d49041e104024100103514100d0400c1c0b0030b84a00c2d10709914100d032504002d0000130200d400c10044450041d00d44241c000092440c0c031030081d0320551500c1e01143c010b401301c00880c101208e42e1002080a42d0004404c1c0c00240040058030941c1c405916220f21400c96000380c5001e020103450f801242d400210100d00071030a4910302204060040161030f14080e16695196501600e03881d4940200c0e41d503004c0c00c0301143d07001c40c0f0181034500c1a281400031b00d003003049040d240d102c2e400214108507130381d0440f24000383c040d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 731747176 1250 731745926 731745947
    0x30815040f0f050915012312280b0a0e0703150203040318030f0204051b0a0c14060103120e0d0212010203040b060a0506040611010605041d0d05120412090503032212080f0a 75
    0xa007001d0a03490300c1240c069a105100a10498110158204510700c3c40d4588100300b1890713044002b201964590304070000007000c0130741190403680120000400811700c64030300e0b21580a0f01d6040160b803440e1604004100400c44010b00d291614104410004942c512090322a0181c0454000901d504c03030323080d100c3c8546459003201710102c0300482c02c82c83c1550400c030200e020750300512643c0310392142203c000c0d031107a1090100501d8007040d400b8203c00343d07110300340c0d0441c81040909002c42e20105900050f6035900b0320001c0b041240e4001080004010008400f690040c90507100403808604003800100540518040d68080ac4070491a072400f109003504840001c041c00350007005140ea00340110170610b25035150001c003d10801c10407460640c8124120b8a41c0503c00c00460101d0300d827030b41c6411403040030000b44401c000303803100302140d20b980c140024005403038020884904140c1200d20b082401c0141e9100d161180c613011941d0000c10400d204940d03814040c0780c1030075500c00b048034041d40c103003400703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 731748426 1250 731747176 731747179
    0xa05040501090605131b1b150f0b0f030c010e01030b0d08120f04030903171e03100501050405131107050a0f0201030f18030815040f0f0509150123 64
    0x206000010b03108055848002601d02c10380e2400044691100c500301500c11200080c11056030b940e1000003c14400c910010848808042c41045610540c071198400314404071944c0c112a500d10380400e503503200c0c1c405d034880ca900554000b05031241d4000020b844030b040c4880181489007030505100300781c0c441da0010049107001040b00c8081507190600080341c0d00600d410051f002c403008003041111401e070044501c0b40c0e60654038080258110354a902c020038108640204040040c840c602030246c020b00303c0201c441d58031060503220316010061900780355895124506000c4100001d014640b184414040c61348c00600000c03c04581e82d604144952140e03001c00b40c4540034207041d81040120000141c02501e000340c0c1e05100d0000d8074510003086900383d141c0c8618064840040b0130000740a501003550000c00441c112610707001c080c0208003510300d005404a03c00b42d884508440c0340007c1d00c11140c004094000a1020458042d002e2485c0281805840c40c0d807020541c11004441c1120a8203040540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 731749676 1250 731748426 731748431
    0x60e01140d0b04050709120204090602070b04050a050706090b0405090709030503070302060f0c090f0411130f03060509010b01020a061a100819020c0c040b15030f190207021e0a0504 79
    0x1000d020100401002c000a40b080b404c00c004208220300c20700441c4155001c09404440d00b00082e400c1200403d01c501048400903000e001c040c000c1022440034602c00c0c1d0103100505201000ea00d040c0b41020190340010040c408000b4040c41020450000e03241520001d88a000c1940c40d01c031000d0b20030500652008055100c0040d52a08041c1e010404500600d451400c00070f494496622107c0c5034010f0001158101e00380302c010816074075258010702d0b140e04889440758541080840349105a0100742c01008141004407410410809a48030781c079482204d200007000340d8410080002d480da10001d80c00740c1050b0f291541c0e84a003580c0b001c0c455081c0c05000b0400c842040c1a40c1000d0040041102c0418007280b034403d030342180060034005c0703c0c0c0c03244c4054043c2000d1a60782041100034410315480075000000c6040709409001740e440118014a140074400c04980f90854610200300110451503440f140140651001038440c02e00320420303a0211044550400901000304070800c5c2c0990100c0d42c45030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 731750926 1250 731749676 731749687
    0x318031603060b12030a180501030c05092707030b1810030803040510022b2f04080703051e19021201020d06031425030b040201020a14010605100e0109060e0114 70
    0x81d04202508200c209180b419a00c2e140d540300154101c07403130bc046690108000704000222031500003a0b002c540142e080a1183d27491400f0010079007004101d0b502400b1aa50b502c00460385d2502000e02400a01c0c0101c103003c0602d005210100c030300e0b0862000078080140440441c08014045c00004d080d220701a00031525400780074a04c2c043ca0244000d1100c03080300b80400c020100c0480c0c011070149a403a0840c1489400711540f0450684203640a2600280b400340b2000c2031441052103980021801140103000e40e50a59150116903924a4482d40290b40841c50807505d080c40e20b001c42050b150110341d00320310041200c80c1140079116005081070317943d2814001004214201100b060f08490b01e000700c80303444044d2003c244c0401c4030310b140c00b0f01c001e0701d21208200140103240c0d0300d5400344c410f10588601c2c10040e0b032004102998084d410203565182d4409100301d051181e41e1402800e0245400c403c0d00344014000f80640782d023405082d0030480c0541010f131469004418911030320b92108174140d50358 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 731752176 1250 731750926 731750947
    0x3070b04050a0b0601110c0f0301060806151503010e0c03060d050f0a03140a0509130e0706030905120304150c0e190e09030301050a0e0915090318031603060b1203 71
    0x4009000084981c02c0126000c44c660394841c52030020224021801800d121441104120500c591007010326459901c030980410054014003003e0700031100c1ea007010800e20083c1c400c01c0308c03401114400c82000c85060004006860411401540040224500503544d44402c0e02107040c0c0c2d4120540580284602c0a984071b01510014a00350f04500981e9900e008100c03805900040d4814440c001001840c10700402010b45081f0a14020a5107026000508038006070002030a010f020351040d004030750f60300001010306c401485495052108104407500c0c51901c0c4d515091050000a0030032605592030380307500100390044044011442000f0854590601450381552042c0110f01070200d0204081011900f41c02000003a01d050700d60090400003901e043c00c1401d40320700c40003025180c103441075900c00a9890450010396004905c0340e4050b6a85001040040c1c140000b117280050099101a0941d69a22000309035a01507030340c4100c002c591401c441001455941e080c00301034041c3d0100084101c0107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 731753426 1250 731752176 731752183
    0xd050403120219020610050d0b0a0e011d07060c15150f09020702120606010206070c0302031e0a18030308060607020406051302070b07080f01090f0f111e0304121103070b0405 76
    0x340c2d684d82250140da9501e008160400d0319441101c0d08141d1a14164001820303090782164441074003100003602c03203074030461582900e25030b0030320742452011000752505841d02484084007070500c600300030b100d02c086551240078903a60003070003444e034660b1092881c1ca400020388000c0001d002c1480c0c2c0a0384191601c0b00b180081d40b141d0740c101e104111030403080e20b403500c021510034828201600905075507980e0b050196860a002c000407001c41c081006003109640c8140c01c0704800701c25484406480340101580600300c070020f4007004c201d060749483c007000020f1b84011070a500c0601a101252100782a00c01f04000d060349803c84c3d40d002c40388448045103d0340c02ea001c0c10130b40d40240c290303021a443d410800d035080d28040d6a001c079140c501c01c006000c150a2034000d107540d1401c82c1000644600c02d41c0e511811103d8005490483c2d120000c2c41000c0300355920084031102c484c00740310501e14280755a60340c488800403184c500034001c15241034920440c052095905464100000c8089440c041c50420384 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 731754676 1250 731753426 731753467
    0x807020d1b0f061104092f030402010c050706080105040501091b030e0c0a0e0a0b09011d130f050a0605010b210903040b130f090b011715040e010b10030b01050d0504031202 75
    0x8040d2600c421190400003000f9640d801c4c032120309102180b00410300c40b1f003066034001801603040c0001e2416981c00164104440741c000d29040e5246912541800c0030031041c0d51040e03100a204608103800364044040300800c50558001c5800c0006043e00f05c0555517060400200030715600000103180050032030b000607a814440c05992004124007041c00b010007070700c40030a014044018001c50030040d01c03600c00140460b00141c80001c078016440d02540c0780580442e038000110f03481c3e00849045800c110b50b50003040e000d000c4c10034000e400c05214511100300d2814201d2540800010800410151701c0b040c001c45000d0070120445d0b507521101d0f0603203e040302e5840d125150544820107030000e0b40c02c80b5442201d1500805a44a908114207010300c060f600602500581c40c0429048a0b004150380b2403148201c01c030401000401c0440c4590304100005003011402c009141c02c0c409211000d070f1f8444200e458104510000107401e858608049a149444118124496100040d10b881c001d09901c0b40c0c3e01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 731755926 1250 731754676 731754689
    0x210d0f18062a0b070315030609060207020f030127170a09060e030c013203070207091b02250b070f12090b0a0e060f0d0c0807020d1b0f061104 62
    0x14076440d12484025a4002080d4068620454000801c1491744203412100c02c209030440c028022544a841b03d0085400e90a4111002c1d80c0c0002d00d8000c508040a002c040c00c01c1c200c0c001c0106010500040d00c4a422907480c0852202d06d884ca45001c10500f44240c007181400441500d460341c04024003d01400480c0c000d14020411201104c4020700d00000c40030850b9006a40b40800c2048008483d40144040e0010709080038044d920100d00e5032000001c3c1d07114200d00c0e0b004080f89840c0078140d4049454841220207925022022240c0c4d103134001400403c4924407025940c84849480052400c1c808980c02100c03440c14000385110610849182c40a01c841c01510386000341368111b041580d440d0050305c0744045507034082c80241c11660103280400c101d00806400703540340a2100315144010341c0000d149c61106036a61b40c00d4996650704c8011980c1c0300c0221700007001250311218001c1c0c44403c000310340d5883c55600060400400080715000a5002d9009109011070300340e8900d081d116170828003520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 731757176 1250 731755926 731755967
    0x5042d0b1603120e0607080604140405030a0c02031204030b1506162604090905240a1e020a0215091f0203060103020c030d0902210d0f1806 61
    0x425409101022640190108502140c0301c0c0c01c240e50580d03501820107010343d401d95403603458580740034003800413505c82c00c03403503070750ba0700600c2c2000810040310310f0b4038080e202481c0c82104201c0002d40000440d0072640007410b10000c072500c1403000a00d002214000c42002c004003040000801162000030b034003c400034400c4030000803906040c0080790140d410350386c14003800302c00d00304081240341c40100503030500c030714034800d907180040112900c80c0e101d9841b47c184d5603524003000c0b080c01410710448040100800600403c03610000d0429099800607040c0b20085941d81030070b50490301102e006803002000031a05640300d04013140040d4580503e03008141c13441c852140081c440c064081960145800300d503101d084818001741001d4029080100101d06141d03007003244407640d10040000e00072500c903d81010400d05171502c10702c40d200c80101600d0150700d5000c410704003801e00204003000b100c03410349031580f01990b5001c0300302e5205030110f40304801c8008032000826070a9002941403401d402c40d0010303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 731758426 1250 731757176 731757179
    0xc051504050f1b210d12022203170a05030a05091018061b020304030803150a0f08160b070204020d09060e010e1606020705010f12020a0806091501050f090105042d 71
    0x413082100b411a40c0203000c0c1d00150b004c0c550141c0115444444d04c000440010b017031a07000c40c4000a11807009042c40120601c000c0f0800030080640d03903e1a0f0311130a449010b0410100c1c99010300503000141c251a10303162a60300041810004100107103e074503400d4014050500c0c1001030a10010f11090f0594005041c04525240148a00349540080400f60700840c5806d1070b40e10303141038540003c2d004084045c803607542d464140d660102400301608a0303040c1c84084518001450380b03000403c107890401755800f0360080101104c0c1c036050302d030303099010748002d40c5c1c900c18121120018180c016000700450b24080c424a23018505501540d01210b00750102ea03034412242840d500c00b081a481140b00603800340100b131000d940320380c03011020000c0c06e0805070450010082e1060030785c1c003d00e21072400076060900300481450314040058000000c8400c5041c0103091600080c00c61045502e0310303a184000242c0000d00fa4841c81c11203000381001040b110030200920b184144501c0b02e50450166001851030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 731759676 1250 731758426 731758459
    0x90f04020108060409050f07060f020601080a02010e1003020d0f020307090816030314280914090a150f08060103300e0a0b0a120c0c051504050f1b 64
    0x40150145030141c4503504980e46100802000e0860640211464040c901042d0070741c400400c00040a80140c4c1c0325079292000810b002450039405074098941c583c4002114009030360081c0a01c0e02d07640d4103885640c00240c80c40000d601078401c185942e40350701c6c90030341d08180e03444059000e140903007020394401007071950316001c250340c50f000c071050b1070140310608204100007030040e0454100030007641002c5d070500107850840c03100105105008044010003c800001e05540f0649101c0500402c103103c140307207800c409c08038040500042c0103202040d91030460410946100d01e0300c500500030352504400941d261000c01d610741c81e0a11080702c51541409c7c220700300f038002d012590849180124403c8401a0001c400c8481d00100314400d9002400b010000c103065020310700401a010040d00c07441c0311190740c415100b00702d41420b10203c04229040b00002e0001d0301c041400118180d10715400030203a05d9034202107041070b034010000e002c14030600c0c426191025043c0f004030b61486085803034440000c6d4500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 731760926 1250 731759676 731759701
    0x31707090e01170f030c07050a1d07030f0e07240503090d0c1a01030b04020a08161202060d063003090e04060603140a0c0f0e180a06090b040209 63
    0x24150566104100500010508160420500c0a880c040340c2d130200c0181000c50031039000010341c005640080c98180514140040e0a80041204002c0f8440c00030ba9011080400d40001d40307400d0400da21805140b5515070b81c0d400c8a4600c0030850705032480345035207000401c40b100100108100010082502c41403403070149050381d10a248201c0a00300580030400c0840d12001140c0c822946805103110a0221040100b002406544600345510840c1020b004200d80600d0380d500c81940c0d540b05203400d10103052a10b0128003100c14540d016403902203030b0300c0029068000c0d01c0b4410911450280c00180f00019500100b520400c0401d003220b403408690700541101e04409805004a071459070100180c4014102840c1d200c1d000380030004070541c0300d5039803c2d2040c03150003404800764404500a000c3c445211001c00041c200307004e050341943c1c584150817208110007422040b41c210001001c0d419640103002d04c4a610764081820002000a860040c035801c50030768041e4050084080000c08480600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 731762176 1250 731760926 731760929
    0x10030b060a0c170901092714090f06061e010c02040f06170d08040206030601110a060209010f050313020d080c06090703060b0405090c120c150a020105070f0c03030f060e0403170709 79
    0x1031b51600c071007e042c06c1e007444407030b940c2c40700542c0481c010101030111580300784151620070a9610401d02c242c10414402d510f01490710000103016080711052009554818001101c01ca0141c0b02c44407600040800607264510180000b0750040e0034028441c1c1440c40640c800c205980280982a0b20300350074103000c0340d6071107110200c2e001054841011a000d0320f0000c0246602a80514108207103c91100ca440d0400c0c1e49484100d44154011503003500943e006074038002640014944a03056240c0381c520b05003540c481400190213103c8040d0310340240860344c1c0403940c006042c2403c6036a20304100e29841e80d198100e00c005c1e05c640d031a080c031000491030a40540b41c080c0c1075940041070300c0c2c25610100442041909060201c0344184800307000c0c03036291401d20a00030100e05c0c42d20303030321408500d801a00351031000303010208100100000380665030700300d415100401d405150000350503d020322040300625241c0c0208032981d11081c108810590301c8400700c1000d10740518840143c0d00d0300d00d815034895106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 731763426 1250 731762176 731762179
    0x140c0312030c070b13051501052409060d0b1c03140f2215090302090906010503120f2710022e091a0a0605010e0f10030b060a0c1709 58
    0x1c004110108800c41c144071713002060420402c0c81c10060f0364483d46440542d402e40e40b4a0404800104030a251003440081c1c000100c2d07014407407800007120016010701c1901e59003445807001003684001000c04e60b2001c0184880071341221681c01c420180d220140103c071070304070002540124586401038850b0300350f03540c007211038400c1410244500b00101000b00030b140c0519201003560390001d4164142d902c24805614282c07500038500e802d60060100d00400141000c13000d6001400400c10303520001071303a0101c2e4010b050600c2c0c0341c01506060b0710481c8522010f09014100e820102400b440801418440151045031908503075504290282e0300d41862a601420017004503600802c2400003801d014030f0a80341180000725160242c0d05c0c0c0c0643c09030032102643e240894010070403044054440c00000c0c240074204000501e020700b00041651074a0403485003c0d28044402008044c000e0300200d8800394000c11940d1030b0310141c940104070a1f008201a14106101e945444030012200e0072200724440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 731764676 1250 731763426 731763451
    0xb0c060406050c0901080a38030606030d0f1202040302040203010303090e0703060e011e0b030c04050a0801020c120c01180302030c0c04050c0301030b04031e021b0301051e1003140c031203 82
    0x7d664241d007004052142060310300381c0e03130020015001628000c2140348400c500e6902c405140540d81810f14000c8010002c50090f444507a100300b0f140d03003020031020010120314101d40c50030880c4179070704003038000c60f40300941050000c00044101034000801a05481d010019800306640d00403084080c0d8805d442414803019001c401031006e11000d070001e0043e01078290b04c1030f40b0b440c2ea03400b4603d50b45e070040752284032660000c2802c0c000c2c0d2522000c818001c00742c0c2802541003221300c80720107482e101070308010a5403410024011400038006e4014030f14503102d03402102703c0b018103418044e44980c0080d0302c048044c010610680c00c14505441500d004a14114042d07045030700710fa45080ba8041d000d40309400388586c00b000107090005040012042107480d901800e1800d8100b032002201106051210384680d041900300034a8802e2070b045480c11010458103000103481f40c0481403c600480d41010f0010749401484007044200050b1143d0000d209504075450f11649030080e407414001070b10b0303c2c1407045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 731765926 1250 731764676 731764681
    0x27331707051611012a0201110d050901032307020d0e06040303020616020102070b010803040513020a12110903030414030f191101020705130905100605010c08130b0c060406050c090108 80
    0x10070340100c0c103d1421040c100701c40c000c0ca642c1000213030007611202d801030b00441c2130071000440d644241c044422400e1440248811000c11074090018040d0700c007900c3c1099600d9200d15410342828040b004400d02c0c008842842c2c0c24000b90003912030201c3c410304804510500040401d40c18850301310740823260154003030302032901c40005240100d11004038102c2159000e0104201140c4007441c56402010164019a5074914060030b100b0500c5000e040501305074810b000011000e60080b101d0026180181400900d80d005203000600354042c0650094040c40081004102200301107100940c40d40d003141255156000d48180a0340c690203030300c0850852140d40c004100050144100e00001c00050060f12a1a034a51300032403e18800c5858442e8900c1e15180301c4c10501000303001c1c00e06540441c0000740715407420200041d008a560081c0108000400160001c40e0b80b880031240c0098160213210903640d80d00c040c0380564900c1e080d2019206140b5040218003a0000c031404c8515904041e110110a603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 731767176 1250 731765926 731765933
    0x5010207090518030a0903110d020d03110708030d0b041802100c081e070b070309081c06090e0a0b09030325020a02091006273317070516 60
    0x42c080070b40810720320701e41008400030001d000e002600d080c2d500755a0300005c0d10b207142030081034919007064a0b806030122113034000140c1c803882907480380175405042001440c500c0702429464007680c0d90201c07150b80030200e803604400549412489c0b0290013100d00788203401d1100607d1201000005001354030808551a15030b80602410321380215900419805091000c0e00c00f0395080040c0d1080c0351030307100c0000505101007040289501d0f400c0507251a042128401d290b032403a28520560202010480d00246405d0070601c1503040700029015440050200c81008040166500104074048402c1c0550500140d4545030000c181e0b072044031071070138910a1200b06040070460b01c4054a0034811402004824070250302d4028985000d85114141c26100b64030703001d8014041154100502c01c440d0180440d0290412480310303013400d803000300ca110b00c400541c07003d4000c40310780400d052040303000c8003000810100d0307000794501205c0c0c91507202c00c8016954052040700c8030321800050003a010851003000c00031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 731768426 1250 731767176 731767181
    0x305011a03090d3f0e0c01020619090c03050616020f2a091302090a060b03040605070c050d080f15030d0c02131d010c020a020105040e0408130b0a030c090501020709 72
    0x3d074180c100038414190040c0310003104281e1001d02c503211000b4801540b501340c03101748100000911070101600c040040040000d40390381d0003802c108000d5040c0c0c03c0c5506107211650040f036082c0d070310000e2000300503aa80b800c07039100d000c1141c400d0003040214078029481400407618180f400300800191820b4006a07031410281c8815482c400f03001250007404c49100d85901800a00500c581b80c00640500343c617104028005c40d0092030724050b1403c0610400244c13035024103490700294403000104e2503950344441203444c03003500c1001502d24440d0407100c00d0556081800c0500455107600c8140d4180e4030746d0284004480b1040d11150544c0c09404200800c0d880341d440d40401364801000d1070001c001c0321001c070080c1c03031820000c0592580f401980030a41f00c401d2088a12030111800540804040c0da000607003d030140d845021082ca40701d40000d8100400181129082c1c41080c60242e60241c4900c0c87c0308540d00014032100100e40b0b8051007103481d42c000d03d11001202c070140e00034455581401c840801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 731769676 1250 731768426 731768447
    0xf010b0108100b2b200a0906031d03030106080f06010806010909020714030c03091207030c0509040809090f04060b0a051f090f0801020c06010f0f05011d09070305011a03090d 76
    0xc060030064403160138080d0005400a0161041002141d003002d0145c03c03248806240780648032020042120101880d04807001000300c910a09001981c80880c0c0f091840d81d8500d031130f4880640c00700000224181350400e48040c00b0f454040e5082036241c0e50100151000d0b9416200c90303020840380a0100031400c16900203101c03541c410000309280100c6000201d245801130b50511040e03400100700c1c0c010506006c3c9030700342e1482d9040c0081110625644a084070b030003060083d1800344043c13400050a010402040354034a0030050281107451a000181c03403201d8009850803078000d030034402c82261919010040a003a1403009100d02c40500d00d40d50b501c40b0041c015000c0c8014002d07600340c0000d00c0510414100010003101001594031050800001c2c10102c05030440c00040000402c2801900c0c0605480e02c00c1c0c40c428249400600c914044d00e050a07031029100e5584503040340c04000002e0740c0342c0c01060403600400c6400481c890580c0c509070171390100f225007203030640c07110300560101c070310400f404038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 731770926 1250 731769676 731769697
    0x3150f060f081b2b0b01030305040e0f09121e1c060605040b07020402090a0504020c0a03030e0f0a02240304120212040305030702090402060405040603050f010b0108100b 74
    0x18001100810150a0300e41036804182440364441040250740d01c18004812150b1100c41e6200154030703c50005650003a007002d202c900d8806085582c0c94030101400003011058003e40ca410b21582c2d2450000c115601601a805140c041c10002c20707d8250313000c00c900e00520303810700582685142d01d1942030264000a1501805104808490480e1341100000f41206e0303607072110b070009442c0f001a1a000341c070a0f9520681c02c11404020070465400050242c2d03050a504840c0581d980e40000000741c241e0f15542c200c0c0b035019100140e030303520a100c00560014410b12903201400708100010030304d6194a803600000c201a01700ba0702c140010301e0040118031030913440c21459201401826515420750f00202d80449455007229444118981c040040080d5030074905041ca1810f401e40e954603480340610352000740941245000301c0c04541c0c448040d01c3c06003d000c0e004001c1c0d00e07641e042c07107030b40c50b400b40301126003035480c2004a1034194414140c107441101c403209080c55440c601005104560301080c00300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 731772176 1250 731770926 731770931
    0x312040608040f0c1d0a0507180603051f061808010204060e0405060604030503070507031a070c0b060d02041107020f0a0302061b0309061206130615050d1404030c0309080102040308040315 82
    0x1150f42800014585501043d0b005c80c0d201600e011800fa104079840a4101400e020036246124150341803419480d040d80d029140205c0d060311010013a0080562003100b01d1780b4030105800c00f145140d80a003500301e51a241d4190054402c0d0b03a0303409031b4203d00c00d0703002c0c8100082c40020f1907400e60030141c0007036401c0000508200d1410356207131105030454020741021610750300034450401c28040040c1d40444100188682201d0504206002034030308131401d800203202c003140c400010030564403030411100d1700d0780241c41405980c0783e602140325190701c046012880b4606602d5600c01c2400c141c840d103420b403507010f05039529121015014107110103082103810070a103c10018142a629407102500d41c44221030f0400b00282408402c100802e0036545568101070b00d418000c20101503d4981c0c44c000d00b0450524550343c581215040c40603007510f4620100300d100e804180070416510107206c00310701d80a0350b80d664240352960000ca0a0740715600c00035051701d005000c248007180d0b0500505208400f0003100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 731773426 1250 731772176 731772179
    0x9330e0d0c0f080f09241603031b080703060b0705100b060d0207081c0203101e0509041401060803180f01050c0d09030204050a0212010b160c080303060312040608040f0c 74
    0x1d103843c0e0b60007008081e48a803400b0a0341c0c849401e00e002c03890b1001d2404e035132113060703000644a0103005000d584462010b01030100d89450615000f503100f44003401302203685407040c0e201c614000d0000c40d41a610040005d280000004046845006030742c0c0d5641d005018110580c04640f031200903003074103074105902079420056940c00c07003814030040490038420490039490380c1c1008807042218007140222245940100100b000350000c0310b40000c1511044c0d0011001013107003041c2044500940e401091300321106038140300034018010101d02d1946440d0000703008058858140d113031240980300078031801c0c1c050381c05c8003001441e1101101d40400300c180340c52030410300340c0641685022441d050200105182c50030a00c194205402095400f8811440c20351400050486200012a05105003001a100881c8000100d40c0d501140008681c000200c9400f0f143c89c0d580300390b180d80c001c0c1c440d18401d01c901d200ca50307080410901036408a900720b890b003841654071074a0741c41c0301182c0c0d2841202c1e6011600e90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 731774676 1250 731773426 731773433
    0x1b0b0613150305010902010315120f0303020f0a0305090c060a0215070216030f050c040b150c0a020303030f070f08040305160c03060608010c141213050109330e0d0c0f 73
    0x54040c0294000c800110340720782c5d81d0002404595065049001d42c8240f250280715801402e00071640855100c40785112400050800320002c0c000c80001040f4641d000800b900410750580103140681e404109a404504282c004c00003940b15400c022000b41e049102c011030400c041d0b198582d44140070b8010782d1212541a000003035a5545074000b2542e00145400400500c13004000f200051442640c042202c1c240f174100084030510000005550308000082e05200f010040c000760303400d00e902804581d241d0800d07441c0020802c0703088406a000a480090010042c1d00c241c180c14055605034072401c3c43c107a880542c80b40c212103102020b4403030901342680000040c141e44920401404000c000151814000071700401243c60800721000c95502070001c880e0031100404815005941418410724000e140d2600c01d0142030340100207000800f5103200c420781071011245a02c1002044d104140701c44020161160031a0580041906950b04c013250941d41c031806450610784042c09500c41c1c0460031031b65507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 731775926 1250 731774676 731774711
    0x606030f030c05010f09030e040c12050103111503060a031712071e050c060106030b120f01020403110301151a0c070906090b271e0f06011b0b0613 64
    0x81280002d00d0394600314144082071090141c01e0030b0108061050800c035031801040d4600c09814180314640e41c1ca04181c6160058144101821a5141c14031156a5a007040c4900304400e00703e45010b5900fa4540d07030200c002000031a886100d00401e01d028440c1551122641a803c200e0715000d1100200030360541b403400ba0540301d2144032281d8601829000300395402036480200c0d161030040c02418001030b111181e02240550645546180002d440005d00000855082245050110350b00403480e60044100c0103400900c2074034000c18002c000c40080409250032a05011402c0400302000354040c41800310f0f00c0c41c18801100342c20440b038206003000c540345040ca04558008141240e655008000c080c00600924107900300884980d00e4410340c06260300c0702107000e003d03e020000109030007e101000c010340c80d11840c0c0c040d10980e000d5071400b01e1041665030402c0d26094041290000510643c44907040c0f44100b44d0b512070380910716616503206000702c4881c1d03807454000c1942c07510072030241c00030140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 731777176 1250 731775926 731775953
    0xb130c03061a0315100f050a0b09030a080714010b090c07030e010e0a080c15030408040605210411090105060307020a1709030d09060314010e06010509040e030f090301050112031704060603 82
    0x94910400e60905c00c407808490150390b4840d8481403800201081a0b5407000d2a80044031160490036903141c4803000002d082105c00d082c018580e201c0801d52106026010040a051141c407400811103c1e60b0141085002ca10403210841e400604010960010384a42c0c00b1090068040c100380d03001c0d400ba440000c0052400341c01100c2242d02c008450b80040c034041010050040414030b041c0d18500701520f454400384103a00504080c004001082e00701d4600e481c1407040100800300c0056404c2c2824504000d003c4803109140748640860f400200719450700c0c404807401901c05070024802d1407803d42d21080d00003140601c03400d91103418040c4440c41e84040c8131486518043c7d642e6a2041d9092a00c0501150301c044407c01e014040580103010707403208800d800c1c0d000701d0242407242d150440e11700001c01a000c2071070602c129000214180e036080c031004001e0030900c1401c5009011680e00ca100c03203094102c00400c040c000903102e003140320b520a951800150058080d083c00f08450743c1300e480301c65054411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 731778426 1250 731777176 731777203
    0x709051f14010917070305031207080a0b01021b0103020d0e0303070f05030402090c16050f0609011109090402012111030403090509040201091502031e070b130c03061a03 74
    0x2a880050800310499012030050300603011518180030094000030b100300700901480e00207008140c0381540001d4100008401142e20104803941c50140744116406034070103130741e00000318201c100498080940c1c1d0103010342909060780106945035110301034400b18601300000d1418103500b00002406c03e00103000300e81c0380002c030700c1c0219902d0500c85c00042040c1061010351041110600503c130042e41d0b040d0300c15400000c42071802d500c403800c01c00001d002d001c1d0244001c106104607410380340c004002150140c07245070392000801410505003101c0d10944510071b051903028640c200000c0041d070280207070640300300000d00c1c4505440300b03814485044400051900d1b420140c080104420140e0000e0729001a000a513030740c45550810354001703001c003c881d0282054595981c4c000d0013030203200300156034050002907a00f0002404440d10341016500168007960707900c0b08000000d20300300a11004900490b44841e82d1110380f455522401c000b4180d5a4280700c10030202140070701165010800d0080c02d510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 731779676 1250 731778426 731778451
    0xc0807050609060f010f06210e07080c120c0904031e05091e010c0b0a151725090e01090b010608090c030c030a020f0a0509071805040213060c05070905 66
    0x14010061031808800030000c101c00903a440050141a400c0910241298400d00348030108001e0031080c0d00c144506130548000827440c0202402507d007001031480c0489020805451240146209100c3c417031501441c9040c4540c403c0c490380c20316040000141d41e11600916000200107101407028070503105032841c034000100c0201e02ea076410b02c0c002141c1c482150f641c101c8400c00c81c0f40304001034481e0f03546140140240044800280040c05544c1014442c003a4400c0a024050349511100310f07694280c2e1603040072446540000710103012072144007185220082c40b149111803034140d03140050103106a4240240d5218508500096241d07074004d0b010f0490b45e100c0c11001d01c6d095522034a816903206240c0d10a41c00407030803160701d032008240030360803640543d4210020103112001c1400c50704aa4082c40e00305a80c00704020f1400d501110366140d845000d04106281c80d9108100b0099014551055000c4c0c54101d0042016600980000034054450005d944c406036460030030710200c80c0110351075083c0780f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 731780926 1250 731779676 731779681
    0x501140906030f0a0b040212011e0801110403150b0a05060d0e070b090102010b041e0908040b070b09061608010b07140604232410120503130824070c08070506 69
    0x10903806801c1e401700c010b45c0d0031414080c410b082a96108018841c2d01d000f10441500c01004480b428909030107009031000034050240355444003012940184800c2c0e450240300e07011541024080c0c02810004003004022182480c1403c080112503404088441039190b5104001800020107210100003487c0201c0c01c1e0342c03500303003207400642500c50612400303201d18a0b2a0030704400420145141448075400100015150719030b281200140c4516041815820008a051000c00895000f280d21991004007a54143d17280c1c0000070300441820031400001c2000b031001444406000c1c4003a211450080300c500002d0380b6003009960a108090300c0583c1c1d55985419071043c2d110303a103c1c08049820402000b00089403007006e003031200d202c8005190070791440103004221000c001103228000352003400441003000d042454219aa0750000107044604040d1820000d508170f808113021903407454141d0064000380c1c07404461040f07140002d0840c000c1c4411105100c0208a422000e0011070788102d00811050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 731782176 1250 731780926 731780941
    0x7060e0a0b01031a060105360405100f241d0405070804020114090a14040b06030a0f0b040204060503191107080310080106030503070627050607080c130501140906030f 73
    0x13084002c3c4420305204003045500d0241854103c1e00d20070f0030b00341d8140000c3c10700c2c45242007142e44581c5910355125040c00c0502030711090710140d820407900a1489070b11a40c0da10809050054011941c182088507005200c0003910302410000f200301c003644c2c1580424a541380e0026003100c10544044002030034000c02c2104650b08120280070a0b0050b00d00c013418000d140740024400c3c8800e0144502c5406403601d08146500c440d04448170740d034802083c0ba034881c905a42c00034002e00d40b20f01782d01c0c481d074140140c8a1090030305108880540d0103950f071301e034595510340001008042c1d040e6122202c403907035400740c052480d43c0b01000d044603d00c18082c040da02d04042441151068103074001300c600b6407401d0400c10028800108485550f030b4007000210742c6089443d2040e00c02421026500002e00300280440c041001c0418850311405442d1a0407880d601e0704c080c21203060140320129078a8400e0003c0901c07880d0301881009d59694542d0321541c0c5801101030201d400c542040e100141031351111014001c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 731783426 1250 731782176 731782223
    0x203040f05010e0f0a020111012003100909030f08130210020109060b0901120201081f06090618060516081c020c06090d02030a050c160b04050a061407060e0a0b0103 72
    0x11400c03428020240d2000d45484c844e2121302c9100024103000c0400d16201c9001c000790001c60312060410f0b40d01030031005040031040305a0044603046001c0c6081d903004100c130344407846207503801a01940c2c5d00e004409502d605403035125014000c09000d4907010480c1f4010f1f40c401d42c2c1425240fa9070750000c42c0e40701143c500f00042d105003501d041c2c421000c03c00144140b81043d07070001c000640902c0c2401e02900c401032110390b490b01c00801c0300044c980010021030415080700b502400c03948075607180118808661203640903540680124000180100058400e4040403e8419603440c058140140b500301400c0580d5554154030042041da182c000c500c215201e60f0500040c0ea0090400024103031903041c50b20001d440784181c030880c0040c08004503503250f480c601000b010702801111511007414545503282100290028450395220b218800d0b8003103a4030313204a02042070a03013124605d605284166460f94060a88242c08440074801c2c9102c2c840412a03c0300d402c0c2c029805520104402168140458503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 731784676 1250 731783426 731783441
    0x7021306140f0f0d02060f04090c08010f0e06011e03020f07060905072c07030e030d0905010506030718020306191413020913091407090e0c01020a0309061d040203040f0501 75
    0x208564000b081075042c0c4413080d102d003006504444032a9115003114100030207000d0341d04001c1013185048500c000c02500a01d6840c10b1700c000300309801005a40d28030038880e0f00c800301c6820740010030081140007580000c000107002d8200030b05026040c900c0d0206403d600b90014081500c001e41c0300c007515004d0220500240000d003166081c3d1901c80400181d960422907004000b00200c0e4820200141c6014801e5002c19141c81c1c000e03065994803000300f000382001d4000798000781d441c0d5190001245451400040c00310450b000d041d103540c41480701e000400002d4200400b090303045030010380090420030009100d074000d021020902050111084240301401c0114401c000b481441042014016aa240840e460125242c4404514029203107000714204001e001c8600561150205c0451410526003282d5246540307032040350100ba0038a0700481c1c5d03461038140c000c1c0106003055030a01c40343e482804c40c00b1a2000800042a100c2c0c80d000c081412030740708850581d07841a4a107201e900b0407070203004030391 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 731785926 1250 731784676 731784679
    0x2150604021e071a1b0c030702181f05030c040f0b030109030207080106060e150d0608062e030206041e2318160309050f0604030806010801080a0b070507021306140f 72
    0x895924042e5040a064007802ca10312030f017440b01240a6132440e5081045885080c5c0c09022440211400c1030a120f182c03400766000d4003020103010000c1240d000ca5120700d02180d1008004200c04042003007032000a2440b4103200c845c042e1114107048290b02d0902454200b41c0c403035801080500e190521290869106070010f000300000798081412030341d2201000002016a41d041903903400e032a5161304002d03c615481801076004207820040c1c501c142403002c074040c0312a070607031841c1440882e500002002c55804020740c0010184410f000c00349144000030000340060500e6855580c9424043c0c030380150b14140000d9002c1700e002414014240006e000104500c1100c03046e401c1c2c2024009000850580c5014004040d660208242444805c10110b220300e1180002d0316001c3c149824001c00130f440844050b8081444107000046c1c5520000f5a03610140e04580b1a030f14a890f03043c401c40d80b83c0e110030f0060340c3c015124485109181601d101c0c0d00014620480c0704010682c03168180402a4204031046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 731787176 1250 731785926 731785973
    0xc0a0609031a13021e0d0602030a11091c0311071e0e06280518090613030206060f0111060702070e06010207080a06050c040f090e011a0102150604021e07 67
    0x103e101c0300e085600b4000c6034100c4800507283c4081199030303a8803440440c0990b101020024540921580d40c0c0154003864402d6030a012001004192403201d00c1520903490b00480d000c4481c01c00c02c0c10070640c54002c5803082c0345c81c401d1582c415010314580f041680201d00500035140001c4020005c215082c00141508917001c000380c40c0c6500001c1c5c0c0c0444408601003014115114828010428011390014040c000d0105615111a610424002008071290007480c0310307000101c1c1420350b40107400340403a0703455402030031150b40b08003d020903c141550b00343e041c020344644905589000740031f07130707407003200d00d5802404d1141c81c20740c1d18519814094410f5056402c40c0030107014440020603000074440d003103040072a41e521074548102c4030b4030580d030000c81d1152103030201003044882c54120840f600300400091080303111544010200001000106025038840c2c4441920295680310503903201d90014401400e01820200c1070704400040c3c6001068141c0005d000010841c84141245113680e0310ba641 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 731788426 1250 731787176 731787181
    0x1209070e040f030c030302221502030403080403060915050f15060406050d0b060405030a050a20130f0e071412030a09210f060b12010902060a030e0c0a0609031a 70
    0x1103420b51852600d0140030004000508028540290115001d0314602044120010201c0c00b000c4203840e0b1b6409900b05001140e5172000e20f0a1000041d00d003034980010074036180a185641304401042c117403000b140c0090040b007003209035501c244100c6100303136000215010a031504900340440840704c1090644114024081405215440300035645d65841e0000c0c00070f4170009400c001884e90066034030a03035052044404040c2003010121300543d00e1403148408a072030302c0f400c1d10118058000c139400180c0006404040301100c2c2c1581d0040031010b000d421300040c41014000d0410300b80700090302300003184100302400d6166030a00107500c0748503d0817680903506280c40b0003001006007006e481060410509501c200540c000c01110072191150700011701d4562104a00d01580034100c184c918502c10f0032004280b0350080d806006642c00558010300705071400b8458003040e8020a15188108038a01c15001e040c02680c881410410203401d41e40c031805006841c40c903250710740b001c0743c0c3e20700003040c400c0505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 731789676 1250 731788426 731788433
    0xe0d1b030b0612070b0a03020c0f030304050f0d030b1806060d09110307050607050303010905091e010c08010b0a2c030102040909050105160215040f060c0e04111e0d111209070e04 78
    0x51b140c10311414503000d83c1e07921600207400d14000821040000c00e000004c24441000030008a203040054000d00b5589003044080707003602280c40001d075007a007142002010740000ea1000e00820760080001f01001d00303002c5401400c504417030b00030070101c03012070b1942026030461808022030340080608a035814a4860281e4400b5100c1c081807081a1481c1d0b00c500108440d0b2000344407500031610b02084900501c0d10032503000340070303180342c4441c1004a8061800131401c41402e1007111341004140c0c58880046040080060003500c0d102c0030034501c2c48490001130300c29a82800108018100c2d003070042014003190070141d08503200541101c00c4203610700c41c00802c050300401c45041500f0a034841c0015a520f9050a694408504000402003860041d649c081c10350040740c00c80c11010140c4042240704c1034485843c0e0360348583c1c1d4801d20304ca0280075480480e807000c28001d011303080c100302020031202c8100c00c2d0544250002a4a40c508403407040030462200d10030004900105604816100e50b410241c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 731790926 1250 731789676 731789699
    0x10210021e0c0307051005010306051006020a322103091203090a06060e0f0a0c090e0603010b03030a12050f010b0711031e07031a0105010e0d1b030b061207 68
    0x1d6007021410804110003506200c24070513141810b4015051310042c600c420403d00c020902400300f25003591401c800701e0b0030015004164015143e240d00180a00c08031921444d414170070468006c10200340c2256a134900807580030070b07001c00d99450b00090003060710408241543d2800e01a00070f03d002c401f8400c04c141504005002486042a100707501c6d56a2102048035041200c140c0e1f010706202e04015000500b050441c1440c0d108080c54102c003e0f854949c0341025056449247d4400b00051251070207020440345100d071103401c4034005000103054135521010034196042184000701062032040102800c21f0319008a6500c0701d02401202c041c0d604001d04070005006402c006040e407850441000d41030b0300c0400504001c88149071002100d44000070030382d0359684c40c0d40402c90f41e0300e01c00c29800c500d45282007aa581600e034142c403404031170002030041c0180c0b170890742ea054810801d220340c0c00c08034404411520300550b001d6090654145846024030002c02d4102450b0f50941c2d100940420403c00f019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 731792176 1250 731790926 731790967
    0xf1d09031c02040306090b15010e010e01030c020709050903090108090706050406030c0e03070e070f08061e211e031204140f030d090c0f08030406080a1d010b01021002 73
    0x70800c0312021003100354500080c0036641004168a00c0c205000d000e00000880d498443e0038454850384120500d140116040310701292203c1c04641000d00241c0c940d8001d81028042c01c070740c0c1c411564866035401d00c0b54280c410517100d035042d0f5000000d034a440bc0d41c1c0301806c25884400c20004140300382c03800390024024401c0e84500c000b0190f83c0c04402020340e104180030f090504005080ba410f0a03150400e0702120501035442a010804860050101e00d0007241d0b500d02c1100f009000010041040300110740e5044180055a031000860b542c3d81e6003040361018942e0720308070300303002060666200041203a84921600c5820102d610070701c615201c1440310103105074410382c4100500d14440320380702207500e4444c48440d0b40c0e0b803500000c07511008030143d81d80140b14160060044132940c558a680c08041d601090050040c290801c04c014411b15004e50f014030303041101c24800080b5a002c00d0244242d0180d03141e02040e507651181c556100560b410010740e546080c2d0765200310b10f8135549a00c0d038055034000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 731793426 1250 731792176 731792197
    0x304030b0c0d150509010f0503060c03070203070f060b03060105120618100f05060f1207090c051207050d11040b0405010e4009020d02040203040c0b040f1d0903 70
    0x40c6000440c4641c2500c169070301c42c40c1281c0d003845140f1245410a0301040d850150034060802d203000007491040044800d81100c1c006809820561078031340c2584800d9000034030010552008100003030000764082004240d543c001c150001d1288145820141040d0701039005910800c10f10000030130680010650710340210103d4500c0100340d145050103814003039100b1522455501e84201200000f04507048688908021246960011401000c003d1100802060420035074440311061040800ca5800700981c0400e0303090140c00c2a02c255440a50b10300e080710354000280d004551250b00417500c0c015000c0140002800a0406082283c03604079401140308032410040d405a0804840d1030b012194214080d5407030f000403040104000c0080500ca43c201900d5610410014201a42002c1d00c25000c181c3d40c0107018200310410303502000040e40001d00b041d6207000c581240005e10201000040000b1b00e60740041c1d41d001c40c0346c00310980c1030500d0154042e41200e070f40000c02003009004011111940103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 731794676 1250 731793426 731793443
    0xc12090127020f0a0f08010f020c0a03051806030703020d0507020705031b12100b19060c0201030b040b040905010509011a06040306110c010603030504090b2e0219060203091e030403 79
    0x107600001d980d0992982d0840d401c030f008020003080f84505000d0500580325040300038042d403250398040c0ba080b4030840c040641c064002c90700050010f442000141400c04030034041006101d4040000303031041c0c2c01519100c0c00b103a070000e1303000403400e40d41c0291940021180060a021840c0a02084d12030f98a00300b05518002080c0e11032a1680d650043c100804042034110350010340130b410120024041804414420040384051100360401a602041a20782c01c0ea207000c00f5680c0c40d4010b50140c18001061345d03200b62100742000d400c0d1100d10400e90300078010400483c0505049041e142100c2c2d429031018408411401c261a603500e80d5402c07641140e501c140005901444103415181600880f000e00304154202000003080c075034400080c0090f01d00440041040414217800c0006604c0c4104142155060442881c109001082c102020804d05070050382d00307403500d00000326400c03420504c0c21242140d0200620041d41d40030080d490750500d018000450949010203100d90764000c920000b04110b5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 731795926 1250 731794676 731794751
    0x3110702031b010c05010e01090c050d26040506160c29210103080a0f0e01020606040c270e010509010b0d0c1407050a050d021902040509150c120901 65
    0x24804c24039180d0458000b0000c0000381d00081d1341a01030030b402c0406440303598081102140924180c04104031a5a020b801c0c144000c0d1080b40206c0781c402402103021951200b03010008198032071030014881c10003505c0749c41680701c3c0541740100d0400c0d8580c012030b600d58114103031000e00030340750300200013030108184450b82c940d14015a0909441e4510080e85c140c410b018000008120100380030700403030340c5103413201c4400d206d450b2012655102812081401a402040410350350f05095012003c11041c51620045000c2c40f02c1c100c1d50304103030300c6109210002c241507042000034050a032031805000200c2c0d5518244d450023090507a0380c054094483c800700d60329002898023034041ca408040301580f01d40465100c0030305040443e2074145002098515001d08006104828401308680102c07400d05240000000569028000240340090071100c141c41b85400720071401c00c1c50401d40b481951810001c035614440b141203401c030083e0103041c4144582c107100c40d50031844e52108418650b4403911400c4136459 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 731797176 1250 731795926 731795929
    0xa0807080a23042303040e0a0b0108152d0a2103110a12050307020c100203030a0e0106261c080610170c0c070e0c07110a1701090303110702031b 63
    0x100f07a0320000080c840d0808070300101c0000088081d00c12218244204140c992301d4480351015114548215400500510005004902c0884011480e8107000e000d80541d14649100001c1c1100d0304011074080d14001e601c1e00800d4078010302c3c8003000e400100c0b019a00803040d030440451000c00400000c0a02840480740a410031081020188582d0825103101c07510000c844041e000303074030548400d4014000d280141c8258100703104420f190000ba41e000750f10315070358405480700811021a0200c080d5403540c10000f010342d81141c2004401111b50600424000c1c02c0046500d03040c00100c05030450b4294203440c03000b00b5007054002e540000140c4601110f60303900c3c0d508841d4491310044011120b0300940c28010344401035806002d1807409101101d07801d90f12144446600181214080048902041520002158215401c065080140030f2031380b0369031130740950010700d0038014050089a5407800c0c40f000b03055250003064084003140c90f280786001c10603004240c403142d04500e40543d91500c179a00000c00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 731798426 1250 731797176 731797193
    0xf05041104151404030312060806190c02071e17120d020a0e3307080f0922020705010b2b1115070c15120b13020a0807080a2304 56
    0xb4a000002c00e01d0381c641d01c0c1d107030140c0002d0f2000499800c2c54234080c0d01148081000500034000d0081200c00d400108d000301c03031440075002c01c41200045001e0180005008010000800c544500440b4140e081e5402c100761402c0d40042c1460f135418580c4800b00c500c2c0c0344140a000c8916648903040050fa80d2071005209562005440459540280c1000c6050001031150100c01607402c0f42a07140103c4a84d0303c11207610309004449014001e00b00c20000c1140a0711a01d005005060001c1c1130382d099240251052180181002107005441d5000154902001001e21030229460300c1142c603044440c1c85214580d81d060b0303c80e55409042404601c11a091000108010400b581c0040a03400c0017100c2c079a03414615000302038203d4105540c8070020410035540b0f01003540000071030360340300c50201c240380d070100c0a0450340032019002840016550300c1024180014252030b00c3e43d8580c80c00354208200010516140109030081c054681300d07180301038826406008124204101d030402040c0c407035003031400702d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 731799676 1250 731798426 731798447
    0x170406091a04030906020309030709091e050f0f0d0905010804060f0204150305010801140c0f12040f110102210a022d160e040605250305010f0504110415 67
    0x10440d076010380725206104076801144658800d5559404044c2d6a0405a079640520541c9550580200c6011b01590300e131903000710440350003904201545001c1240313041c1440c0c28910151007980000a0180001000300310800103501b551004000c940c10000c2c0003442854140101c6041118100114042c000160440320442d251007170115070700d50361101d40c1004249802298400302c1e080c6800001c5420062140100001849540e02c82c255101d20306000c0a9128059850f074030071080c070800d10320380c070034107100d900c02e0b8841d0400703c025009900300b900700e0001d041101070445d40300a03d91588195001d00002040320000b68a640b00d0118520990428030740c0206030302400100510141800d01e16008203010818071000d8031551414040c80290b81c24082c0551100b030700c101e001240010301ca641c482a440090294248034450381400d0140d49c64281d4800840000c0c0c44500500019a1711041c1038010001110b04005140c1d52080014407405507201e031000c0089400148114a4000d000444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 731800926 1250 731799676 731799683
    0x203010e015105031e010e011707091107060e19030302180603041505070f0903030e06072009150307030f1403030a0609060b090315100f0308250317040609 68
    0xa064001c2d10030042a0b038008944120505d0114071003100c001c503c50f40c00358180e858040845078543c1c02d203c03075881c4c0342004010403a090b12524074001488411486038040401c1015903044d0f440405080c4807040e144002148280b03508110000240400440611840151b2500340548c941c08907071074200c00c214034242030304d4001c0b03800410402003100020524545201c0070900b0840e81d107400c0030869100703202255507000308240b020288042030140342c0004030f810b001410310789040341c02e40c0c5402442e00e0a0a2801c044861048003c2040c41c215400d0b0b030340310168002ca0b02c04c0207500000255102050322010307100100351315046040c4001060303550501507800007101d540f81820301d0100000c200354840c40400718503290011030142419421030382110310090040c07000c2c8004a105141c600030213025180300059001000880154410000c0000c5011340d80807034031f44002c1c2c44181c03d01c0f915081b405510204042511000a401511548031504546400c05061390740e407401e00028890a100036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 731802176 1250 731800926 731801069
    0xc1018260f0d09112d0a05040f0b030d08040f0b091002041509150c230a0f140316082d040f0902070206160311070f05011b11060702010201110a02010203010e01 70
    0x274014141c658114181e01c00b004d6048462000c44002d0495011106071402450446620701c0d11022071036031850290042400c5090f503080c0f2004129081c100c4c0c3c0140d02c9507841c801120078501526800032a003200401a40200482955403400004d010446c0440700900b0007000307014020481400c0c11684c07004881c028201c407081d903800e0a00d6130400038025012100650f4184044120f4100801503030400039030445251844011a55040b0080e00240040c0014800c588450604124a0101803480c5c502448246658030b08245180c0000621604840c1d0b4581c01042100d00580b6400200c0b041400d4081c07603403540c3c191a1400320342c002e03411410100c0c544198035000c00c5a00001c80c1604c11105e00340c0707030b407003090082d2441e44241d800501c0700a4014503c419000032142040340080028500c1440005000401c2c55100c01d81034022640e80c3c8010b0794044018441044a8000207000d005062040b110014101800b101c021001ba5856907800d4030b6400500740c1e00b040150612100131480f00031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 731803426 1250 731802176 731802191
    0x3091d19020c160f050a060903110909010b031c0e010302070206040b13120c090c030b030d081b1201140a08030702060f0d020c1018260f0d09112d0a0504 67
    0x75813a9081030f070007624400c00d5841d030000384c03403030044816031f00b00e035804a14208401003c00401180040c010000e1030195240d042d03002c1a0395007807103035540c010900c88015001601c1d01c01c0003030040408010f05818184104205c03009a070712101542e0403200c00d204c4c000d640d2443c9051500300079119911604240d044c6600c01c2d010007030100031301c1c81074455000c01008001401a0700724166034942d482260190460b54800d030405110b004010b0388042201d01142040070684c0c8041a01e6105107100c440302c109603401407203580e030000e0b440d03400d0702c0c3d084640714601c50525400f15141d10528000a126600c0020345001e6121450203540441d843c6200440d01d07a103445510741c0d00c400002056101c2507203000d040034000310025072000202e94116440781e440031b2070803140501200d19401102c40b04035045c0501031042d00810018140c05807510404221a4a24504100140c0c00346580a2281200207411000e0500c8419040d10f007504649100880d0f145080120f8060161038004682242c01e00d0351 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 731804676 1250 731803426 731803439
    0x30304080102042c0a0e0705030a1a070c03141c09050a03021018020f190312020c0409030f03051e0a09030810050f1e030a03091d19020c16 61
    0x1400803101d5200d00c100d4034015803010240343c180188524000c0811308800300310440302e958401b1144074169001c4030f6090b522080002d10300180c1d0030701240d0440030f04010002c812143c00690b904105c0500306028460207594025021840b420480a140c04010602a040040e0f03c980100760202e40c540400651005042854580700285016005841452080c16041c0000d00ca051000c26402e8042610441c0c2c5e0f5003000715240d2980401030b80150300c400c0300420005005950300065114114440f600da4009902a04040091429600c0341d881c1400e400b01094104221001306000d51a0003d01c99454070903024810741011461246240c0f050100010503596a010004c501d0103500d41c85019925101c202010340c081c1c1c014250000792562500c0761a0a01080c90380100c40a0101010301034269004240381403070748081600051500f0108101404070182c201c1c81a02000054004134505900518000500300000c2c00d4425800515001c40324001c2c80007091180388417503460201a510003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 731805926 1250 731804676 731804681
    0x41401061d0114010e030c010c02010302040302090c04050a0b09030606040506011e11070911070308040812040b0a05090a02090610090807090c0f0207060905010503060609030d030e0c0a050d06020a0e0303040801 92
    0x2068100030800e83c0c9203072150f008039003030306407800001e0007410a803041d50011500808a80812818950240700100040c2e5a400400d4400e03004c6047d401d407182d1903c41004032001c021750000c032180404110500950f00d0114880750b0285082c0d8004c9401e86504004031400c04040905142440b00b8910448115910a0f100401e4614038021282180e8554448604842c3d800300d420070301030b1007003020400280c01131341015802402107103082d007800c0280b02d01c0c400d404011a01150890b00820420180440e144600b54022a45d00014400e2201513800b00c0c0d035400d030180400f44500400b0302c4420400b480340d12080050841e207015030304c2580d600c03a80c2030003806860500070f0104000c0f0b92440400fa10000d03403001101d90342c0d0b9031304c240f080c680300c01500c9a03131014190a4000e034080100f0407007a201003090000c903001075a000130340c0d07101030140d0030700b80140006c4580c42410109010081e07551140d803515410f030382210005950705000031080c0c407041981c2119030307010700012400003050841076 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 731807176 1250 731805926 731805929
    0x91f1412060907030c14031f02070203030a1101060b030f0411040f2d0c080f040629010905030d0522080109051005090319030b040b0a140f0d0b041401061d01 69
    0xc05405e0314071038454810072414210381d50302c1c0d50540d08c40302401d0f40d0080c00c19010101d40f24800070041c0703000b000c0d070042419a402004035402007483d40360b000f000d9100034800c1d1001400995050b900310305118100728450b0001400103085291110a00282903130340754441c40d5503401c034001c200012a4480412812514000c0f414048410f044042000b10440c9008442d10100250b860007c103544609800f881050701078829115683e449a40e490b01d215201c03201c03410b00d49035009244400481d0000104440d2041e0401e0b4080d0700311112805070b554110341a80d03145031840b10310349008007154032484103590301c5e90b1085440d98246050341042c841d005c243d11a441d190000280000d60722614000d940b4071a04d084080001c03130500c10716540da071003030303000041d0000700600c0131600c0940880095900603554110998180e1202c0c0c40608a01d1710003042c000080003540d894100398942d40b908807420340c0080c0064a001520b640401c108a82036000c0000380054a0320b01c0340c403079401c1c3d291b2901c4a009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 731808426 1250 731807176 731807183
    0xc090906090b01020c0d050606010f050706060b0919050108220501060b07031101020a091202061308100e0105160c290f090a020906281202091f141206090703 69
    0x54070014180790070060905800c6c80e420000401040d00c403000116035620602000008200050100800042e841d01682c001030031849555519410300004000001c11140c0502c40e02c0b0080031400c1240380d800c54421540a4035000000b20b244401001c400038401803035000409651130f10402050240740c20001e00611802540d40d56149080096410300700c3c840e4098460209e20482001c001d20780600141c000715034406031009040442550904004000c140c100300e086400c00440c4524404031441446400c1c80004024042d60074260700c0801100b1099102c0000c100c3d00c0104401840500e0503c1c0d00449041a42500a4140d03500c10040200054a25100c40b00016010803482d0a0001e800100070b81c00a06500142d1114030070030459a00f070814043c0320b6646141e28040d1600c2c50180000102101c152001800b0101d204101c81c800004046040c030070824841815000b080101810607038034080d180c26540b120b014000703a00c00310350040440061050034200601000701190400481c0e10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 731809676 1250 731808426 731808433
    0x80a0506030f0708100605060408060a2a020625091205070b070c060306052b0c09060303020c030111030f01030f030203042d09050601121d06010b0a09140d060c090906090b0102 77
    0x847e00200080352046219282c1e80d80d002e0b1001c03c0c110600303640001600030000404400303152400504981e5890562100405a04168100200e44084a0f84180070000b00c0e180581d0940c0421005006411a4001c4407041d0800854100405c40204049000351284030b6020b5220043d5142c01401e070b9108c0d0040b00e001038280171000030f650414900b4604048020000c10b041c40104124600801c00002c00c1900c10301d010390300000d00303040b4a00c00c8001a60180c0c3c0600355208942d230925003910070b08013004016000400c104045d18003080c40e0a0b0550b44e000404011200341c1c0e05040789140519001682c0c040718615070a0360902000341d210142c40d001e1300c018100710360340703250300000c0f5082180d6081c0801d91080b1101c0a00042d9800042e42d450401480142050210410342c81d2100907000b1000e03c000000d115403426401000c2c1034002d24043e06070719801c4001ca008a07201c0740c00044010000703520343e0303801078486028902e040080d00003100d00700400c940d60b00031040a4040da410304c40c00f600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 731810926 1250 731809676 731809679
    0x23042003010b0906060a090306020c0322060215070504030b072001060e190908071a0901061404021c0905011d0a08040b070305120907031110080a0506030f07081006 72
    0x1410b02a094441100915614440c0c1e22034003402040d60040c040031041008a650120006489102410054000500458031252100d10025444680200c40303400107442941c10451254000b805110f0740e00d2000000d43d40382c80340300054a680c05580c2005040743e9201c010001950303840181da01080000d60403800b103620b0200c0c0701500300d504a0089038008400701c000225020201e02c3c1c41901c8a10002002405204613264580c05400102c8100c58103e92641002e0001400105098121940328002c010040c0fa0504c46510035483d03642c4207005640105640014005101c40d00c03408503480f2030705200014551038054000d01c0d40c084511481e001c0c0b03441443c03e42c41c0c000313442d440b0a07500210a5144c5820f010501d503494200250880400008200c103090382c451107404503018804501c004e21925042d446c01e61480a010712105005043e000300d0418405c0e030214015811a07003000c80011f1544a1a001c00c0c10405610400510703803041c40c40004088070002071312200c48802c0d81e0101b0005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 731812176 1250 731810926 731810929
    0x2090d0f1214070c06030509030c03030903040614040e06010c060b0301140603010e0c130b0a05030a0f020a0909080a08271005070306080d120207020a15090603020a050a03230420 78
    0x5016182c0d000d44803048540c414032117a40264840c0f500090440122401d140000ca50341e031440e030086545060726040840c00f048035940013001c99002070b14010103282060704000d503079150404020545810000a54114024061103501c1107240100140c000e11440004094581900000340d94240c080c1d841e00100c1d5039442c401044080302c10100504004007001c040700501d014220308442103a2018083c000010f09603401c10403801e0071b500c6141c040a0421060041021402c015440244458146905c40300020740010880b010704001c0d0038a02a80e80750110318480c980b04150381c803908140c01d142101c1c503540f00050314041030550104244010f0380c5010003101030f140a84a0094180d00c0f414a80340058003488608903418a0a0780040c180411038001504611141c0e0108400300000840c01200c5944030039440301601060505524040c56601c00401a00ca400641c9003003545d00d14145003090340c0342c1c0349004010003101c0c4046450501d420b0405a83d8030304120001032010154107545507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 731813426 1250 731812176 731812217
    0x10206060a080c0d051002040e18060103020109050d0f0606090f050a15050d140105100302030c1912050c0d030f1d0d0611210105010912080d02090d0f12 67
    0x141d84035080a40700d108502d000b44844c600b071015003160315000741d01400303c0071529440908002d0000b0541490141055034010740c070401c2450039181d00703030081d00051025036003100c1c0c8a130803950165444850100c544c10025054819420020b203610700f004030003d2240e0a50300b2440340b800b0300140812143d1549c0d01070b58119076820f10160507201480000304214a07111070000c180314003884051459505101c2d0060854100300c8840d80c54041008042c000e50808100800e0004d00a6550000760740e4100c441c0c107c110304a00c52207081d01c801540c03040800c04240103d51000d00301600928407403101e4038003d0300c0402800071800020750540b001012024401100011107580580019a48969a00c0e00700142014001c10507109500b0401c2004407080b40c3c207290104110708120421550422000620004481d40312a03203100d4551088408150320004480703113420700c00c1c401030303460020700c003c0b420100710084094170a1000c1d0323a00d002400f6482c89414074070001655001c607240083d121a500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 731814676 1250 731813426 731813429
    0x1e1c050a1512031b0b0403050415020d080417040f030b06041103070c030e121c2c0618090408070317090a0b071101060915080d0519030f0c0c02010206060a 68
    0xe03455505101c1c00701190080c3c9404c40d100e030344030b0030300c071078a100940341c80c805100c042d9021000900c00241c00c028405890765182c03140038152000d80000319484800422920000c0c0001c1c000c1c0b51507001c1d1075007034a6403400711401005240d81c80081203550381803074040d0b524110340c05400395003064010500d070180300003224401c03d025250005a184a03442c215445100f0090054009820030801d003100b0100300301e0000c0100c00c2294455446042c064010003485000c69114001d400d21440103031321120440c9e114460031003c0d204641c0b41e0405480301c81c90140203403076941c6c120381070310188020b000c041c03801040270a000c1e4540525004a12000c801011001c40d81c0030100c0d0445503402c0001484402c18036007005d906e19040081c2d100703601c40c0780d08450300759000f440d600c0d03510100c1e203080006102c00140180302c0d50001d020000c9007044060075904c500c0c4919940401c003207a134440320b00d00035805080c1140c0024010005100c0310340c0c01074142c103014002070740580308482c009181d91920294020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 731815926 1250 731814676 731814689
    0x8250603090309140612040f060605010f0c020108270d090501050a140c0c06030a0603051203040c031e0c090204050f19210f030807140c031e1c050a15 66
    0x301441d20f0712a0f4005920a6200e0185e84010308200e406010520b4103801030003140901900c5a43c003071940762640c103d074042c1c1d000c5418800310341041117030503802101c1c808000ba0282003640489c0d941c0480c024100340f83d84150900100190b00c51320a1100c000303054105041d1139103d1486040d101d400640d400d004040985c4d000030a01c00350311810501c86800b800c8810221022a0580a0844001040741d04101d4000041980e9040100240710003009040308014159049a1550425444400180050f400094100d513800050142c0340703000013240204498111100208150b1030380803d00103035109103d00d5100300c3c062800d641851070310048481d001c61403003258001d044d03c0d1410340c0c14603030701c4800c4031a04030314851011000701e5407418070318008920982d21610b00d80303807280019000071035284020103a69410300850786041000021205400c40440c101240c1d000d0180419405105030030403802c85204400c0ca03115011442e410160091011010511407500d5800c408080146c0501c12803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 731817176 1250 731815926 731815937
    0x20c030303061002010b15090a050d0530280527030a06060f060305181b0a0b070c060207060e090408130e0c041d06011d01020304082506030903 63
    0x3805450180760f03c0c04114000e00002c5070003021840000c0c0e15003440c40e0b140112003000103203541680b80c8203a420010f80001c840410366001c0d5915910f0791a241c028100030320100c000c26402058004551102ca081201d02e1178942e18000c1030b038191200240c001658905801141007010124010342c240c80b00c0c403d0412181d0183c07803e02800301170881414143c29098007891450030007044050140102030200e404101281c0351030480010304441300148102c0d030704003442040c400200c1000c01c00226419401549050341400c0c00000703204055a98000010010002450001c03c034843d00300004898882e001c0c0d4026a58884c0207840d03660400007201e038464807000000d00040c1c0d9500182c51828800000180036584920090414003015900400c0000c8040340400c01607500310080504600380520481460814000103000b0019450620342841900400c045190340708205a074000c0c00b0120484e80243c00b90307203401c50281d415440c0d114150809a0011526500038012140070540c144d417030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 731818426 1250 731817176 731817181
    0xc09080303191e02040f0503210310090507030506031b0d140307080c0609070b0415031a21151b0c150403210b0609190f03030c03020d020c030303 64
    0x48900c0d401c260050482c034141d85050404803141c1c003040300703511011101001030303840c0c0c2420901100d03007245501c000c0c401e41c40714540101100e0148645861040d410030130580b20303141c11124400b1400c90f078002c9010036141c5010081c1099140d0080390055005400f5140d2441c5107003203180c00b807180d40e074040f0b030400312400e140e8000074956806841110503c006880c14400c0556641541d940540c0303030710609a0180083c0b02246c0400e1040380001d01500351402e19140c1b801d0610280550020903c0d801c0c50f5030340e03d00000d0300c200c10010f440201c90040480a807005081d49400a0350a02a4210041d105024400040d003104552460041701390344803e84800096031071007900c5a10025180417203010b01c94407408800c9034000498012486038554105400091842c0200321480032070400301c081c140390040110b61640c90071696840c01c00d9441d003440410601682c3c510180680c82410040d580c11000010300d507026a405c01e010748294281c2e42030540e00c0380120703520100c002034140e05400c01c201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 731819676 1250 731818426 731818441
    0x31a0901060f0c170703030c1b0203100504110901030804151d040506150310050922033005040611040e0c1b0313050f0307030302120304050a0c08100c09080303 70
    0x303070b007032815105001ca054a44103400c1c42c81e242d500412401c402003500c41c09042407181d000030321188105c0e50180c27174030114100b07030b000242d9501140501c802c0d299500c030041020b12a01d10102c1c80d0542d409450a0403d5a403494000a158000e10800320308401da021002e1825105040c101d842022401c000850540300d18200401030401400c8140d111030403051080b41030f900e51010b58800c030360001d00e00383c0c668074010500c03032031640003010f40703800c180c00c0078610181d03107014003500c0100f80c0c142c60940c0035164003031124a400e0484001c803652008030318509507031103050751f0015445544104001d101c0349181da00150f855000368020440c6005861001031161901940984025072141003001c92054140090a0655115000d900c03110200f903070052046040ca51461110604260004c0100519545009481d1036104121144644002001ca0207011080125010003a00198092601e40ea24808180d68070016019507105500b8000b0b110700c0580a03010ba4800c98624601452840e5111034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 731820926 1250 731819676 731819687
    0x2040c03061a0c010b09190e12181c0209070e0301020f0313030807080c090d06020d060609060801120308010608040c0905090a05071a09120f0d031a0901060f 69
    0x90003016501d181c00540c0b06802c075030501482c01e101580c155200480400d5031300390388007911164001c0100c0803c0c0110741c07050100c0421070b012942c40000351a0b44000b600380c01d103140c8810323503072441c4004103002c280c40012100c3c14421110407242c0000344503100007540c96011000d0006075002013a1000920342c0340c011401001c003220010001450030100590421450704107881940c5402c4006000a00b0107810542168100810b41810007443c13810f40d603050180e20031040c2c060300414400400e1401c1010782d4050710080c0c4041d0340180145a00d4120003441c0f6035891040c2000180307140c000103028a0070704000ca030480d8141d40c4420301e90703090610030307141008003800031100110913250000700b980141c4105802007588901800c84c950305403d0103890407510b600003005440d1015101b4501c40b158004452070101c05540c4000c0c1984c0c03136040340e03044c1414400390342581d004103552038000b0b59240c0e1140303021040995030551060110300038020403040901407000410244048001c460740106c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 731822176 1250 731820926 731820941
    0x6020307080f0d1521051902030a2114040308030c0906120103121d0306070e01020f0d030b0a0b090a14191715100323011b02060105040204120204 64
    0x2ca80032494180300d03505110494440c0091222a01e180340341c03d03c2120058020028014014006169040303210380751203031a000c4174a010721002044d0010341c0c0440d1800d200c1081903d07085800f07480c1d40c204e030235801b01500d4508000c98001464011420040020301000c3d0707001d40f500040c00e281141d4400b160303400c01707501c0045141d03031000090010204080d00c00140a02a51080c40701e07403600508844050541c0083c45026a14160701c00422805a180002d40c8c0da484450703460310300903a0384a034005038108010184c0e280114000c07000e100c0001e54140d007201c200b07400c5c2682d00c140000d560b910829100d00aa140080d80140741001c2080740103100c1159030b000f40401030000c4044142c0000d10209820240c0c40b2014541102e030042c1300400043c4511100d541020b5020106807401d0f03008030015031003600004004100011100c104900a01d4616011101400082002c054240314807120116854440001440380b80c0c00481d440c2464000e40e000c036125201c00040b032444070307801c000152018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 731823426 1250 731822176 731822197
    0x15040303090b0f1c0f180209010501090b03040b0406140403080f0a0c0503060108040305091806210d03090c090507080a1b1d060d09080315040606050702090a0605121e070602030708 79
    0x2d410180010000c00d128004046c0000880200c24029505c180017010b9016400581440407411080100c900c0341401c403a80a5031051800c50513035128509070008008150850f000000741e001007104254105180a0180c1c40550301c01600e030791a0b0f0b048006940c40605c03540c0021301c1c02d00101c0c0c0a9409414101c1c0c126101e4240030f828000704101103206031000c8480103510841031030030310440d400e100c01c010301c4400d0781e8040c480c21046213000181c1d507024201d2030001010380d00c500480c1402000d52000024000120080c0014104542e00400030401641c81c210304c82d28100c21400482e15608541082a11503140c481002c0c00001404950040f22280a0f80201c401c020403030039114688902e42c0d50910498115407a82050203a14503c0328003810100d002d20720740711007444040c0d0802e0030781d0401740e0f0441d9080d1103581c490130003201074211603004580101c0b6024241c903414801041c441d070555100802c05000b6403452050310b540e01d60900c00d11380960800c200f00c1002c0b65032000100080c1a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 731824676 1250 731823426 731823431
    0x360f120317091f020a030e0307031b0c1208030402010201140601092616180e03032214010b0112140115110601230907171515040303090b0f1c 62
    0x2001c00040802c40ba90080905510390300203010b1200e150184a01f144144802c001142041c1e84d690740a00150a101c100380740c0d841b07865440008110044000758044c21051307c00303100d44001032601d00b101d500240d0b0224050350910398119051910040001d100d2901691082d0140b854a4103400c1d00c038140030b0030411000404000300708004000c000c1c22842e41d50411502800d02d03d807214400200b100c0d048582000381c1800c200d0b1142103000400d03a5000900c0b030031950040c15200800c0c1c081d040e0520b03402803403090740044007114041c0650180c0d00c0e19030207894502000c0450106c54045501a483c0040d40101c1003005110403a001401000d910f6a94189601c03503d1003003101a03d0244240e01c05940944ea100403844000c1508072254a001002d4905032160304202e036006d0003000c0311314038a24006070300000141c04101e82d05003040844d40c0247c1140c201c040714005e4004a80c0c0306000030707000b00301054000104000e10604651148000d010a2402d21440005012080c1a8a0740504581c0e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 731825926 1250 731824676 731824693
    0x3100509190227150405011409030f01060302040e0309030604140705150403030f090b03040611040f060e270a0c0e060406030212060109050d03360f12031709 69
    0x1d00e984000d104028040e001107240c0c094212000c0c1c81c076840b00402a00a40c41d0300400c01c10401281d0564080c0c138024240450b06901541100c1c01d1b80c040c025400d5454815040074000010065000c2001d60b802070f142846410454080c0a5403446110300c01500741e4803400028021074008280c030baa4072400d1034180c1da00f031655000010641c1c02071603140c400031580003a0800c20190090f405401142860500440f90f03403810404080902005001034885612003190f55628400b44044074007900754070940204554542000170300001030041c1040c09095220449808009000304030351801c064402007841da6500c1849140103802a2407011040c800326003d41c40c815500d00c0050400742a05030350058603800420160107020324042c180718144598503006100c1d40d04d50a041f841ca680d05814050011a4102003483d284076081004c0d0201620035003540c1401c4604110100480d48121003e40c0300345c1d160740680814940001c40200130806d5003843d070300e072001d440f40201c0e805000340c1e05490210 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 731827176 1250 731825926 731825971
    0x30c070e0c12070503010e1510050c120a09170303010f03140102040b0d090614060108070c03020705041529040311040b040f0501082509021c060e0601080c03100509 72
    0x1004141c5800c40031600102c01032200540381f1240d036034002120a21039a6031030b0351102040407002103081840c10030100095a1540c800c007000b008000211800a043d590559584005c1900a040c000c0501c0c0240f0015002003206001007075030305849502c02c0c0b154455141d40e0325040884280f41c000039981d5001d200000d01c0050650150240341ca480801083e900c0c060301c0c103041101c0c5090360030040f000c0c0302d201341b00559074801111a0f02002a051400c814681828182d01c2c00030030341d000d103620504000c0203a140d825091005c0d01110040c10502e841c170a80803c0c8040144562901480c1080d414801040072505421140b8401d4901502c0002c107440000045002e64004c50007020342c080d100c01c0100501d00c0208958034004002e01c010504010482245c124180141d10a1401168020a0b80c0c0d80c040c40d000d0b2540c1d5201200e4504005a5565100c2c61480d100102c0d0058081413540000400c00380c0e0580c201c0384030390030b1004124662810320003000408003025107500d6110503c01208200f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 731828426 1250 731827176 731827207
    0x30708010c0f080a1802010f090504090809030105220f0305070206121501030b01050d02030901061508091603031209030323060f0d0c12051c030c090602030c070e0c 72
    0x116240d603075402801c000035050260803000040e0100c180c05140020300c0e101d408881c924811246c2d42441c04200c0c891032880101d448040d00d402003039005203400351490800c40b11000802c0010340940007032103903036034503061802d1007002c020340400212040c080500015600c001c030b030501503110742009400c040c07464011131101d80085042c2420a4022410300ca06080000d011400240c02468240006864240001c000340a040c0140c0361117600800452340c020001e402c850003070701c01d00d00c504004410304007005000f01407d5803480c007140140d60210040d4622030700842d0507680c1681b1500101d82d8468940c5000f014005801d40815a40c0d440c0c1c81282103800541e000c40e80070412201140707003015000c001d88618a070580600c42c081580074400061003248800c0c04491a00302a004021040c0c2002801c1040300d41d20b00d60402c1002868940458040d4404030254a42e66140040f8a407600c8059a5a2103500052001d0350f225010822010400100c000e40c403910120450b400c003120100041780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 731829676 1250 731828426 731828441
    0xe0a060c03020a060e0606010e0402031603020717211e0619080d0e040506042705010b040c1d031f020c12070b070f03060e0c070503190201231b0903070801 68
    0x10146c10003000c1c050030b5039000340841d01141c0115421865410300e41c10308401a6460004681499004264481804582d00040c2e040200141d4034643e030f0b4a0f00e4440c20f4204c0020039013500746500c5200801d800200280c4040c401140c4203405a0250315200b00700300381000312002404800380c0300080800c083c0c1051207140c400e1007058442c10520b001403010401a91b100510b4607010340d14204800b03d0100070740c0000b03000e10b60200381c0092040e02901f400307405000da010402d9000ba041512040039954003e000404040d900c00315141441a458101920713000802420030342c054403944540c80407403443c0d005040729407000d01250503041150074694a82d8210040030f80b102d4103c0410000143d800516401984240d0318040042d00c0c00c080403984501000f8202c8540203c011500104000040044411448002d46c140b00e4160018000074080c01010b405a04402100313484a004401c4c0e0506c0103000c0c6084000c081d07416111820300f008141c1269210360f6051003807042c0015860420f2042a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 731830926 1250 731829676 731829701
    0xc0703031107170c0d020105160f0c0b150a05040506150901030b0d1a0c0406050a0503100b070b0a0605030d0c06050903040312080916031e02011206170d0e0a060c03020a06 75
    0xa4a41610304c054a040c5000b030800c0c8415a410f00040100460020300403a0345003105060003d0810385d07400003150000d150309001440b59401a052103080034040903401c1d5170000444900c0f041d03030b44a40c2070205480b01134134469005440d4205d03550b03080d08404060000b490042c5400107003401d98200058814480d8102500c02c1200c23441340082c80f00303041c40c0d4039500c000d000c0c410518043c0791034030040880c0704a05c500401c000010010a11070f00c07410261500800d501680707240c6845a600f8240d612000544001109511701030b130000d402c0c1400b09905908240d05e8079a051040555260b10340a080000d000c12490700041002100250700d070344004041c040580d07100d0400380b03030014101307181c420400c42801203038a841c0c1040000800c1ea480001004044040f8a04201d88a00c0180d4004000c65001c1c0e2a040c1021750100f003491111142c02d0051000600720351440c0940308003034910407000303000c541c0c00c101c9000060001a016100200380f182c030070f20458240480c1c684a21084448900003003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 731832176 1250 731830926 731830973
    0x105030a1a1c06050f0f070c0602042c150a05090a0b041806150b0d020901090510030c0207120803010b070f050a030e03150c0a0e030c09090303061203030c0703031107 73
    0xc80500506114040d407045c0c60702d80400880c28030340c00d4021040401002d000c00c0020951600040206a80665005011410107403030b0300d1184140303034645021b10610220048010200003048000c0207090030021010240040219904040030300481c1e060040481540d140c50b200108215203541c82160314a0640030503501c41507140c1d2502c0410f440d441c90350501603d417518400d01c0742004480489150102e04007005a40c0c20050300141c51483c456800030784d0240406415900880d0540c000100c642525826105110780705c5000341d0001791a408040d00303120302070006000045c009002080290f000e0403088451400b19550a89048580c0c0800c400003035031160720b2803c0d070404100200c01e40c02e881c0e8071903200b0310703261000404d54010a06543c04124154a404d0455101071241070700c8241c003c1c010303402514202000070b640c4d174030503100503000d522006040b4803410408010b41b4060300a00c4032091030584d441d10b080b8003401e050f10980c0c0039030604120745000205242440d24070660501e600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 731833426 1250 731832176 731832229
    0x1030b13050f10050112050703090b090304060909050c09040507021f0c03060501020303160e0f0d0c080d0207060f05070c0e0f06010e0406060c1713230f0105030a1a 72
    0x8919108043d14100e2680c104807414440c80c4e800130918050781c04a00c000203601d694031b080c22000b41800701c0010301100c01010078842c680201100404c1541c1e203545400c1007007959040000d04480701140c8101b80c0c400180312480a07460290019608048a0720403596616040f540c1107450346840c1c02443c408640d1b0390144050f82d9094080c0030300610090000d107086140c80d01c012450b074043c40460702d00b049403480d40d11001c0c4e66040d0381858480d0010309528003a50991404080c0b8a003107000b0422244180796002654038400203071a400d40c1c5090380c8650034040e01c807e058520740c1000d0f1b4112981c41e985440400ca01c0700012000d8407030203143d20700210a0070400000b4086038aa07400f144c0c0120304003001030000c150001e00c5800c006074061200d84109441c0c0061132003a005030492407507200401c20f80040d0344146602c5140c004400501c0e030240049814040040300d04c0c1c24415a1701048041c00020f01c03400041e4171017401b4941c40e03490741c00250f14902c00684549403a18100104951120a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 731834532 1106 731833426 731833441
    0xc1d01030f020f07060b061908070201021e03060a05010e030309010e120d02071e15080402030f0601080a0309050607020105120406021905040501121a0f01030b1305 72
    0x20119250b403180c038030b14a4a0307132010005581c454109110010319181020442d48580030700101c40c1c0101c0c456040644104c10018009001c3d0b55003030008213101c841401000c46802001e1007007644d130f45000c03010084070719040c0c0c010354100607050078002ea19860000458403088404d08111052103451000144122040803280b1010301070242d001250075000640c00c0251425030403102100c81c8140249241c1c912144a0340c1c607100c144c0b0700541035007030003000c440b50094001760a907040c02e41c0c1c81802d54980303102a03001c0c038802d5201219600c24158481d04240c090002282d2282c500351040d00020014051064207042da42600da0129040007481d50443d415100c01c002d001d000928000d00250086c1c000e0701c159804204a04c00d803a050b403890707106501d00c0da00040c11030108881e4981c02c2c0300e50404401110b60600d5620741c41d04440340d036194090080302c412141d0200710307850f1000 = true := by decide +kernel

theorem cover : BRFrame.Cov 731654676 731834532 := by
  have h0 := BRFrame.cov_init 731654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 731654676 ≤ n) (h2 : n < 731834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
