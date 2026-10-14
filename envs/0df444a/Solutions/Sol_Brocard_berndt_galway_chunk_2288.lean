-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2288
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:15:00.312353+00:00
-- url     : https://prove2.me/submissions/47f2d776-8d1d-41a8-a4bf-7c696dbfb834

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 411330935 ≤ n < 411510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 411332185 1250 411330935 411330937
    0x30129010906051602060f07150902010806330705060108011406100c02012616031a030613020a0b180312070b060f010905120f07090209030709050901150b091212 71
    0xc0d80c11520720740e440411f0815505140500c4402414401d001c590807a400c9442c2e411026070580700b44e943d54015644e900070040000345449556401150089100c1861804c6420b050304a50b18004034908100b00d90740d401d0f2502000f40c100300700d20794568140030f81002e0612122500b22404440a101c141c1303010100502559402d480681040010303c0c1b4182c0756000c0f9920400700245584043c0045d14100d01400c4058840700e81d004000b034540b07080d4510400b2941c0d0161903801006010780781c84c0c0c0741c1c441111881c480084060341d101d00322a1000034a0a110030050014a0402a10401e0204000c0405080c00001604942c17074480401141b00041d080e802c400364800021a001c2120f00c0107100100d40c400810307000b2540200215005c1c5424600000704001003101c094200da14041d01c41c0702d5202a40245407002e41c260313010038001d0220740b5164001e80c4d400701c0d00800018080004180000000010b0703407001b40c000c3d400084680300d600301004800d00864140c0020510002e0b0360100d4001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 411333435 1250 411332185 411332227
    0x70b060a270506030a0201051e160609110a35030a0801080d051e0304060912021e161206290102010b01080708010902090310230f01050303120603012901090605 70
    0x83c403c04581c800d15501356007002d54030980322b01c003d041c107859501e240040003800c940c07000b5036000700d0900380340780c0624108115205031000354800c28502c3c180000c101c40d101c0008510141d8000340c0c016000f0031010204090403c1658a0f0703280806540344c0101c09080188200e80801000810019600314815200c090603903440000b440079070b255103d04110300100341d42d220003400f007070004249a107000e90008548680f030110f0312287c14000ba00301046540c541408aa600d060070440e04c1c104041d4403d400c0e4040010700402020070801e01d09078901c82502d1010010305c850381d00500c1c0c059015642441220020b080c2800c107400e0754244100c000e000035005102d00540d0035000503070b42a00b5181404440c80700c20880806010020000000601d054290700b040b065504624000920055200c0d881e1812142c007c0c000e1454204c40d24043ca58098005141641641d201d21032003210300f01109812800d81e8050840303404000302140010070702d486982c080340800c0300c180b01480c03241d1421020030791 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 411334685 1250 411333435 411333457
    0xe01050603150406030804090b03190611070c030c090c021912110724020601030b040609031103130e13022d0a08070801110a05070b060a270506030a020105 68
    0x307100c1d038900034410b12540e21144850f4015052640c00070401079654081c2c000d954040708244a403c045500341340c0d0720212025514111956070130b665000c9681c0da4800c1541079400e14105181482c1ea03150491004941e03032081303c2003c5450410800300070544141c1655490f80e202800304402e162949944008440d00050b00200c00007840420b034600444149010185400a1b10b0049a03682150400020008444110384401185226800d440405c107103041c0c030713400180008180c81d9910785100030031030840202c00f4031002c50081907288104001034090745e0088904503505038140104604420409880c5d560440381780c0d040180140d0718503560000d0f000c91a02645858500040c034078440139100c070f41240c1c001a101ca000b08507580049160b00c00d41d80001c00070301841a02c884d580c109480b402c4c2d0340c500012414040000015142d1a90036046840182000744031504e400c0c0210701c030f541c1040030100740c46000d211050305042034010305500c41170440140114074059000a040b510608001c14 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 411335935 1250 411334685 411334687
    0x70f0809100c03050916030206041418090102090a0801110702060d0b040e030403200109090209030c030303150114130b1308190614042d020d0308011505040e010506 72
    0x10310016040209440310700e80e280090000c00324050029008190666003601203000e10010b0044501d100d403030f0b480c100d90b40684142c2c5498a810309401c40c092020603095840100c0ba200d051851620940140c00ba10604000580c0d40b4460300800503060541d600000d56079042204441e81440d0300300a80e035401d901914103550b00c00f54071041c88000d0041c01d603130b580d10a2801d08149200080007000d481540e1053381e0b4030011001140784004442c0e0340b010302a000821549040c00948055000b400c0c1459000c2c0440c0c1d640d00c09440000d04540044132442401c15010702c0020b01580d00181e0b175074002448c582d4551920410341e1400384061030794001c03850903000014940040b0301140b10540010209030080d202ca050a806620f01000ca148005494007410a03260010031604404058000c0d54050480720b11403000120300d036504410111600c2c1d0346941c5070600805a210210f80741c491900ca950b6007c0d9941c100394400113104a81c5664808008083c00b0074410785940171303c6030741035900803580c107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 411337185 1250 411335935 411335941
    0x60c0c0503070806090d110703110112060e1918030c0c0b0a050301030b0c090d0b09100603110a0e15090402150d0608120c0616090f03030c020102010b09070f08 70
    0x5415400910361000340c0521500340d001500030782c0030a80c24001d4030000142da004585111013101c050100010300c01701c0e5001803508100050f06000c109004003c10304210045000c4441c0450171101c0d903901c60804181380000308110303d4200605181210341c1d842040000c0e0303640c0c840c4480e196449040060521240080507024024502494001480840f07030590796179880c04002001500280320494220102802040700980b501c000c0d1001400054950b00d09074904ce00c42042891001d0b0449003540213000c503600b0340000c180a2080518010350000408140c50424080c020350980d01c00301e18501c1040c02c2c80000c1c0110b0340c01217400d0500b210301c4592515035000003400c0000590703454059410010342c2d403d80c3d2003650080c00484840c101275804105070202011a43e20402c18035000941291000980440103a0540c901500a5140c4600710365143c55101c040075100c2c0e001031300800c111035006000c640c0d09000c0e51100c050181c41c2c3c04000d003030400c000b90200b4400416403051000340400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 411338435 1250 411337185 411337193
    0x10903020a0b3d06030905100903030b031b03060a06030221031b010506100807120f2d060f030b0103110d051605030c0303030103120807030f05070e01030509011401060c 74
    0x81030051207402c040e00c00c100c8190448903c0b06040c0d240891041001c600021080d00030b229004620380c1140181c0700c80e0000c4440b1100504142c08100d0601d5501c041c00d000944040008255000100c0309001d0105521010546840b000500342c40340316090100520050b00c0b54803006200510400001d054402804000b60642c0208090028040006040d05d6020b000540055008203020340b4204141a175200c4c4c1100c3c0a28100c03502da000c9600b00102240c1c0000c9684490112035000d24000350200075061510031010a9041c2c003c0710003860035800c8001e486c540701d594000c2c91038445c031010861641c0c4d5500041c1105100c05004416806403070440740d20b4807c004c1000560002c10788040071040110144c080c903d500455010707105240d0700a919003800002c4074140c9801080300c201c05802c400d4200cbe00350000500c2e070b204040d104c01140b04120050700509024490549074101000c400000050403940c1c001c8c02c3c810160305001801d5000d0070440c11031070640704680741c0700c1e40600150030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 411339685 1250 411338435 411338461
    0x1403121f051e090a0f050703050c0322020a030303050f07020106030515130c08062205060619030c09050a0f14010e0a02040803040e1618120f0b09010b010e0102010903020a0b 76
    0x596540080d000404c1110400782940002407220010504101a494400046045030310484207007848200070800700e140090a603030408046c01500402d4903002100d035001c5502c0c0020303035000b100826201e005110304103100040103a0b0180f403a200030811940355840d1240e030303401c0300750410fa040d0084102250103035080d480070072041c5e03401503502401c3c4c0e6510134905070340e500d048503141d0b0399228440c3c6020350381c1507006007000c8085c1c201c001444541c440008010740540c840e04542081d2082903000030007d4684d40f640402450420f50005492402a00800c1502c81ca40a50894a49001c0c220201e04465600d05410f640c9201000b51141d03031810840b00003445a500011114440403d002440c1020490983e102d88044210050600210001901e0810800d002442c04c821909000d00c0074094900005244074001c03840c1d032a1203076540c0c5402203500c0c0305031860030310380e5151070f180c680558214480078140402803008100d14019034500079118910082d0007890151140b02060350512040c0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 411340935 1250 411339685 411339739
    0x3032403170915032215050c2502040f15031103070e0a0f0b0906011706010306080106030f11090c07060203060f0d1a060306010807050f040905030307081b0f07030503040f1403121f05 80
    0x54101c4055002e03000c0e01001e40340c9809e03080348191b0400c0da6095084049001c3c10f0004d001c1160210036031411070780c822040304c806d00c0003070b90184569800028041146040e060103a0b0200200003600007000071440e0035580c503142209e0041782882e0500c032559074090300c904160300303101145a8031500c0b05030040b0040c00c2694000013140d0b013809408814851032003104c890b42803080600c1c84c030b00c00400003403005a10049800b0030744a1800c4c06031038082001c035002144d01207002030111030200035910004a201c1600d410a4401d40b0f501220890404115114140c01000460003411158503150406030b94148500455000300000e07400000917031220b80018184540c842c0950b0f46a01c0d00580080c58100100c40705045440e086d0305981e62001040200c0e021071380360420651400480d5203040e00c050713002070011140b1b8042085610003180806d07600d100740301040009190f039090100007030100c402003e003088911600c201128041c80c0b200301465030444400340c03445c401c49001c880f5480800c64103a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 411342185 1250 411340935 411340957
    0x10902060c0d0e0301111204030e04020f04050f0108330d1101090902070503090126010f1503050115200f070303032403170915032215050c 61
    0x21900080c1414082010024010b10380e45140104a0b004105426103ca040c1d00407004d80c000c10420301c03000041c6011300da01c2800b9007851010220701d000464200c0c5d12094140384400c20206d4144924600b075200108840000d19160105003480e269032881d640c2d900e0031445890325180c0e00194540c801e20b005a103801c5004256002c0192981000b0707000e0000051841d00041142c0c1010a03005002c3c800e440000750480c0085003803040c4107005584031100301440761a000610403182c100c854400c85183e0203440b45242c003400385032030a200043c071131000c46940d006140c00e040050000c0c410514051100d00c400c3d25102c000c44c25065000c0c800b01036290540350584c019414104a400300c0022100112032080d5001c0202c86508107201c030100c03141e24207107900229904410004544601d184031001e071411805186400200c07030004640e40f1400103001d1000c940803082000104200c07602c0806550070031413103518a0f81d256a03052104180c1c0580221299460021503022103030a0705441c0c0341c00c00c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 411343435 1250 411342185 411342187
    0x613031509030809030403051015050301090c030203010c0309110402030408090a0627031101030507140703020c121906020c07090c050c06071d040e10060605130b03070e1201090206 79
    0xc01000c540142402003001d5000c039902d540807804007880003080b14110ba811001a0013503100c0c0c030000c2e0780944113503031544407040c2d140c0034085120303507003845120340a0307214000702c0d40054136510516096400b614081c1061510704002c0a0100e0441113550304030000444005a82e40c2e960303e07101d04e4500030001203e40060a0071030200700c094020005c00401019009000385c2502540c0074000c2c200319034000146000360584420040c0e50182d0411074105501d0700300620f502201032a052980d400c8020140d0050b440743c621400300b410486000b4403284605006041d0700810115150b4404030a07130030003003426a0003e144001d016080c4840e80240050440074084405000300080068001501d07096460041c2c2001ca0a82c0d80104141030202c0602c03040340707003075084060800c002082c01c50b003168003601070000313410030400c208c3c402c05010b400c0e5512441d4039078071160100c1c1c00464080e006041c00010400c244004c141d001284200c9504046402003ca072890540d000e001d003480107002504524 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 411344685 1250 411343435 411343463
    0x90509040519051605040b061603230406030b03070605040b1803160e0609090607050903010207150e070e040503040b0f0d0c0e030c031c0f1803120809011406061303 72
    0xc404101d20850724840c0c0d100c4c400c1c00703458100300710071103107a0000107501c00e070300704194070710364441c101e50000040c003d0410440d1104c0c810b0741080c0300c0c512401d1011407401c0010b01400304075014807a64075101010383c004c0c240380d0f0810784080c102d40300b40c1c090700c10555000306090340410700300712a000d00703010081e003903410000900090142d80a0f42d800345004244034180040c0c507a0802c844014418018003004181d203407603981050360a0350010020030b03019502004880c0100e0024880380131650144c04001482d582d00e1603c003410036020343c00c01c0155119150501c80031490000c19502036807600401103540d076401c8a43d003591f511802071500151414001c0383c919080e00980d00c00e10f000026001d41d003035030464004254079200106204000b0703040c0002c515100500c50440b441540c2658140305508a444110b07845051582c2d500480c1d602e080c0c1e01c0030001d41688022025006680c1900901c40c2111050f540302540780020065802001d0114014140c02400c0c0aa0f000441c3c0200c3c998441507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 411345935 1250 411344685 411344693
    0xc030306040501090b0306070e1504170717030f0a0905030d030506040b0d2a0e040b011d0c03040f03090b0409060f0f0602100f060e0720030a090509040519 68
    0x5041210214071071072400c0300015a4401e140100c045220313005001c1d000980d03030321600360380d412030495100341c014003885c90880d581c0c08841c1c001c0014054114904003c1c104450000d441c1100d5908410f04c542c0c2e41c01c0c5c018240717520000a58442c000c2d4121000d4490b0103540084480d50066400141e2501c03c0e40c55840c00c0540507840383e03006840607242404255001c3c000d0080614120303000420b0307804001c0b2054900d099402e40c000880c0c64980d0b00301c995a0750303038607440e032105010766055840b01382000040000e0743e80211456aa0b85030395101600a02c1c100c040203180780402403000e80303e040d00035220410144607100e090701a11480b41c1da2a110358454883c1c6005100602407114014540403000c00d684c103c0200c032030b08541d4568000c14500d440002d1840c080c1c03043d000c80d1400c141e2141c001041d2100c19144061007a003295076807001035031000c6c0741004154120701c8000e046810800c89a040340f54000c403e807042d02c0c8284ca104005d601d80703190507131501c2816103407a0300080700c13460400104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 411347185 1250 411345935 411345937
    0x706020c011a0a05040902060c0f1c0306031e03270303120203041101180b03040f0201120c02031e0c0d050703090617040b0c070203120301050a0b091e030f01020c03 72
    0x80d204400007000881c0311200e014840342400d0b4074081d4015101e40c001c0245107080c0e00851150740c0701508990504070660482461b0250260301900b8540200070044d0802c1c41d00145565144d00300e00d014040c080c030716203601000c601c0201c0d00340d080c45883c21062007810f00990801851007080c2c020181643c182d528020b10351407150004070b001600d03084180700701c2002802030340c1c00f5136040b69061015010600043d5246450070846011001030070500003a5898882d0186220340c1c026a08081208014400108103403900e0441491103860007081c0300030280d001040d585008951000c2d201c40203003038001c80e1154050014450303828852201c180190540c000044d040b03561080c1c4401d0107030798580f14241c81070b4501c05044036280c4c01c0ea40002c1e002c0741a41d0660364104604000c42c502e404003d4010a040c41d4640856a4070070038000010403c1e4102002905e0060002a01890519800100040c403124680408044029000d5030040047d602440071a0b020030300c0c00700841d80d6043e1243c03a1a12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 411348435 1250 411347185 411347197
    0x31701080f0705041e180510020405150717090102010e120c0105070206010803180d0203030a090e010b09091503070b072108090c010815130204030c140d06091106070602 74
    0x202e000304440000d1a0500d4003544941810b00c181c1d9030381d001c0c1101420002010381000240399208034441d8017010800034041c0c54100d054240000d81e8450500052214070910724041d00034001042013040041020450750704001040038003500d40c1c4400850040307000d040f915000580324041d81040c040001c500d8801407618141e144028401680e035560166107488091242102e40c0e0001c01602139983c0d44a080150031100c000c004d100421081c4d00444d20750b4000740030041c0801c03c80c0c4030a00a00b95a42d520500402c200c1c401c2038074203515580410b40c5444050301200010b1400500514180e400b070100c0405001242809611480c2030704103400403214444200340314844a58103400d0300e40c8104490352041c0d221100401c4185074800c0112800308004203940448074044075003100c00e40d04c0c4d91208100300e070420710150300c1e2400c40c18280100100395109034882035000818a401d0b4440000200e0100d40101e4001365408030b40c100040c1c49442c4442080d40080006034140401c030890303000d010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 411349685 1250 411348435 411348463
    0x240902041803091202030a080f1b0f0a0201120906020307021e12030c0a090b0307020a03110706080f07090b1204060b030606090a0b01020a020d06051617040f03170108 73
    0xc444259150403992a02210000d000241c4482e000d00000b1100d05850762550301c043c0407220040c00c2c7d6252004290000c12201034540e070b001402109107001d61003a056402a014090800d10714401103040d511410000000e0600102d41203000d1460215800481ea00c2d0b08903c06540e0382c603000130000e4a038160408010030030584a0304100d00000d0009108104049003440f0b54a15280c00980400d41e8110165900410417522008604441824060350040000c0e13002041009480d2034040c1164038484050849036101c0c034000c0144030750100400d0341040400550401e5600d8502007110407682030b42006054820015480b040300117801c03c91442a80109800c000410b8403008054035554103850182d0310100788808580e12440c150301404403190305004a034041e088030307400f1407004410342c03c0650300c00d5942d40c20040c26040030f05040282d91100e00d440c4d40c0b0011110700210002001901c080d05890800328404c0c1014000c100d201030288504000304401d60f03560070401d503114041d0001710 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 411350935 1250 411349685 411349691
    0xc040507020a1e030e090406090c06050406230a03021c112a0c01031d06010f0e06030604120c1a0a1521020909120c03130f0303120924090204 62
    0x1070f407003e08007006805065042c0d507130034500d104040801030b01a20241064400b941c1d81c01150000900b9410201c006202c2c6464407501c0700c0c45c000001d480c68969502104044003d9156070600e0031411040381e05454041c01d0051b203540d89000b07404112125500c0c403154243c81c068220700400c0c1e104000d403c410102c4541c44508a030b0510742c5010800e00100c4803911680407103080255076001e50090124001130802162689000d9060070745000e1081c2d200340091454064103000e000010304900707034448020b4006082d2030034035903a007014000a003070118041056400d0000304100240c0b1061003c9404841c2e80c1125080c030744a903c2c02440362100400a0201681c0009041800200c103400c07230001c0d00d028a80c0c212020380038492084c80040400707030039005140c1202502d030884800b610700200c1030402180c803841843c0010703030006500e8100c0704011005050070800a5844200c0b48244584000c0101c4c0c4054185040064100d1407010000800560000301c00c0781602a4025101280212028 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 411352185 1250 411350935 411350963
    0x130801051603091212020913050a0f140103032a05031201050405010b1c0216050a030e010203030f01210804060c0b01121a04110301050f0f06010207061b02030c040507020a 75
    0x40e800c907404014020300c0b1524031607071001c811740501404001000d82100140c83c04011038001000c25010019960001d60b44200b0310110401d00e2040344034140e0805400c01181a6218440450540501c030080420032860b80542404a0782400603110030f0b00c10841d11020900c0d882e000740c0301d40040c820301c0c420740d074400c00005441c602801141d040300c2c010311081f8940405003400011108000d0303c0300c2c1701c0c0c580820983c00054801d140ba040180c1c0110060541540d0a1400900a0801013072150440d4014014481c40c201c038080c80c64116440f0303c9090b4942c403030480303660302e002a06840240c03040801080004400ea04414055201072051041602517070720f42c00b09524000320500040c0101d6100030051540709203501006400502034000d01c0498400c0c0400242500c0741200d940503c85054001e10034940508013080f03800c500240041c0421504003d80281910f6903d4214a00400b90003084000c0d903d0070b000100420704090024001c81c0341002c03002c3e50b5044c1240d42120040000b40744 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 411353435 1250 411352185 411352187
    0xb01170f12041406070b070c021c0213090620190801080d0c1a01090218010f0e190305031206013507090801020a020607080a020c0a020d06021308010516 67
    0x422040c0c80704201e20103081c0360900c2400c410352100d00788041e4001d0b20400031000800e8290a045210b40c0742e80d5115682c24006105210000841c81c1500c0c01c92130f00c030100300c801a540e036044884e078000c10480001d1041c505080080140911000001000715480240303110100140001e10040c2c02c030f02d40d032400c0f104080204940c2d5a00034441d800154002c41c0c540302010b48912191103c990003071400b20031000c2c1c1e10400004017602070340040710b51035001403550740044280c00a040d0448090038510396404568201a00f0f81d81ca4100c002c1c440c4035540454a90821b44412140103941c10004690f126130124002c5c00204c60155902d45c082903410008030000d10081003031801e1038038207011201d107009860217401c142e00c0c4003034804018451014004038508800b480605450a0254018500f0342000000a0003039a4040c152081c84d5004003c401d020701c00019160301c0c460782c10707150403500307155134207006009009800070414010340b0745800150302d440542003030b03008405940b442c0c4842506044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 411354685 1250 411353435 411353443
    0x51017100302030c061b0304090204030615060804020906040f0c030b0405060f061b0304150806040605091b160b10170a030807050711040e03070b0c0711100504030b01170f 75
    0x1c0000e602d40e201c00041134203030030507101502c0700c040c2d01340714885600d041444140c21504946c1040740e80503070108080041c00290b01614160346486040351882e00d00341030009144502c02480a07010350342c0c00300030454070b40310344d07204104003500108100000c07140150020051f03c0c03082e4042c3d00c2242040017240691500440c4050801c400500c180e2504401c101c09010717099400c5510712040c08280000251512600c8042ea04988250b880c1c10152078250f0410040760890740100d4000e40303c120410803407002191581c2d44803585110030684071007281c0011001c5c8400018000c01c03030b000a201380907000e40d0102e445000e60301c00c20781b000d90807200078407400d9a40040c00406000a13142c03c002c80c1c0300d5801940106681030146d1a0040d0030107038500410140e07400b01030484405d5100040700814400c440426603040000c0000071403400000e03485011000e505072180c00e00c0f4440550200b0002d81c0583d045400465001c913100a807903955a0302c511401c2c443c1c4504411a00500110170780e4444081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 411355935 1250 411354685 411354689
    0xc060605040c050a110705180109140103030f05090a180e060a050618070507120207090e070503070306020a1701030f120f02060115020a1a0402041113050607020a05101710 75
    0x6650035013860030ba4481260340000000210859000351100494079803103007405c83c00100c40f80c40300c2400d036501d040708280494003003a41c8500505111401400020352140461a2241c0d192a042e9100d400410000702003a416510414100c03880f045464810380207600480c45a4821a050350703125541d00680205847d001c03550141d0040c850040340703e0800c003001109400030414540fa5080c004c241d6100011600074100181c0982e100780c40410901c2c8c03440c00b440600c40608001f8010891400b804039a4412941c04010540c0d90081464140f09114107903003841d40360000841400b559481c14649000802a01c00b9100102c0f03440c07a001580e4003910138401c82965030b50060841e60b10b015004411418801401d40840c090201042e020403040440b044040b48140c5c0c1d4401a4249032040000700c45800c0040101c25002b84002904501140d0199040b100b050350b00c142d903140d040c800614500b40581046501c41510b03c100d000703459028815076a09203080e041150f0325198481143e503210307018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 411357185 1250 411355935 411355937
    0xf010b0612010519090203180f07050102120a0513030309081006050310270302010506030d090305150a110c060402040501050405060d170c010e0d020d050418090309050306070c060605040c 82
    0x111004112a00f0329018946a6943e0b0401e04120702c5d4503080c03a00d040e80e2003607445024905081d214480303003010078000d60705d0a244400081403000c0c0380a0010752644000700e60481c0458000c00c9081d0742c24007480c200c814424401103000c3c10107850b40390207050342c2003034041c1442622400c0c101000010040c8601001d0710001401010256503d80b40a009040c0d0300300c01140c180d01d04a050141c50b0480a0380f10280e9202c0c0d00041810300e040300500d447d04000c180d40303408000b120f03002080840c40124441c020424212018001c580e60410700382c02034840e0340760419401c0000038041410103808918580035900c00c55041c41940d98070020002521800e803090b030780c40341600300c4800c0080d00b0751070f95629136035401700c4032130400c44031008032801c640d01070b05007003025001081e85011a03607060281c0d0740141ca030382c1032542c01c160400a03031a0041c880068900070240c3ea400070034090500550421005013001401c43d0100c2c6845140103200c408802c0301111100d0402c00041080d24290107490403c51071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 411358435 1250 411357185 411357217
    0xd0509010914040f0204091e2a0504050d06050601020d09230f0a060206071e0804020f01032d0b0409050a0b060d06140f060d0327050a080f010b06 64
    0x24801d100c0b00402c002c1194a51003940d42041501690583c0050001000356070000a92121a580c40301604110304800d08541d900d80280c040946070326414240d10342d4600c80c0d0f07540740c50003800b00540e181d109035044250302c001c80d8207042c020403a640c5c004034410310081e400c4c1e4240300c1420500b075038100828094000300e491828184e46800070440c0e51040d801000400416588032404041381c3c01d110380303030440c80050b0400410410a01c0d0802002c000c4036601c2040004114141d0000401d181c1c3c001e13100920603c03050b204d014241c3c3c800d42151481030403520b001e0468503012034066885078040c010a6401e0360030000c02d04582d01d001e20580c10701540100140104000035601c49100c070328000c254a60200b44800c240d4081006842004c00d11700d640c140398002420b0803c2d1403203104000810207031084040300d00560009601252192060114540e154030a44507405565007510301500155000340e50914006044c15000031810030b04400300000704590b001c6c40f82401071070320030100304c0804200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 411359685 1250 411358435 411358439
    0x1030b030312181204030c0801050c0c0307020f12030c0c010f02011e0b030a0c0f09112b020415080406050f011203180302060307200102090310050a15080d020d05090109 74
    0x1030b0032090103c8000c0005a4622413403900c1c40e00d82ca50400d401c260b6154101040620100b4424031640ea04074800a0906041c46211281250340303100c2c1d001c000b40152100356000c0e506444003a5240c240305001415262102d0121401b01c0e6500480c3c4020340c009007a503044d158280340103201d82c0800d5a99160303c4140c80ca5409003200c00b07002d085078011742500c51a280a4040740c072021410010b00310b40d1642214062405042906030781094110484102040103060803150f201641004500c04280d072200c4408a101c0546000f070255512410600d2350100070740e140c56505c8526584600d2081008200e182c460400e0100111002d01541c95801c101e2a0130601080c041d0462521728a0300c81b8807203010315169804551145c0040c0c071040d01082d60007070011070401243c10310002000848000318146031070b41d0700283d6100c042424181c10143d0321004603000c4616608030802618061029109103030307035000341c2d9a9039106440004014040c15801501d02841807046401c10035050b99a456024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 411360935 1250 411359685 411359701
    0x5060c031005010c0f0c03080a0207061b120903060e0106050910050102070501050d06080115050f090903160c05040219120504050d08090115060e180c041a1605070501030b030312 78
    0x160403040145c4004c03004c0040e00f00007810700e003c5480550300c5444101c0d1a234900d0a40079190034000d420860a114010002c81c0351688102e0368840000d8004809400d14294841c0c01c0da020401c9400142c01d103410f080884140413015049403040f100c00b070301c08484654a0100405200c40a402418016000040100240d41c403d0000d0b00119039001000034507070b42e4070214070b4212825076106080503c00b4032401c05c0585400720308111580020340e50641c40d0724190f500d1b5a141e00c2860014000d4030282d44002c4c0c01d0014000c80c0102030500900210750701c103001306000682030030000c000c4001407010311b1107030300700c040900441e40134a13441401032403544003582e0300382c3c1c0246000701108980c1d0340c4c803d01000b0344481580d44000030246510740c40c0360401048240706c0d440d0341da41030700f03407203006514107000040010200300c40890740f0b5000324103031180008070140150f125144c030805c0c10040141c0003005019001c034123030b030448809807010452824000103050b12405000c4464042d0082c03903000a40742 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 411362185 1250 411360935 411360947
    0x30509060c03091507090f0501110d0503090102210619240e04090b0106140c0a020d14030315041406010c030e01020c1008040b06012a051e0a05060c03100501 69
    0x8600e40c02c1d13810442c0a4080445400c0d41107404c540090b6048508101804495240354040c0000703203001d010030301c0c00c1000746d65100f0088e8401d80400c680007000902c441e10a505070341e9482c4240c0c40390311070413031507400d24040c0f080d007642c0442c8034060681100e40b20500c466080001c443c04a403090340e1000c508681c40110700c0a4802c4101031100700819095507680ea0700c10340451038800d8032a2040b6504002004112180d881018170b07405504000556060780c00040500030264100e0b60310640501e01e10b01182110042440809035200c04418801071186001002ca83c100c42901c0030003801c0881c010b02c42d0f00a20680d41c2d507010800c55203660380800c0c800e002801425006004580000311041c02113030082d81c101079180001641c1106000030400c02d094255000030007440c0c400da102801c40700c5849001c10b0315010500b622031142075801000418481250449101589003144d28038007562103468032410b9001322018090a000500c8540c0c5210130b40e801003000c0b010181031141010015561307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 411363435 1250 411362185 411362191
    0x60501230f0405130504060f02253f030207120302030a090c08010f050105100f0c05010608070f0806060306070e0d02060c0607050a0809071212180b19030509060c03 72
    0x1010700c00700408611034a40c2e104e00559403a00401c0041c0925081c281101182c01983c650203a080c0100a103189c4060080c5044c1c0e0b81e02c104124941003043c0320701d040c01c800d4940c03c44000000d10b030030303c0441582243d2000f140e400984c05611410251035010304804910440d035000b0700c060040005010240c0c0700383d000d5544110303032480005003c03403d43c0b0768007407a44e01940311070b10903915048081201d81c035501811340140011794180356040350119002c0d145203280e14540003004502c04940050200940004006094440541d20320f951501d10f016030040c2a40544c82180c0300e00c50110f5400d00340010101d00c101840d13030f21440c004034003408004014071820010b9034801000e01440030b4091043c8051401644280c80b840c2d640c01700400d0207088480c00070138004041d04007960802281c226405040d104030341c84400005014130101060324480a03184070a5051219183c000c28100e04901c01040304d41c01c01c94180c0c0100200140890503a0411100c044242e003005001c078056083c90009160 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 411364685 1250 411363435 411363457
    0x906060602070810061a1c110a030f050603031e0412050606010807020c0108150a0f0902030115022107031b0303051009020c03221d0a14090a0f0309120803090106050123 74
    0x181000000c0a47c00503500075064444500d000040c801d800d403600b51041ca071400314070384800d00041c40c0943c00a5200c0c0210240358541c030014160200c45092003008a6024260100c0781d038480045900b052a80c031b00713084494602182c030820216041c14000220b00c00d00600580d5000080c0c0d440d00e030040510000b19865680169103210085010700811000d800a01100c800042c0c980d8540790355440e22840c904d0200d82507400524100d03040380c00340305003924400482130500b6a100d459141c101c40c1c080c01c2c0240441000840107503042050350541100317004030004800d055440e038880304810100d20410194041c203610410804e00a40e003515000d00f012590b500d80e240145580c2c1c1c508074296022141c1c0e212032901d502c000c00042030741c24820401e210b01a403007e040b00317240070722031aa0f1b10b540001000e84070102404500d02010f12424a603009030460304200300280d1040e00d00744082c1d4109070359121003542000c40204981d44103c013890180c440c03560400c0b01900103400081025408009036103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 411365935 1250 411364685 411364717
    0x120a08070923032e060f05090c090607080c0a021f091a0d0915050903070c14040b19030204180b0103080c010207050102070308040516030b0105130906060602070810061a 74
    0xb113103000090301c040c0d039281800b980344001c60b81180109000c807240c582214122807202c0c54103004a45403411020b03401428101c45a542c1c0741041d0008400c0d00a01c4e100404811001441245428001c074407124014401d5030383c1e6040d203038605092143e8030800c1701083c00140e4080780801011546404005204000f00c205c2482c21032150404c3c130a440400700140c0d140003d018440c00c01d10b00074400c099000d100b0002031420005a55508401c2c00c01382d2081a410f5000d40d10038440d0380c1e480344d1104400700e2004100b012402e0300742c020600d20389094030099105074034288400141c4d51402004807249a44415900348603829036517240304540080d60482e071107650a220950004000f403000b0211107000b515000214501858054130f0030f0400b80c030401200d40b040c4420000221744039074040c15142c0450b02e1040724040100b29000901c0c0c3e0100240545080075400074036690013041e4841901c000381f0a0707820000f403e428034070907a9054402d14001d01134880211920000260142c140e005104150b8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 411367185 1250 411365935 411365953
    0xf1b0509010c110a27020a0909091a0103060e1203041e260301030b0601030e0d120207060f0b1503070c02040b010c1a0703051501090e130203120a0807092303 69
    0x202c0c0003602c40f80c102160703070a07000c41c50090080c908440303141c0c03817200400c095107005440e82c0000c0000409118107100e00d51035400810420240c100380c901074902110285800d0760b56420048003404000d0302450080c0030342801e089003800060212445070ba045803110410003c0c0203020000104201c2e0b0036600e61110588550034070f03c40511b4a00c0c001d607076001c16616541182007480c40e0400160855042c140b030202d1103d401140031030190440882800e00780c4a0005509c4100040c0c42031500040c0030918000c0c000c11511000d0303110038a1044141d441011004241c00c3e42e085510003903030a0008100309129040041c64590803030180c1c00f20625100154041d01da944003444a42d45c800b080002d03030f01d10104400141d0520402e0f40c4086040340c125804521200041d20603801130094030040c020070000658610310b002480c0d80380c40c0d40039041340c40e2036440742600311241e048074603004001251480131482441c8a00360750019560308442c1090240c0107600480c25091045103415014000c1c6108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 411368435 1250 411367185 411367189
    0x1e1b0f081b060f04030c240c091d04030813020315070f0f0926120a05030708100f0501111606090515072d02060d0f1b0509010c11 57
    0x1d0149101e400600500101e408007501c0c1c10000c00a108128041d0550704102c00300b540880b076004a0750700300410388142d144140112016030b000f8500155500c1c1042d9400758580d1707011034110120385210959022602d40010b084010660035070f0003500148030003001c46c00d001c1011a0700112180f0003011182c10400507043c0e11840c00f02100c050010900c0c080002001c40d81064001e010300740036207840854103041902c11604102c210390004e0302d501003000d80142c010b10400100b090190304002c41500e07113100e400f0041c020343c004c446180c002070803040804d105002030000c52040d100040004000107007041700449018024a4a00146104142d0f640e600081007109501c003500380d659035142d200341400700740110f0b03050100680c44450410007450740460b0ae250f990044440c5190b05c450f25180040220300305d10f00042c10701a502a8000a1011400c00c1640c09907803181d4a081045c8903852035900442000f0900b0b02c1e0b00c6c4003290b42040041c80741d601c03540c2d421390100d200c0d02c41d80010300d80c4440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 411369685 1250 411368435 411368437
    0x604031206091e0509060c03070c020a08031614030a1d0102160e060102010c140901110f0d120b0d05100507270303020c03030301060f050a0c14060105011e1b0f08 71
    0x6031610803400580f81c54034000103907004880d4003c1103000104501d051a81c0c3c202c2c007d1100030002c4041141040340c507400c41d65200c0d0024001d000501c210b80d1607050030309200100e41200725040368940c02c0c4c40b106129111003c07081d152180c8280c1c0358080781410b190241400c200080100cc0e0440c0108004450b03843c90852a081c0076060b2100222158641a000603007196010045d017420300c0300451600051840d101d04540d080c142c20300e440002c00e08541000340c54403141c01380f17001003402281003850003640d001290103d40c20226005004192501d024040c3c54500d8504c00b410940084004012443c402d8200f940c00c098186440c2d2942d4140c1c42c0f1100e05000e0039580381d9002d22803031008105150f810002c003680d40c00100e0245140d545405405441403000004180601c840410020306190141d0781c00140c45411840c1d5050a0441a04603500c070361090150301c2c00f01d02d2003480c585400300c4580005404100b20703210345081c155850600110a5240391041303c0007004e5102504c002102c0030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 411370935 1250 411369685 411369701
    0x5160806100e0d0311010c021504080c12030406020304050618030304061d010204080c100302040e131506080a030f031a0607170f04060306050603060604030201030c1206060f080907050102060403120609 88
    0x80e803421480d004401c01795095907507820890007154007445d1807140c041084d92203a0b07001030348140f202c0e80d00c2c1001c4104070705107910311121020400c0301000304010f1101e250003d5105611940c250307041030760f800400c122800e0400944030000c0c5d0052000800056140d40051410390410200c20a41454a400746d426a1311907000110243c014401f90001424107105090031000e03941410341c00c250505001c0040d0000050812010001e0b0324561010311582d8030203040b64080c0b405040c03040e0341c0c0350b28040e03a483c079440c00c00300c0c0064058840081070609ca44107041d0076819011041c0040c00e8001c007003010b550444041945c1d511800030010460620a2005058034038003101e6941c4c81c1c80c0303081005011103070540e010a0240c1d00030070420010795031300f4013110156503090078001810140c0d00804c07242003400010000c040d51a0030b101041c0b450f0012903217159000959038242c1c0700d9444201483c0c60b10040e2040c540540d100301c01040020707005035601110001d54002c009941d40c2c3c0e405800060326104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 411372185 1250 411370935 411370937
    0x10e060411042d02130f03111302090604121109041e0312090515130206070602071112010b0f0d0209010501050a1202132117031306060b0c0105160806100e0d03 70
    0x52806080c40400c20500000c0caa2204082030380303441c580710b903480408d0503008140300361000030060b612201c4a0341900c140020145c600c83d1210340f0f4100300c1044200000040d40c115841c80d0725810f1a10300700c11964419648a1042c502c40da0013941000102c02030600c048040c03022400040c49040c00a100302801d5a005100601d8a21040c100f00d1103040c201400407508c20780e40202d50030241e03c400d02143c0806a00500060755010b0f941800ba0040c010080402d5000c0360b44801045000b605410400c04d00000705c580a9640940004008130f1100042d4021340081c00c00b0010000c80d1f01072005091410a40c2c1000c0e5440e00403c0070200c2240e0100c00f41c00c108081140c014022a08130004518403c0c03010f051a6620003083e440d80c500350000d00101182824000000508100d4550650009264800341c1404035640f64000c113013054019401c000441d618080000b100c002107801c07100c1c0c0d080042e80b00c144060300d414045c080d268501c0c40c5000c090000c1301d00c100f0f860352200f001c524110f50103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 411373435 1250 411372185 411372187
    0x80604021e0906040314100b270601030b03030a030f1505030a020603040305190c11101b03050c0313141c030c02181503011401060f03020c1c11010e060411042d02 71
    0x21454101040750143c4481c8d40c00340c941c0b26808142c2c00c40361188411040340b103400420155403880c00480c00b4155203404140c05010100d508900580c00d0380158034466151f100c24840c0d18242174080c8841c0c9070600c0b50aa040e8030164500003d0305068009540050003440d00b00e02e8615164200c1034005143d51800300000e03031030602407080c081f6980070500c1028044941d9400c001ca81200106118681c103c40080750307038038100c10702c1050700500c00c8551003485081641d0704d0b11002c00d22206000c2e040d101d180384103203000b2107150851034948940040c94400812100d81c44505850454862400d0417040b03030448440c08100720561404209a07200d012500580386602c950034040c0760075030b1064010255150a000c3c01440941e4010003101c3c1c0359491441c00580740d0030010701c06482d20300301d03101c0725900b41551481404401d1380210000b10351801c0d100240148030000782c03819034480049801401e249000c60f00f80d000e41ca001d4202c03102c4500c20781e4030070f1008000032842c1c401310003207000d0001e0080d034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 411374685 1250 411373435 411373453
    0x403020604030b010806060405060105071407030b1504060906062a0609060b100315290301141005070816081201060831121716080604021e0906040314 66
    0x8080140947c000c406903018805810401700280581c060184020301004030885082c0580e03c0400ca504000d68007c4d00505503070400a5040d034190005107007481c052420242c0220340046203000d104c0c2110324998507041ca45400120315100d511280350303485d420f40c0c00f044864000c10220700901603403a029800020303203101c8043c10440d1030140b2240c40b0091609065401d1103801c46d032107a0310210360506540c881d0996a03044240d120355803064003841c0e100008000403c02c81100c2c0c000d11111041500c0c00340082c030600005580324000c0040050182008101603082c2c00c4031000702c0c00350141711b124a80d09202405150020190090704014005080d480c20810000c00203a10b09807031200c000c8a9000b100107054020f016111803c0c405440c134016001802c81551003107220364003210040c03810802604006a800c1c590301298848800061b00345400306a1900d00391080f0781c0c00409412980403600202402c14100780c1000c0344803a84203800b0f01000011030701c4005000b0510641c1c4000e40312101c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 411375935 1250 411374685 411374699
    0x40f03060b240a03140f070f020a15050f011211010507020a0939090504090201090302150405030115080c1513240905150c19060c08280b060403020604030b01 69
    0x10710041717424600c01e669401404902070201725103e800803110f1811821100249005078601001c43c90010301000d40c04072002d2140409601c014011088440c01001c9039a803a159514282c400481c0a005242240d400104942c002c50040160324806040003d205944040005c12503600070104800e000c03003180c5026400c0a4001540072400344100610300c0c8490000005040828030300a00d070285a40f103035044d00303680c0103081103001198001c10b41d0019a40d02d11105000e50014410b00380030b503003044085c20003081858032240c00c1d1000d42000b01400003949003003040450320184408880c20f02041a10036045d011268040607128001d2441d02c2c143c0e2780f15030354030b0700f0081e42c840c04100b100d5100d0a100c666a5140100100e407500c4050300d84070440c900f0b92a081a054420044c40804030f141c0c19004c00007150004003183c07000761990b03040e6a84481240c0c2625a0042c3c8000e10b00c4c20650070b5140044507544075000b040b4002d0515030800c0c0c0ca960100b0b5641c0d0154100707980c00300004004102d90 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 411377185 1250 411375935 411375941
    0xc020c04050115080c0a021b040b04060b1b070e060d020406080d0203040611190f061b2601050108071218050c0a06050901050306041e11030702010e03040f03060b240a03 74
    0x1c00703000303180391810301508002921584040082c0c23105401d5408411a2603540d6040b000f581007008004021481c1e59500c0c144c4160300401050b03184944684410f1f04911010520200b21603500000901513900e110800094070700b50307901264023558510020071591002c115071814202c3d641c00465440b418640003030004002c902d89148142d10540c4911481441e03140700340c840903400050203040c0d1426123000c1001e0200d503180b04c59000d207401d0181c00b007280c2c003283c103d80c02d500841c03c06001c81c0d56000c0380100c613042402613502140c07a01000c5400e040c80b404500c03148511000700098ad0546000001607c400c00110a8901d5400f9801000852409005000c0141403a05059103060401e40019220340001000c9a110381c1c2e9541c90420f101442080b00785001c2e0910404001c1c0400c1e10a0003c90b94105031441c00066290919800305072100108507406d6031031080c407401c0c505203545d0350344000c0e00b0040075507600402c000040c104005000e0381112400111944115113030040303000d001b004c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 411378435 1250 411377185 411377191
    0x60e0106060e04231803070c0905060f030d050d090c0807090c080124090302031e060604090503030606160b09011a0a14151e07020307050909100c020c0405011508 71
    0x300300c3c0b601c44011310354019040700580301c5039280c141003c60f5940d0801071440214580c07612400d030100280c094200302c01295280c0030748141c035a00700a180c640500703104910054003071040e0140d00401444208902840240110b44490500804c0c0b4160715a43c01074121425404011a40d00c505000d00044801d80100e40d80d00e005840c00c220030350716011815030b000750700c903182000c00340300c0c1881009103501c21510030028580150031103c03142c6804d0500ac40040321840140c046001d03c0c0301080380d626142c0110520345400200070350440d01d6079403c12940f41d100d8055003140d4401425140300041440d04102d120762204000020003607180c0c9031541d06051401032130351084280d84e0061007010000804460b40d468203035580309442208031440f0455108000c0e036844003d0048090403180b082c2d003801050620b200790b05072407a641ea150140464801d01f91548440c5070011080f01c04221060b5005405440301c910444202140c61000300d0105c490a80000044a4109802d020324079006650380b50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 411379685 1250 411378435 411378439
    0xb04050c0909071a0409051503010606110703031b060c020303041a0103030906080411063103170703021507080612060c03070e030a1403070519050304051507060e0106060e 75
    0x806240c101d840940b11800ea000300139150040402168000c20148144c0d0042c0c00005400c0106007425100300322201200b07041c1d54030039800c0c00e40c0810310512512448032550a18002061180e0540d503043c0c420b24400050001e07001800000b03c070124101d402416150388050b0003a60f62801c03d820410400704841c02c8002052400900410002c0d078403c080701d088500030b2806c464191200c1c0b03840c0034952110140294002000b06000030540c410a50f003010700362600740c912803800c2c07202d900407424250511015011218408484071440750001c010f000d803521910594202d0300011403a1500000300740d0380d0200090f803c800300329907418180d1a50480d120404020320083c600026503080c180b000505502c204404a48140000e480822004400b00d601090540542c6080c42040c4d0b56038100e0700050b0f510303108880c40400132192070419114030716000405580740c2803c0805000c002d00586111880f00a020405000401ea030b074898440036036541c81c004103040c2d02d0214020441c40703400702c8a038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 411380935 1250 411379685 411379699
    0x90303080f01080c01030b120f06060406170604110a0e070914090423120c0a0302011817070c230906030d080f0402010512010914130503120c0c0a0b04050c 68
    0x2018905002903503107540113091801055140c2e03000042411100b410212030f40340e110f09003024000210200300d9510542090342d08210890382d491140c85c1c24079510100c00016009200810041803800001e10609030015100076080355a62101c00600602100d030394000804080302401600e12101d50340401c0d11007120070a40d28101030715000c4c1c5544520070701c4200c50304c040340030090b4520148100000c101c941e9101e03a1f00e4014080a4644803031450314102c0040d440c06818844034201a0504808075800518804240300d4461945465a010304000e4407203d44202d030000d03841000758030861080341d5107404080b0f03050a803818003990741405041c05210740c000900d1190403a82c40254680e02c008038a006030901c0d240c40c00141c070b0a1180c0c00c000303041203105200101c2c600003240c02032100c030001c1f2080e0301e2190340c401e14581c501000106008085400800c00c10440c00400c001c0c85420185a124043c940b816081e021464198001000c4030f08259250421060005c2400075800c6083c040e901d131 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 411382185 1250 411380935 411380939
    0x20f01050405010e012d05090a120506040b041704090f1b1407020d08070503030907080d05040b0a02010b03010c111e03091c0804032010050307030216020907090303080f01 75
    0xc1d002420040302d5504001c40340581803a83c0c00034040d01410701c1b40140450001038002e1400034460350000e203036140100c050100029008000811031600984c020b000380c1510340f03c176a05d254400101a10590300ea0078010700f046141c8030100c0c0144001c000c0b41c0000102c0300801c020407026107010104000740080700e042d2503002e0341e402103e02d00312151941001d640c1e40d05580b001944180325442c0203460014049220010420000011070003000d10030100d506c510b40c2e031483c2d08d80d5035000ba035907000069014801040b0035060b031400303080034410314000440c2510040012a00710b4000444200005071740311095030a200c024071071200c1e602c0703070304d44500c800308400c40d0020b549200780900e440c081d1035011300d400e404034840e44803a190b440c4c1c05219590368540e81d0810614103110780300350501c1c50414000c41600c1d8900803000e5110342c200d5450305400d580d1590310135402500058209034015000740c5200e801a0398035880303280304a4654580c0e841150841c2401405650700074400000c011500c401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 411383435 1250 411382185 411382187
    0x815040b0f1506090109030609030302030108101802060d0e250b070210260a09141501051e0a080f060105061303060b060c060a0c030c170417190302030103020f0105040501 75
    0x3902034100300c02c0e03c926594120340d83c0121845040c6500140c00d076860080208201036050b00114100c40e540701c101c82d00c0444204a0b07804807582e0002d83c42c01060071010360801801d01001038a60b415503c200064400380300c5200a044c4500c4186c00e0741040320401512403000c6400c0b6040c0701a0180c500100e0604201d40d001c0b500c2000440750403024001081c214402903d11181d200744040c034140551203060903c0c4115001a0881c000c003250101d03402c80c0d2440e0703103480019441d0300402000408d109203902e89424885d03107150081907d0520380081000155540700e110764203004217560b400400071010303d403d8050402074181c02182c868441000382d078040c0380030320107088252900041c000481201c4280010590310520b13115800500580d4100711612800b50f100051380340064505001c80b000e1044106c95002c5154a541380c08010400407601042c070288610b000b180c0340e00c0034545810f82210f580001c00c00103170403803000241c00000500c1141001d0103202450002030074401d09080c10721300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 411384685 1250 411383435 411383461
    0x10c11070b03040501200703020d0f0813260d05060102070b07140c18070e010504050a0e040f0f0b090f1522210908030a0c0f030201060815040b0f 64
    0x4503509034024080b01103010f005081d4440410b084510300400283c0d10000e400c01c5060304010340680140c01080c50007d5240d001c1c2081c00000042c90790b0b514190b5540140310300d210360019206403200c0c103003401a140c00040e200c01c541c042482e1a41e885884000c10020602038820007484241150042681008034078041000d46002a07403160007403c060441e42000d5280c001400c00507030740f0022084d10101990054101640122904ea031540c48403110840107554500c01c91084c1600101064010003400108404071a00315208075000c0d59069540e03210100689600e01c401d442c0c50b041c22080c880e000804004120510414a001d854050425058407202031001450b4090002a10401d0f8201d0000303103900000c581c1c0e101003240319a01c9000c0545410307803055041c403804a0203064000c0b803d1320002007614140415591908071100c090b60355080300c002100000c030159074079914049a045014040c00e40600c880006500d8103246c281001d00b00745201400100102010700280208440294 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 411385935 1250 411384685 411384689
    0x901021e030406140f0906070c080a120f0204031109070f091202010c05011409010b0609060421080307030c1209051c091a0310060f080a1a0301091202010c1107 70
    0x103049489941d03605060014081d042d41114850350420104060101040d9549004859400480d425aa44c030f04041d40c0d0114400c030040e008103828001c01e04414030400002c001600c0042000c43c43c440d6049010b004c2c0e8100d41c00c211411100c540d0004420f05007144039651016652606170282491504050304007545070188205200d9681c09580659018800d01404160300600801c030039194020300d600e08d910192003040031035007071036903104d95032405400707403030100c00d0060101c0c0c5420b2130100f8200489038840c070618000c2c2d00d0308001314041010301005c2c511410ba1500c000c181034440d884010910f41c2a0100054002d1030680f140021840c0020704c40c0421481c0007150805103e0410140c4450040e07600050111340c1d42c02002d60400c40d40805513001d40c03088520007200c640c442d001924507402e2804240000760700c60340001c03042691741d04401403801c000450481c030079078180c0119003507502e18482507401c407803042c02080086909114909075005145000110f118040c0d2915450701418 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 411387185 1250 411385935 411385987
    0x60c1201030b0406020c160512150f060a030f08070537080c07290a02060f04110909011a04020906040e09010e070f0f09180f0c1517090102 61
    0x42c0005000c00c941030341200d03403400101007100c418104043d00515441080e0141c2d50081c451908401810003000460b004414003000199500c0e69920707500000c0e4480040100e5400140d0f0031001003c145003004d1622010f0080c04515a510b0507070900502d01115080c0e0307000780d43c24040002d06041d0311a459003020401d1250500207a0f030035410104518054158591b1450003058000203a02c5916019600c1112140359101c0c50400410f00541c0030b809000580300150b04010001024040600749007980700d4807a00d010304180300180042a04140c2c2250b03200c203289c0d9148040c42c0142e002c0080760f01c00d840101e13019840d041010b4040b600b140101c0c842d05440c10040d4010401c1d1100079040711114038521011156220b544070121b4410328110f200c0c035220302c0f003a0b0402246001782c900900c0d00180c0155612514051156a0000111223100c01a29107291070140070900002241c500300c01c0000903541e0001055a250700c600e0502c0b0017a0084520780c2c070402940c8900741d8005244142c000300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 411388435 1250 411387185 411387203
    0x13060c09090204080f1c02061305161d09010e1c12090b0601110a0314072301150503030310050111120a0507061d10020a03020c010207060e060c120103 66
    0x24500095820300c8050300312034106400824085040e88001a150b90340d035100e00e0485141c2da0b4103c05512452200d5aa40c00041e000980000c210f540781c1d0003080c003024882c030700301c4584284040310390752008a19003000c90f6600003010300c1984408680061600300701844001c000d041c690994480da11001c080e0004001185480e40e20081400703034840d01145109030a09000c03020051600f09150076048500d2404629460b00c1d201d4040d80028080318280e44c140c40d101c1c0b03159040360480c10303150030101088680381407102540180488121800c0106040708001040074411600c10302c10b02c0720143c0001e4000e034414010082070460340040901129400e0804d00080061800f1860800034281c01d40026013500062000e80141d0001c02005250701805080240c48204800409990512160114140c1c44410140600070007603001707105030142424010326006112a0807401e980203c030301501e01c1a61240d52080d550028802d4070340c0b02c10b111a00501e080401e031105a00030206000141620306 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 411389685 1250 411388435 411388451
    0x506010c020d0b0a20160f15060e0901090309150c0b1303080f011202010f050c07061701060e010906030c0c08181302091e0a051203120f1306 62
    0x1005041014080d60007400c0d80c03400d00403604044840b00415160760081600e05202e4000c0c5414002c18240a400810303500c0d0701d80341c03a403046203084601d2000c098898141d002e00290010304100100c02c40700a52000c0459114541031121040500042c005546641425254800240d200a008040e80c0107902d0090040140d40c00444102a0343c100043c041b0f1844018081c854400c1c082c08400d4a100e40c1d50903500e0b44d100c040e22040c10701c003841005402d4004c00300c050019800f4072000b2a240100e4a070040c10801c0032421030f85003000790b0713210740d0102e0100401d030921103140a41250240540b81050313240028031000003026444144200c10030560760300c0c0310594440c400d001039411150070090f600d45803861500749003e440101d01c5100e00c110822500040c0c00c036a45d000760b1ba680340c00180080e05051703004007504102221b0805166001c000c14101041e030f5601c0041d807a0389080b050004544607685070804041400c009400400b81290310300030803404440c04040400310b1a0302c0580810200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 411390935 1250 411389685 411389687
    0x60901020c030a1b020307081b040c0c2306010f1409040b0712020c030315040b0f030705012a030806010f09050a1703090d060b01030b0d020f040902120313030c27050601 74
    0x10061a001b54503000e03509001520038800a0518242000da030101030105d2018000c01003121542090a0041904da041c2c1002040144080c41010120801c0e2800112111444541404001d800000300440a41014480d50700b0740d40c444a00d40005895505207410107403218100b04a00511101c1088100c00d10180d0512558040c2d41e10340c400c15048903107038204090724810701500101c415008038030b800886507803890400b451440701400034015045903824200115204c81c103569411031310703548084403a4801a070780105045004e00079038031800705040180004004040d601400001c002c0e511106000c03036520420035100700c520595500241884954845040d4000e1500c0240d108554002080522156800841248009030780400052100b4020008a5039040034040e4000c0405030745180c16090507400001d556000034080c2141071084106030346103501c03030300e0014901d190300030b801c204020308000c510303000c0c0402004100d00c0400c995460141d0150007512180c40c651200042842c607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 411392185 1250 411390935 411390977
    0x11e0308160f08071112031305102102030109060e04030909020a090302030d0807030f0204060509100e03060a1e0203040b0a0b0109210b0a050405071a0d021605060901020c030a 77
    0x4103034496003c50319054a410311030200c0c1d16a61000380200000005001804404402c507144403801c0c0381c094844500f40028890b614403820100e00c1031084150341d144004540c18004000100c0048025903a0360504449005480a0742e003d80c030784025010900000030b4000107000c040d00d074004070045c1c40302c50240b4101c0350070805a00103501409401001c40c02164404001407241b0f810340c07002d1007284800407007074080344240e12410300040c5003440008054074140018005000c1c1c3c0780390400c48450060006402c14a05035403c841d810398030511a84800094800c2c0c0c40700a64081d011803e5207019120407aa00500a056440302550384107004091303809004c204000d8131281100303510109a110010f100c8070324030413056400043c2440042c04080e82401041d22855101e005800b00303500e001d1101001408101803403420f541d0900a03030a01d010144060096407900821441041d0443d0400b6400c042c07020b4400c0d100c0380d0042008540b003400010413200701340c20f94506004400141e0f4285858 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 411393435 1250 411392185 411392213
    0x60b0f0f0d0608150f092119020d020f010b060306040f06090501061205370212040c0501170609011412060a02040815070801030320070806011e030816 66
    0x80c0ca14102021400070000101010540c520110018a40e100c61001d00402e100c121070451b640d91020000d45d106110600340c410941c1e2400e01c0707050418420001e0003424000f208010780c0164040300380307280415410024551484800310003001307150036241c089542d51200600e80c1d07002d551620742ca04451061580180300620301d040301000a541c560720000d0074090b0071001c00c0806400d20300456035070b800d40012034690404a11540000b40452407905c4450707018103200b9041c8550030300014008220341050b103031207a442155402003641c00c010002d4003c0a0240d142d094085680040005a450354080c840c123407201c150003284c2030714a810001d01c0307200c103060342d5091900480c4140000c40c0e81030f4010380f0565074420190f92000c040c80040015031381341100d050000450540040002ca4081d0308d207a65241c50502c0400a40c0704040c0f0500e1406c0e61680c06050290f00a200400c00703603001501d42c914a6080d246040e51017440d50b100c0716101d01503800c2401107001c52460781800c22554841aa003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 411394685 1250 411393435 411393457
    0x609070c0b390d1e0c170109050f19150f0f0b03040503030601050a0311190f02030f07020f0301200c070e041e0312022b060b0f0f 57
    0x9401d25100e22140078810000698110080c00442410920450031212001000b41020030350704150a40500d01d000d0203420b8000d143c04c1000207464030114100c1d0080e180100c2c81516000301d00815800d0803904c0c5641640410440c51812043c041c03000c06054040c0d4001d0002c0110203c04200070b005080100058000b59815061034880005c80e01010341c0e0000484003644000004c0a689080090482c07200302d4006115820400000f0140c0d0b000d08040d106101d5a8030340050581061342201443c1ea00501109150000500091154070f900c0003c02540002910186003010210850300c45140101000284a08141c00e4a40010340b425072124030010708614882c4446002448040754940c4801d41500c80c0d405920070100361207002290081c003990b4030041080c00b0f51082c00420001a1300108114108110103400004564160010700058202400301880e003620644000d6a00b203103200e1101e081c030381410b43c00c000840c075000644000041e0900c41581c1c4402180c01c0550703920542484075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 411395935 1250 411394685 411394703
    0x806100504330302030f01031b030602040602030705070f0609180f18060b0405070801150e0909070504060e07080711070f030b0105100903080405010f0c02120a030f08010e0609070c 79
    0x4600680d078070300b020907a40e00c0742c1d00741c0720080c412020031410791104459124111010500410014007802c8111980300d000d8048420703102e449940307680990703210358007840050307001180d24030600c42c047c0b0068001b40b01090101c0c84082c94902e000c1d000711807510031391400588101661070300c0c980541003001400101c0108101202ca0001442e524019080c0141c0f45c10b460015689402d0509104041c021200da03140d84000340c0c40e2000f221521030001000000304200d40500c0320058413140e4a0f24000c024640141901a08210511044030803543c056030850b035186080c007611b0b80d000590700e030f0400c0c400e140003c2c2d4505803105040c0340814503889000b00c021021070000900030711544240c11303070340c08480413980c2c1c05681504071484041400f000c1c0020404100400441d070040816024640c01030034000e09070205038000030350448201283d184a0782198012208041c0e01516240c6507215a040105440d4140540404211402040d0301e001d640031901003040349010f40a01702e0300c00e40c00765040b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 411397185 1250 411395935 411395969
    0xc120a050601030b1e0601050304060f09171803071202010c1b0303030203070f1e03020c010b0d060c0917101d0a0302160501020a05060a11090d0b090c010f0806100504 73
    0x13030650007152108007090400046441c0782c441d00b0200b5000d010140c3d40e5608548403600c8100c01401282c96200d00280c0d50081440000c1041c00240408010350a24030b4494403101e4a4140c0081d1008801e8440d03007100d0b801b88082459004000300e555028a0003590405007460320035207508001e45400b40c20104018000101039058008500c2400580e40390410505451010f5620b510700480340c01f21407102c0054015003520981c0070303010004200c8004a004c03080e11004c1486282454403e5603140d0b258034060440da40c00044541c000c003108055000b6000c04101d031562a9107558605400084c1c0781c41d140310065524003030303c1712b1510507501502c0211903103280c041d5681880c01e40d441000c13140801c00084d00c2d8000b066400c1c941c0e401c0005030089a60b01c01d140d000400704200c81034092141401030b03100079240c4134414501c1d980f04070340c113090900f050302c0568940301d05c08014a0420400000d03114000d5440f140d899001755094034005c011081c142000d5405001e80e4001440c0340100d9451 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 411398435 1250 411397185 411397193
    0x7080d0e0c0901050603040b071e090f0f0e0109050417030a0f05090c0a0b09030106080706080703180213090302460305090904030e0301020409022a0c120a05060103 72
    0x2058003824080400c480341c40c80348905210000302e003442000c0d0301c11414400140852800484160b1044e0035290501c43c41d04810f20114600906440b128001244a1010702100a801c00114090300d103590440d101145003003000c00c0d680c0307014028101c1058581022904002e941506038644510480b40703130740c40c1d1030900324880007005483c0e00d01c07918030b00f03220100d11807903004035070f07659410b02c0039000e9040346041a04c035101d290302c9041401c0c1c166584400000d506901400702a000c1c0045a4070310041d8101108000c0c144d56040030400080705100745031b00c0040c1e0754104c07042c506001d0804046025030440c10140d00f0b101030409506034114140116202c2d0180580c1010381c21000d50120401400d96011005d032007a0211000a0100d0000c114210300c40c45c01b0401d40d6880ba03c2850010a144060000320342a80c1080d480b1384401600440c02560342c3e400380c0c560300d403858a07500c2c11001d10039003500c81d01d030788000d4500300300d008290102964418400501500c40c103160403070300300c50303107542c1d2464 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 411399685 1250 411398435 411398441
    0x1060f12050a090b062e020f0304080d14030903162f0102010c020102090306011208271302120a0c120e030a02060906041a0606041707060912020a0b0c0307080d 70
    0x9030880b0694a1300d030002d5420300e407005000aa00401600c45c1401d03100310080000960000090042984a254a60003191004000520191050038064441107001d146e0103407010101d10032920240405000700a2140400016580195079a0201d504180754905000c0c0714088040d0200403c0c01c003078040060440c0e030a5411445038502039000308034903090b20204034201c0c050022401d5242d0807540040080c044551100c0040300d0051000d1440c04131582e00c481404045403940e4401e4103000310845002e4035241d01c0b0b143c50200d81e600190b1034507012400c401e00c0b0710001000141c4039603403840b4000e0054800c0600c005400340305102084100000c4a0b07480c0d030398204440400c0184038400004070042000b2551600031580580e5039039400f180e00c9800c0c1349402004094a4015405000004004425011901c030488110020300030072401c0040081c010711036a0001032400b8035020300c003c0146c490ba003400c400c0322000002103072264105401103095100d940c601800303c10003c280050301e00320a034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 411400935 1250 411399685 411399701
    0x141905040e0405070e0907030f060b040b0d0b010f0f0b1207021c09032d0f031e111011090904061104180506190302060d0e0105070e09010e010e01060f12050a 69
    0x5c4542d8065585d020021645c8003141d0000034904010401002d002a00302d40042404401c0184042040a1050013040785043c1d4484141c0742040010010002040c3d00c501d810094120110010412414441c03120703001c1c4140a47e82d0305540d803840010306a14800e000700404150300c803e0210500910310310080102503240000d5078406072000d000303101800360082c4001c40010b00180790b0907402094403055040301001d40e0a07414407106603000a59000300d45840040d451240c0c1b980c0200505294413545411401003a1201061905102a03a8042c0b10420380d84002c81c111070861095650313251410107494040001c2c1ea020768003007001700f0f2107180c00c001c800c50b000c0c80b6402004565910402c011058140c10602c0d0170070002e1440c10310260500000800714001c250030045150040c2920301800c60b80c00b2219000055000c0605a45910703049030001e0041506140c81c0a031541407c420300349003201840781d0020300c4400000118503600900b580e891412082404200c0d40c82e00b0a107031800790443d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 411402185 1250 411400935 411400949
    0xf040e1903080c07030e060d110d0e0105360a050f0601062d050304030c0f060c02163c080c12010c0f0809030706050a1b141905040e040507 61
    0x2c14006070310f090701c0310282ea1405405503151017044902e08284000350340450405200d1949600c6e100300d13811a41002131000180504c800181c8241085005084520241c01880c6408454035030180c80c030f90080d40c400703000132401a41c00c50075144d00e03940c0b1328058440358010618042c0154011080c4000700740b0300d04803107481e10750f482010b22503030038000c0480d40d0ba0900b26401040858901c21288548040c540c410b1107410611000511501c402d070a18413034410032600d0355120060680082d038180309440300d00400c200c82d00e846c0fa00700700c1c822405032490301000c81d000042e503c480d0341007481881d02c0141c00081c100013004032600c940b806501c4060340c41e0303190b014862903005540c0e101c0341442400c180080556644007880d07524a0110f4105030003800e1402a0311040c004000840c004e0700c0b4103406100d00000009101c4111030f03883d541c038100048241c0a02c810100004940780c0c3c12000c407282c2008520040311071610044c4141d40c103000b1900440201501c85081108216000070401e0542d210 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 411403435 1250 411402185 411402197
    0x81606110609070b0f0708120907091a040504030302070206070c0e1003110f12070e040606050306011d0703060f030305071406070906031802040c05180303040b090f040e1903 76
    0x358900541e40c810081d90050078951001000f040162100c1010300b603514100f034074943c80c1c4042038a0300c2c452600880141001b144101040c02081c80080010b00002c0284040034040c103684403150805000e48000501e024940b070b08001130415100fa1f04171400158010003043c2c41e81e45a042003030b11341c00117010303000f866001380e008262200014042001201da02545c4030041c90000740501c09102641034031550404090916000201818001b12000c2e01c90300341c0002035842c060501c00151011540941c0c080c3d00315034014060900000c2404030ba044500d00d038450070340c858585c120010f1140d81c1c4416a060003803035002c0101580400141801e900842c0c003420a0003071075506a40f41c0f507098651340701003070b900e02082000d14040c0e0024003d802d4109035040d0b8503021500880c007a95500645c8100141000030414004541c0e80c11088001c0c81c254010340c141404c081c502e6280b44905260709204120030a682c0c421565250403030001e50048609a880c544410a0b164902c41008841200403401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 411404685 1250 411403435 411403457
    0xd030302091810151b120908060a0f0b100c0b04031e09030203064005010219020d0306081504020d050a030518011110090515100501110318060f04081606 67
    0x1c810200f50001e0072510910880c055015542c80750841e60382079001c0144040214000351580049c80040d100e584420004242110b42018034421680c000140d60b00c1070040100e81e82d501d82d40400311244550340a0481c1d140c070780b2941030a0741d00040000f1172200d12019019480007103980500d003d021a8402d5045070345503192200fa10300000404500c0b0003562001d00c80c0707a150310f500492a500601801007100c0a248459140c0500ba0303803100c2000e502c50f14075846010360107541041650307029041e510b02004480c0c1040601034442032204240c01e55100c415000c58159079800000d0b00000e640b02c0111054560b0f02c0c64060704540100e2050040341c0036492010034030354007641d190300301c040000c40640340c014590100c080c014210707218291001d104003400c00c1c00c01c1c140f80b40401e001e014076000e2440c0309407810000422030503c000d680a4190014445d1401e10b183c004140d21800030301325040360304c1301283d00132683c40c1c3c0520b60003000d80d4480c45440d440409864006207098407031559500e14850 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 411405935 1250 411404685 411404687
    0x3070e0a030b011509030c5d051005040b010e0403021009031202030907090b0607081c09050f03030126031c0f060306060513020901051b12070b0f070e0d03030209181015 74
    0x10280c0f051802e0b5403044561038021608c0e022510392001c155100d0103081b401d4607840b814501320010300030902c01e645c2d607820300c8180104181c1d414010302e50900e040742c042c40c0c141e400a403540b1600c0501c07039125481c1e03180c2d4001c06000f114640c07612084a007046407285060850300e030f0b072140e031486602c0c02c4501c1c1000307215481c14103030100d0342110f400c421203602d040c80307000510144200302065119016613031030070040011802e100804441d00200021341d00c07541020700060440040071940d00c011106240010b1401c140807003540d80850701c8586c0488074a05084c03001e40a00903802d43c20031b0701c0d40340810200c1046590b0b40150b003601e0054903110514420748000a040384a0318140c00c0c0840c0084c42014141c1090300041991000c601040d1004401135040d18500398000a03401c8680d0900c2e9820802140c1c0ca40404035071000003450704804143c6400040f811085a000001d02019000501e0800ba62180c0c160703081c1c5210010509407036842d02d1801c40010149034025450031509a4035130000c09 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 411407185 1250 411405935 411406019
    0xd11070b09031e0c0c090a0e0303010305030c0c0307050901051021021c0209060301050d05160605090102060f04080a1d031009030206010b09180601170c03070e0a030b011509030c 78
    0x103460b0384d801040d91149030410400c801c88001c2015054907152001c2c808480d000b400078600940c4540015502e4401001040342840050071056000741c0c003000c4104100da88116480707046a000f55400306400c03044941c2280c201c410350b00c180b900c00c0a0b40c913220000b07019030390007001c400320300748410040b51184c1c80603001030303204800c06154401014001407000e0301d42811200543ca00c190100d07201d440180c00480090340b8139a0100c0003142c80416141050b50301444059408204003200d18034038a0642c2e0340407a40d0050560000410481d5038401c2030000200311000703525140201110907804070030440e4000b5084804007100180a0a070000031403c04500c01d844030410f00506c1c2c09251403800c44202e152a0f0000c103254108144045214116481c4c612003c0c02201502c2c14507a8030314221001030444900072038803c0c0140e440200c1000894440105217055070410700c044401400746400440b0500801d1704043c14040900c00005000c1c82d0013522880642c040a408401c0d03007410460003010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 411408435 1250 411407185 411407197
    0x30624010c120f05070c030b06041404020a03060c0203040f0806071106130f08270f0a0308030a0e0a05030c0a0308010504050702030919090e010b0310090302030d11070b09031e 77
    0xc40401c61500020030340240b1030b8840f031020502d40141811210340300c1c201a49115841654422400800d118650a16000f444280160303158040c0d803e060030350100c1c8600d00c3ca8480600350b580e5032a41b80714000e10a0045600070400b0680090116032280005510740000351290000719807000210741901401040c142d111324804045285403551584950350a9144103c088480382000c02c540800c0302080100740c40c441401100071903200e01c140050041e08600d010155103d15040c140030000500f94000702caa001c0c040960200d0400002913059107071092044008002e4000800c3c011824240000c00c0c4000306e01955a0341c0c00c503680d40c0c050108a940c2038074101d0058000700003030080c5050a01c540030007003110600c2d8842c8184d6802545003190700115000180f0f94550207103000398a010441c504c901e01034104108807441c4035aa01030360700c0c8102c00000040549415031015803031002400c2d5900c40d41c0012814100d0325045c06101c0e144d034040b200e5500c82c0b648401c0755014203030032a0150381c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 411409685 1250 411408435 411408443
    0xa05131a01110d08070203070803011e09110f0d02070c08160509191e020d0903080f070c02091003060504121b022101090203070b090a1e06031a030624010c 68
    0x440003d0707031941140c058400070021001d61104001c102c00254990004500804040350703449044044000301c1d41040c1c8442d80700c2062607042400301d6840c0e95000080b941444407007000303281e84a084101d040040d014a41f0301030950220504001001c100c041072801e25007080e621450265a1a00100042001e080c1c5402c00401308006010950359241d600c50b07400c2c51118120401400c900c02c9a1034260f0340501584c4e4216622512240c0405411003d46074010403807014151843c40c02c02d0303008041000780c0d4006481b0341c44e0703040424140026000307140701554101a01744003e10707041c10014004a80c80303042800150015112079000ca01494041d00d003290f00504d0b081d04000026115002209046018520343d540c644000b001030390108840c400801d4082151516100d404007003111010b219440340e03444c400840081e290015150001c2c0e4240c844508000504202c0702c1c60540c0e1030008400d4554045c42100248000d80001003801e08101c4503440450318041044401110071b485081d034010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 411410935 1250 411409685 411409693
    0x20d021e1201150902030919140106090204122409061a0915060306182508090c0d0312020d060f080a0c030b04051f050702012d0b0a05131a0111 63
    0xc00243d150740c004640111f01c840845208000922080e0050306e100f020440d0100c580750481040c0810a0044c0401030410365411030600b46088100710b4039540019006040c0c071811803201c4039048808140303c01c0f9201d11507040003694900c1c5031610051003001d151207403001b4485010743c485c1c0740075440c0c80e10600c59080101d10003084001031052940010b030056600008156041180380c0c0d601d4000387c403603100000f04030111000540c000c0030707510402c03405408111012040040c90310700000c11015051060342d1480000c005820100c0c0c50000400d5003114090000440750601400c0741c105009644c00340111030110796135502c40d079940e80d403500d0005250a103010020404160702c80040c60303000307028005a40740d01d030b02c4170480c0940c4440b4585c180d03100b513030720700610080c02c5d82482000000c415183c0080c01c0106240c5818407228814032100314003640b92200b80c3c2e0b06844c2c41284070000e0002030300c403104044181c1c0e4006d02030070603190194402c804220b1201c443d98440c85250b8a89555000a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 411412185 1250 411410935 411410939
    0x40501050714010e1014010509130308070306090203070c020f0f0d06050411030f0d14031003140115090902040b0603040c0308033c13080d09020d021e120115 69
    0x140d0000b00c8001d51003941d584c4241c010711562040c40700b000300c144200c0700081c2c914014206c16090071010f803c441c2c0035a04e510100488282110060041d050305810031064a41d00ca60f0101d014001640008041c03030b00110501098a1304440c0d64409144203c03800b090762213400c070a1000400340000a564401e940411060210340380750b0205070440d01400e0b0307808600d046000400d20b425400c0c4502c0b9010340c004620342200c5070780b205540403013440c41c42d13055280d400c0c2240210240c041b40d02020b403011850140f0300e4043d403000d50104803e0100079100d00441139030750305280d0040000b2481a8041ca08000319103c0340e24007101241d10803588103030014000c07415030b10303070034213680004003180c003140002c58074a01c00540000312700c05510f4010000105000448868000c0d040c00900b031181c0d00020103040c480040c9118003965981c40d120500002c41c20401d00010b000081000300103904002d410141940e5401d0310003021080e0340c416034540040751845203d1501b200c41d12400910300071380241c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 411413435 1250 411412185 411412193
    0x18042316080c1305030303100f06081608150d140c01031806200c061e07271e0f050a0b07060b01030b040c020703051b030a02060c2107020f060405010507 67
    0x9404983c07410310803034038101e0f15200807038555071080ea1008514a201101084a00313407a4103844040c01281c5014181d50800300480b042003620b4918080902c20008000303000182c10001e10b08071580000e080c0440c0071080c1c2044080d11b0024002041c1901806005005950003030103480c02d03401030340b0541d19142040740c40b1080104500380a4000222004091740800aa0400507000710348040001c0d00603402c0807070700c00031244820350710b040094401104000320b45d50020040a149a054040c0d0542c0302036520443c03841c151160030210208802400c078290003900030421400f5188486c00e030000c3e0544400821a01c1c421b240b00c3e40803015010812000080c107203800520003150103040206241c05410000750a03103447c2052000107a02c500e10408c2881810018504003030380610780d843c40c811040010039214090003102034040c040001d0401102c42c4200507800401f510441030001c0c844201c010621a5881102c0692285144000308280341c030b016001c03242103c0058640e00d14042c07081c0c1d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 411414685 1250 411413435 411413437
    0xf0c0903080306370e0a1a0d0510020a02031b0a050318060f0f070317130204051806130b0c0f0307030c0c06060f0e10080c0618042316080c 61
    0x140504155040300c102201600c0344c0d040c02152006404090f0b8006041403124003942400a02d034840c01030500498074210004914420103460050390581c040c45104e0a2140c035007a200144141076510004045030029800b0004e4003200e4024004000e40072510b2140507134500046d040984181c10070412401040020584034220020203002107042c07444207800542680c01281c031200000d140000d2010405902c002c1220441c0e99409125019040154044407445c0d6600c000a00441d9560045807805104480585401e0054400c0700c01604c2c28980c0a00c03a00e2641e603003141d044504401091500c2c414038183c0d034065510100c520308580d60004101c000e009a07c203500244601591010086406030041c00040c013483c010344200e041c50141c02c500e001000a010741c01c00300000c1c00600000102064208550204a071615119001203d02e0341c41000100c2d59154010b01d450440c5080f022034a0004600003e041c0c6c00540175550340c019001499600503600002480c208002410300340e9400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 411415935 1250 411414685 411414709
    0x3100e06070c1b090204091d030a0509010504180b0a170303040204110c06100609051e15040b03040501090212030a0e150d021314100f032703030f0c0903080306 70
    0x500c403c1c00c00720442150103d54009030085403403d50009030500a0081e5030040700d15610524080000942c040d85929071240103401d03034141004000280010b01d40c0c8940e00f50740181911400c180521010451824010011d118041e40190002100018500c030314080040c2e920a066000d98034607a5660b080000800041408001908003443726401c59102004038500c5290101c241e888100e0031b140c00688034442a07071006108050100c00481c0c00d50341010341c001c03d800142c2d07644124000b0b481c1c90110700d004d99080143c00031404002c11003400015044800c082e0700076241102000b030341c119500d4a0b0f109146200010031000e8070b003c021070910142e21000991184030b414280202c00603840d0590388084500e91585640400038001480406c5a411841c001250055005078540b04050600142c0380e04400506645d09031800d14040d400940d0303051703441c02c03840758040c4000900c3d0240c020725140d0008102103251200102429014501a03015242c0003036942d400c69649108004022440d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 411417185 1250 411415935 411415943
    0x40f0b06010c0f060b091006020714010306050303070302011a09060609150f04080705030c2d0a1a0d0b040b0a1802040e090312070203040b180d120e03100e06070c 71
    0x9420076070049481c0b4500707080c0b507134481c00703020400344c880004025503204054104114a0584002005010303000a40242242d40141d030701001c030360030b920040c1c00900b411380c00300d901400001118400c041d819030024030000d0701c440141d80c22a90000501c692201d04407a2a07801500030001d845051401c2091500c20304c14001703059160182c4042e1140780c5410941c00307041a64810032050080e0f280501203d070844c1e0069640c090700600074040300021510404451211407040f410326011038503110110805480d1aa880305480e030364400310100145d00c220302d00c0d40c0103894100c0c0307002c09142500400003205002007443c4003090600c200c44540c0303035051079286159039003000b00007444032401020f64032403081040650f0711040c0c0c40d817070007403040f50040590046420810050203460a0300301903c80403800440c07001840b189038008610381d0040c141010f0310210301164000401c0760701408000c0464015020381c1c40308048040007000307032002508684041c0d0454400a1001407040c0e944044079805 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 411418435 1250 411417185 411417197
    0x3030804060f061d06120715020c0a0f050906121018021804050d0c05060c0a020f06270609031b100501030515070c050d140c010f0e011103040f0b0601 66
    0x1481000c200c0d5900c0d4040c80c102e241446110f9030301c40303440e405203600017025504a1004152130030029103032891400303161160290407104241032807080124001c6260040d14090300240c6a8158240b55044e074881c05100e080854001081d5060118038020400e5507100101001180b200010b0060041400303c282da130340181a4039800350f07541c0f400950300041c295a038031a25040600308113041c02c0e10551000144600980c003100040c4001401941c820820382020b41c98048440040b410482d005920680038170032003040c040c0b02610310a0301441a0401c040c0301021241c0c1a90306925100304941c409000d03002800200107112001d1401c91103000030300251030210b10201c420300708030307a000e80080c2c40641c041308103860031031115042c41e90040d140b4200300c400b48160740c1d2041d42d038400116100040081400c19800006007920546c1d12181240000341720361340020085000030041e4032100441036082c220004121a90782c01220302868000d414508291a192240903c80c40090502410042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 411419685 1250 411418435 411418451
    0x13050d030b1210020d050c030415020d0b0301020a0f021011180402040806100e0a1a0f0402041a19031b030b01050d09030e030c060a0c03030923031e040b040303080406 73
    0x10180002480041c1d003d20040c0c4400ca100300840131a04020f186c0300c1c50f000d003001404082440c0084429503c1007289015948100d083c05030b0b0701070000c0c650310640540c00130428018a50704010000c592180e540d00f1618025030744040c1c00191b440c102c0ca00210050100500c084011480b0143d0881000c0600301600c0c0a5807851000d00c0d0070b0003110007c0741c58076a00401d1100c031080361000d90701700c1000700c01405101820060150210f140100f450300c0348021040b0040d0030384864054800404080101a900e009030003484105030b4040c824490b10710800001c50300103a0b021b4403e904500d02c6000880013000010b020640081c15a10003050600c8014800a076040036103005001040d4800d42d2450204d015400070b00d868100204800380c030070304041c01080c00035940400709100c026098640428014100c1c1410004e03c1901d000c2100100172088645000000010040a0501818810351400c03006408441c1c0da034090f038014480420801c1008201080c8902400d640241c040d07500010301c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 411420935 1250 411419685 411419719
    0x6100e030a050f060711070506120a0e0d20030a090b0a11010c03020403050118030f03020f0f030702030c070f0608161803111e13020a02030706050a06090513050d030b 73
    0x6819002c0e03ca485900c1001042452680400706100300b510610003480020704040c00039415009802844034014030340c0d0001440c07900140c10000c1040840c3d0180c0388010503102006054018030411510031464041e44989201e0000084654100c0c09548251700300782807078400314040c0c0c0180d490004203c0e1480c0c0001d4168070a1254002d00c13005603e00580d51481d51801600f92072540010440c145148000302c40032a030091701c0022013046a1400590b21010703c45d180f84180602541c80d41e94640100821000e0b580000061041e0080b100454181540d80c2d26400c1c05414540503d0000407240008a0404580041103112450305800c00703960b25104072015811910080d401a501045a0030b49040c80d0304001803140544407008000d8035a10904002181d040720b030742181040182e50000f1540c03079107132081c07046e140050303030050042c0400c1c20048481c2000c0c0009001d5210041d14110100d50b00e10b84805901d21a10f070b110003d080c15004d07401e810b8006040c06600300e60003078111100c1601ca8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 411422185 1250 411420935 411420943
    0x90902150414121c03050a020c0f0304050a08030c07090c090509130b1006020309060d0908030a06140a0e040b06190902041d06010504030803060d06050a09060b040506100e030a05 78
    0x54440c00002d80a034561501c01c121010104003c2d001854218100800d903c110081c50346440705420704010800d600e40000341e00081c8107401c8058200e0117600c204903149034010004000310f4200b10380c25a002516001415168403d00b4010001c076401150208103510030394011011115550619200203651400031a03004641115540c07a401d80d4607400c03104000c510804180c01c0b46454400001c03842c24100003a40d2407264803a0b2522034000803414141041d800d4205007451540501c0407a10713400c081e114130300034050a000d074580c00820030121416504140801e0011208681603203241038540341c9600c01c01280c05400030b60040421001030f1000035509076403034000c050255006903079600c0e08800220485010030101141c01407074050040c56a48001500c0c2030726000090f41d640e0f40ca81c1c000140e210400a50024010b5007003101700502414958001c80e0310034080c2506121110662040004603501158540d52100441844070301c52441010400c040c240040d0494249182030344030301c1e00e8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 411423435 1250 411422185 411422189
    0xe090108031b060709030b0408070611030a0606053603061305010605030c01080c0a03060e0a0e060714031f0302090c0408070e0910022b150605070c0909021504 70
    0x90703910004100c62030700c0b1054105840401c491001d4070035802c0a82004022a001d03103c050201d2066070302040601400030f0454440700d520182c10040c01c1c071503800c11042c0750421070f50b04900c070785032100016120380288111b4510000c88007050310b9554150740907020301350070400c1d0101d15030f01c5404954000c0c1c07810041d01d13003d0030001c803c641c1c0d0443e4601e8610309440303c9030802d500070303080000c410030203903008641e0640012800e2840c689a400580088004140350742c00540304032010b0003885881150f56218601c075a070340f441540c0130703a1344510084c0c5e00d030800310158141201c030030400503203955884114025103070405407010b80c1c11552900000c810b0b00e42500d05654041001508206c4a003003007041c3c0e002000c200385220481d02d09001c0c03850b2500c0c019030103400201d40004000165080c01c0c05203021440d04c40115a49007910f951068009200440d2030101120010300082110390203042038400b01c40c0d02c051864070b014100f070a5034018100e90f82c802c81c1c0100070b00d040910300500741006000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 411424685 1250 411423435 411423449
    0x203010e010b0a05040608030412050f0d0e0405162f0604141c0c0206070c0305031314060c10090303020f1c0606030b01020a0b0403121103240108010311010e0901 71
    0x42c0000b8640c02c1000c2010f059001c40d00c41e5150150070000800d011042d6000c660b02151480003d1b200f9052460078801e00d4540c224050058107444040f00e40c210940804071001590100019582e9649100820f01c0c0064a80041861004005c508100c000d0840c515090107411900d0000700a04642c0c0c9400d80c150380440e502110b465041c1c6c0844d40070052400d4210500403080706100305180c003d010102d0b01c40f0007a0165000181e0441844054005280110fa110301203c3d030f92603110322a0501c03845903020f1102e5840c0811b1003140580b822f6425a110350a0440190003000c203a00c410714000d02065108805040c0c090284d6041002c21401800401400d0020305061191050640d021602c25030004024585800c000001690780000c45024882d80051141d0703064481d81810354554100c0010a154541001c402003040880c0c0405140688451610030320241d14047c40c19014140f115a09070000741c6c1d038401040494142049116111418180381c01c4071000100411030004003608000b07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 411425935 1250 411424685 411424691
    0xc0b0a1b0206150607120e0607081204020405060a0b090d150204060c03030e150f0414010c050403170f0715230108060a0b030c042030010b030609040503070203010e01 73
    0x2c2840608001070700e04101c401c94825140803501c0e0f481d0f46c0001e600443e290b0410071104140d81417602d49200b1290000c1d001100f1700c0d11403040c0e1010b07030490a0100c50807405181004046070b000e040400d003070000d0b900740015140c1401c07029010720002c02d1005c40c00362901d072403a51054011103141c1c8003c0014000340d59401007210302c9401c001d010f03540d000c200801d496000100a002182e1466100b6800c60117884440c0ca498449081202148011003201081d41d480c0001c105a1590070400504c102c0c0d22420100c480014200b820458074000d080310503070074080c100030724000034402c044440c40b9000c60400014054600042896072840c84c111801a8920b041005110600d07080200e1948020300c8a020702080e0005400300380c94032800c580b0303640241c5d00c40d04800c44000d1a0f0000c0450420042002c6460701c0c20b000b40c101003020a5842e10107501e0030341028004100059400606030707400c002d0041e1a60329038805015021130020015542c90205104200060b5000c0c0202c0601d00e21120001c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 411427185 1250 411425935 411425941
    0x140601051008060306040314090a1e050406080309190e0f04171809061c0f0b07080702030403170c0a0c08010c020c010e09061c030906031404030c0b0a1b0206 69
    0x311001035507000804040c8280d901c03c11015640024401d641b0940c146814070740d010103044060300e18040d85072403d90000001ea0082030032030f00045e1004841c003002c0c0280c443d03165110188001c80d0114044e03d12660010459250541010b201030fa40301212240004c060666404007a031100d5010745030b00361580c2a01c8107010502c00401d102c2001003a41144040c5440c0d0340c40141d07901e0092014050b4001c030b101800242d2a80d40701d11014000f0750030000704887d20b451600d02170f1400910b1007000c81f02c2c00c8144011a4401d8030800e011881124242c00a514290941d100ca00d10700c00d4840c1144c5c4040381c00c00810260101c01d00031a40801c1c0700e0030a9000107420700440a0070f4415440d050f60856100055854460303901c0f0031040b030300074010b0790000500d4035054040355900032210b80181040414070885010554003c2c0304a00300ca80c070b6a010032800c5140440b260400a06031400790015140d2807000b00420540d0f50320541101d1803074000903100c2581002c0c4d40111a202c0440f0025811510030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 411428435 1250 411427185 411427189
    0x50f0409230c1c0b010c0f0302070807032a050a0e09030721080c0a0f0e030a0203032d091f0c050601080c01020f070807060f050c03070b0a0e01110a030b04060314060105 74
    0x181d91150641034000f40441307100c80000034030010b9140c8000d459003000030100003d1600a01006014210310016105e96a481c4c2c1810303040484072005002c0c0c060445442d00076031800e1180c03404c0a40f0340081245010914158146425442c081c1c40c200300c40c04208411400544645900803034181441d0101113005060316001e082110024008080d10000f0048011000c2d03000aa01c0c845000d00c0c00c0c0054140d9200020924000c000d500094040c403001030381d490100416000c0b050740c2e031b10500a00401044441645009018103106240c02c1005c4e40c9030909100c1a40d070343c0e00078120f1640f0303005040f00380e80d461b00d0385411801ea10402c00d42d00000f03018074165905001c0498000b062100508685141c2981d469840546100d002e040165004c504000307148031790101c4200720030b910300301c0342c41d4080d5051841041c81e0a0b215404107600e4040001102d400600407100021001c1e540e49003031000a01054014090458001380c0c4555140e201000081d8a1038140e5110581440103009548c10101 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 411429685 1250 411428435 411428467
    0x120b090a02060a05130f0603020301030b09031e030903222310030b060705030703021f1e1e090b07030b0303030f0606090d060f05040c0501050f0409230c 67
    0x1002110a4029804900140c0c8030182110a1008249044d0b603840889030340007130172041c0580058050301c0c480e4800144883d8181c020318141c0c1e0180001a510340c441c04a4255244101010680300208142d9610103007220b1802650784205010181c81c42e002c0b01d803100d10b0590604401c1920300c20201039060040031050101194000d491100c000d103071110300c0c40010b054010140801c2c04240d111820b20126459120980d55003540c840210303500c0b5601468065104d560302032120180c40d501500101120700c05008143d218a111401507100d00c0115000402401610491420b4846804c2c0c030260307080100e2084400650181d100840241068100101030f00c0b001000349207e58010710511041e6001e005045400280842d4501e03900e20341480844c042c00d1940a01800c4946003201c92051114103070003a901c2948038486101e03116403101d00554a80c001c65104017600c071402c0c441400307100300940c031103002c000325900d5540800407111000c4506500c00c0343c50b8014444007140f4000c0303030700c424030f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 411430935 1250 411429685 411429691
    0x40c0314041a010503120f0d18060506090708060d14010b10091401080903250204050429013c0b3a0c350a1103011e0807120b 55
    0x43c043d203404036140c00c1b01029401206604d042d0b00c0000a14980e840d462580522450b1806035030034503c8440364140307800100401c40b070341400750041d030b000240720510800400d8422031009210480060701c9803612150342185141c14102c0d50340c1c410f440c0c03d280d44c41c02040c85800c0201c1d914a440d140c01c10b454002e449054840c4a0705104200080c410041004415149803000c0580319002c040710040506001080c190301c083d40240ca07240a000c107105160100c0f1141c00103c40410503041440c0f02100c0c401d13034003485008183c01b0408810321141300c2200d82056501141c80d0400031200322010300fa811003042d64041d0600610003e109038011907240404500c040da40d03100407404280c942c0d0082c0050000c00908240c060352410b0944d035203070140f510701a01c1c4403000300e203059407400c1d01040a994252002d0340d58969416100154204966000b545150b000300c1c0c0b40304e0309507460042d02d0521107540154404111041c1000414014420054040109800040882c0020a905150511201c00703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 411432185 1250 411430935 411430939
    0x8010b0402070819020a211b051b0307030501021201051009030506070507021306060504081e0a032111130e0601080415020c03040b0703020f0703050705040c0314041a0105 75
    0x14002c0704081400c2c031050b01c04159000142c040a0701d52003c0c100e04016150400501610004402d002003000e019403510600c01151504019803008e00c2d0912002440c1080044c490b9000a402ca25090142c5445004c0300a02400f140c410980702d680d92820780e08020320004141a070100100b1044ca4048100050b00c1e485040c8031108500f1602c94903105c0d00b0007002c10090250008000c000c540b10104a80d80020644104102490320380e080100642d20910901016200d41400d080004800300303000c00e031031ba03482c40040550790580d0344c082d6407140c1640300701c0b03420001000300044c1751486030098030812a00400c0076030742c030040798049014440031904802c640c141e02c0d108110069800040498001d0742200312415004082c0c00204041e22035868062000d000100d0001120041640586040345c800d8084c0d41012204a201c1170345c60755a071001401d9a440440d040103a41021782c0712005e50300c03080c5404582e2600c82104800303c00e81c19181103c05c4603191002c1d10619a031449018054641 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 411433435 1250 411432185 411432187
    0x9010c2f0d051203071e03090506070e0d12020c0a0311012c010c020301020c101406100f0503070318030f030f0203190b0321030f0a0207020904030e15030c0408010b0402 74
    0x102e4451035a107021800321012014000004100c01d04d0092890b800c2c1905013010390001c07422596801005861006400c451300d10402000c64115405428014800a0b029040220580440d1035000c0cbc03041d407003000041075000d40b40c4c100c8540c0e114005a24003860244c410208022507440005202c401000322030000504605149042070542d44000c600c0e44000b407800058a10960001038020f11861581420511482c0d00c1e100401140303800820782c1d107030002805801036444505020051038503100754000a545040004001405007001e99004400c0740341c002688400c040300500c1d4001641015800f0400d0b82002038581a4140196805031419201c1981075080489900200211403440450845d4950503511340c291005c0002e400c90200c001954061460b8000c84030890303030b005a400030351554070400081c142407030364000c0310500ca5006c2c00195075692244c50442d00b02010901195200f4000810078414100d1a0059801482c99210081e40d4600c0d1951003805c5a802524040c043c0340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 411434685 1250 411433435 411433459
    0x1602031c0b04050f100501140415020708032208010627060b040b0909070e0a290313230604030c08070f2103051510091a04030204050603010506130209010c2f 69
    0xf8400c2c162400c990383c024124a8501d0444010390402040c2cdd044000107200100c0c05084040443c00c0c110038044946d070072502a0350720f80c00310314243e170018055141e1340c40a00c82c280140d0130101c10b00005003403900b000081c6c1161195608542e42e80150310080c00031101042913401494554000f40e000010380c106004a18000e101140017160248580307107180100c02414041400403045011049400500300c1d41d03640b6080490718030740c40341114242c422140221031481c075504a550401481c03000c0c60028802c55440e690300b02c4440b01841c0c1d04650442c3c1c14170074400040c2d001180e4041851184a5002d9080180c080b00e105030b01403001c00408040c205410b1000c1c0c00318084000c25603c20959604408a0019800341c40105144d03001c034800c080e6981c226007542800340d000d40107688c82107070207001c9070302d50104044c00e0b00d40c1034074070f558800480d41d01188040c080ba401000604c00c18184108403140039101c3d00090040080c007c00903400030981c2000303065481e480034281000855031219064 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 411435935 1250 411434685 411434717
    0x609050a0b0a06050306040209330403030504090b0a12060504031101060e1303030b09011811090609041e0906230c0a0e0a120f0b1602031c0b04050f100501 68
    0xd48140f040740d06010000011034440e865980403250075000180058800c4070000301c4801d900040c044881c2c01c0180e04131098039103452980116800c036038140c1c0e00c0c2400c1c2800c0082c154014061040d0a80d40300b000b07104000303802c8080c0c112146a050240d86c00094520303141c18058900d640500c4011070760303450040c050090094a035800c0703030030188005c0c030251010640e250a400600601941550051000000123134901d9101030702e61441900c00360611006290340f42e402018002d44070140d61014091040d018070b0b00b0300d680700c0c0420f0811307007254200d00300c0504080c00488c5d81c550b905440c0c1c1a00d550030400526401c5078244404413000d03110b002a4600b181d001c1c00741c0d00440313400c1000c20440c5240d0302d0050b42d075125140003410f51950f148000640034a00f80c10348290812007159004205000203600241d1000100c211f003145401a40c07410030f407280c00280390014258403d031060369883c05100d00b919140b050a104683c0f481612105003400c0034109140c0780603500c82e504200540070480c0d044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 411437185 1250 411435935 411435949
    0x1203090a18020c0609070303030c0206060906010825030c030e06010302030d1107053c150d0e030a050903150106120e0a1709011710171903030609050a0b 67
    0x5074122000d80c100c060500c03503400c020b4454030780b0350710745071040c4030900201500110b0300104a0388a80c5041003850301c0500c0c184e03140c202c216022a40f0480703c2d40065004c1d4055841903521540700b07140290721b4a2440072030301b035441c400200640002d40e100c1225260076014812038401c0b20740034000b000c0e103600d994000b80d81c40002e440000208111154460360303010301008107200dc0c10004040440386441c0700000c00d41e68004002034000302c1c020724581c07207a10f400e500745084140170241040c10310712504400e40070264420804424400d55401c18500d400030280054600c00003907a03202e43c1c1d00c100e070904140c0360240c4009a6502c0311031010042041760b400c054106902c00c00d503007001c80e03550340c29000c0c5810005041c030050701b5840d12030031105000694400504401801b40c0303600020f803d8812010fa03403018215203040141121400610003041c1501447c6d01c961200c50440300d01c5c45200c0c1c2030030301d07100ba500404c4022940f21801480320000900031998088100c1700100544102017002a8038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 411438435 1250 411437185 411437189
    0xc090501180b071401060308070320280506010308030a15080309130204050603041b060318020f04060f0b0705010c030c020d081902070b1527090c040f0b1203090a 71
    0xb4180014840d000c0000d008000702000c1c120700c00070428641d49080c0100941c0c04900d04800045910501d44142e042405849185d0002c0780700600b21603820352481030b501003c0036464a6290a0305030300c940010001c00519000c0e6204208403a16424031412801c00d07180c0c142c0d18009000e4541c1810b01a0080000a549450380d0841e1111210056000b640e0003d1040750003441d04000c00100b084240604100b44158100c80c03140300a0180c2c1c1e07105002ca0441da4999400d0400c0000076256802620b0b190a040e0350120005100041599860040320448491a071102c1010304010aa06050000078400d0460360006803e05000440c800d080003922880c69117007050a100905000c18004649040f115605440d14503045594803103a00b012102c10700111560b180201d054202d6079601c0c1400c07400e0000101c10b6031000003c058407110503800d1500300814035500c40c4990600440039030340d1402074011004004200061019000302402040094141c2c4d040b0700341d1040024903400d0300d8600017441 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 411439685 1250 411438435 411438449
    0x71b08070c170102030603120301080a0f150c0c03030c030902100807090b0a020a26070f2628090b090103061203030c080708060607110d020301050a0c09050118 70
    0x140e036448926024007080010380282101c1d140c2a410038091920560081d40030341c108070100c500c0b00400380031b64100e51009004201c0540c000c002c11100188200da8400c1c901482458801b08400c541c150900407116005e0041001480340b0001c0ca003032507054421000481b1403440d09010b220b800360040740c0610740b00300b816070030081c403403000a07500b5100e1070180026004140801c0e0b5202c01c2104000c2d030751300d0281c1086d1007000381c118041150810540007010680c1c15030702002d0824401c2d4603060451804200e0650b01103a0440001c03800880c1d001c0185004c0d02d400200507200e90b25100c948098180d9003c00010911780c0e41007195009402c10401c0e821109400945660f8105810040300a440d0300da10a0718001081c110030000c064141d00804d083c00c90654800e0340590301e40c482100d01e210f042d00c900303407c41c2040000c040400d25190110440b100090104043c03040c103a030100c1d084650844242490540d200c50140009070b102c18850010202460306011036120300e081c41c90780c101d291040f5a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 411440935 1250 411439685 411439687
    0x90a080f0f1e04080f150109020a02030c03032805070e040b01210e0c0a0303050a03050a060b1c061403061501111b0301321012060b09071b08 62
    0x11036142200000c0780d04102880e40081c030484030507090444583c100d400350352844e0081c3d14007000d00480c0003640e5000030300e48111a0f0196440c1c01c007000b00a50024010400f1070100708140190454200000c50080782d03101099040c0f0b0720542d840015102600300301c403d000b420603080c40102ca074492a280b280140442e000604d00e80041c0069944820800c0c0301d0841e80311451004403401c0599200d03405503007a080960f0620134000b4104074a48003140001404908240300c0d09031064440e0748003c4d4070045c81400000c0c2c40c1c1d04e49490b101e054000c448a4a07100c03e038003490460115490140c0c1d8020711048084032140880240003e40b5010700400070340e100301c106018000305038801d00303480302d240380004107139040d01c40d01d04580c0b134481c070030383c10701c10701941c00c240044500a11b00509400c001643c04100c050040e0100904104c44401030070440f00400c68442c041040c51000b0300d950003040c81200005003001846040c0180c500005040700305200407500500c00f01610003408006d211b611000306 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 411442185 1250 411440935 411440947
    0xa0e011d010527041e050105010206040c0b0d0b0d060f0b042d02070602030c0a08060d150e07030c0b09041d060c0703020114070305180a0804050f010507050d080708090a080f 76
    0x510fa103169082100d54801e051100110256a4548031941000580f840a01040c1c0e00c40e00166903440c015035000b800d101c5800000c001e200e815030082d01c2030905049000c0703074541040c070004096100c1105e0544126075510030807015101e0a01c2800d1850f10184c40903c8031b0000c2151030301e99001040740c2c60951550440b0f6081c1d40450550440c0c980b01d500c880c00f1520307404c0440b869405c94004510260214a1400c045003443c42d1500901c01ca541e800340801e1345181ca0b128100e4080c1c40010303890122032050002c0070002903210311016000d010a03425140d00e96a82004000c02e9501c03071502581100a1640c0821040c0c402103001a070040c020080d040e0303101e540e803804900503c0194180100081d0903414000d610380c1c0b40d04441d002e800405114080d0104405d0003e40f101b4142800034040e0302d0411003048281442000c401c0805c00504169080c041103403509402c0c80c9082c10311000050f03020041184072a00501c04039040b01a0300020400100d10b070351a03841c644a00c03918420000004106 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 411443435 1250 411442185 411442237
    0x22051501063c020f030d060f0603090f02010e010e0307030303051605040f05040e0a0f0b01050f0315071b0b090d090f12060b04020702060a03060302150a090b07170a0e011d0105 77
    0x1113006084008084940d1a07035003c550302c0050038140030310100c51410010000308103100e409042c055541185103407003001703559401503c021000070f440078140140c202e18009a0ba80030301c1884020b500070b0303d020940e40b43c840130080001402009070001e0080130701c800d000941c0f004641c1000d890040c1d0b00000c03035032282c0450782d02e040031448004166494101408007000300541c149412074506441a4001108180802d9240c000c4010f048442c20015000130b40ca07940319260521480c515205107045852181e00d401d00241403c40700710080d03a0100101c00c000b554482d1054008140c9920041282400c1880030b1a480509002c080c005544400060300d00d41d07220b504691000794010403450382c0b262441c60150144c8110711050f0700c00d000b040d1460f412100a002280c00380c0c01941d41c1d803803116003011440c61603504015410fa845545818210f07207945840b40082c5402d030785507219480d00c5d04003c400107000c10301ca00ba107012458032035803c02c829640c12100b581c612082c0f45424802d4030782c202413 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 411444685 1250 411443435 411443443
    0x50d05031204030504081605280801020f120606040b07030e01030216050f010b040b0d08180307030b0906090318060a021c2a0b22051501063c02 63
    0xa03203407860810440c24401010b8000d0000c00031200703800103075a4003e920a0314180f48404500c00d590708045115035040e40c841401d40d550780d180d100840e400245503101c4507940c0c02c9030040c2c486110b4114000500001703c40d000386109501420449521f4901401e106200d40f403402881d4009060108410ba1003185a00036015142c00c01e4610080c5000d083d40c0c1c0c20040da031010221101c80361540b8101400c001c1d402e00b805491079014000d172021400103160f0342e840303c280c2d102621001414007402040300c00340e0740c00c0c0022001140030342d24a40329400d160f50305505019014016202542c002c00150348620403c569100c014041250000d80303800040d401a424000c01c01c03030442455900700c0e000300390a600045504a010300400944109125100910000031101000501000b2002c40011001c00050034032500c1088a8410342108101075580e071032915031074034220001c400f0b20300018031103c0d500412001503080075a40040d0104441407400d07400403c8400040043c0080f0550201c1d1203000304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 411445935 1250 411444685 411444697
    0x6050c0a050708250303050106170105060f0c0123040b070206190519110d29100908030406020303010509060616020f030307080408071518140d02090f040507081204050d0503 76
    0x11501014200f013038500100202803d0203210085448099881704d05020b50035501c2c1a40d00280005242c805104254402e642242c03003086015900c3c1d1814020402c080101e00c402d051182110008508003850841c800c0c0000812000442d80a0420804034072a00d11903000d03501610900024107440310101020581d101718080e00010303082564030341410728060014540b18074040c40800410f01c1040c010300f0300c0030000b0004449040700405112903850040010903060354941824039126a607080d035581140c01c6584450056003005c00100311609051000f00c0e4810401c07644035203410003940030b106104d20480c001a000c1e150501c903140040d10104121071500b40c00418240d00c07039a40c2d11003d07540d42204d01030a4204000c41e0b030b403584000e00400c5e81da89002e10325041d410041e030511002058a4500d02c450035800500d1441100140c0c42e050b0aa90290445210140b000d19040c100180303440e0269010b030005502c4014046d1010303200c40b00750340544000b00c0c0c07061901411800c00781c0ca503010341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 411447185 1250 411445935 411445987
    0x20d170c0708070b040507080d140a1b080a03060f03120c08160f110303030712020d09060c0c1b05030a08090307031b06020d0e0a090e0a170706050c0a050708 69
    0x19401041c030010a034024415031286c01190a595258041561500e9220241c0404030306c4052050707040382c00d81c6001d0610302455240c0081200b0304040b501c24520450041035425101c0010f00c0080030307a050185001408103500541400e52450307403040c900608410000003000704151982040064810442d030340101045103143e40b014550030040d500b00120041203503e00307035840d0245c02034140401603a124142545034047c440c55040380840c040e601501100300d041d540c0b0003400300014817070300c03500d0840c205650f25200c042c0c100f40340c0807006500d882200103070315403856003c02607036030b00060b11400035600c80c0c3c2d51a210804000402d14050b42600001c09510380c00d0070300205650310411050440b51a5400c89030503040e028400c0d2400791102204603008203030f02005100040d4280c000c823908400e03c0048481c0700c1481d8441c4043c00c0c4c2080001345039604006005c2c020b000c100c3c080d194101008100440ca4402c403144050721a2140144c01007844401045540c04042240b010040903101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 411448435 1250 411447185 411447187
    0x151d0909030a030b09040203070302150708030c0a020c0d110d02060903010c02010c08070e03070308210106080907090e0d08040212100b0a080a030207031412190906020d170c0708 78
    0x501038040d16500301ca001540082d150110700403003480c1007020301e4040d540140c0a01080360964083c0400c107e00751041002945041003a080050b50b00001980704003000303040c1c2c40c4c40c0e2101c440000c0c203051404002c18898051f00d85603001141e030411132900c01107021940310000310340c180b02040030b501600021b42e60551800221060840d0103400443c82505070380c4d01d844080d41c1d94801910f0700300c0031072186a0140e002c3d03802800003805e000c0041c24048000003c010107166541c02d000642c8109812041c000380110007031040c0306030200b004001801d1a40400e01901d1140e45186581d0310f60810300c10100407010300441c2c155182e030441070009a01150580d4100c3c04e0512299014142d8204a10f000e5000c141c40080c0b801404100001c0c03003903240d8040e020051440e1602048070802c1c01950390603024903c508400c9020030302c010805501e002c0701e180b0010f0b80440c4c0180212400360320450941d04044400003413564402082205109081241c00d0641c59413140c0314014002c155004129041c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 411449685 1250 411448435 411448441
    0x7080612030c3007080304082802060703020408030306130b0306090105220f061104080d09081606021e0109231e03070206030405281101020601151d09 66
    0xb02080c0102410101010b00324107421415000d802050310006401100405001c00e0001a000070021342c0c0081c000d800c014146181e41d2440740c51000c040c0320503032010402d8001c4514454050000e29070002a6042c01c40c00c09182004940c2c0b41d10004240512400300b1910410043c0d00543c00796050000280440750140b5150745101d00802080e22640c0c1c0c500701c1005070860401c0c1e0080400e0708030358005031914044d04a17a41c2c040103411240c07081c20a501d428000800d04041c20007650010001c11760702d07040103d103800d2005040c40581d17034503110030350042e19041c8102c58000801d41062880511043c070140c006800303940c014001c800e002000e4002c445c036035048010404030711f000000b140710260340c0700324088103d1110840ba4480c800000d80c20a002c54005807030b0030b001840d4094040c1d020b49445c50950b41c0040c030007200c0203400342521058018090180480400d0100ca4070600780000c04003541085e2072844141600ca00c1141004408040d09621030031621414812510143c0300d180141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 411450935 1250 411449685 411449707
    0x1207080303010806090c0109090903030905010e03090906090709170a05030a08010302030c0d0b01090b1915110d0e1201020d0c120b06120c0a050c03030420180708061203 74
    0x107802071040e04824807541c000f0171030700b01012460030100c0c0c105840d094400780c0751826840c040c3c03c080c0029030526a5a03400354003c140b00780a85428100042d0145945104000404c454210003801c0c26018200030300c200304009810072200010380d040c121030359400400405a00d0721f032441000000b00503000107e081e03164640c10114040c1624030031020788034180006000c0c032010b9403000c030003d0402d100400c0100120b5006a005650070200134203d9501062042e80c044c04004065205c5104010020303400c044084d804541e122200c1c032100040c0c07800c0340900e5001840744252600d858407034994201840804802581125116412242c0074040d00541c210f01504108400c10040754042c10302c0020002e510701442210180322032060140003d48515141007440e40124040d00c00b03000c410490012003880810103140700300d10404c64001c100514216860807003041d400024000d01e500c2441180450000c0c20490b4440034a10707141d10181d50301e078000341d2075000300603203c2018000000c60401c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 411452185 1250 411450935 411450937
    0x50304020310090c0e061806040209040608011509060f1d0703020d090f0b1012060c02070b040b0405030c041404030e04110703020604060507081303032f0c06011e0e040212070803 78
    0x6501c0109610086c0d0303260030600010100e10305442a0040340f100014040341b41c25809005056030142c00042c246880d02022821683da080706520756460320030080010000e1402923501a02850491680755481d1047d40c6200500030711440c2094650040024551482541a0342186000750401d220389250f0341000300010099440907501034107941c00082e802d4403401201811a1007c80c84a124a40702d03460b0b910040482201090441c0104c41d8002482240340003d00060b10540748107d41d52031400c000c052410304060990b5005500300250100c0d40b80070f01c2c03941940507070507080120b801c0191b04009001007044942d91000d0740d201107854814140d0010300648241d1080c4010806500c0701c0400703517061743c802c66804000710340d84170304400003c0c82900210881d00180100c00d80400740703008954025044080c004000410119007280c440310b080121500404403281e241c030070000c101000d049804280e0062151580740000410b0464845d004940c1c00c2c4081c0340b060380c40c1c054486200e81d4907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 411453435 1250 411452185 411452189
    0x3062215050402130612030507050a060e2506050702060313060e0c01120608060402100909060932010b18031e0715050316020a170306030d0302030103080a050304020310090c 76
    0x184403036130a9800310f400d540c4549016240c4001170030403418000d0750700712041c1c1c2c0451000c03070310740c0990030342c000c0007071030358048e00301d84048a81c0944520610700d12a0b000280341c852117180015501c07041003203001e030848112142290182d8007150b4030ba5402070082e4118a21420052074246003160204002d0000702d01707803a0741790090740c8040140d244003c0e95025100383d1302032660160810408100149002000010820914144045a1591007115004a540503400503503034941b06d580420070f001c00c3c014071104e8004c054248250b0b0300c00541c12081c0c440c00500175610000800a0881c0d40c041000301c501080305030060032a1a985811501c66080ca0417049010016205003080828070181d406914994003d41c0c6e502c041c1140d584091040424200001240c2035001d089068008204e102c00c0e804010f01c00d98510030b6690816206240c50142d1054101d400c062042c4010320018100d9007c4404604083c60300d035840383c685000080c00c0084040d220718886103004814002c000901200c102 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 411454685 1250 411453435 411453439
    0x16080d0b0607080919210c060503190b040b0402030c070506090615010c0f021201052203090e0408210103020f040212040b1b0d02090901080106030203062215050402 72
    0x1010a00d04814030041c1e01440381c0c000d100c8103007440f1411113420000c1703040c0c43c00500020701402070f03542c80c1c800c03404100705a42d02d016445409440181031154500700b000090802e40381040c69490001144038480c1d000781f098251894950b0150840743e40d40da040250106d01c003c000719501e0500c41c01e141031980c03000008075580c0c021070b0000b42c0d0181d400700710030b4800d40d50591082c560640d00001140e03c46061039048695042c02524407015031921804206005407610002620381040c880385401d40d101c0301601000d4800c044184c10001c2d50141581d422106110b40400342612107180024544c011400782d4060324007003491000a0a06100c242d9049900a83d1043c41040e0004140001d07441010301090f45400818003280001c0c200d00704d80703179001c50604908810b8114600c4103142507409a033151602070b4010441c850745180c030040f8140100f42c1c0000070030106117582d01203a10b81400900144601c03807030f00821040315100d004d0003103090780c4c49402514441c42024040009240a88081e4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 411455935 1250 411454685 411454691
    0x5030d0606080117030405030607120212011e0905060105070314040b03131502031311030c03010c0c02031b0d0308100302040609060303030c080c18011403131718060304020102010216080d 82
    0x4444c1e01010040f6000c1d501d014002d02081e5550780400d13038025010006042c0380c180d0070800742030900341401d440760280c00c1c07440040c011108050304135200c5290b150494402c191400c02442000d03a08a0221021241c2c982449a112051500c0380da040340a9a40071080307031030000003000541e0000105111905104400e44043c049101500c1d41c1280070441e440b444c0b5440040f40803022440846030b000954000504840010301c9100101f820359000d01003100114204607021011880c1c240900c041e030440544207140c201020310300061300146425006000d02c01d00c0400301e80b0383c8a10400d480095038000d4414031078255900c1414004280d030f8441580001d203030040c1d020075075101c1c1944902942c1c0902c3c181d410300030b07007030610803100745446049030521503c51480b20100e20722501a51141c4070600c0f0a004034189420f101c000e2031007201402102600c00c100418050000d01a0102c0d209000d0b03409130b445e036aa0307100503070081c03241c6030a00000b10100102c200070003001000806142003005c10078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 411457185 1250 411455935 411455969
    0x905030c0d0509063106091809050a020127030506040b0c2704090c0e0105010f0512041b17010e0106050a0e0a05130c032006180d05030d06060801 64
    0x2240e643c000c10308101d6002c41c0070410610b040751007a01c0b1036207860141880c2c004440b0004020b1021800702d5004c000498540380082040014107108803c801c6e069440c180720302085650b803e03490300230959000341417040b10040c8810b041c20250100d06101c2035500c1e42d4400380e440b400c0455440c90100c40031102c014000002545003004401500c01c0051311140c00c20409401c8401c40700c60036900311101d50425034035203508000c943d002020000400340880c42010550510300014032000d85488003405205042000c40711591050070041e92080d0440d210100c1c145c0300f0004042014007640c01188006113400c2501c0301030b041903014120100440c0e00800c0741660f00c6050040503141e42c800c1030039a00b00400054404103940c0c03c1203a110382d00442000701140c0d1640c0c0d443c084a030a0700180c40d121860390008a00c01d15500044040c2501110007038142081074556030206034548101c1c90007900032900d8032007045010800e450205a9a8000344031050702c0d8980100044024407514240510381024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 411458435 1250 411457185 411457187
    0xf040e1e0103111014120405030d0204091e020f120712050a0209090f070f110a02060703050307020613080901030903031b02010b0307051f1b02090114041b08060d0203100905030c0d 79
    0x1174022005a0701d01c440d041944034442281d000310002c1090703440d40420810f03040f110280384000c10140924440025030301c070018504002008821007900c80b103601c1003103450407a400e80300a035850b14020642d0065181e4562604580d141071034000303585814108410f0003c80c0b01d454000d02140340003130f1500d01240e9642d4028102d41f0300c0648000c0301082c00c01082c40303e401c0c4541000c2240e800729200711100b04c1d201e5808609030f980801026000154003000303100300164103200e1a034015440101c884900c611032344a014607489200300700d0381495903400300d41e020540a42c2000c0841c2c07000c2c0002c0e142440c1076081c0640070300702801c00503229014581020405250010000d0000102c0c100480000105260241e840c0c10301c1184400307004203080c00510040c1c1d901500c82d406440300591840000c0702240921055880081d03d41404811012100590583c4103c009520480407180c0d0207486001c0e0000c2828200d4400410310000c5c00c00c8019418048000010281000303a40102c4080e4420840 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 411459685 1250 411458435 411458447
    0x5030a0b030c0114072a0807090219030209030c0a0e1501030e0601030326100f120b071b080c01020a020d18050105070201120c020a02010908030f040e1e01031110 71
    0x2c0001d02142c80d41ca020140700c03000303e019101c0d0a10075440d0000720001c196400031001c1740c1840815054080741c00510581d00300780220801000c20040235030403c0c0e2070b050f8901c80004002c6c0c0a808040e0b0100f50045150b5003007110741c03110710b070113080716105030307110300d440031a029040b070383c070300c40fa441c19006010300c0e501c2072240d8610032000c8005410140d0039035508440e4003100e910301c2081078140703c040300c29050022808034040c80100e507546000701d190181d20fa0b910710265218103055a0242e0000703000c202480910b950114072407401c5034262840101210300d9028400002c1c0c55010b01107540e01d115030303055004154034100c40e02203487c0301b040e101040b900d83c40d000b40c2210b08803c180504102e20750003100a031000a1050419107245200040450f0403a10140c00b5038005034030841441e015960040c1c105c00213050010091858001418803988491183d445110301201c03c0000040d000c48070012006005680c1c0f40241402d07513540c1c00c02c3e6004084101c641c0348a1841c1008040007507020b4a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 411460935 1250 411459685 411459703
    0x2101a0d030e091b090603100302060c0102030a11040b0a08070504081b031005010f0b07060b1002011e02130b0c03070614010f0906050a05190302041b0909020924040807030305030a0b03 81
    0x4c1031262420038200244422a04060f09200821803440008001a901e486c050080000b90308001030300c80c0340801e0280d0a8a22003190440d59410401082c031900741d51ba4104c50400040e420500410745400504031a82c1c407545d80301401d240949015144100b038001d2020000d400100d00b201c0744140204440307070488200f03105030841400d030000100030400c00c6001815556028150000d40e81342890081401e143e1845c45440042c0d54420214486081a003c2c01c84001d502480860a0002c685003c1d11044402d00403e00ca00b10007281c440b4025508100301d5540d664404400c0c8007600d09020350320740e148020301030f0885c08145071802040204461240c00f0848800408071130f005440d24061012005d5806076250050a0705107011025803070703e000d41d150b9440810200104512100310040958142c0e07040140191f0041046c040a99211143c40318408408a50301b40c880e80c40c04003091080c4910761010b07801d8060b00c400001458bc0007400755201d140741450034031104c0038020400d0b40b107100309 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 411462185 1250 411460935 411460981
    0xe1e01140d030f0c08070f1a0708071b020303120f010911090409030512010b040503010c0c020915190f061202031b1606020714190302101a0d030e09 65
    0x81210407011a21446003d8084200e07400c100313040b4040350303c6030b800350342c0000c405580c4010101e980004028144005100283c0440404034040c2406a801494080041c10000c20002c0210640c40c4140c0178004100b41c0310f5000701101da8400d40f5100c000d803001c038202d80218400007404000038481380c490207580d14441d0218451450013541c0002c02c001094001020b84c10400281b0641030303200c031403074001806096041800c0740c68074640020142507603224151582008944404100140c4901400750340020402c4030b444007101d00c1c03401180402d1004d4203456424a4101d000003501d40d400d0040d002036526580d140d20607410040080d0b02a44000e079000c601781414100c00709a076810b004040c181210100c0c010f900e20420719110042660000203081d200d86ca000703031061445c00c000300011060380070070550140440b139007610003a494005c2040da05400b80c0d103440400240c480c14031402d12441b40c000700700344511040c43c240104850503100700c403405a210480858040400040403000d54001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 411463435 1250 411462185 411462199
    0x11106090c04110a080c0d1113030501061707180209030703030c03080106051213110a1e050d0308010b281106070e1c020303040909031d0402310e1e0114 67
    0x80c95901c3c540f42d500c4940b00e0720703c4a0765591a123025000010040c80c1c0148480d0fa047da0090540c104a821030b605035000c40c408411030541c0e10112840810680111030750405a483c14000c15942600a0312a10010a41c18041c0510100030941c004480102c031900964841d20141e0701d03031f030040c1c405200300401d40d03428441034000140c0c444041102428100e1058608180c10f41840b00131417441c1c800c075082100390710b0301100821200c0d90301080c0180144011120f035880d03002d00d61400b60020506008480d940203000031108800300641040c07030003080c02410f4814290002c844018985910486003e860380103035404500c00c144900706000700910700405580d010740182601a22000600208a825001c140400a0544160311496110030301984808011311065214040a49101031050b441240705000002c2c40c51002c200c2e420b0040c103c03501c00c6181c1c940c44444c007014203500750b00a400e030600c4481000f07009c5420f20036058040708140740440551362503200900110780410315040d04410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 411464685 1250 411463435 411463441
    0xb010510020c10020c1e15130e1302010318210311041403071d0a0506190315140103350307051b2a011106090c04110a08 53
    0x6009009030024102034012100e160341e80d840416a040e1445031440c0158105480062a504090000d0104c15800c400107990f030654010001e0700b51003000700b5040340d005001c0341ca100d00040d012507140140440d41d0380082d191401c0d1010038900844600205d000034108001e400030b61012903600c0404a501c403004d500310003c00a401001c288072617105604268549001429140e00c110081c00906400b070020142d903000b000500d4a05400d5503c01c00c0c41011200d062081c450880040b40d8100d00d40c80b40200c0d00703031645000684440700e8140101d5200c0304810000040013803500d01003441c90486c900a02003d00240c1c001c0d078011b07100b4440039000240e00c4a4460341140d00649441141a22a0200e0001d02600c4c14070201d40d0011200000803c00005017500a810990301008101405400418003030880d001748a0100b01e41300402c0c00b4841400c40c2098040c0c0c0130316004605014101c0c1203c146280525413242e803005a41007050140703103040300100000191500702c7e90058410345410650352 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 411465935 1250 411464685 411464689
    0xa1b0509060a061407380907060c03030e1504021c0b0a0f060e130b0f07020c010c03050d020d0504020f01020a05150a1d06090c0a060c2a0e04031b0b0105 67
    0x521504c80d054813010810800011030b8a00188052502c801c0c10303118480d080c2c1d04550744c1b0546141480c0010318a4001c100d58603100060340c405035112031420590802c0ca515098014100b00b420000460180c1c03d00c0c4030201480010f0684124000c8a24030550003400303403460718128078a80003030450b2500000150a00c54540c10640c41406410390018507580c2e14255102d45140036544101c4c2d1080c0c1410030800d1007402210035400c0213118103001064202804042d43e10711000360358506000c0d800c81c1032003d1601920559000c0c2601d42e906541d81d4552041c0c250080900301c0e000c03403191040b80228071031540700007140c0960f02e9106006100040c012004404055401802c40d442c0540301d003c0200383d282d400607540e140c0d140040c001c01c1c00c0d04250010b5810700141c482c50724002c0e18901010050075a1044005110a4008500540b003190604c841c007428250300380e844000303d00c203050015001514001e0207104174042d035100388100f41c070034611441c03040d40c120000d001e038120540140102c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 411467185 1250 411465935 411465947
    0x240302010503130206030f090d02060609010e060406030b090109020a1a03180705040606050c010507020c0f060d0216210302070201120b130509100b031621050a1b0509060a06 76
    0x40078043c1c181c055000e0b4001050740d441150480b078110800e400f0300000c24800c00141601c00d5150001e08900c0c0b4000c404a141c81805118000714440a40c000c20019241c0381d20000203180c20180505462403c480d00324068000240c040340285181b00780028120038001051024000c44a07200f8550307104e00d2580d049801d914000b4500e640224a0001155074941c407403103004003260b03101e0541b030700d011145080c00c41e440141610299001040c503100d16a0b184000281400c404440854459401c030701440000d005403107451354210040360000042c00119180c0c41040d504609940c204281c0d1403e003182a80651074000707004c20101401c2c40380c03450301ea40218400313030405490646031903944980c0304190341c07098581d07045640044c07100710310149041c010364440c050180c1c000c1006124a00d1110a00005071107011064180524800780d4203402c3c8030510000e43c0c10004598881034070742040d0511400d08038040f0740d400c0154000003102d00b08040300d50f220340401405144914070308a010350394 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 411468435 1250 411467185 411467191
    0x501050319090308040204050105120a032001050f0a241206110d050f09010b1302090102070803190f110a0b060a0f0305030c19020319020a050a0308030a240302010503 73
    0x140001c1c42000700719a945620911079414065940d01560f410a401030108865040e00700e1402840040b4288140260016801340415414034002194081c001d000c40113208981c641100c09500f004140504070300c2150b070300e42c007511460404010040348407a01c0e410200d8810300e45006014401c000300000e01009901d824001d00950000c80d000301d0142d40310722150700c4150101e5203250307500e0500c148403075100d920076030000041008016a2807140c0005224545880785400740c1c0b40c00113a01001030b4820311240d401014484112501c0e844030444030b10304078540c0405003000035010200703203240c40c0c8100c102c1c9542300031310006040d5151f0903444c1e030360b01c0942c007c10050700314401d41c000080740480010864011070081000c2c41d02e42010b02038160070444e100074107800c01100d801005025035008a450b074244850303107450402207045440807550b013104681c440b540c000780c0e0a4001082c030202000651003500000c40800099041d010700d4182c4d9000072008414030100c08000f0300055008100560b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 411469685 1250 411468435 411468451
    0x10509010b0307031401091416210605100f03030f02150f16111b0310020f04170c03010f0506010f0c0c42080709080c040911030a2003150105010503 65
    0xd40701f04152900710140c10603e8444002e40e109103041e03a50965011040b0010f00241150769054140000b0b914a90881c0c5c030307001038032090340c80f40071600c41003146114400a0000042102c11550380e410058244040c520314032016001c0c0d4185000060b280644061017140075100107421500d0f0207030042400c040703108e03984050243c42c00c207440310b030a4108055441c1c14035010700b540014188509250030906035105101286005114058580f403001c416501a10803111000110030500180c843c501000c1000060305035103442d035403041d42c0880d60820383c812142a29012008269040111900c2e130b10100040c2a0041d507240078014044031001c29509403014025040d501c44206106900801e0045d042580c11080c0c090031a00c000d8106078029030001d440d09140b409145050901c81d115861148440c0c400ca0352440d126040240e1000980301310b031000380444800789404d1034072003010000305c41c08020b240a1140540454900001c41d0308a2013009404801035919200042d5220342010307101302 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 411470935 1250 411469685 411469691
    0x12030a090204110309010c0306050603131b0303050304021203070b04060b01090b190e0a0f05040504080d090f060b220917120a0f06140112020405060c0f010509010b0307031401 77
    0x4009641c50f40500c401c0901001c800035a20704003a0851405c60f102e181501d818503050540030001b550325a41501da00c1000300d284030580c0e00407460300101c00260351a034450504400c090100c10b00d40e1010141d88540d00c242c1b2229010420000619624010950000c000da807a03a40010b0020380580c115680000c01810001c62042d03c81001c80701c5504400c212501c0350003540c80e2010702550000912100d40c0702658502080343c10281c60100d602042c0c002d0b14022921600441e00700040c0c02d00700d5045001143d81006040e806140540c1c800455030301c151030301810024030074818500801c0000f402500042c0042c0210303247c10a0300c003c0c10b40c0c0c1d50150703070076400c807200d400c80544408024120761b08801000010346c0b40c400742c81000c4a082c401018000c500c0c0c440184061010162070000b0ac1ca02420020381003a801c240c120060b10980d00400d4200f1404540400501e20005031040e808160030b0080c001d507030341d1481d03041c00c0340c012000c1d2541c95404050108041a218050706410700240c5c8004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 411472185 1250 411470935 411470951
    0x1206010e1201021803060a0b0a030f0302070b22050307120b041401090c061403010b030103030315170106030201020601050607020a06110111041211030609030a0f05090d03050702090f070212030a 85
    0x28226000350840c2c0f03420b403160350100384c40c9190900c80d495008050150410180c01c0c15008a0300682c1c1c0380c0001440ba81e800c11540080c50b000b00f0000000780300e1a000c0317603a56068060030b5520418441e0500407018400c0402082c50315012603010300399080000e2100c0d1812141e06c0c1d8a00708000604141d40c0001020002c020b69102801041003c50042c2841c01c116071800d40005c002c1c3c244c0b5060500c070b0307100c140014001205001c040b00d04483d010314012a003020480203040e590103140d400200c1c2828660308141c3e2200064021a0440c0d000b40c00f5189640e03070f01c40c10300800d440b40301002940005d5032030007171100724002d07080c207200d146001000041410000c01c2e0185203074845e030003000c2c000d01e61141c00d00c10001f2401c04800784070300540190160b410012881a0b0b80d01a109100d030600c500c261a14014078800ca040d0349002c400182030304184200b03814040c041da8002c6100343e000721803340005a0109009801900a5203590f005200c3c0407019114281c0ca1303080a4040d8030007a03155203807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 411473435 1250 411472185 411472219
    0x30c05040308160b0c0a0e0922060e190218070903080301090b1005160b13080d0c0206060303120f0c0702040510140f010c110301062d0b1206010e 64
    0x14050000e83ca8403000b40b802c03414188007450120040c41900001c4007017003000c0382c2562108144448150544440b4802e455107482c810b0703026000d02c505c01e040d801c4a03d41c0c809012580d0050b011608486003940c6520039580b90104400181020181d0441e06e40358900854040c50800981d01200a240c40c1c483c00e9126030b1110b030103510a174001603078107480d000300413020310b82503142000d0075803642401841d00c541032421000040c0300700030107085414801c0c0002c00721465001d00c01662540702958903515000070400300000d080d80d802883c0144510310006803203003000000c880c408840155038140564a0306c41c42080c040000300003403000c03801030140c1d80040c9c81c0e901035103000d101050300d4040c0540c10030140355407080450000303030b106008101c035480b2182d0700030525010050300042c89030040a00341c008240940410360018ac00180c041078805152950900460200a0300c0c00e0348150712b035a43d0101d6182801703030b031400c40b50b4981103001182c850f600900740d1550078400a41401031803101f03205 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 411474685 1250 411473435 411473437
    0xf2d1406090a06050306180601050108040b0a0b03030405030d08010806011202060318010b060d0207020f0105040f0e1e04050d09050303030103081c0e06090c0118120b0705090319031101050105030d030c05040308 92
    0x240c82d40307051f80e00d10322a0040748040c07111502402c000e00c0e1006492600d40c81702e0f0095003010b440b4000c290365400000030f5603101801160094900503041b200850708985c8010502003091154600d00e00600c0004903510f000705003a0000607800030002404c7d925124100c035407040550900503013642da5044c1d0104a52149000b804005180d07010058039498603005011080362a03039030003810810100018801c89984098110558182c1c44a0140d1a91036841030601c101b603d407a102d2420303594800708400c10000040e28204000c055940805d19a543c0c6c040c11b60300d000031f0000411808050001803003119041c0804140d6014160001c1800c002c80c00c207041c20001d00f034840902c1c0b13400c116000842540c01502102684169102c598805450542111407094480740003c0840d1900e201081010703100300c0980d4080e01000702503030328420754020903840091a24104401168014181c403002d0f16040c03140504a8401401400444030b9585049000307000c00c0441c20305008003400084040382500f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 411475935 1250 411474685 411474691
    0x21903031a032802030c1305010611010506091305030d0e0102030703061a0a050f0409050112030e0303090f0f06071b0f1212050306040f2d1406090a06050306 69
    0x620300041c1040025a40e41c0c2411101d0749450107640701d04485400480000755400c030284a040902d031641d4003503c00241004d090001d5984e10441444200704481001c2c3e006034103d03941c644031a200d42c1c401c201103609032201254056404000c01c0009803042c4240020341c0c0e0054400e109891401e0922082e02c4100c982e00081c04440c4d0b9408410045204d41501c03c02c0040d00e41780b040020304240610480c1c036144030394010041000804504110350641d04020741d4080d10720400c09004a685645c0c0d40c1c44040d504007015400981c8c186200b03010f5050100890301c1c664000341181001414500600c904104881115a0004020400c260209144079040950441e401410704001850040d0001d140c10098202d139011040550b035900c0007034250304130a1158402c60409503101e580b1400040c0c014481d4400801380a420240d42c2119242c0340100c030310f505188013100850941d851844e0340c046890740b0110882c6c184070384012505515080380141e912140c52240800e107581c0303c0700424203041d015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 411477185 1250 411475935 411475937
    0x60405070302040b0111121308150f100e13080c01090c1403070f090507050d0515150309030d0b0d12080a06090b010903020607050106030512041a1612021903 69
    0x480e010301c11072406001d00c0310242024a004d40b03c188410040035111485e07a131160102400c0001d170b400742048418079507002008008141d8a08959445c060580003404481646080007010001940104000180c0c000d4402650360210f1903900e10000b01103150701600e00f950b038110140702c801c400320000d009220045200d569454012803800340948001702910240e1f902c241c000c0302c41409131082c25081715007100c01d0500d0124031034440074810769180c8112580c0784000307400c010030003803008404808245120010b40302e0181800c0940e038003a55501054070740c194960420410385075031601982100d082910010300b0744000d41460303940c0262101d07004034030001045c65102000001c0a40d803040c2e400502500e182070000240c0341000802c010200c2c00020b00c11140404c00d10103010096000c02c01841d44941216291190b451b00044d403500300e40f140e14009080070b4240b8408400030302c1581c14100d1100c01e140e40c4c0c0e80c41642c8203110942c13202c0200003144951103030305140461900f0940400d40c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 411478435 1250 411477185 411477193
    0x32032503020a0504050c032e06031406040603050d1d0a031a0a02040e0103020918100f0b040b06030604020f07151d0c03061602010f1506020610032103060305060405 72
    0x1841c4188840c44015a2145204520700b104200f12428068226580106e07a8a0b440c0d81d050b00b884a80780f0024031200001c81065641a008286117405511010415810f01c070303900a5665a80700304016224180001002d54104801c0301200c40c0c01203281203101c1044c3e41c2e4408001249030301180c81c01c415031f40141c0381101e11484880c07116440d4044503420a4401c2030075031400c0d043ca80e0318070810704107110017406245400001358803940084c0101c8509c40049040d2006409002380039800745c41c654003441052403030030001310f40034a868410440d00702d10261125003540e460100b003100039000300c01003501080c81000441d0001c4c04012007030140780c030020710000704a0328010b40341200e070305c01c0580c5a1182e8010044000b0f10b540c000351095105899441c1c201d03404100329002c03409800d44078040900c050600810455034400c070f0040d01c00b030742d0300d59088038034036600e2000c00001400c003440f020f08810304522500942510483c00544a00d11074200483c1440d0340b9600c05103080000c9a0a850300c1e04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 411479685 1250 411478435 411478439
    0xe0f13091208041a18030a09060207120302061603140703020403030306141c031e080a0e010524060715090b0601030c02030901081e0103050307030207320325 69
    0x700c104907000400001d00d4030540030700d0950b54245152200c80c01c0030710b1420400c000a0b810030302c942d049200c0030820f00c003600c1d200c103160345002d030070401c07903024890150085000c00300d4041c508011416044da050b0f4000c044036160348401c00e00c4030785020108020591a0b1480a5012558105450240f201135400503580d80c07540c00d0090445046801071540d03003400d0310183c4020383c0c50306400b0034a10307840070949591122528050342e051150880c840e4890128445500c14680c11410f458455410803200303000000b1101c24580c202c0c2c00807075210501c04142e8440700c84070400030b00003289070725001c2d200f9031034140c0a441d42d420880b0221588a280b940b5802c0d00010084904442d41e0409800e00701401241c010550282d2603006e4140b420741000040d80024600e5807a100c4200c107610080c80b0341115558481c104951242d11400e006d0b0050302c20001e0010b90006060150480103c064407200a100c0c2e100e03942e000110400310001da0316208003400010154280311003140d904c4011a98261094 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 411480935 1250 411479685 411479693
    0xf02010b01050708030c0318060a140c0a0807050f0408070b0403030f08010602030a031e0912230403030809011506110c0102030f120402011b0c0e1302100e0f1309 71
    0x39600000581c1004414448000007514540070360b60808a01d40c4a65125511000350441c060451040c5d40b41c0c0d0700c0f600003407001d0030b19582d000c440d030005800310070f0f031059860103610320044c030450000b1300010307030143c0000b0f91035407040010b171900540030400a481c107643d0301e004520b080807e4101c201e41000001f02002015046030a202c180151400c00030303c0c56142040180d12400749441c64001d05440f900d0a0705000502402d030100540f0382041003190b80c01c175041100684104e104850003191a11000210501356590000482c0d41440044c030300d050305581c2c04983c1d4010143c0b00416035904c0d81c201000401024190001810541e9200c1c4881ca44d1a85220b1401c2c0c0742070046419034204100051051004004071201c10b00140101545621140700403102c003507922248124001008141c4c2c13040000000b90300048405400d00880b042d22914104201341e00020002907003c4042c040c80807006004901000008030010321000e540418400454000303505000f142c0c0ba0143c2e1224414204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 411482185 1250 411480935 411480941
    0x809120403120f030c090905070201020f0706020901080f01080703061805060405160b0c1207020d0515061305090c0904061d0312070c0314093f0d0e011b0209070f0201 73
    0x40c6101d40713000d01c00703100c070f030399020380401181d0250344941500e500c00509400d0007501282e00068813600030310b2ba40d61031070820100075046079413450700085669010032031800440b10b00606a42605024088042c07540d520783c401000c4580f01c85a8041102a45101003481844018801c0380903401400b4600402c00e0b28844686940d04a1440e25105000e554000e040003e5900040c2c001e446000780d0341c249500000d41041c0e102c280080c8580b080c1d90b030140d420403014403414001d020503255002c3c5004000c9510b41a01c104030390941507580310f4110400c1ea803400c03880705504107005081c00206020880400c00000c484030350300d41030540c400180c9003c0310100381c0c5000e51041d41c0380390098044501d590002c01b0501a62002c030381c515800314590000b5526045d0305050006581059025050f41002c4180c24011300c00c00301084034500c05190743ca1031004149280a400e0980d160700c907944c3c020303006542c4002c0740800d0000e10301c1c03125507050050b00d605030207500800e025140d68000d81141d4030001d00b5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 411483435 1250 411482185 411482207
    0xa02150603011b0c1401020313060f0c05070f110301050106030207020a080f0a0b070513091410050105030a090807060c0509100f1e050705010606030501230303030106080912040312 79
    0x60703031400f40000d03840190034400290f0120b40386440344221440e81086040008202c1440c5119440041441200d12400080740e1107584100001e00001c061000c0480c01ca84406001f000400c9082008100048055044a803418454088041c00d29440c00100c0d0031650700340c01c4071010903030005500040d403400c401c0d250018918480205a028031400f807403600ea02c042c020040440a501d000308208074014000d0391a030121081c05281c0c0e0a5840d104580501030124a1011007045900410030203c280b5904030705440703042c0c44961441c1c59814400c401007840002c1550006010300010001403034900031048500e0b090b5950b2922800d80c4d07810804150346035007444091155891481066541241c451050b40446031090400920b102034142d03200e118100c0010119460082e001c41e40301d400da80101e0594121060038000c2c0c40410130600802514082400e615038018001040101c0c850154198000c03a6201611030641892002924982094004503105000c2d1802c9099095101941c041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 411484685 1250 411483435 411483439
    0xf060305241005090415050405072310050d0f020304080304021503010627030503130f0b070203030904090305040513020d0f05040f020405040212070906150e01080f040f080a021506 79
    0x41030300700504a00d40c488980d2040d50b000c2c0d410000005e0504ca4810410110806d2400044c4102d01d0140707440758a81d10075008520f240c02500c03041058038603001d0300c070522500340500080d1100b001ea01c1c040d507a07034212101c1501c626443d51806440f8252a00255004500c03600903152a420980f0402c041801c459081358027414091004111040d84860f01590007692058101c2410300326000d11122100b0b82d8001814a02c0000791420720300001d945034100300c443d154061a05240c403140000b070948901035001c1c0d41a4000d000c088182e1a107607000405540c882d0404c50324084e40c88011441c400030b41303900319998540c0420440380b0308146000d603070241034002c1410003040c601a43d4151080c000588060f0245a03241e001800719100d035408050000380890841c0c0e0400d580d044040007500407400f5085180c8419460300c201340c2d001e0002440160816140d52405507070304d8292800b031210040046d100100010081c5c0c01190301c503401800c807038100350301401185090580d45c5404001c0646818 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 411485935 1250 411484685 411484753
    0x121b130e0a03031512030c020109090b130203090f07150206010f38030901020408121204031d06211024020c03010509150702010618090201030f060305 66
    0x1240010300820010309095060400140f00b540754080700818400b41c1c0c000034036115060007114141a000800e00c800d5903c04d0313a500100c3c6880d14904415240b00000082d0041d400d404101455003003038019543c441501d000311040701d552103a2081c501511a408600d0b080000b0003507154040d03040c010b0501509000300208409407900b503c61010394031015401d800c07490a681100c4c03c01c1030481140c24080c0116508544a00380012058001c0d4494410299144034003c4041d00029180c8203594280345d40c0728107004959200e44080e1550048060300201000004c41d00321110350b2000003400804070800c0c80480128001c098844031024064501c0e2500d071112403042000000b04400b800f00300c40031807a0b0316595000481c060b494031303605000040d4154281010403099910000702035000d07208004403d011078031203e0f4181c0c2254502d0088032006140c034001348241c1d200c0c1d0341158040ba481031500044181c0e50303c1b213400498100343c104450355006500038150807045d511600d4003280c0e541e1484 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 411487185 1250 411485935 411485951
    0x180e0603060c0f0c070e010503010c0e060d020306011106010b0d06050303092404051203030417031927030f020c040605060313110a0b07021305011203080402121b13 72
    0x30707540707420051039401844000240c210781108018103445210b0802d004481681b070715083e010030f03680024007690340a586004000d6440c02e10540019103603401c042c02041c50300c400c03000060701941c00180080d05202c0904509486a1002c008040c0207180b00705009880703519004040040c0d461940c0914032907801884180c1455448900d2410380c4905103840d500c6c2c070308811090700c1701030040c0e83c40386500001448950b102c2000c040000c5103c0c62040f030a82074900442544996140001d0b0f61005025400f00e0903801c42840b00e40c403050b107451000340321072400703103901c520454103680e0400e085000a45c03001c02a58040d07010030107090310283c111020f00000c0c0c103110105426000050040a6000940303181c002885009040c0d0454100003520380903034291182c100c4100f5500030309040b40074a43c0042000c48544091043c1030584000c81503a91001c8090b031001c81e5403c9028000740c0c0d00155061208060b04000c02c6003405071f0540e40c50350b804107034940040040b840c108200228000f402e240b01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 411488435 1250 411487185 411487189
    0x90804080609370c1205030d0b190b0c0127020109050108241c050607260103080d1103010621020307200c03030f070b06041413060219180e06 62
    0x8143e4801c0a48030800d60b80a00e4200003041d401c80c0d03030004001d162840804003e1220100c01480080b0844800740080f240354800d001d102080190314400714040f10b1003d1003000c00c0700004045429110b0008500c8504a145030084000004400c8403181041110002103580040d0b8000040400342801c0d80781c0d1600340110400b12581c010110115800d110103a10b090b81c403002c1d0500340445c0700e4410809450686000ca68450081d1412404501c80080540e018070070032042c140400023001d8240f055901c0c507501c07041c5039001441050349640c1c645a030100803000e100003850082406594140090754020f000004061911401c204418010400c02c00041d4106084000c44c0d0f00141c8140c1c01c40a05412860600110001c820350501000482e41001e14242014003116030140000ca1b041d9100c1504000498010b60428221050b11400080f00c00340d0b011840e1041c0d80c058000540f40c140b082c0c036214030b06240b0744076100214140c1a4800b00700003144861001070b00c59030490000c54103040c00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 411489685 1250 411488435 411488503
    0x4060b0a0509031c03020a12050c1c0231080a0f17070b0106050909060d03020a060b0a0503070e0f0609011a03250f0f0e01080103080c01090804080609 66
    0x10403a09000700011440520780702044110108580c20002c005040c0d036180b0020b01950000150500040880302082c9980c0302501c20940201d4050f6000c502e8551110588988400d840074800c2c4407550a020606905000b00c0303c2240007213207050050720717028182c1d420352a0484503400c040c4403640800d1201d070004030f81104440d01150059010411400e0420742c0c02024421000c0c001c0248100740000170f21103402c0701c007620400034104c070607940c16500c440501141c94078100010780103034490072071140801d0041e07008142400c1e01603c007900850302c0e180481d1a00280761f00c01c5005001d0741c3d00f00b2102c02c0c0c3e0340382e000b500700004031048005540361a92600103884c10400c0d588120400002080410303007150884204000c51903104941c80b40c66410252a1141240701d050200c1c0e0010251524544900c1e07040010000584407904103908540fa01d180075041510b8030840c5641e101e400f00f0202c0d00c1a000b420003400500014416071500c62202400c5c20101d42d00c0307819000d4401260801005080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 411490935 1250 411489685 411489697
    0x6130204290904111e1509220b030f0a021e09010317120103030e01090e1014030102040902042d0311010c020d14160e070c151b0809010b04060b 63
    0x2140b01d4210380f540c0c2450700c41c00c01a00022030740983c0380700b0b075a0311501200d98580e07800e40c4211400e03c21102801c400003a54440d9113800c40e07000c0004030f045484a822103c0c40c0d22048022800024451902000b1a14044000030001d0255100c2e920040071890480f8080600001c0c580d4983c2d00c1500c4200880c1c100c03003040c0001082c0a00b040040c080203141241640d2462040c80211203075542e5078180940b8082c00400841c0c00103400d00008140c408004801c04c0c000c14049056032041841c04401c0071100c400070345060b6043d5002c100014029080c0c0c000360000d80440341c805802c812241c3c003810002c00c0484c085501e10301084104101042144e0300000c0d02c41e82c00e0078041c40d810101e00c005100043c03e401e00421507042c0c0500844d4546000441c1c4841e15059014031100c0d0342c80f900b0240d40b10000b1a052000208032000001c002080c000b0741e0480c040b0507580101d0444961000c2055007000b0808407070024000c1d104000140c80f0901450030715103020ba070100025818105110f000348102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 411492185 1250 411490935 411490939
    0xb0607020d050a081603080a0e03041211060c011e0902010e040f09060c0807021203091c0c05011404021809060105060c160b0d0c021506040f0b030613020429 69
    0x41c00c400c100344036062040e00c01d80b5500124003983c1c0c109080c20ba8114001c0c40310103400048002c400508220007902c40e008207440b44000a40c106490003074545035440016008a51150841c00c40e101c1c0c64a0b60740c081c4c9000c2c80c0980021600218404010000f1a8182941c1c4075490406041034090313600032004400c410000d940c0400c44025a003c9500031b0820007a0003042e0b03616241e4480071141d884459240145000e81c03d5a0481804513448038250005480080258201500003619041a100e20510000722070074191503c0c10305441c2d850031101030150500c20003100c13400300030031860851490301401241890080c4282010360342103580700014024940034560000d102030b00392608100b0303007040b00f0305821210940c90721000e1088481c0c020707800b000d40540c182000c0c6000540041000c0480000304422080d2a80c0c07001e0401c0050260b10010b40c00c007681e41c0c407031000c440d1000e0000920501000c90103134516009441070104444034050f00b08c1700c3c00e944c15081c0502c42c001c1042d40d005240c003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 411493435 1250 411492185 411492199
    0x1507080a200a0201140703060f120f140f060a02040b0d1104050d060921080c030c040312020d080709120303020d0b0303030421090e060108150312040e01090b060702 72
    0x80080d081c02940100c40740036030540d030081030ba518520b80c150000c010442680401489540341d015003603094602d103014600c121000050b09110740d41500400405c654002c440c16200181261a4448142c6200f20480d0705c5802c800d9014030000400c018203600009401421854185000440700d0180189205e5070002d5460f050744440c40480c010941c2c01414000301400720088052400500501d102e440884450241d40300b698850510781445d07075803170030080d100c4180c00c4d601e1411425441e4001403062180c0401804003002280380110461004050703500100040d501142d005801c10310000c0003603082007050340c018014030030034000c01240035a01d820007503190146018140040c1c0710000816400d07100100800081c41550701882050398400c0d514001004546681100c82030003030f02030650281070000c080b680b5540b00303000040d4084482e21038107120210100000c2d0901e000151821001080030405100105807640d560f4010000681e040004c0301c0c00c00d0101e000c41c051580d010b481002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 411494685 1250 411493435 411493451
    0x6130b0f04020a17010218041a01200106030305121015110a151e0905030a0c0f0c030803150102011506050714030301060f0f021609020d1e020c1507080a 67
    0x484681e00401380108154580708030107030048160003504507818810b0945c441700e03000030036410b1500c1100c5221001403003e043c2c0180710380c019190b0038260100e80038001c010790b0038810340e28002e11500d809141700b65101c550701e2003030540d1115000c1014058129140c01d10008000484810001c0d40c1c205880341040035401c07030108035039070815400f00c6005d01001500e2411034610079280d4410102400f0408403418005999090fa804940216500401c40e9204000342c10000e400380e01700340007061041e403012035881d51640da01c192105a903403003100d17462408018040914440300101b0780c103000070300c001c105204840c4405404241c41c0d200300e00c14000d00003600003d02407525181c0c48003698050440e9501e507941d600052072900482801000035400c1860013404520101e90485854560116800d40c02c0c00e00c003810009500960f0314034003240c0c2d50021300b41194681c5e003644201061421006841d0001041818240203440e800c07810784a44000800c8000c035000a03400d608540308100002d5000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 411495935 1250 411494685 411494689
    0x60a0b01020313030b0f07080702060c03191803030e0a020607080a0507020d030c0606090203070e01030e0c030706050c01050c0f03070320040801050709210609050307021c030206130b0f0402 83
    0x841000703003c071800c00219501100b484260b40c441e6000c0c50504a0f030001c107994049044a4552003503903100010f802c1000492014010300f000f6603000b030000314010160100c030440c1d0004480311141d60700d40c2502c1450201c02459054852048016007843c094041c42c0b0280c1e0000760319100340c04000f0103e020201c0d01e405154443d405a03100f07298060481d00c4400e0032814084e10120881c1401c499503804c082000c540f46206009580c02606192178483c00300b1142c000640140c65000d2000000e03102c0c1c0542c140749541c0400801e03000b4003c0751a80c07680c40104103106401d489000b00045c1020004220a4560307100c00412240d0240262800081041514005010544045001020031034002c10080b170322500c11740c000e50080700f441d150384030700c20358a42e140c40700d00c000c11071342c90403a10003140320401040540d004051521f22840542c1d103003404503400680c644214007451002000c051104104150701004980d811031006100000194666a50601750b95001401d910340f84222601143c215 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 411497185 1250 411495935 411495937
    0x90f05010503031e0319020412140a0c05010f0201091b080c090705030112140a0b15031c120b060315150f0417100903020309030d080408041401050c030a0507170c060a0b010203 77
    0x140b20402e81550303a00d031b27211a650b070100603005042e500c2103e035107601d6410800026500041c564003d6421080520f01001510850a05000d400941d500e030704409000811400610f0641c1d00600a02c0b05c00a00304454107140c0b0028030481400741d8200d00600000c190041c05407030442c4e00d840c01c0184800c06503d01145040700c50300106c9120304c00c000180e010040000c0f00d1301d11680702c03814155549040d940415641d6000a01300c00900d0410210146400f031050340b07855100c504d6184007044441c10b000205030b00340d00c11901d41029a9041c42c3d0808280707413402d89400c0c0c11360400147d504104515515502903c40c52103001e4a042c09016441ba8048042c0080c17405550305d480204070b000e00b07d040103900c9900029045119000301040c41c841a0b000e8070440d800303542c2020031a07040900b44450711800d0241c041200703050100910502a41344030420040c8a000015a1455102d120381d141800746200c10850013a5545c000303104500c4520000940c0c16840b084421010586120610040c2e0075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 411498435 1250 411497185 411497221
    0xb010c060501060201021b0303070c110a05030604050c0102061b0a0e1206041b0503012007032007060305010e04080d091518020f010e011d010216090f05010503031e03 73
    0x803031420100001896501903000d02011008890710490950346104d000391030b07100440c1d01c0e0002c5140110b0910111711621400c00c14400054034001e032450300c2d00c0010b890001c04640031203003640003170b00c0d8807403c5d40d041c4400350f0400307455070b085542d000d100d0901241078051041503108200c051044100c1c15920003141510601c00075003500d10609050034458060f0780d84007824001c0c0b503111400014113040522a0602c140316103908048402200c030706425507a40090302c00d50410440a04140c2d59008000e40341411aaa040041601510b030500c081c05840059000150300300c4090b0400000c25100402c5031071200d445000001e00b003a01d0304c1e100700ba04128120340d00d00c1c5494615410b050b11a580d0107121880d008640c3e03004041110401100d2911103400c0003400200001d12141c0c9501603801ca1103503080d0140143c504500c0b205800c0704032514a503124003c0c86483d0804540c076490300d03108840c003405080d405149021030101e00d0f00c602c0d150849400803400700000c00200740c1040d268007106 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 411499685 1250 411498435 411498443
    0xc0906050a140d0905070b030c0d02220e240a0314101a09010905060a030f0305040801020a0f230f0f0d09240b1c0219030b070905060403150b010c 64
    0xf4036981901c1c0020000c0400742c0003140c20f88076000c000314840c400a010799220340c10041003145400400310f0300ca8086d4101d00c0e2142004130305044040c0010b00c440201d003028100f01d8001890030300d480c41e035100003c810114403882500304101d403030209440311446501920b8019010b91580800345807090f2a216150100d0341c8a60300d011180c3c400508401d0104403040d508451040c17070f5988178440c05080740c1050b1251a806140c007581040005d00103030046415500070700300103092598605105099034032150684002a241500080c581038100e9100c1d141091302d441d604103c204012400d050394480c240c0455480c11001c0355110b0b01107010022140c6c1e004405406000101203403900140c0c450000e40aaa00e41500b0b002405018103103200d007002081d80140500c680d070742015000c0544103280707401a40c200082c8044405079480c5542094019846550201c000c2e00e40386100502e2181305410961240100300400c202013480844000703d107000c00940011040745220060301c1030314507014024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 411500935 1250 411499685 411499687
    0x31503060f2e0317070b10090e03091008100302060c0f121602040203040f23011b0207090e03130b03160e241b011b02010c0906050a14 59
    0x4440c0d0281404603024520941181d8810400c0442900d544008001e0070000b201d484081003010500d496510420032020b0300e4224909030554170f13065800c1e103007103580c1c00200d507030072000304820b1856101d1040801d441a01440c1080d01400010794490110005a010002000d010074616408041003c00556000f004a03640e80401c1d070f01c09440320040c1c050940e10b80140c010716007803400d036082114034100c1030701d55041ca0001d036a4200402900050302c1540c04210004c00032000404189550740b616803072044011041d0f42c00c071035240c2951b244804400b4880c080b03000310a690f507000070b0b0341419116502404103103404c04011041c0303940030b0004541c10315030881100040c4090201c00070750161505002a06c086841494152020f1004418142e0000c01200f240c0c0400c50414082010034a0444181803404110410082c00041d05c03280710381059640d030b4002d10740002030f110040010b60701800240525040388001030588a081d100b10030500c400000c40459035486604002c802107081d9000d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 411502185 1250 411500935 411500941
    0x8040b0912070f060f050105010503190b040e100b0105090105070f052803170f010902180406090f0b04050610050f0f040e04030219110f0406030b0103030c0c090e070b03150306 77
    0x440400c03e00b0b2102650701c0c03407a00c0408021a21107004040c181e460684445207591602182d0700c003203000c2c0718001c4400507940ea6400caa00c1d6a54058815401e8200d402000f07960342c0c4802d036a0446255101030b41c140001003000c904181d80210698921a401140d120118102400e0107410300a014850019040e20502429016900010f003215024002d0b80c0300c07104400d21062007180300c4030688070240c2c098040001007021150a4004150340c1660008140d0000c8510000c501503030466041005d071207850300c40c41944202240b180b105d40480c221020b00440c01d003d40803c003c200c04400c1107040003400100b000180241c64121040c2400c4201425507560b6144d807900210300c002d0701c04900501640e94504c414041020342200b0480e0010031103003030240d02c0c41c2040f80ea40c09011071181c0103a203800c4008003041a030a600c50085000e07807244605031034249032940444409400034840985030204d08680c9030700c00955041929003115200c0e0b43c0b51039160308586c4a80340ca0410b03640c144502820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 411503435 1250 411502185 411502193
    0x106051e0a080405061008060c070227011805220f08040312090806040c0510020f0618160b09100507060c030b031b092a0c0c1503010608040b091207 65
    0x1841c0303c1d40c0a141502c825440d00600000d4030146440b0700401580240d0100700280c12520003800d04920040507400b22000115201000c028105102903842c02440c1c01040300400515083e1b50b1104072410030042c62a1410792500c1040040144a21840030200e4110130841e00c1080c0d185090380002e2600e49036560b13407509091035445010344000140042c100018107240c00101c49026551003503e60b0101800c120900c01c807610740e00785a108606c0741e0071011008007418025280140b803e04a258035084414809600d40f410110b00c08050f071004090402c120750589040e1a0301d0141114800001045a681287d150041e01000382c181d80c80d1212130100d40380c055000707100c0c00c0c80c19010380c0d00c1c4040c00c11984030721361049d107a86034010030850b0010b100e08039240c5445100c0b440030180900c9c0c030700da00304203041690464048030306158489810a621072070840300c80f46110b112908414503541c103007100101680000b6000401c81e6824101141c500311045c0440304441c402c111000d034803400742d410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 411504685 1250 411503435 411503447
    0xf15031002040312090b2b020a0507050c010f0c122307060f020f0405040e160f0317040b0f070201020a050d0f0806030a0302060f10050a151d090106051e0a 68
    0x401111160f60b50280d507000c1a001c0c2c00c10004030f80c2020841070508041c0c210300e111f00101800012490b4418070300041694a4a1004d0008031000307541e1113486200e1031074541c0c50320f500c1031862030600138001e0510a215500101e8001c80c80e5000003d8205400d441e0301c00c0d50ba0003c14600320200381d00c2c40f0300450500e51010003502000b40200c000b44040400011007504030f100d1610841c261079410001440203042a800aa40e42c0c0440c0003281c03200210420a006d5502864102014401c0c4d091410000c4c443d005801610a10010032880c1c9410324143e41d03481c13103108107980b4540e442c0d0041500815a0700030f20807010003d4010f01510259a083c0c0c00042c0360601460741e00d030104030408080b49490a0000340307a0402d9905800500041e103440e0008503108000070084a4070110048000c1829103401400c1001040c101c1080308494811100246c1090f0401d540000300003605811403103a69128a8103e0445007981499545c9004403c070001c2c5031089409203480032800007400500e0382d07606c0341c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 411505935 1250 411504685 411504689
    0x304030308160e011202160b09010501030209150f0f01052107030c02010902091315090804151107050111120c0f120a050706111c05070e0103140f1503100204 69
    0x40b01020b55446408015038042002c4189540081c0303001070f0307400008041d5802007210300410300702c0c2c00003000e84d640d0300d0501400c12298804180d4480004100b1810406070082e0007a04242c08000d08542c841c001c10307260440514618894186900351807030a9000300c046804528039000030801103030520078038808000c01601d104c030000e0300c4c102d5020b044c00d106100c0e4402c0c046c2d0003041200251100501c000400744c22010903102142e00e10908954611035218114440e40306108a07900c036840c060581c400a0702c00d004560900a00603405103010901044030f00540d4000d00f0140c401090f9540d0f01440c10b800081c540c00c10000c00602d91000450005401c0d07400300c00c13103040751345000300004114100c0c0122004040414418050800051080d42046004102c60845c082c18180e200583c0740034500d0807140400165515000d1000d102e9100f68550f258007828281030121081c0041840c401034402000e94010044060104800d04d1208e81915402440103044651000000c48004029072081c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 411507185 1250 411505935 411505951
    0x606130b0c0c010f0c05060f062205070f0e0303033709170a0203190c120e130501051005030402040e0706021c1805040f140c04030204060e010305030313060b030304030308 75
    0x1104080124900c2007101068160b40310300940142d464528900700c180708c010b446075520020004c07941104403128405a800d00009050225040c103200310f010b4188040700c09120b0400400700340c2d400f1142c400004881d0000d000c8203500700349803200301c85102c5040d94179515080b0b40d0448000c5d00300c201055044a5810707400b0b09582030400012030340340106481080305400158005000c26000658010021740440c07801d820001c0509105030703910444017816a1161000c6545402110400d00380005a40180124410104403c0d418040050014440074442d441004000000641151100c0c1c10820710700c429078007280d03085916070b140030751100d01d00d1441540300d4a840f05040080e51142021004080300300781b001400314209003e100c05040b100c8001036001391104400c034441d0100c5c000789c0e40714481d040e01054482e4153302c10407007900c00702d5100d02c400b00001030040c8082070020080b641c100783c010300c203c240c200703051515602910114120982c140008207001052681080c2c281d4400c0c103034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 411508435 1250 411507185 411507197
    0x5100c020a0b0d060603390e040207030f0e040c05090f01110106080f12030f010e0405011e050601020c030a0b06060c07120605040201110109170c03040906080a0b130b0606130b0c0c01 80
    0x4061b007002070204401e420449911043c803070165010b03c801440074460011031410303001c3c0c0010035011505032f0b0f001c1041180096806402c25586030340c090195400d000045405002c4484100e1008107a401090300b101d104903844041c600150303028024540016441000900213150f80358181511080800003812641c00f484a0101620b0340780c01c1183d11440b80010400d41030703400d00b1a050100103000f00104ea007596100c0e008800252139a07040b0501e100d40304000300e01440c040c40020b0808070103c10311070095000f200707070000150302201101d60009003502c01a441e0000f0280744c601c0c1100315800412a503501d00d020005029864200c584998000c1c1c0340c40040d13905045119080301c1d04040081c09502d40301c400a64404840070040010141520490b400e05889500c00c6040300c00300e41c0140140d5010207401d800b044110040f10f984915001060f68130050580c5400000c510024009486504001008913040c919602120080d18521001c0b98403462000d200a556408600540d0701090b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 411509685 1250 411508435 411508451
    0xd090530070803070c11040e06010513090515070903020604080307170a0c030f020c031603060c030605030d0e010c0f0b040b091b040216020d0302151005100c020a0b0d060603 76
    0x1036000d0407100c4035a0b00542c09072540d600c0356400c441c5a0580581110300c4070b030003401004103640b907000d00019400b0070005042694503000c2000994000c6046414143d0f0a0115100c0070500c080384681c2c040101298020b00355071241c60450340c1501d035410003940300002103808520580d00001400c83c1903c11038012140c810003d00c2406180102a0341c00c1c0010102c02400300024410110480c074211640115002500f40c3c9000030304000c080c109613000020002420000e21500e8040d50600182608080043c0307410040070030384600048400f4420301c2040b20189503183d205803038107001980c1040189003985040d00d080c10b4922401d8500307a0b01004103a01061842d4000301e54249440341c043c800e1104554000103220294010034404445058618400c0c0056260b0302c04460500f84207a02400c0e904040d03d6402010402c058258400e10142d030703006004030b4031070180c941300d41a42400d10a0110b1aa44005103814440c2e800901d03440801281442e204100c640150043d80c810b600c00340410300c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 411510791 1106 411509685 411509773
    0x22109010c03150e0105090c07121d0108010b0919030203010204030501051f030507090e01021902070f0b030606030126121905070201080c0d0905 64
    0xa51280d0500342120b0740342c0b040d0070254821560007160a810400b60705101da0050080c00d000d00c21a03004100c0d001c501d03800b0307200310903442004d44440405178030000300420900d00340045104082a81c2d05219070158000b10b05a8121200c03550800d803c01082000c0b4035a201049030800c200d160010000d030f1001c3c0010700203107024400100da01d042ca0f001c3d42031003414039200c880d541464243d003440081e41c04242042107400d8440c02159900d001e0b40900d00a1041020407201d800722448011181500410201c08035070308030154402e4244d03100020304032440b080301c90f10340c800010001440030030074800700c0c404806c05400110710041c1a40b0100c41c9001c1c10070380310800286000c038800c034801c4ca42400c400c0062503980351190404106070300103441c2d00300150801400e4130012a02d1404104681d1003c881b071a0014200c450668020b0441c41c0b000404150682c0c80d0711005090314818 = true := by decide +kernel

theorem cover : BRFrame.Cov 411330935 411510791 := by
  have h0 := BRFrame.cov_init 411330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 411330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 411330935 ≤ n) (h2 : n < 411510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
