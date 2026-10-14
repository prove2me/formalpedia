-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2521
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:57:32.117056+00:00
-- url     : https://prove2.me/submissions/983958fa-5c1b-4ab7-ae66-acf2b0a5d476

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 453237410 ≤ n < 453417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 453238660 1250 453237410 453237437
    0x13030210091a070c050d050a0201180e0a0e21191404091401080307110909030904050c0c07121a0714040603020a090e040209070518030109050106050906190e07 70
    0x7104140c1c41d2800d44000180031041001064044c0300402044801d0704800c60f568440c1500c0b00c550800003070411111446800000290b150120044c2406041300c100a281000070300340180380c81c010703174500d6100350840c3d000d000d8001200e4040750507482c00007a080c03101048440200f103c890901c0402d0011845030400d1090250300a00001d240600c4007081e984000446403030740000680000c01c55400400108000c034544505101c200e2030280c400200c160b9442e14007a045010b92031250342d200341400207004c0c94000c10400780006030840d1040e078560b15519201c400c2441c03184a001421a9001c43e01d440c0710124071052564001e0081c104418452043c15590015034440e4000c04040f03a80070800c224138560210030080503210382562443c8606060f00051155000180040c1c100540024410103801070071031800b913000c0740170b0000d104001c814038115019081e01e00466000b100c100e00019160b00c1e10004071141511146000181d075402c0c5134090640c0d440041408052156507030072000e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 453239910 1250 453238660 453238679
    0xf0f0f03011407180639030305090706050405010e0906011812030215190515040e1e010212070305040219140111071802070c08030f1209031303021009 66
    0x603180b881d014814482c2d46800032002d0700311a001d054913442441000401c0c841e0341d4103d54640c2e4020301400c04442c034040004600250b005424001310a0b20b003660019408158141c0c21090161480c40b081e1000a521140110b58501684c410140094a440300004090030001800b035080030061400c8040b80008500aa18051181d8030248800c3c11303080c2c9a005041d414050300b070807403800700403564031410001d254074101140c514402d520380c0d07a03410124200e1000c40092150740f20000d40103100b4495110b40b030503120035070410311000b1107140c000040800641842286e9507104200da112440c0d4440c0300080b030042000800807a040446082c12800d910030304110007006107086107080000320b140c2c400043c8064581003107051240c0c0821003d21024000d1111000d1400c0480d0300140ca600513805c201c181c0302c0ca603501c401e0150000064803555440a90000c085480364514181d07041d44031084003e640c2d20a80b250588200c0900500303100524006400303400d808440d1601042e000c2c1c0350035084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 453241160 1250 453239910 453239921
    0x70c17090a0e090f061603150f06020709050603240405101d01180c170703020604030f052109060901020a0b0108010b012d0309020a0b0c0307061107020f0f0f0301 71
    0x1c1100c2c25010400f0340c01d4104a062600c18412018020a0900300349212402142c04d03e41c0041c9516003408085145120040038020070f5003810b5005110350b58540a5120301703031030282d1102c003030404000400310704000402c03c51a5131028491208032a601040c003140c010b0107801112907000d00a00c500c103140307e6000301401c0b00b054990840e12407405171001c5007101c0707018240410983d0010f0843c1c0205694580380000c03151841400000b1086604170982040519040254844004500402070244140d00304207414428400c44403150315020694110b030b2002d2400e07901c0c0000812a164160500030f000c2d00d19088117004880c00c5442d03641e10004007200980000381e0030703903450400a01541e8406025118000c102698a20006030a14002d064986110040062648800c410300854403644244002000405101c940b10074800014640f01c3c1d003c45019200581400258480341005208072809660700500003ca03480010040c80341d55000314090310380c00611043d4040d2191001c1c05503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 453242410 1250 453241160 453241169
    0x121060606092c04110d0203060f09060612121c050a0b010206011508041205040503030d050f15031011130303050712020d0903170d1107020f0108070c17090a 69
    0x100c0e07a0b09401c040065406401410aa180d880f0700c11402040340c0140c50701158006401c500a03a0501c8030b03400100f0015128610002e4051060804000d00c5034004260603010b00c24060a851300358542c030042140c000e01202100f40705401000d0420000c03000c2030020010524041510941c0b020140701020484100b251140e00e05e90312008031000c02c2d0f138103200b03290143c02e2088851446907680311000b400801300a1000300440841c2c034452200e203010320240c0e0010200201120756640c8184c81d44005004103481543c66040f00d20045207004414820540600002500401144003c0c1c0103c1703010b0081c4c50550307102c0c40c908001060002c481011030314041c0d4042d44800e9565411840c121000102a5080300c04540029500042c0150300a482d0f808030382e0484400e8108012903420240a442511074102143d03141c03802c500a554803203800740085034021070350324500784071f080015030b2030f08011500800011142404000096000c1c1890801e45400b001c0550501e00c02102140c0d0002c2d20b03400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 453243660 1250 453242410 453242417
    0xf03180602090a150e0913060e15100509040b070309051e120304020a1a090409030305010816030506070302180405070804141b0d050312040b011511060121060606 71
    0x42480b218201030019000801d94629414030425035804020701103501c52111a104409400120f412400441100c0700d00d0741e045141046484014000036640e00245009510b807032854000041206500240d0001140c4025040c09000d94580e50b84c0080000300410f64000d250341c5022040210304208940b1710682e02c5034642c003010780d0b21404851f1600420395080000303403c007003040200507280d800c29481182e801c01142d84800c5281111103c080c000c0e0038103c0c0e0041d2505071f122084c5540740e0842070407100144c0a460240342100108500ca1602c1c0c04050032903400000405c03e210707c241d00410300701c940411000000c0030200001429030f03c00f500d80b200000c2520041c4000e000d50f0b0803892640035510300051200424090000410800681105201c4c0301241c1d201c9043c058280b04070b80703141503544c40030403091034280303400b401d43c4400303029542c15454010540b111050095010b040c1ea003100c40d0003044642e203014140e40d0303942c291007801a10090f426a4400025805000b0350018060310745 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 453244910 1250 453243660 453243667
    0x902030621011d030406090509040521070f0602090108010e1608090708010f0b150406021002090a032910030b0c070501230a0b1e210f0309032b0f03180602 68
    0x110080c01d803002c0b074000a101d4540c0270103100000344000f0f5601e00d04803c0004c42606480c281d11320300300c18080c00001a21004409403540700700440d076030041170000d00988500c91666200c01d260810700008544034910de0184c40503044e80d540c0a0180d0315030003000042101d100c6512400981c0c03c0d18040d007a0700c48920b445e20a015410b1810401e04482e40e0804001d01c1c4c01c007072400d84c0007940e40150b076100048456002441709429200d82c90b4880285402841c455144d201d243c43c1a1001401a130400013a034000201080d50b003e00e040312542113907001150322400707032210740c0002d599a00c0085d0444d419035940a480281d200713040b507542c40b248904001c8000c2480c12201381c0059902000d0355502c00c40c840c80014034040102c0d4101e0b03501240a407600c0f00b0350a08001e0801d550808038004810702c2c481c0030404011210000000d0501200c15070940b03e0108811803090801440070141c044188100c81c2e1012500d80300d68200c03000300a0b14500450f469041501c4901c510b110303510103456440c0c002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 453246160 1250 453244910 453244919
    0x1080321152b0f120f050307391209050a0501030e0c03010c09060e030319030f060b0c0106090e0d0512071713200a0501031a150309070902030621011d0304 68
    0x7515072a404d10280c03d00c2c185011002200825500c002400300050000f903402c8107c144110110000c183d170400003908049c1c1c0065a400001c0d40c05221040354010b901c032510030b602510440e13202c41200e101800851480303040c80015400390144142c540c429100d41103541010303503030900600c20170001ca51100450701e0b0415a00a02c1400420f916074040c1e0700401103812102c84128071407403000b0300e80c90001515440585400060320142d803107049420404916004005410342c012400c0300ca07110001c1200d0900c0c00340241c2c0351000e5019002c0070030000d00c00d4003008065402105c1e8010058501010003044425048a0303440c0144e842c4220745c011490381c44100003a2201d0425403c00c1d0707606030114001c91000080314081c890040c0d0b810551248100c0e61590101e1926141c6108002c0000f0406100003401031006d4100301c448520710b1082c1040000d800d9010b20890707006600141036860200b91201301808004d140c81c1192100390342c0c501a48158062165100347d00700901c1d4055903895140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 453247410 1250 453246160 453246173
    0x901051c05043e040c0e0a0915230402130f06200c031e07030c08010203060315010f09200d0506040c030b0307051003021201080321152b0f 61
    0x5604030902c07043c0c24120070025860710040b00101da046a021401c002c0584040b10000b14000805400a141d039601040110060300850512700d41c071020a08455038580b280d2900019005120054420400d004030b200e0415400811703081800c99998100155651881188030145500c10000143e010050150031074014038220102141c0b000184a2483c100c4002603d4a00c014090703c0c0900c11200282240e40e0240889401980c01c2030081400d2035459520902039030003103800502c0390040726121100c00480102490680d001c0074100f89040381440004401420100000558005000c0c08100b0f04001c0c0070007005d0f1043d20340ea010071359040010a002c180c80d40265404141820510b1301102510300156040441c0c004072121003c00d02e180b07506400920800907080c41800c0020000300700d4000c000028590030b500c0e841000300031001c13202c03400c0145605a46147d281d60000b9151803031480c00c0c07a02844002c0400e9032100000b907414580c04080307440c03504226540802020103c003032004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 453248660 1250 453247410 453247463
    0x4020108061509010c0311010c08090606010504080d080c07021003091b2306071202030a11060c030601030903120606030e010b090106020a080706110f030411010f050901051c0504 78
    0x400c1d02c01d5180b800501c50720300b11034000c00303514504100703590480030241481460308005501c0c1c0321b03008110040c013080300208004021500d40e0040e00c81e44012404070b520440841e82110303003510182210380d034088401c880d10807024103000500380060129601503603c0022403184101d0365180081e09404600c0c00e4503c00650b0040c0c40c60341043c802c0200103894800c0440c800801558414240d040788440004207580075034207018103a11a249641458282c0000c0201880822500d41303009030009000e045076a11012070341e101ca010070520100e20709501a41107607030b00a10a04140c0c3c0c00d03d042982d42d10496401da4041800292514446400300400b07204001840105a602508a60500301c0c017a540d00b000e40c0008141c4500010a541440480d03440b0000990b140440700350f88a2030102404a5600306890a4582031403807402e80107103600840d4080080480350310340070b0810407024010742c0c0755000180e04100b056042044029049041d116861140d2311a20400c0110ba0301c04e9034103a0f0240 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 453249910 1250 453248660 453248671
    0x120c0a121104051801050a1e02090406180917090f010e180702011d010e060106080405122206080906010902030a020405190602070617010b0d02070516150c020622050d03050304020108 80
    0x61a1145210411100d0021540101607a03030015035a5a00c0ac008100181603a43c4624280c44007403210300b440342441d03003240c141c45000e8000713802030903410902040075208005143c1e5101122051380c29455029802c503042614006050756026081c01000b0f840c040310031592100141d540d01500502c94081d940170300782c15100507008220280403004a1740d42d548040c0207041c1800708040005040140402102c80803120b50820341d030f00c07000c5140d0310520607a00035000d142844008100407075840c5c440c10850344507400c042c00419559103442e603010300030b50010341070540d1590200008600340d2103402d49a03210501181c01c0203141c62400800a0414160783c03c0b010401501040c010100203240301143e05440180241c207076a0341004091a0081c81a920700402d04d006480000200402c05072040088403000301000c29012600d8008444904404400a50280b4180400c2005008002e107080005030360744078500240c1d0321003001400c00f2020b41002c80000344008104070840d64411005034005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 453251160 1250 453249910 453249931
    0x3060312250228170f0c12030418050f01121a0402010203090307080309091e0c0913050109050f0c0901020a0f060902030307050604050d1b0b0a1415120c0a12110405180105 75
    0x44007000005c0b600ea0500b03039401c2d48980e10070040240300913018401c0790001c040d80000c54480f0650540c0d8203001d04000c51303080302007145c100000540a0b40100320f200b401035000310161041421003404c42107154002d00282e0441c4800e10031009151000c10020f009003210400443d00d6032200c01c1040010b910042a40030341d8458180344610040c80d0b03114654104c000410541c4d150003e0f900450001c00401e10541402414134000042000031948200c1c012071601011070321a503035407800c070100c52183e800c015005a01100850000c2002c190210310910320401000c900028150002465074000e41001d4615070005414007041003000c1080103045507190415400c080030b5020b01500390300749154003519004142000644071445a4005115992407004034899404c00010b108405d5900451042c000c80c20f02c1c070039140110b00065148820180140001d01c91810301e62138205d420340e1708270106c0307107003201d46111002c03a41c6034090b01d4800c2a107481f128803d40d480001160070340d5009000300080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 453252410 1250 453251160 453251173
    0xc04090201140d09060c0905040b1f26040302010c0206011d0705030a24090f020f090d1509031d0d050604030315030501060b0306031225022817 63
    0x140d0700042d40c0040103110301070068072419803d4560b4050064070f41c0082195103030580c0f01280e1500200c06c2c4040e00d00c2a00c0c200100325024082c00b282d8007014141e8450002d080d1403c0d46003920803075044001001041d2450300121500080b60b1088030181c03021000340c0d441c0c022000305e2650400c6403a00501c00510700040c46e680741034070701541803009030145041000000000d400f6802c03c0e0003203500340ca507142142d0301d295650340c0030400b501154060104518100032408222074180c0c02920a00c030101d0fa041c900e000c01000030481c8070320310f458084030540f8500724044089505481140c107664002e480d81d5030040d02c0011303c221009907298541d84507500c07208200020400024000e980540d05081c0050048100c0032402070000156100504560034001c0116806002030095801010300b03404031b680109021a401c8514020070314082594403001494180908400780103a80c4280040d140810210303034141000d82c0043d03020380d00b202c0c1c4a14908100003150a45401846014612025005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 453253660 1250 453252410 453252413
    0x80315060f0901032a020a050d030e03091c0b010e1e071e03060b0d0f050a05041509062a020705090903091203092806031503080a1707020a050c0409 65
    0x21902a520903030f0704041e40c0d00c002c00d03080c0c110b0146240c0f0070701031440c50400f2030742c2100000307503134207075400c000c8803d80103000603511001d00a010f0410789245000186041440f0700d03044c0007079260445111003002403051442000b0803100b880389806803502c004030070180d1604203c40d07501542c80300700f101a06d0304c0080030012070035808880800c0109940f108030301007541410089018240302d0f00584140d090026080344002c0050340310007070541c826030091013160340c1c0c03160440440700c0885001e00f6030001e0040c0010002425403100729124450903001440720a080b01541540c214159105100c0c076100d40700107100ca4040011030003c2c00d045481ca0317503a180c03000500b5164000c903030400e4000d026004550341c0c401014403d40d50b010300054078898003810320051081c02d000c4003240010452079004404980b11b44070740035910030008000042c1452918568a41e81190b0051601c901003108184c0301406030800340310b8440c0508860b50003840642140d0070001d0401900c02c00c0c161240c1d00c0c00100d0030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 453254910 1250 453253660 453253687
    0x160f050307080619080c0f03070302211005010303050a1b080412020604090903030b1f051803011e02030105031009050615030a050105130c060302130b130308040308031506 75
    0x29804222031601d40c2e800e444400228038550a00c00c4001e150360070f1150b002c9111600000d0520304990110350b034000d80307601c45e002e150700c600e294040650400740c10021011044405540090a00b6000c0c084805d480c0c2d11200400c200c45003a04110002400010003580c03140c1c1c481c0d111490f0350204544110900321030b50307030300c0d5292140f88681070321413544104c4541555603030010f44004202120060040c1c0e4080d260082c01050702c1300e030952044408801c41c00384541c00c0c00a0390741030416a255140340006a80404003003a03040c0840316815900c40700d11000c0c0130465105106120340181005d40c40e54145030400d4100024a40c0f040d141d140751800740c9021400003d011074100103401501080da9003c4000701c1e05041c50114040c060f503082c8018000002d6504400c2c81e0664002c9152120068440134102c0a27486042009481880000303800d001000c0e1010081c0014035400c040c4401d0942d03030b07a032440304a40241d8001d4078044408820402124140400c84419810445107540b50000c21160304 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 453256160 1250 453254910 453254917
    0x60a1107180f1b030b150318120c0307020f0f0d14010f1a0409020f0d0803040303050609090d08060118170123040b190f0506010f020106060c0206070203071d160f05 72
    0x9000c25803181322605c0799440e03002d42c46603020486008541e8070b00d002a64154041042c41d206446031041106026101200c0001e8075245000f09010398500807141d001c101800c0350310701e800742d807218180c0003503071190382c0b0380d0342543c0e01900c580e10a500380d1402c82d20341c50842e8000f07018680c4187c00c00606040d0f40c0c2600f80c40044220040b00c00040094682c0042441c100d10483d1150300100c00001c50303414081907802940c8a28440e54050115a84140c24016503e2007900c12a00c070780d110641118643e40900f0b000c075440711061410500f5210601e043c004881110ba10400c14608841c1030128094002e0080202c400d6445a44802c41c511080000100450040c400b070501341500c000f00d14242e0b9811032503900308000800038450100860000c10007000e066880c10702048a5500a00700a8018040c0e5070071104030341c84882c9001c0440d02404850b600102040764980071f100e801140250034031606040400f6951030307041031860b003602800d031504801c001d4002880541c10005485640c44000c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 453257410 1250 453256160 453256211
    0x602060112150b03030301081f020f030604091109100603051308030f090f1204060e04050c0315010e0402040815010602030c0607110c0d06050a060e09070302060a1107180f 75
    0x20701c0a440001120b85009240c000110b9a03d4000000009242000003c05905040000e905480550a100c1082080744076100d03000e030a100c024000101d50f4506507100e0088640580200500c041c0000001004442d084031140c07455417038102e040c44415854880c1561080380c1000314482188584c81e440f0f01804004c00008080c0380360000607112010a0010b40e80074000101102d29801403604500a05d030005c0c060314001032212a08800246003d00489000c0e290a100003807031511541000c0300803403408068a41072188034000680142c80d02e100030401881d250000e020205154410403c0555060f405241194418031440d110a00c0100c0e480d50460001d0401112607441d500e40d06040082402d04240d100c802c0a450000b800803503001345108824004040103070a817290403104040d0010b45403100b00c3d51010310180014100032004055076800360408403110304520103014509802a00880901c41015102005101460043d0320701c01c1c0c0040401e0103022141401e201e840c2d03000512 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 453258660 1250 453257410 453257423
    0x60506120c07051c020a140303060a05010509040603080705030405030105070f050a230c0d120c021506060c1002194e0501050a0b0408250504050405010c090602060112 73
    0x500804001c0300b041300c07114050142c040420104c86841001e5110401080155606007050a00511400d8080100d0b80304520081403030803201d04000045030140c203e04052130b0015034600020000c0b030300c180050039109100d03600850f5624100301c185030039144040c061205100700b500d2540078150300142507555490383c0e49441a400141d80c030070b041c07010315032141c04a640240003131401030120000c00d403d00704504075140d25001c8252014040110780f4071150050068001049400181240c4155107810800007441d03103041400030b4015034100052080c910b40e5041c0e0005501038468441c141c555182c039240d0034000021840080846140100c0c55480c9038050314020003c0810020340c000801d01d24000e03031030780e402400d04009a50041a081c01180e1107640e05082c0094010420b1081782c0079141d51202520294030030009042040500030742c4581010000c2c04045600d4032240b08441c441d41c040d400100740e80c0c00080e409041c00704150040d00031500004018050245501080c5008070350185 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 453259910 1250 453258660 453258667
    0x602090103110712020c01051309020c01091e0b060d020619020f0303070c03020712031407050c060a08071b2006192105060a1203050c0a0c09060506120c 67
    0x4030700600000c1d14482c0daa080c0820300c901401143d50746400c0303600c029021100715017070900041d6401d000b546990440303581c12540510400b20503030082c0c035074812540000304020089a0343c5180d91f0a08034031490114400c41c480f04248200e151409402c407200f500d4406801070203401094041c400c9207c04414503140c0f50352520264820004500010305100c2034980300e0600000c01070400c001540150010b01ca200400315940354003030541e2300c5255142e140c141804040040801d460b40020030265014040c035004000513071907031001403071046002c2d43c1e48180340c545840068011444500081180c00f142c618420010340182c0040901144060711101800d0141e40056007502c070724020b45480040c0174008411107900503080e29152813000c9480d24059059070f9822040b51402c5070903640c0000b002004001101021010035800ca009103805403400b010050241d1030b1003030302e41007190744400c2c245041004500d1441104003402044034032510704510020400030480010300181c400d41d0b00003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 453261160 1250 453259910 453259927
    0x80d08041a04060c0f020312040b060d17191121041d0105030d021507210509160603020c0c040b04060e090609060f0106051e31060503060a030602 64
    0x38407004114800c0d80003841480c0900d04100540721000f42003002c035030a504409800c40c0048103465070848601c4000380305603510f0b201d280c0e00000141ca5103411030081c107102e101088082002804101c88402c01c1a0b6a0f4003611605010403420342c850740400610340006012100081101d10b0032442120004002c181507825003040c903c281ea12112442c01880c440c441c080c20035548040c12100210142c40f41c02c45005401e0b82c540614205401810b41200c0c0090401405920504031a00e04110300207400443c079130000c030490f441602d071000030b075220007000b9040c40c0d9404800009404a4541503041c83c954455175580c0380b0a0305403a074032507500d4070800419521541d01000040103c03507950314040c10010750481d03d0f440b0a680c001c40038080c2c9800503d0855506000d2030403a01d00e50741b811310308100403400300c1c20500e01c08400b000f01c280402c801403d1010000c40b11607104150125420711140b07204c800706400c55542d101c802402030500420000b90b03203071100f010859030440d40c05643c5280c039 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 453262410 1250 453261160 453261173
    0x3040b0f0c0a08070e060f0c01050129190203070f06380603060f0d0b0a060f050d080a030e1209180702070b0c0309040906021c06030209070309020103110c160906080d0804 75
    0x212100141c887c00c001c540b003aa002c1f415040304d8100d442e80245003040d05002c9000f18581015140b8078140e03000100104c03014008840c090340240001c034410350b4107004d45941c0700f9a50018444060f41e0341d6071a080740f0b00080c050f44540c00d14464040c40d03010601ca80b461500724484040e95441e40c81114048006001038498038061014514010003250b114082403401c0c10101c2e40075507071802043c0c5406004600d004401c80140c00340c480040804540b222a5952080c175039005801010403d0b40300c003604a102d55080001016210791800c580e5210400710b0241702a038039080460081d54882d01701400060b603004900315056400c2034825036507075640039500c18511301c140c482d599001841e00064900340491a80503060301034500ca1391480d09200310b603a25060701c0a50001070340c0140c3d8440851075460083c0e1000c010305106040100d9000034480d44824103421038048101160091500c05032810000404030001d40010613080008c5400d24155941d505030802040d030a000b1000081400e0011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 453263660 1250 453262410 453262417
    0x90b03070e160f0e0a090b0103021b03091207050a0311060c1506040b010201020c0d081023030606190b071406100302030609280206090603040b0f0c0a08070e06 70
    0x40c00e030018800340c28001030100031401000544070005007618491001030744248680044600010a000181760801d4102e0001340341422000f8103040d13003000307802d0a4000c00901c403900c6105c400051900c6405000a100f52080c5440440351150043e0702d0a20441c1c0d0340748529000d0380d400240350724030000b15a001c280c2e540b0030b24600403214800d022007e81400304051503a0b20031501a10184490006000168241d0040300d802d2a110340000c0068070300c01c0c1c8a440c10030f600c00da4200e050504641d4450b0760f120a2400340a103204001c5104145020a050402843d50802c40030b030b0341501482440b8100744211080c9018140210700c0001d10340b000d00c422603200b0840c01c0c1d0810b054038414180700c5020811b2251a01c0120300900031040041c1a481c4046541101c0c4c5600050900c01c0940400c0034019890500d14101e074041424040030805884200180d03118a2080c051700c8084c2c200100c01c0404608000c01201003664100040b2581903444079905403c078541e0b0410841c0d4803004030009d5542d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 453264910 1250 453263660 453263669
    0xb0a1d0601080f100e0c0f01091a2124010513080a20060406030f1413170f091011030f0a03060e0106020a14011103132a090b0307 57
    0x8900400031404040114a24020020301e20884413440f00400c4820103a03200d13000c640c405a006418400640d08181034002c42080051400d04000d903210071003c072091078945404c4203103280100c0e0090502c41d4511549100441c101007445052030941c03441003c0e0301c45440d040d80005001d030254a0264007c005590a0070b82100041482e1520b440415607510301e130010540c0e24000300740303001c03048050807500c2010201d006407806103400d08004054000c2d010040b4178940d100c2d034031900681c10160114000780141c400d4101c0500703c0d4081d0400b4041d101c0c995002d9608402e0800c5001f10303881601c1c04a80009606a4034450000d4000c0c4003550b081040d8002540355000004012090000e00b400400d1020003a0f1030411007140c40c1c0c2120303903204401340601c0005d40d00c0845084041006196541d0786a52110b00101d4000641d0310411841c2e042030711640051848004610100404a0400b0b04050440d40c0707046092158940c250a01071038600c40c011150340c0d42c84048016840920100b405030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 453266160 1250 453264910 453264913
    0xb041e0503061b090d060b0102160303080112080d181704140918100e331018020403210c060f0905030708040f08060403020d031a1201060f09090b0a1d 66
    0x1500542442000342807216407c41c01070042d140091101c1107048014000d40c0c0e09540c483c10b01c0da00340307001075003814a211410b40f80d40505020440101c0034601401e02d40d102240c0c81080c0140c1c1d00d180c11642c22604480074059010107000601054601052030444c030203003111861500d0f200d0351917865031024014402d03807582c0100d180e642c80340303890782c0c000404402c00c0c0c0303003141e24000c1d001203402d80c2c54005144642111451181c0348140b0f580581d42c4641007a010311802090a40d144045407504450a0444004580206081061044054524044038015401e007421010850001840310f00c00300c2000740520340e0744418203040340a55000f01c0585901408480d5101c2441c240200b180e0040e1181141c4e03140c540e80086040e07000840c1c405d0003168580c00038030766081c41d00c0c1c00f540a07050340504d05811600340e81c0e00c07070100d6a98010001050098000010700e0070704100503030300a690150452019182001c0d10741d030000d440c1c43ca4881d88806e0700306000900d06010709120001c044821030980f000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 453267410 1250 453266160 453266179
    0x6080c07021f020a11121009060204050d03020609241609051e0301050105010201020c120a02160603230c0f0c0106320102011104030308100902040b041e0503061b09 72
    0x3071030f8000070b132038071210f008040c6445041c040b03c08001c602844118079007a15004000e00b5501040f841e080511028130814002d030506440c0e0001c182c0808107a5020f9005900ca0020702c20984c4061000d044841c0041203c0828540d4072181407100a4000c0c00c0b40308140c5191840b202145e12828284020308002050000800b82840000c2801d075400144184213510f09000040d181d030051003192042c8101c103000d401c00f14175000d40740956810012000080d401200e0b1180d4080744014013680241c1503903100003c50b680d5150760009040e6a0711444681c803c41d41041c4003c101d810300594840c4141d0507046907803071420107411805084a84c2c0130340035140c6220b0704960081c0b00c903078603842c00e007000703400c0300201c480440012804d07038185402d880c103020000c02003440400c2c0300f81541e950082d506242c0f15129941d402c8000c0490707000390b002c400c81d454041014001c0c80d0f00c0c0002442540c1c04554082d103035505210000342c6070b1101503c0784c161507020480032403440034440242d5051140040c001d124 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 453268660 1250 453267410 453267469
    0x91504110f040f05060c07031506080607080f1308270a120302120304020f09070302090d030f0906051309021308030c03030a0f021c020306180a140c030106080c0702 72
    0x1c0642080c002c44654540b50340340420a41401401c1d540f107410070200509050f442c588a02d082030440d80500c01c103181d110803012035068401c00c0710300c1c096a090380e1550001d107407107089425802406080c03a801406000942c101186501090b03410401c0ea0a000410700c0310380c803441c3c0c0314440481d00481d800041e1460000364084038115a58401402502601c210318440301003c0503e00c41150001d40c0300448842d00c2200d8201a14500c4d440200f82c1030040c5007202040001d50321000500d81180080c07101410318400960202420005041c6410036504040307030b410b51090b41208034080d00c0c28840c0c5c04901c0c0700d9181e2204414800070b00004050302c1d641d9140810940d2281e0040f00e003040c1c0f80d420206080c0300315099100311450741009881c0c0b01300808004403018080c2d4005040f166002d0f20034502560080b4400d401036014807407269000a0319140c051007440710a0300105040503042c8184010040c050304072040a6101058440c510342c1d1701400e10004e411542880200320b2905038859041c0b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 453269910 1250 453268660 453268687
    0x7030b0d0807060c0504121211250807060e090a1d07090510060f0f200601030605070305060109060c05160b03090c030705030a110d0515010608060d0209150411 70
    0x42c15502414080c07000a600040c25100e0380310f40d2103480100c400180c42e14000c030b2111455402d4032603491800c0c6800003014420a0701d02000c0c5a85884506250300d1600109524540e65174020f050b0702000d016603528044c005044038510f01c0c103290162402000041500e025684110103003445404400c0410001c0c010041c1d442c10365006218240d0f14100105031081104003001c811079095640c0d180007601044000c540f021102c869660500128000c0c1241c4e41141190103040c0740d100b440204a198914100801502c0300500075005140c98442841034590b0f02c40100380945a42c1e041c41c55020304c4514159280c69155448500196090301000c90000c20f6200198004d50096044801070b2281c0010103032100c103240b02d0642d250384524a10000110181100b4920ba00000c101d00c420b0760042c1c50380c909143c20344c12840144052200144503154000b0302a035080701054402c1c20716540700d80d001c20207003400a03090007541440c0200004403a45c803a081121110303400070406c0d450705159040e51 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 453271160 1250 453269910 453269917
    0x9060d02040908360301140a200423152505011505030610080714060c030a050705150f0f06040e0d090f080109050c01050a0203040b16020a050d020f0907030b0d08 71
    0x40181d2919000c0355a02c3d89814021190700c522508288841c6848091423400100072030300c080061240e400000240c46941100a00024940c580000740f20448600f00301884285544c80b2030310500b00e01030700c02c1d07044513504256024009100b0030380c80d0850f003132202d0758202020590001e18941c00c000d070006903c102d9800ca201201c000794202c680741e41b1408800895900a80a03144075944144020000c81604040b81810705a016084a03d4031061071155070460317020404c07000100328005100c0f8104031003040035138000c28000c44583e10382d04110014021942000c0d100442c0c005010010a0003035070385034440c41d5810484021541000d10a50014048040034890a0b801c48121b042c00602a881030050041040e4010094001581c0102c019100f5401c2b50b008001144003d200c080b40c0c0c080c082000301212040750390100407031401c520400540d003289400480c0100384855044c00107854100c1200c0380520308452200350395840c03413411002001040d05150344000c2c3d03284080c003440803c4001b07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 453272410 1250 453271160 453271237
    0x4150c0209010602010c0c06270b1605070c0302060a030612060e010c0203090d0b04030e030a060b030c040c020a0b07030b100c050d0809210f0301140f09060d02040908 73
    0x80d0740640e0307641c1800340d0881c0c0f00c040d804004224950012400940e095000c41d0854010324000c1500f000444010040c2618107801281e40903400300520001700701d42e42c11807500d581103190071071034010195902104c8010521009001e240041906440c0ca0302940204024101540c080d1908801509016001d003000324110300d960b51030b10907600342c00b40c40403088552482d0040c09224922046544400c42d1b000d00800903400c00c080e100c001d42c00366906015150351030380030301030110309032042c10201070902c001a10020701c103a140000c218004c940100740003481580180d8004031560307401c0c0082d400b91840803401030740880810132100c0000d4002c0190780c40d0900a00c221141d182c1c00c87c0083c1c07060784e0180c54111180d8080e5200841d41040440f00000396608040b0307440c28444100940c240580082e0030410043c20b01c22841c00341414607050360500e0142c21124007500d42480d10218800040400703019004503100c0c41c0f44420f1155070780460f41000801066032071103c0d1306903000180c0d034030507406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 453273660 1250 453272410 453272419
    0x409061e0507051b0111070f17040e04030e031e01090b01090908121510030501062606100e0a0909021207060219050a0f080309161a0f04150c02 63
    0x28040c40c0d041140704151140c052519003d01e8005500482e85209512080c2a000c56490380900c440510054015102c034500c20040501041d000e441e00340310720801134041a800e43c60501c0f00700501d0b10708002054101d5018109003860325a00b401290410841c40c8240030f00b401c07079041c0d0f140504c5055014400c19401040c80ca0126600c1701c0110f000c0c2e842000c0b029101c03100900c1005030070400c3c05681900488910851513101c048400402c0c0c1c100964075500d00808c0d0748000400802e60401e007000c00d0843c42c2d200c3d0701001420110103026004015105500410820004076031181c010316581035001b400800c116459030741c032010036015003c1450203e004040204000569010028015003542d01c0c0d6006040c41c4110100b0710f0901122180f0180d5081c403c03514140b003c511400848151035006056403070f601d18100b241c280c41d241ca80c1016880100c2c9191003040b951030b02460b00d003e91012402820b66a030f03c038082c500c00340c0c01181c0103031004100d86030414041075000209056028070030358 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 453274910 1250 453273660 453273701
    0x6012a0c08150c120c04030611030f06030f0604111305160e0d05060f06010c08030901060e0702030c060c0a0513090c02010c21051f06020a0203011a0a0315020405040906 74
    0x5100145070310058891030090f81c8140544405003c607188803940c4070501011321030070999203481e00000d44a6004101010070000400c0c4512003c130081c500750300c01c0c42600180010ae100e4082c0e966508002040607100041c03144243c03426a03a003042d44082055410000d006a00700080410031030102c403031501022600000101c4510b00f000702034400b05c0e5410402610140d03481c0c003160044e619008210750704000d1142c40044c001039011010707500030394250000241e45402c180014002103c080d0010040d54420300c60110b0368440012031390741c440750211031252a20940503040c2e400c2e00580e44181d520703596892010501c514580c2c0089141c3c1e88130350090008140b440000d40f104111815802449080741d40314200d01d40c4203400c05a00088000d24080004045a4414070300b640c45400210050304003250b0501585002d000f82c0d0f9a038500c50a22101071140400007925022162100800f030000101c014151022242e040c0c40040c000904140710b07000c0c1034904030000f81801000952002c4448 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 453276160 1250 453274910 453274933
    0x510020709050603070302130c0912210905030a020409140d0809070906060f030203060a0b0c01021201090c05040314150103030804050114060913140a0b010807060206060906012a0c08 80
    0x2688001b00c0742c000d072038500c0e4050240300070005030a01002180c1444135406000071817402280303d4058843c050301d03480d14826502d10680111000e100a0107040100e006014026998045505604258122000a1580c0451400354415040070003082014040e810658141507007221106105003881020b984034a9280c007000d00c00c40d201c600071100017844543c8085041c0c0c0c00782d0700958001c040101545103150f42c03425103141690015100048994003ca41c8140350161111403c0c00f40010381d0042c0014901c1600c02131140c00f40c3d01c8068101c0f00200514604107800344068481c3c50f0040e08968000c0d0b849090150103190180c400300d490350b20380303501e0500e210351484420b40240001060507086448044021004081c2120f00342c54001c10140219540502004500d1906100300000d641c950325017140319041400c42d41c840000d540140301082401d68807040e442c0d0344498242070804c100c80780003045011903034074601d440d02114a03045107401401840c005150031a003184007150b0018444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 453277410 1250 453276160 453276163
    0x1905161508011220061303060c140c2d0d0503010e070203091e190e01170d0c0213090f11040f110304080c0c0a06120b040b01051c060510020709050603 66
    0x141d0078091301c21445002c810601d0f02c031000c0010240e5000409a500300303001d81c480c1c800d0454190f07004544c102d80d40e0103a50403040c1c20508804818082c905c10300c0c100484034042903200d40d07105060110f51600002c00140c40e00b0100c01e41c44a030705050044a00e51502d0880282c8640e10038052595500035840001e503101d88000220741e12140302400400d41201c0ca02940b0491230b081414050340190200b0b80324001d512540c0104004020984440307510754941500c840185072101944480e580003108410741c0b880d044004e0301052030341564140504011101507400070944880001d242e10803401d12034080c8180781c40403c0600804803000c000d102c070610540001c44011101c1c00c4416082072000501107190040035000a88101095842c0b0070402030020f4441d642c030350840008981c0c5c0400445082a4502c42c1740748044c1c043da801c100d5030030b4140018089015200100f546000c0c00554000042040e13004030008080240ca01b50380c030042032074046c0d01e030f40041c0a443c074114948800164203240 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 453278660 1250 453277410 453277439
    0xf050a0c0b0c0c010c0302030903012a0503070807080c070c0308070606090b1c0f0615090606020309061605011b030207060e0105010b0708030a091205040611070503190516150801 78
    0x1900000e08503c0303a4500152000044100190250302090007220a141c6003030040001070405035a5540901000c101000e219400442401003002814402c12201980101403076400c0802401c00c81c060b90380340c02e00381c501840b03140402403500306451000420408400090200303144158000d11031252107072103000444e128608a41d074084210f40600a40c4400350703000d000c0382400340c5211100c5140c2034581a09444022101c0991103901c500100500c9034248180c102400e0103102440c546003800300000d4090190602c284110700042c4640020040254000e034010294030f440300101c000d10344c10150084d003051109035002418a0b030111148801072060f5410b07144010307142810300c991902c5060781900020400d20300507942d80d80c420f0105018601004048810740c2e0342640e15408c12400804c0400c038500b110010381e0010000344000d55011a60301002c1e41c1620030050304c1500303820400d00c0c1000018516200c69058280030500070100150030382d10301895201c1064030390381d8904222614a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 453279910 1250 453278660 453278677
    0x804090e0f120d060905010b091905100e1f0503010f0504050c0d02091512150d030206010302150d090515070206010e06060a0e060a08070219051011070f050a0c0b 71
    0x8020b500c084629540d800041d001d1440f4103c000203000c0d450340f0040040b0358080e0021030a410022076a000d0a14103100030420300c0c840b840c4030b8840907103004041401d07441403150712018002105140d0301503071201c0303580304c424207100040010520031603c40034080b50f100780140541d602488078040740324101409200c0c0600d292107082440c0c0258001c0d100b009420125519a120450891400e60951082e0240a03440084800c584882c1030464101c8040d0045000d580d00a801c0388c0ca502d00440d801258050440390165182e820740089a540780905200c2c0e0400c101c1e02381c0ca0041440240540011111940b282108540e44c2d04d40f107120b0241d0b947c200c00d10851090300301c428009a075a00301403003c0c0030100a241000c0f002c6101c400c0004000e50018400703200018002c2042000c0345604100c0d50207020b05400d2020120f200396202e480c1c944100c6811480c0c2c06850380c0c00c5800d004402c0040307450444d0404210040010145056900c54071806001e484913440550082999600c200c111807106 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 453281160 1250 453279910 453279913
    0x70f060902010e04330302090a0506010314040b13080c071d01060801120f030203120a0506040c09060c03050702030c03060910050906060d120e130902011214060d080405030a0804090e0f 81
    0x1082c20300d420a101718007804500130441c1c0d503a4400001030f183c09880c00d002d100384440100305031600000040882d0340d82c0035111180f8030783c08248400315a09007103040e000481204210058034042c208503450344140c480600803440381d5000060b030101450380b16080c088031402d0098650f45d03268001c8400080a0084061a440c43c2c00000c0004a001401e444864402c0c015130b42010702400983d41c0010701180c144205545980810000e40380ca4410f0400080301418542d500354103096008003100c0005c0c1c001424071000203120402c1d564200100500c0300303001803c69015140440b000d60b00c40b0320140c00b4491560511010a074140c4020841e40d01c41d8001400003801280280c640d111030405241c121420305c00308040c144090f03160190801c2621000703280110713006045200051010080b1080325026a03d401c913034200401314014802c0e000b010413140000340c0c510a09041d149881150300c8141e040c4100070284040018003800b400440c5c0301c0a5081002800c18025079458800c8109902d845 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 453282410 1250 453281160 453281201
    0x10b18060903070b0310181b0c05210c010e0307031806120c0e151308070311060705030409020325080907030b0a0e16030501060501090e011a070f060902010e04 70
    0x4561301d48084c56101000020210b103042c0c0d540300d00300144881314001c0c100c10342ca595605138000f000c003102c204440c1c950b242200c1118010f4880301d440d00700c0e40f448515110300c8801c0110040940c80f0603181d00d241d40700004c10561f0020700c1d566580354800d16085010426061030806a1182240009c0450f0f0045e103441100c07211514140d402000e000c2038400601003203851b1b814241d2152180001000c012101040e5509080c1c02c440c11154072507403003400030358000d003010300c001070f40301c010142200e40644242c1d44840042c5030441c00d50160350001c4d102d8501c04002c200e4042c2420401c544021400c4903007640083e240310f4210f03184841141d181015601c2880c0800010701000d1809134044220100003a03410a002c203507d04148103000351500c0e007000d915080c0706010f0b0a01c2820b00400007405c180001da8034002c41c1140c190307014891224031452205403540714800003000c0f99407051b404030f44194100000e15050005141c0c140041c0d00182d280442031007542018400d62412540103402c075002e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 453283660 1250 453282410 453282419
    0x915030b061603260412200a030305180705040b0301060b0f04150c021f020708160e0106030b030a080a05040f09020c010533030307060501031a0c1201150e09010b1806090307 76
    0x6804070036001c1c1401c100030501c60281e050610328000e0fa01e0b08001f4043d082c148802d080c01400d4800150040b02c12011200d80c0080110340002c40d4030440750150303804244d0801403c0003074010501135010180d40b013400078920300700c00c04000080064a0902902e40c280e501004000c883c3c0341c40d12a00290051100013042c0141038103d1021744a0144600c104c0345880e0b111803040342031400220030401590100f102c2408050464841e40740901045d1808000240400c40020396841d0a860042c18403040020035018183c8a14121806446000110f400f0965a40c0b503010095105181640c029441d16000c182110802c0343c2004803002c29072140304030028841c0c601400340110007581c652604c001c014010000312140200341c000c40c0a011440002e600000d0682c5203054024103030b041c481400c0016801080c2511350490558102103e800349407000200181c1d41510b405042540c0718180400010301d0040303030f00090011100304480345800c54a0344003400303103034001d1010603549a04080f00070701 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 453284910 1250 453283660 453283673
    0x100b13080d0c080301030b040c090c02010b091605030c0711060711010e10050910170a0510140607080a05130f080c060405090601030902030a08040608150d030915030b0616032604 78
    0x54015010b140c9d0321081030750300c1c104003007101e9000415102507510b6494910700e91800c034030016070103401c031820b4061f04001c1800c010164840140700007980301780072582400740000441011031520010740350941c0d9a1803414250301c518011158540050908600300c2000d06203502004503048450b1103c600781446001000b280c80c0c1c91040c0a010091a202c1060171280c1c3c448090740501668440001d03a820051070912516401d5085203c02031008000c0301100e442d00700441e50815081182c15484d94940b8174102e81502c146181074200e00c1a9600105203e110214a002210303940d40445c7c18030143c00d400d01409000713520070158420801c1c00080c04a5009801002d0400d2000f400c0c0d850340e41781a0f4038480d00350071030341200380050084004c00040c1408501d50381045801210341c0c1c00010015540101703420440e02a84038100200d51044a10364040c3d000704042c42402404541c54000050709134401c0c2019040c140e000600c540b0801150048181500504903030807001a40c0c242d85540b00c49 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 453286160 1250 453284910 453284933
    0x9010207031119030f0c0807032409050a060c0e030106140402072f0a0b090d060b062709130f0f02060d05010602100f1a09100b13080d0c08030103 64
    0x1500070702c11003c0844060480b5401c0c802a51041841010065031810a0104080c081d00248030540c003051307003400805c0d80315140c002c40010141e58801c0500c803040380c071307001b61000e904001c08a01c64810b9030820025580c1040c422895035580724050724041004040c280d907000c0c4611001e070309140c1c040001c18146900102801401031440c00207071149041c1c610b0020803d5a107034144844051010050b03032910841c500c0c0106181d03080613052143c04000120700e1001703108002c10b09550742c016004141c40324419640603400301d041c13031550000305506420619801400036481841010b001503040c1100c07511040c68103401c42c0c1001a001d91680e902c4082c00c00c4100140c1e40401c05010100c401d14003401030754080c28180c0d024040c0c0c031418242d0001510007911030a040c25003400c8101d0b042d03045810060f050180202c41d001560f4441c0c031000104101c03e07070408201d00c8000902c0c00200a500c110400480e10345000701c135011580309008940d0b10480c09001007038000300304010400320300c004082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 453287410 1250 453286160 453286193
    0x10060903022e09140108040b0a0504150e030c060915010618050a03080405040f09080a030c0c120f09080a05060a0e010f0f0f1a09010603051312080f09030901020703 72
    0x9040c81040c103505810a03050030b6505080001d5140300d01802209121012241e131000282407030011400c2942e541490700340b005000140c0c40b5556400141072001911f180440032b002c07090700b0401e10404c2c0c0c80450300da0b804548000b80c14841d8134007007107110303038006000042542040c0261120f6401d03c0021141e100c000541c0c4074441012940c040341641e03480040030300442c440c0850b643e80e64941030900c415980a070451031080340c42e0100c0e900c04a8180c0341142d80c240070a1800045118140b1410b0f5130500700c140c0701074400c28500f408140ad454201c03140284051464555440090769074240c40d039240c0280e000240070303802110218039000215040180700c13000203000030850298401c2100100e0b01c2c0d802090095544518684102c0701c581d01c64035a00c094081342005c40304441e0400304901000601c0341204069481300003400708050b000c03a028807194820700003030311580500d01c001d211080a45040a80c62890800300c2d21150317000044a0704010183c0140c03e0310382ca140ca80501141d8034508 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 453288660 1250 453287410 453287449
    0xf06090721090303050108031303120504090f020c010e1222030503070302011a0103091a0402041410030b0c030112020d0201050d0e010e0d090e0103141507080f1006090302 75
    0xd081d00c03510100318040031100d1004a0014148405090090a070360041e4451240d98004110b448403160000c100f201c103498010302c1e8800c891200c1502112144910351003d803101f4a0405071040045640e0000e20042403400020b0144041d143d01071900c940d443d01543c91444000c0180682c8080d000d07403402001003801d0300140032a0350300e8444504540c401c2c80c040b80180d41d503000001c4410f40301d002c41c07000c0e01c4081c0b8040188482590b01e52000d03c140000d020300e8120100006000c43d41c55412104031070541c1d40118042c6d0910030040004a503590004032104108000000d20040f1000247c1c6d04a03030b54018080303c441042c1c0c0a00000025620040c0c0c10054104405c20034020a8040c04001c010504000900204150351309804d12a13200c2001081088040c010041208403c0b090380c15a9001884080050b41031440617240011014130744a0594181007002920707038100481a1003007400c098100ba250380c480c10b10b00070b00584ca001710741c0840c1400300c00344094244035034210b030601000030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 453289910 1250 453288660 453288677
    0x402040209040c030c08010602060112080c01180b07170c040902070f050d020a140102040806010e13020a0f05040b04090213020f04050a15120605090a0f1407110c090f060907 76
    0x1000302c0d0948400c1103404000c80d85079841201c5a95000581d01d004184c644040c00f110350505800c0c85540c2400c00c005003042d200404d400200c2e5400b0b50000f610441c040b00d100756007001501d00035007510000c8911030041546440e45039501c0c0101021244641d100034007031858242014041c2c00207421156080e03c50303070459400c0500045080101c01020400c41e0000c000d1000c6900c0e040400c4042d0004502640c0d0040c40308110180000a456040d680400000310316603440342c7c032030b00c1204450355020750312829000f000072301c5003030504500c4245c440070703202440b1740c00041c0c0a200965005040081d006802d040004144d081541e018001c09003021501c030f40703040d948000080500400350041c40d19a050518510318072a00704906d1010088180801d0041519100010310804c000514440d80251600d902040b083c0741580f2904842420446150040c00d2005005040c0003106160862a121f040074444007071600021440c0700f0303c4007500c0381d85035035124811712030101030107020007050100d8507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 453291160 1250 453289910 453289927
    0x9120f022206080c0310090b0708070c06020d050a0605010f0f0f09050a03050f011415012303100528090f1404140d110c090907090f02221d04020402 65
    0x50041400801c0d03c0c0300241990010103041600300455081407000b441d2070814010001110740700707015072021160400102650310b8a0007030303c007081820709c001d04662001072030b10484d0180c0e40c005030255440c1d42c01000810303140e500640b05810201c00b80400f05070540070b00341103035104180c101807500b201e28000e03070320756035a04c049401c000d41600200e80360740241d08065a503080901c584425030701842048520f41c00c0c801c201960490640250b14100410500c05880d404071111030010145200800541d4929010414000254140c02028072400320900501c2500090f170b94035003140ca040c0c80c0044110351401c03852500801000c0541401030ba04d58002001a551032026a8807903800b1703803034824000041c0030043d4100540c6032342c81400d224464004c1d648081d0009840d000d903440903109982c0c0394540031104c61800d5005e40c8203600d82800c04a01d06031034120394028100740c8400300d05490700c1c02c0e4501d4106002d01171902072a40100e07401103024820401c448070307241c0c125001500042c9001c00f0b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 453292410 1250 453291160 453291229
    0x10b03190b03070b040812070c090b010c0b0901090318150509030f01020a021b0303040e0708151c05070918120e311a010c03031b020d09120f02 63
    0x2075004407104e0310082002c00c6107034410b020034250f41290045c054600700048e0341c0c2d0002170040f4080d180c91190380d060b00c034146034041c00102d0403650304107a84819524006008034060100e440e8110001250580d001d1941c01c15401118261050310100b456040c1c0c0b1410111040c0c1c011030318041d814420744545050755a02803000301a510025409008101d00100542c0ea451040842681c0240d0017088200880c184109480350440241c4c6040d25140d194280161608010695010ba0010f001140d404008031180390703101446200e0410b50301019078420340c41d01220300105d00c0f10b0305000344610681c0000d40c00100d0401500071410090003012081011418020204c800c0d201101c07401911048858840a0384241a4071422000c1c0039100c1c075009400c174014513011a69041c494890080010107020703800c1241c2c035500e0301c8001480c01411603002036460ba554440d9601080030700e540400d0b950b03074240e1441e4619800504840c0754181a900b484000307981014600b0071078000c00c0b21590400c0d075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 453293660 1250 453292410 453292423
    0xc1403070206061005120705161403091801140d03020f010501060507020406141503180a080304020f0111030901120b04020c0d03180b0a02030603030702191d010b03190b03 75
    0x2141e40200024075264050080382c407030324032100080c80014800410080c1d010003900307502081c0347c6881600d034942c0720740741c155110491200070309140012170300301d031103040000191043d403008403940406001c884040c04010310082c014084001a15121148241032400040b221203210348102e0700c0c100c55405216013124000e802c80030000300c00041210075440d0a001e00c001415085032204203000e40c3ca0002009100b52a0981a2014001c00040c00c440b8034000d002c0115000f80b42515444003192900344074650048504900c2440110304c0c411071340d441042607604034070301c0784002c2d45880310000042d1048201d080c101c2512544600b02e400312510b40d80081c200505203c030040c09078403800f403c044e0544440800800f110748007800c0760b10100c0c0c2c030103a1041d0800c66003800181d8a84030140401e0461282d400041c0d080010b40850650250080d031070390342224511248d04181980300c1c8402e80115a0a200300c8031505400e00116602d40003182140801c00d00000000a02c0c3c1480404a800d040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 453294910 1250 453293660 453293671
    0x50f0a03110d08011503110f040b04170c0d030e0a0f121a07050a03091e0b09060901020307080402010e03070e1e160906051617190305060109090c1403 66
    0x41c41c81c000066007280801910300c420314a42090086581410b0b810024254000104001c150f2145420300d07500a030541100d860b5080401c006584a0701c500501d441d50b401407180043c0e584105d40d02043c80346001c603044080020040551040b852075403012180c402110104a41c0204046c0000510b140310030b15000c020b02c051600d1041030301850514501080c2c044c21b0f00c3d14803148040030011550b5000b000c4992803051410005590610741c08c001c4003440c0c249204c101c40d0720f0305054080038041c0c9103480034400c04255007158850b0f500c41014600382d020990714400850000b0b4040342c010740c082c0c1c07460b541d5450043d044039510390b070f0b40340100380c0150162060001d10280c411101011240480b8443e40a2901d94030103001c1c0443d4a0300a04d001414030849041000101d0100821000c7c4240d0302e95060700014246000d403840070ba1300803a648864610030102d25245c456007000c41c064002d50784207003816102d0605091070050400b0142c02c80601c6503080001d0064192102d1034401c001d98005c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 453296160 1250 453294910 453294917
    0x30605010e060f011407050a120201092d0201110c0310020306011101060806010b0c0f010509030901030614010909020f0c0a0506040b07080405060103060b010c0503180103050112021309050f0a03 85
    0x552418071428040354000d4520307402000041203004040e600400e080d1317102a0078000071540c800c2c01d81000341c00c009030050001d1400a0000c2c0b4082c06a6054004101e524082d06800c6000030482c64640000341010202c0751240ca03024039504099805020a001d489040d1004d1361089031748007000900300403140d2180c140382a4048103001c0b41d07591080000e04102d644800802c00340e414180c200e544c2c0d40d030501c00d80414400000310340c00724041c00d007c50903089401000900090924255043d26a0000442640000d00c2d041001030b10340840e6150240c03030001a151051460704110180d0040c0d0301c81034506c4081d4904004200c0e2800d801c1040c2e581840c0100041c0c61507007400d18000c251080301505000800095000b84004a107010070300604580d80540700141c1c2d82004001620101400900640140404120307040b000409804018100c64241da04000b560380721603122002d4640b104010b501700e11402d80458881e01241d100e0103030513000303500300d403512011b404142d450801424002c8000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 453297410 1250 453296160 453296171
    0x20309011d0f0303010e180601061e0e0108060d0602090303040b0c06071e0815060307120b1e1e0a0f08010c0c1109250509120106050d02090a11040306 66
    0x841035000c501a241c03050100540307010038180070309658a00040c000c5c07410018082000c95160010680ca8040101c000390949241e0740e90b0307980282942e540f4100a03805000402c401d01030891055803243c15207030b816190110035071211818014624454a02101d0660b420042000c003036401700301500003040c45030407196560001407034607810200c0283c400420700100d0040002d6001100c001c10812604519000c05156036159020642c402c014110940025001040c0004540e004074411655140c041051007507402402c14841c08038000300c8a0600c3d5281681240e60b241350080b103003a07840c08100c0103031901140803c0080c50809a50344000080640060200b000f01020f000d00c0040d4441404c00c000280502e4440d10148500c01011b181b20380b100100160030511000901c0250203a00960300703420b0755154001816692221003124815028200f64580300744050040c0010740708050410380c0b80c2e44055003407109030100030303050710b48c1c02d51510802c0204045c00030203000151700070743e00403ca = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 453298660 1250 453297410 453297431
    0x3033903020709270606050409060b0f100e01140909010b12130f0b04050a1a061507200102070909050102181c080c0a0c030501061a0a170a0f02030901 66
    0x940401c42d40903200355810204008601520300c0084c04a58884110008001c10036141c000e00801d000d80040c2d511070b20780380c3c10405208069202c10790200082d82d07500d840c0c801d05000c1018001c04880d0f201c0c00591a0b90311410305510411500c0d50b5a601829141c0c00c1484110000700c903445c0980001c01894000b10f50804404c1140c2403c54010701c48061402c1011040d1b02c1c2e080c0558031007500600071081010111b000c00c6401c110507507419400881d28030259240180007604040c0544080e44140c203d000101c0b00d00240000315800c642d400f9040184041c41c141c0d40030010f0214801440c10360040b40000106e05500c0e00851440d81e01c10400180d03a401c0020a22a607150145121409801000d8030411400039420201649076000b007102c94846e03541d442028544030701c00f0380080849488440000401c101500300c072040e900300301054440310001e141c3c50340c11801a000004001401401903152292107803039103d802142c68040443d49400c420348600c1070742e0041da240c4641303039565542d01a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 453299910 1250 453298660 453298663
    0x11205070608010803070305090604090f060513020a05090f04060803120a11160311010f0e070302040b06070503030a050601090b04061709010606020d120e2a01080708010303390302 79
    0x20090071507802e0034030701c650403e1039540c0c1c0d0340100480141070240000d50590150b86da2400c0e5801001c6001040c80720000b01d00d45d8502801a81c882c0c140540c1c01745036541003000d0300b800ae031042000a560f81a0400340300d21300b0000841002680980c1003a504c01d000304070058248000c0c0416641549410114208200f07100c0403144c0070408041905000d0242c545011260046400f405800d8036100013050703e514819070042071000800d003840d6241010348036440a011800c1c0049070300031a0b040140203504e40500c41d0038460030a00030110f80007000012981c080d40c2e40f03ca5007181c0c042c540748a4850f00c0b0070050390540d01641041e004995248100360900ba014038040340d0141c1c0d05030003800352a251107070280d524228070402d403003481038405202c1c0c110f5045522103001c0c610b000048940401c4e0400410b201c0000c0003251110314513000b107c80040d0f500682400b80124110707601d010300c507840c41d1011100402080a684041407010900900000384a441203a10000088481031100350f90314020303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 453301160 1250 453299910 453299923
    0x190204110c061518180715090501180b07020904030c0b0c04210203100209010203190f020d14070f02011205011e060305010f2904080105181c0315030605011205 70
    0x1a403103020000e08144c1c41c85102110103402c003107581400d6501010b02c110003401e0182039040045600c600c800184000c0703074044984802c6810a883e16110310203e88030342108022140600201c03114104844001800c0c881c03082a4814002d01d084175001c1c0c11652000b80d038441c00d07030b010304803550081400d014881071400c00818526026160400301c560a5000c2a00c6004030200c1481155022034140885e074000c5c400c41e81c81010b00080700004280446019041100c04512240103100c0c00802030165405070304013045111140c00c01604010f00c0355129040c408000b54200e04022210013000c410059500030030340601aa2a1421400c0250100282e281034082e0301550406081000410103500419184802d41d100a400c0d1161001040c44c10002407010a010718008400043c001600e0401940b2460003a41451b405c036549844102d2210f5403111441c007400e0643d190300c181420183d01a52024164508060001da401a83c076140d04044030400d80c00b403150b440030040038000700082400344 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 453302410 1250 453301160 453301201
    0x190914010e0306040b070309080d020d05100b04030b04060f0207050a050f1b040c021c0f080c18010c11030a1a062b0804030c06021f05060102190204110c06 68
    0x8100796074881000680c3e00e80e40a4005400341c16404089483d0364403a800410600b504140e80341c1e9160000d2242100a621541030a071659290401043c4266841d4262034122484848154142800c6458444260801800855400360345058000c0089080e0003c2c000d503c5c0507030081d10504005003450741c00c10100012210071508082850000d000051901154a075400d442c0000d401d55545070917031134921740c185150141e090854201d00f031540e001e62040e0406449990b04c6540f070b203e10400c12b1460180400c00104210601d8130000725500c203070050200c4e180511700982c4051a5100403a08248910038182c6012411001c00c090500d10248055003164040c2c805103181c090800d41c0c1b0103100e4504000e2008a0440101c00052021807403e4074065034200141020060b40e40704017954581e04c181020002001d41c2424040706a410301c00c01d8072641040c1c0150140c1d8040380c16200158030154803ca07403041d5212081c0c1c41150300000075108102000c0020011412718841403405600c51514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 453303660 1250 453302410 453302417
    0x170a05010b0114160618080301060905150f0d0f18030306120b19020705030d1d010603050c120106030b040b011d040c0e151f110102040f0311010519091401 68
    0x84020058901e00100c681428100106141804203803408034040c04003038901ca0300703a00d400c06c0424144400000214101ca9550301c9507081d00342c1e0741080c0409400f44000022050708207000100340300c2100b00081074404480f000003d98a0346001c000021610000e0341d80704c052030317081400005c25415100d90400f43c01c0000305028060429900c2d1140c001005000300b05041003851840b160b030704140c050710321a990000030b480e214030440346000300810304400d104c400705a55244600e6034000c18460301050326040300c09000b1444102e0140041804004000e4600303658408000010542403c4601d006900c03030700c125801545070004044480600c2c4584681080c40501444000796403102c45404440321154400115581c0303950b00000c141000c0d880390f80061a912400280302171001500307101030443d40742c940c00b43e5030003c0e42a00300c0c042da000b00000c8601c00d840500101d220100c1c051244201450300601e0545a0801031012000002c0403e012030366020090241010b1340ea0032003c01042031a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 453304910 1250 453303660 453303677
    0x307091b050304050a02010e03031e070209070c0f17040e100501081030050102030a0e100c020717030403140d02010c08070c02010c150c0c0606080f060f0c04170a05010b01 75
    0x100c40d5505c824490a00a043c41400329240e5540d485c14001c2c0d07448041c051450b10b00c00701d4481d400703d0300c1d503114000c201c1c440c4c0c00c860009500d060250402800701500a172903130341a2070007680c4003904000340c2c4600704101740013804000707454490002c2d0b9901c00c100e40000300344a18030f06070000d000c0360300113001c400e00308007000d50501c852007884a8089070b5030719440c0d10b0521000360000a000000a1003130107000395000200b0001c9420158105080209900040740c1001900c0c260140440d90008410801a04075101c00c001201d01c00c0000e009400c800f1080e40e181641d2951540105c0d02c001c121300100e6040400c09610301602881102009200d82c10514403501c0c0c401030003403820301c8480000f81844191a005418000c0e00a00d15182501d204001c200f008401c0d04041d04e0300e4801882120210f0416102044415000c01c0321020708007218020300b1903485d50702000e10400c100805251120b0003d000008400112001c1440c0840300000078003801c1d03a4a052640c2903c100001b05170500600c1c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 453306160 1250 453304910 453304913
    0x3071a011212030920030615130905010213030f0c0e1b0a02011506020102092106040b130b16020105090606010905010c0303112101090614010804030e0307091b050304 73
    0x6044031165520200030704502e041510164002c2151001c0035058000b888820300c0340003002100d04404a03000c9007200d940d603440854054010082d60340258000c00401d51080703d6104075040440304074481c1001504007200b0907046d140b004a282d0082d50000024140d40741070101e61207104d0040d00d546025401c551412500308c1000c401d0348551a580310000140800030240700394481c0051048205408010b00c0e500e4000a01039040b1061407885004c404404901d01007803440080701150b112000341c0000d54940c1c6406040c1c00004042180e10480c0d50051800500c40712041803050b045401480c60710ba04e441030080c2110380c0100405566881b00c0180200c907a0131600c0c01c4112142440c0200b20480ca600d4120041c000a4085114288020070030712920002c0e085d18912503c0c0300c4600c040c940e80c0c3c5514600036581e40348542c054440e1014140c0c4071300e5205600380c0c3d49c424042d00300b01901110b0741c80802d02e0460380b075001201659a0314103841440c00392040d0400c00d40018a851030560506 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 453307410 1250 453306160 453306179
    0x621010b0a08130f06050709050a090e0606060a140f0307031b0e060d0e060a0207140a03121a060c160f0b161a07050403020406270504140f03071a01 65
    0x1d090200c1491215410004000000304c410301202d0740000140524100150b0141c101103241c05601e03c6460301c2640804c2103102c6201c0e1148031102a0b008140030b84401c0244aa00d030301009162082250311401e03284c560b03a44c10001c100411024288907520314006200400b125000780c40c2000b6000c3d400e02032403603188c1c031001c040ba105404640341c4c2e58461032107540c0c1000b0180d40000c001980910340401148030415400741c0302d45402100e44201c84000e440314507842d8401c1c0400180410a20348980030451110750114403007d52401100d1070b194010320018200d0742005003000401c7d40841682c031103c0c501540da0308002c0c4060703703003251014109445500706010754150485007021807415001444203540301c002c41080d480c0c08403162800d1441e40104141c1c8940400d9000300c1c00c0c01d40c00201c0390b00e1f540030700c9060fa4401290060700d89040c106200500300c050000e0700c00c0d00d461411000340440900007443d0307600b0031727000841e84c9402c14903184410b800411003440b500130440c4010060b0005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 453308660 1250 453307410 453307427
    0xd030504050a061e060807030209060406150809030f0403050a11031603030305061906020a0b070e090c0717160611040308090108040c0e0a02030106110708070605180621010b0a 77
    0x1807220b404201d024088480c440c2d00b04c079540305900700780d003440400130300c48070040b64060540703001343c60700c0303030142c2d2150140019140e082c4200b00505c4000d501c145030051180391440c0e0004403100a0783d1814951992941c625000b43c1c0055403290846600002009000e00e00e41d818181e01350701810f0040e507240f0202c1400c420601c006000d264030b40c0c0c001241d0350350741c1012030303401c0301d542e18598249519513500030343d1490030400c202c89240c100c401040e516401044450700821005040c189603968400003c142c50300091400c4540d46040ca408803805025400070300740f803d5507403404000400640c20507405440201402c00c0d1000d200300002e0010038888001c0f580300071800e0901c10059182c510b4905266602c5620410107010250140041200103400860481e030707541d601c14403d0007500455a4582d407051041e0740c1c0f9a8003a00c810031226000703401601c4008110078600c0410f02404001c03440c01d42c0519110700340c50000c0c10fa00600c1a6183c4a00c03405000c1801c080c03410300014041c0a40f1400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 453309910 1250 453308660 453308663
    0x22505070b0d15080d08070302040e04171c0b01170c04120f05030d0b0a24030c020c04021809281802060705060114060f0d0507090f06050a020d030504050a 68
    0x80002e00001c0c00307640d900081c500c0050307940f00c02105540e4001e1251a584420900400a0041c0000c980c44600c00e009440503102c40098050386521075503510400d5050102481e483d154080c020b400711901a4205001820880c442c00709004292100041403011900304859100c00301d002804404c1d2885030544040d06c10f03514040300c100c515410007594072140c941009020313100000e60480081802d40144031001e00c10382d007a10352951601e00121194182e548240c8a042175a01101d103030620907005006100c41c0e03801034039000d03002640860240d03480000c50041c0f25400030044001030a0440c8025444561134114100304800a5510b00203201c00e50f8683c42e80d135440b44012a4018113048109e5080c580c020821030343c9500d245425903d5190921504401a107550060807880c00e02401300d400042d030495010345081e035002440e800400c8040d08a00030880100408590403118000700d07800b80c415a200c0c1c5840c2c0000d182d00a28000540c4200401c00d402c00d0180300016034001034103042c46 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 453311160 1250 453309910 453309929
    0x100f05160201020f0f030904050a05070e1011012f0c06131e0311010e07080c012003040b04032013020a030902091008010509030c0a020904030c02060d02250507 70
    0x1031240c00100d20b040c0c4001001d140074044c0da45580195040007006002024090b1000d0080c4e540f1656982d00302c500c03c81d10134010807540c0c0c651071218a4482500781501d0b1032800d0100042104132680c900311410406203c4030030006840410034004c8920b1100c0c0c00e54a10100b542c98802c401690395290440035280340241e030b201050500c1000343e0108180c81d0307180041c1440d90304003014200240307001d00d0500b14074650751a04480301c1001402040e50002c0e01d00005c0100386624040c001114417071114505100b240043e040c00100300001400200011f100c0920f01300c1e183c1d400e5003442100aa4654110244e40300d070742e128031045484605161015008800c0700503188d8442c10170540160111040080d030103041d05003041410203181910304103884119000300801c0e40c0b00c1242032f5903031040a001c400154070240074400103103800e00000d41d0140c464500400c0c0c0d043c00d83d01084258129614a030011900402ca4400314480203800341400141c0042002c2c904041d0340329141c4890203070185c040301d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 453312410 1250 453311160 453311197
    0xf060c060609020a0e120a0c0b0f040315050601021005070c0209090c090109020a09080312150a0902120105010e0f0109030b07140c0c03010605150f0304061103070e100f05 75
    0x80c0101a405900148510341096549008200e002803e9943c566001c03813040da580d152016803000009407020903194001c0c100c0040905120144010760841c61269841001c101300100c0021180c1500b0b1841817528503012402d4180302001901b030000e40520400d01514000c200100a43e104c0e0b4a0307c61705405907200ca500361101840e85042888240718541c0041d103180002501d404c1c00d0f4010070813850a80e4030401000d848128a45d10fa106108000350001c2d012008034800135022048071640900003400041510b1b9150030580c241c4e04124403014188180d03000400140d41c00c11118080b0341000c0b0303110740c547c02041d000078049802c18080a801c03a0901c20014035014040ca022090034001445056160301b0002c400603030350446d03065150300039400d008000442d4280702c40e582050307120007259141000407901c08005246c00c0204107440c200c1d00e41103400310440c841d000a601030345080d41c03502c0395400c6440c1401201d029607001d0104200a44091149980e0300c502624250041000368140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 453313660 1250 453312410 453312413
    0x40150e1309050d0c17130302040209060c1009020a050103020301320307030b0417070218040305040b0d14010e15010e180c0a030c0e010804111302030c0901030f02040f060c 75
    0x80600041c0100b041c407854050012158004043c158414460782c034030041c1d03075102c1d0b10308001e902454161030040d100d10701d4144010f25144e0060801031401800e42801c0c041c021240c0341c0382001c1000e450b064586c0e20090b51087d070600040d04d8011300000e080075841c0d94540440c082000d00c801c4200c0c140fa0041250700619441d6400d908034844c01b000b0121951540c8030b05241c403100c030302074400326210b0b110511050801407812055514151300180a2a2703958041c816982d12018001e0085040080421010402c8198100039140072506504002031403c85103143c1901d80c081031308003803140b004400400040e0219149014240642032800b0404410904045040071104158484503141014200655100d89001900300c0c1c0382242c1c0d06111000b603000701a01d0440c100140315000070716440000300403820f02d07c0781000c19500500001c40420007400804106d0b001030354114034441e40001d880780d041d030749070180380000030481c6000c602d81883c2c80302e003460160140c402d010900c03400c0c08041d030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 453314910 1250 453313660 453313699
    0x9090708030a0f080a0603050a12110a150509010605090a020f090d0f051506150336071a0313050a1b0f1211010540150e 53
    0x4000e010216038507580e1680000e05403c441c03603807400c00603000d4000501500d5590245c07030100c0380c211000d08407054458581d11404203c03d5094011f1145041e19000c2400080040105560040c00240302c0b088092154000741c0320042c241183e9a07040c01c9041c40f290b507640e00102d4000d0706551005070342d24140c14036503006000f0511441d03400f0322841d1103c03050002c03021403081011b200340191180200c04500800c221401955410381280e50b01102a504282200003550852101404508501030f10384034400c80247d03c9080e0b000100208002c201e2149013046103c02501b505e00b11640080f0301d005c0c8000c0f05000050a60070a6156045554140441071151011582d0009824113043c1300ca0400c9000c0c25240344250301c00c000c1d41c0c0000107200c601c40c000709c0040301d0703124540484d103042c0c850045a25410001011f440b0081914801949107a524160312800f1500452440300411108260002050030b6102000d9190344024950061f644024004511801240c8031100e88440b6174070390 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 453316160 1250 453314910 453314923
    0x6040e0f1c03090204091104200706180f05070918081204081c0603230d080411100206061005090907120212090303090d0e240c1614041a0909 62
    0x107174005281450748018003820707401c410040c0905403418052900041c400102d00c00b400b0b41107030005442402000002041d03500700394600c40c03000e40030018152003916955404284901e0881c2d40381d008104c00c0181c89420f002d5140c00d041c0c03d5240d1912a0699150711800d48110454002c101d402003000804008105051310340c03d4a898280b41d440500901c0300b80300502ca140001e80354952915008007500b42c003000f00310100441e5030090704c03010f43c240e8010748403e03802401c02c41d038083d40c100045403961155103040005200d140d0082080d420f10405002064180070301c0c0c181002810003015203035884e80c1501e940c00c0902880c0100b903000040784d0b03c00c003d00500ca5094940c80110b02031080003030001010358018040b0009a03944810508419a042d42514140542000d0445001d040c0b5211f203485034480d07c01e181616030b1501d41552095130500602c00d0b20401000240c02d010322900000100708151008251410024281009010404a41c040160520880f62600040e024000074481c0707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 453317410 1250 453316160 453316163
    0x140901121103010f080705031207060e0f010507021005010806010b04260d0c0b0f090607050901030213060804031209030e0d02013e01110f0f120f06040e0f1c0309 71
    0x4441d165611084c007000b00c43e0f0b2910500c12644a0f0140106540c680401c80f040c641c004d407040180390543c00c0c0d07944406020f8400d202c80302c6004050710788156030400c1c040e8a00c18800c5501071300c0f0b15828100007004555040e002464103a0103000117000790402d800032a41a2240d0488640c03080c001888189100b01084149040340d000340c410010881c0c0c3c02007400681a4420130300700304e43d13560381070a04140c0c85044513608802d030300940105418178082c40c020804040103140151500e0242c164102c2035110a40c4001d001402da00c04210038154842c0c2821aa040c2150040c4074110894500400098420340d8082c810000020810f0840e80a260902c003005919840c4009003145009900d1401030120710404244c0301100c1c4046928906101d145200c082c41c2d4060340c101a8101e124104a4018420306051002d04100071514605e10409240c030070550200c0e50615403030300c0070500068940d51034103400300b0f9011150340302d00d500010840b03084040c901c5e171400e204207240c0e11046000d0143e5660 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 453318660 1250 453317410 453317441
    0xe030706150f0906030b0604020315040f0605040509060105010f0203120115090806090f100b030307380105040b06180904060213080a0c1406030f130602120f01050114090112 76
    0xc006420f0200341c0002045a000c0c0d184460181e030b40c0b0060000741c0c030046510401d92b203900b074107803542c1e45010341c4004040d08a96200245058542004c0703401c0f0b0340f05803904c944a60100c401048650303880f5804004c0f40310b03103102441c10489444440700001d81c0602039030014501c0b10001d0085036100324100001404850308455080c00d00080082c1c0307505181e1070f100814003412841010010490007500015480540118500325a83d01c81c00042a100100b0310001c01944080300030000c03410101c19080b400c07203c10b5011552400e81000704403120340003075a0180b08240031179016044217401442002c0402d8030105529950b9140100091007410811445584034000201da14000064454002da110ba045030035407980303c1d44003400742d20b001516568440801c000050000d042080b020f50070140700c2c0c1e81401d1820065540400340d0f04046401000600d40340100400380110504560040000f030800c00d00784071030120018068072800c1c00e05418001d2180140000c0d0fa190390007801000303840c94 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 453319910 1250 453318660 453318689
    0x14150f04110909070605031504060602100b22090203100e01150906030c061103041211190506090411070f0803070822030f0210060e1008010e03070615 66
    0x100410928a800e450079110904805803240607400d1003501540110031034001080700038036101088a01e54002801c481e01c0800f01701445c0030075150340c011200a0015600034000551016074500b04036091101c0070b0b0722448000c001f150035141301003401d20a070512103002050f0090203002091401d60302500d0902220310b171950110b04110198000070801c44000f008040b216074036aa110140c804500028141c0000740504000341806001196070960024080c1c9040a50711200c0c0c410f0410000c0c0146c840a43c03640c5409441c1c902400900300c035000e0f002004910504103800b040c0107001e8904200c1c0211740d94000c46d2019503200d001da400791a40000303030070501001352134042c0168105071a05008500039001082405c80401101c0609020741190345900c0003a030b807422034007030354178841140543c080c0d490011a5a2558050000034204481c241c4005040c0701088d00d081d9400c40d800900103915040580c40c01290110885404076003000000c140b0303407180c104003a181c0b9a00d40c094040b100102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 453321160 1250 453319910 453319921
    0x51204050c0f04020f09010c0f050d050406080603011e050c07050f010f0b240702010921211704050106050a030302160501080622270b0907060c1415 65
    0x1003440103100155082c01250340c0c0035060006074024000192410507061001d0302441d485105054141800341c80300e000700e0022500c4071030528144801c0100043c6002030148110740d00800015000a4150020818400c0500340c207003213005074003400c0f807199071203402207a1026018400d070362040d0b812100341c505000385102d5481c000d05400d80c62108003400c044440b0343e1460403503004084e14641c3c1e0341450b5101804162481e140d07001031012818000d600c0808503000c424801804007501144090b458401c01508207840c149080c91000070200402c100d030425699407042d006100035600b4903072030f069a02d272480c0040c0500280e400c480d4004500340c200000f416070001b0350700004592601c0c40c03007403a6125001106c5200081712100c2e0480e44118905c0180488044041d0001c442c40e80d00088030690380031442e64850b08007003c02e00c85840c4c4402c1d1130a10500c10801c42d000341c081401494201d20b0490003802030140504007230a03102042d038042d0900d0009204c080160428500c081e40b940c42c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 453322410 1250 453321160 453321163
    0x18210f0a021c140406140d0914100203150906032b030509030403020105030106050903010f050903090307080c22020c0105040b091603022d0904030c0308160f0f05120405 74
    0x209000c0641c1c514040c0008040b9008000b050402400300308520714150418100fa03c04c0b0066030f02d544014082041034481e103140c0341c45004031161043c09a6010900c01403c0c09140c0010b040178080c07440e10400500500c5d03500402c45100c6800c05a07040b42c41076039514002414500d01021188041659032441c80158091140c10348140030a5242080ba80d20344d99485980c0307000c3e40c04028003081c0f0800061091501510252010010044c008194a000c0c0400b0400b92842039070850010741c404605400d044c501800144050007540000703210180ca0900080c580240211940e60481c21442084000980640403926020f6400d0001e011506043c0b4005500040490301e29030340c3c1c01540c0380300e4625603040c100e9a045a800420b2602203d08096090004018000608020001c0101144103503103c4209140c4610b000380c5030f00301d5900e075034100074040d030b600280030143d817145102582c0a2950840007100c07181d8080c1c50310400400154202ba1101c0c07180d140759650400752a4100f00402c80c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 453323660 1250 453322410 453322423
    0x20703020303130609060509011205061f0201020309010b12190f0506010810060503030901120f0209040615030e0609100903111006050f10120b211518210f0a02 70
    0xc107a561078120546c0c0360300444176402040309140c0064000704000032826407030380001da000300d030052400062041c20426903003134880884c44680942d401000b0804604d10038441ca0780300c154103031405076803070f400c40c0c04081d180d449418251a103040c41711010400d10403420b0200504030303032110480d41c02d96101c100c280d07540c580703403400142e842e401d02c000451241408800d882c0c1031034068481038540e6050755805000342c200700b2895001607500b441a0682c9950310b020f0719000303144510490054508001004042e00c5102c0300f0010568071140c280a01c0d49000a000d80c0da00906681c005030b4001c0030319080b1640304c034505100351300c0d03c54210203003000c503190b034420710480301c040b40c2840144e038003403050192540c2c2c03241d50140030030818000345858071140d030484e828420004142c003403000c10703512540720051814540f129103580582400200a02941c8402c2c1d00140555010517030041c03107214a6a071000501d1140006a00300e45203104040c1c035080039148081480707500320f40c40d507005c150000c2d50f030315 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 453324910 1250 453323660 453323669
    0xc0f0303010806150d0506070e1201020f0702180705031302040b120607020f160537030605010609051e040605090142110a150c031d1b0102070302030313 67
    0x142c64820a03581342c504c1448103540d5000300981055030b0303000022707036034868010351340c0350000403401c0104400a0300f0f2000f008120342040d403c13601e449050040c4175040e1178050041e00700c00b00b40402c0c0460f1981140a40e83d202c4014044944d904100c0c0c03002c50003070024103031116040264a500301d100014013195040c0700c1c0a103030b82114000c0c8510944d05a490418240140001403505018803131810220002040b480003540c2c0b0749000b0450b1a000300301100c203020b81e5400c404040a0072710402c1054004c980c010302c11841e200307000900708400a080c0031300004426038012550b800c25189a211900b0520042c00e00815800f071642e0741d61483c4050944003145464542c0c0750251001440205000c03110345c0803240c8110029807c1d0030b44080c1c0304041544c00391200e03403294241400006507081405500002103903004611900e0280c0050103039940e21600d01c00c0d25429410303140c1c280ca00015481e281d43e002c2c2c8032140c00c4491000060341024110342000c2d415020010b1508829402c1a003d1000ca4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 453326160 1250 453324910 453324931
    0xc061b1606111c0f0c081b0705060a02070c08070e0a02072909010c080f070f09090e0106050a0b1806130302040515010905060310140402160321020c0c04020c0f0303010806 75
    0x2c07503a04ea000c045405d80900c5402149a0101260741051800c40428440747d91440071860166240c8890745405c8003103928030015900020f48204101242c4260001000038074010003c083c1002c084604190b4014010b41c0e0745036000c5880380034482e03034699407a0300441003182031084800c4410140300c20703141119030540660818004041841c80b64000910591780d000c0400c5180d216054100c2d4102e010712441c0d404c0101898004c100c00041d84070b054000e280381c1c1c000103403482c600340c1413244010340c99202030500c21052048110201c1d54051240a079442120141e0785d5400c0c141501d1180d0600b600083e420625140410403400140c05000750020000d0321920406030f540d904000c03040c801111003c031310220103002049031405402c200489003130000d01c09428600440d00000b00300007180d4007980041c0c495454010a00c40c000885146202d26200551900e10900400e41e683e203140c0c01e01501403940040c15220020081c082c1f010700f40c1e030003c1500e56950f5a501c0300366451a06842d406000b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 453327410 1250 453326160 453326171
    0x60d050406061512090201030212070512070302090607171303060b091006120506032404150213061d041409060c13090e0705030708030c061b1606111c 66
    0x190001040640007070362031303944101c644960f0f81100060468564102d040c940c007400300d140102006c1891611402030740d503e1a07103e4605e40c0c584401d10348003030500d4050501c10000240c060b201c2a040b0744406800002d050503450443c1da1101c240e106000d1440d0403034140307260100030407019400042c002d4804541842454540c0e00c50041e00d0039142c0704a00104040200d0711004805030380146500c501300505a842007100308205030454056001d4110a55010908010800200b4a00c984180b03c110a0850801e264031444007138004441c056502408103132000904513445001036803008100241060040d10410305c0fa130b0389030701d03c107035030b164028050707603002460b940000300903103100707140f405401c2504900e409007020080c40c024070340b51258080c1c10b00c08102a101002241c0042180782c0003547d480301002e4049080101c081d0000f1b82c44440e00c0c000049003905801515102c0341102c0380084885114603021008040307404100c2c40f0040b000c140f10710510403c2c41621590014200306110 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 453328660 1250 453327410 453327419
    0x6080d09051818010b06070311010e070803030c0705190c210c03080c0c091014010e0d03082208030f0c091003020c100e01093804060b060d05040606 65
    0x80d01d102000070b00d24800c12a000090308140500c03960031001c5210000064501030a10100340303039910021081d400305110180aa0928109108000f0380c0c125100c0501101410414030507164840640486214a008640035007801001d0002a14029888080c1141500d20b40390401020f24903101c0e00420f640d50004808400c0c541f0300c0c000002d1a4000e10118400e130442d079516403550800c007407c81d03191003600808446512010398041c01180e44040c0341c1c0c5450301d8480d06d12207064085000c43d04209500c440c4d000d442d1504005199800c0c1c2c9420254099583c3d408080b03a41c215072080c00071108244054002440003210007903029209040c0398068595540312503034054031500e0161b541000700c00444520f041c2c82a40542000c01648003610dd900d21508040001d481c03c00088980d80e940d511461020005000d2a4468400308408040c0e401c281003c0c0868080c80035a50004d414408140020204802a0f02028070100020010750326915a042000c00510301102e003160f04034030341400440c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 453329910 1250 453328660 453328669
    0x7091814070e06010c0606230405070e010e04050901090506070903150c05070303092303040503060f06131e0603080901110115181503031e0503100b070f0606080d0905 73
    0x4041d1a0718810482d100d8850800454815101140641c2c0c210f0b910400450318465040740d1016801f0b13002000160b0341c00200c1080304540025102a05010501051001907608007102300c420710300864000406607142444079015141c40b40b8000c5c03480c000c0c0340c20403141c03a8001c640e001c01e0381d0042c0c0444072280b4040010f4404c030354441e4417030b80c04101b00388441000284680c020048880c4034048565000c4180880038035104100d115068554201240038001410304000182e48000c112107440c500e07041c5480862041c3e8a880b10b8040155201c0700041e0450b4604c10044101080003d002c00440c0c0d0b0301c5c20056190b41106080f240000c03408100c1c0c134030108050142c40190301c150101c40c6c952030310340304140c0030303440e801106508240c0c1c40300c1a185141580c01c10708002580a6204e074400101b40e607007070594005d06c100c00030741800020300a104420616800300c006984085400d960385e01254201001d0b4100355660080485080c5600481c200402044400d05002c030b82d150840c0706601c410800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 453331160 1250 453329910 453329923
    0x501140d0c110d0201150b0307090b0c0c030606060322080c0d03020a0201140402400501062a02010e060903060103050718020708090d03092d0b07120806010207091814 73
    0xc1c00748041c0b081c011f211a00651000759040f00481c24011002a81c0d1548603400da00b20346090305203034106443c600c2c0141000d100047c3d1181003150400c2c035500d0025018010b83d8044d80e01054004500a0036000708002003046403c0c000c0b0728402c44a8420761220000c000c0d520105009005500380100c40d60b034202820450380c051070307004100544240c0350440011b584030501c20b12506e0740292403603035007850458a401110b2454106808100ea6040c8000a0580d0b100103491400d03850002844010180111441c2555070381d091a00010320316056001402501460040b01c3e1b05d80240c4000004101000600ca4211030000d64184880004800400202c3c0101c00c4d01500c1480100008042d80c81d080c5100d50b01c142c1300b03050040c03140343c132604200d5120424880512844d0710304007000c642c1003800365043c7c004100c01c080c0b0302d02c0e0000c156156600d81ca002a07004050107100c00c00720b500c80c0e000317106078005800c0c1680108002e40049100041021224405072814040348010200210000c02c03807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 453332410 1250 453331160 453331181
    0x80a020a08072d2d02150301090b030307030e041503080c1c0f1707050c12030a0b15090f010e2e09050307171002220905100501140d0c110d0201 63
    0x240a0294000b802d2500b003c0700a413039601180c0b82003040001655541c0401c00c0c881424240c0c252650b0400625004650b551021a48030f58000d020142c0080c0d4003490b42d41102c40c06072004100320900400c284c0310540c141d003008044242c04030380321500e02d800007800070028551408140450005103c15945c41c001c0103c0e40b000551100002c1e1807001c440c0c2d050315004005844c210b464030040700d401c0f600300806807032220300c40040003080c01961000360040100b220000c4849081101d055503039181d040c8182c00940c0d000e1005120302d400980c0c00f606800c002c180024001503035030500d59090341c200e500185086419201c1c01d6552011051042d000340065520107030092035024140140c004030800e1030b10300140d0038440c00d11701c4404400d10303002034041c140b0b200141002100c011344c1e00c200911940e1300804075081c82c00081160041c2c0120f02901149ca0a00b450450100c95101d030907214840c03803440200b070a04143d00200903e9200036407a500c10304080540e2042040c02e4412821307603e14048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 453333660 1250 453332410 453332423
    0x409061e050a1a0306030309040c050315010203040e01030318150306050102011d060106081305030d0504120c05060604020a020a050d170a060f09050a09170408010f06050d080a020a08072d 82
    0xc41d0110190300c00290303017003d00282200c0c103110304000020256240c0c0c840030340010b000407080c003d180e00e5180351940c1000f07090020b50f040c02d0405440060b00f82c01484094204102421000e4050702c2125100700076240e0390940070880f82d1002006400f42805101d1280158a0010f600c24106000940c1003001c0144602a000e40c0e460031008480d6494050040501c3c58080c0c0c902000043c001c000800d0025149140400d0314039013810180c54800202038010280309601c00101c001490105825500c650102c0700182c03903080360b800c201d2800e849504024014429040c0d032001c0260084500c6042c481c0754074100956544060211060300c519100d8009800a00320050200ca04141c0043d40d00001c071040000e0500d10944400c0402d120105903070704510f800140c02d003d103400a0140341607281d000348082c0b040701c2c60180451b82805c0c802d032021303044800118642500600c240b240d1074009400c000000d440d221039040003526103480590072a038240c40c4c0c0820001c44c1c0d03c0c1114150b6200d40004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 453334910 1250 453333660 453333689
    0xc01091203051e040f1d070207030633050a080f10020d29010e040e0705060d0e0304060e1e01020604030804020f04020c01050f0112081605030409061e050a 68
    0x29802c0d0740c507030044039072940c1e803481c0c85240c89003101d5500c0290005003036040881841c285403400015444400c044103860265051042240321a0001140801c40b070340500006980324020015041c00b10300c0d111040e01c10110540070103616511b4954940c00e58070110381f0380407025624059103039920191904007015403c00c0001326a2038149034040d000c0e00c103010340c000c1980a00e4420a03010b044c0e9101408031000102c0103400300c01d580c00121b41149034402e4508000071580084883c1e581c0d00c5610a142c4140000a5806030042103a007000c1c0c2c907807415078116500c40da00c0d194081c0c4542e51620303596002c1c40303101544c6c0c000070310000b4a410850406070060600e68840341c40072501090014002c1e6000b05400c0400c1d0055150380c0f00030800e4004a00002815080c0440c0310362418406034091031b14000e40035580740c0441d80c503504451040040b01e20081c04182e4520744242980203da004001c0c0c240b402e80c3c006540410201809600c240904064140035102c00801240e2203840c001d1a00880661 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 453336160 1250 453334910 453334913
    0x504031a10150e0307060206270c04020a020609011a0a12021903030c1209030b061003060305061f1703120a060918021315060c02060d06170706030507020604020f01032307020c010912 80
    0xa45982c40e127401d00000e8a0b240600c1c81c020038160b034040107180c00180d100c1800c00c0b0f0303000800c1c8030720654102c423100e1408500709440005490350900380108000550806203245c215610110811345201e1074102c0d448400f40d8a090140884d1040c01c0191509100c2002c503140c1d203403146000c501a242e02c44444540e940310039090103803418401e104201810b550392000f0001c10020002e00744074400c501e0011400b000c14520405c501907040d1b0280361802548070500009130004410344522840c460052031440e91a450300c140941825402031100a182c4881c0300614241201c0154116000782c545a0341502847e800e01c00b06c5540d40b5240144280c010004d02240f07114400c175030925400203208a0505200c0501a01251320650120441c282d03170883d0200280c4090107401d00416176810f0070850751400700030207520340c0c5000788028402c441480e1100705980c0641d200008406030100d501c981c000d000408c1400c060010f0f40c3c4c80c0054480d68003040c2c5298440c840500c103070385456214030310703c00c0207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 453337410 1250 453336160 453336211
    0x150512040212070f060f0302040803090f13050103030807030b0303090306040312020f040906030c21020411040314010b090a0603020d08070302011103091006060504031a10150e0307060206 82
    0x40c0040341e1004041e240d120540342c08120181c09082240d640d100c2e564030307000b0b001e404008aa001601414010320081007022008002c1d116810800d440741943c010b60440091080a0780e1003469405507d000008400d0640c483c1c81c541c031a0a50361402c0062082d898105540d0b0b000300141c20703903d5401103001a00003845002d051a02c1c1c0c0c800712015041c4403140782680007a82042e006243e020f40da401040041c0040903060070010205800015410300b0800001100209000e1000e80075549030340112079000300c4c0390101e030019500a002a1844070480e0241c0340078050040586208041d07100204002e003c0382d208840031258010204810fc1f49241d4400600b81c100c0300042d03013555030b10004494070380b851a00843c4100c503803102420000016171000e204035000ba070007541c20844180030600014503c40303002d400082c01d510740c02220366500100302034a04071175000400b003140c100c0c0f00d034914a5001007000a014008030213036540350342ca51100b2a41d60b00203c0341c8044001144560080c01da01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 453338660 1250 453337410 453337447
    0x51c02010203090d063c200c0307030809030f0a120204050907080f0702062e03020307091d0102190c0302070e07050309150105010e121908040608011505 67
    0x1060042d2410100329000261395000031020507201d1580343c007006e00300480032490044801d02c0900c0440c102e9a1030200407010301d600079030300f034595568a40c180d21400240b221802c0d1205500204103071355800021440b9102d40241b003048012558100104900c01400310645005075151100079003020f0003035000f1111130f82812600c1485607400c000c0410142c5a82d15035500c01c0d100340c2c451070b005040030000b2084581c0d0007050f0342c085401c1402030141601c254140c2034900030b0340205590340100e24600b00c1c194980f01c1e5100075070600c603c5500251404041d0040c03800d110400c0c42c0e190204d2640c2501e05c1c01d034800e202890305c2c0c8580901100300d41600a5603140d01240c028411a400b131500c0301060000c000d000c1e20080081070011081003050b000c02c001240c005496038221445551400b000038007111752400745540700c0c081824a14000321420081d03c00440610682952072000d107040180a80c2d019014000c001600c440010880c1d03544c01c0c01c05000c1550650300c2c107207010130f18141e1810521 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 453339910 1250 453338660 453338663
    0x3030c0f0c01050106031b0503040b07050a030e0607020105091b030309092a0d0b01030c090902031b071415040305090d020111010f05060a080c1f030917071704051c 72
    0x40d0300340071240281000348070303c50103010b043d04c2c00074406003c42c148060f01c0b202e14a040c4104001001000000b500702e81c0250b800000c2418080d40321410804203801500d51a000e42d03216104560400842035815041680103078007010a55100000d20703810290142c8001c4811070300365101700702040c0c02d41060094142d008100e1174681c010713080240814020402071074001c11400300d000c80e8451262714184902d07d07071451302f401c3c20407c003207503490094040051403203801809603001c0006945134809040b4401940001d031074240e95014107290000c00300e203803002c0100b800e200d804402d41081d0550300784103000e141c15031201800c0c040044200480d143c0b00c00c000f2030401c00d04030919480c1040c00d006544402d8850700012415140104c01d00039540c45592040c40c0a504c1900c84040399120340421401521801e6124000c071088000294003034429503000030500b040c003411030b01c1e5440c0780501600500d4821042e0b840700716506003092403107000340c0c000c00c0da11000d02540e29214121440100b107a55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 453341160 1250 453339910 453339937
    0x601051c02030708060420090714160302060a05010e011206020a02070302180f0603191401090f03051b011a0108070c08130f120f0b13060203190c090803030c 69
    0x20581e8046800c04400f50700c100d0880e881442404200300107034895035248203405908000704c0404200148920901805120500c101c01a014206072182d50448020101c0d03006030140748030340d61a00070360340e01c2c04070b408601040c60440080350a034819441a4100c9549240f805040000c545581d0b00a51052401405510910a00000507280c0074800d512021614580603050318100701c1c2c035000c10390010061842600081c0580f070200c49440702109038640c205645010024030b0820f6240107000ca0070028160590001c40a010103a000c002003908400c0360a404440070211482c03030382620010a41920300c2c0d01c8801d00065654030406600354400080c0c504000c402c5007079100c50b8500c3d800b075500582c0d503154140c005d21100015600c1c1000424000035030051800054842c4003030344126a0000301000c0152020174645080745000306100f41e0009821540d038144803e0b03002c098107404a6002c811401c0240c00b04610340600c801c1000c48071040d02a515503034501450080b140d110003132110302c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 453342410 1250 453341160 453341209
    0x50a02031213030219030503070e04020418021902060c030f0a0b04050a02130617010b030907030b19060b0a09090203060102010e030d0204030201020606060408030a081e090114070908060105 83
    0x41d0504903000500410610000c0d0b481e040d00b50400a0900d046401d88032000c04691290a001aa000c070403294000880c1c0382c140c1c0e0290f13010001601a01c500c4d84001110002040250800b0744103034000c040902c050700860f2403102c0004400c0c0c0e210201298280c490b040d09000280546544800341c56102a0644000810040e80c5000070102c03034094600c2d07a40c00c0e40c00b140445000d400050504094801c1e41080703c0d4021040981072800c13001405660b001450100c0480d8246900b0842d04024641c03000750000c0c04c0c5091140d412035500020920240203081c1040052030070105012110030b94500e070b840c100302a0505041c18007039800503124504640d82c8160780002e401082c00645003581014201603511840c50000900c6c0c12000740c00b0030f200e000b00b00810000203c0000444009940b039041010040c3c0e070b50000d4441c503000c6142c2c255946000da5040009517072045d40311a04408400210800985990f4400c0b0b0300f1102602a410403036105c0300041c4201d00e0031500b02c1607050504000b01c02d6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 453343660 1250 453342410 453342427
    0x1050d031e08090d051c090303060e0a1401090b0325080304060c06050a020412320c0a060e03070620030a050a0801080109030f0c03180b0702041503050d050a0203 71
    0x307609214488000018060b03509010b040001030112512100c0f07249021400e28956100554810b1000c1040c2010950313200c602d20b04040c01703034110200414040036030b09000c0c41d148140c60701614410803041880b04840c00045801003251103800f0a807440540186170300301d2801d0402c049002403100d150914000c4510008016004000078000b4181c01d9880c10300004c0240382100a41c1c00c090400d840c081c1c0180424000b09211041c01c038445500081c0800a407001d10007502503410b60741c03090203c1800c107100b0030300001e44005405000564241d0782102a5039403100d00f1107450700c48444003940342d08005c10402043c4d109521109110740c01180320346d0343c0e05d00c11685034910b50010a104000c030f400414030603812908503100707600400d2001e0003800201c1203940d0007080240d00c4c201810621610008400905104180003942e034011440003680032602c0e80711070300a0b60001881203100320f0500c920800c030103076450f902070102c9600c003000342807001e5007440c10341d450b070010403000b401c41c48180803004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 453344910 1250 453343660 453343697
    0x301140d0515012606060f06030c0d0204060302070b090109150b04061205010b100c050a080c0c030147121203070305061201020a0818030c1002040e01150801050d03 72
    0x60003411a03400b2a035444c1d1003d0001041ca0025041a03e0603070008020400962a111321141d071035441103d84966a0740ea420000c07003640a01240710350a0303480071801082d1a50181e0040411a001c0c001c48050356589125040c282ca95100d402400d1541040010340c581480d90406140444018000b0898a80361070314220b51520000e001e0303e05a46861400c191420480b0f00a030301c205075850300102c4c815090301c4d415510f00c0b90300c00040168000044500c0f04860902c010b20b04640018004d0010740c000400d098184e00c1c1150041d480608000007081c07004180201ca806c0c0300324840340b00050806000c04000d0410708482d040907a034082c0644d4022000c000c00d000350b1091049840000d0300781015018850b40ba8105454a50340b40e1041024a0b84d490700300082d80d0f84004440342c2d4100d5414611344103821409a40164086840303000c1481c0620301e11354000c0c0095400c2030150b5041a80e940c00412462640c004140d00818000001804241001201d0030310043c000d0a16200c0700608040d0b80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 453346160 1250 453344910 453344953
    0x150c0a030e040221060406080a0b0408161b03050f01020a2106030f0f03021209060d090203030c010207050c2403040611042115020c1e150c031005060301140d05 70
    0x514040036001048030500c6c15220300070161014a008014094450b81c61200071940034101030320030b4030041505400702c0142c0042c0380c03180b0b43c00254410b103000050400b22041da030900003190039000c0d600560419150500c203039111207046517a50714884042e40350001540c0e40c1e1043da0343c1d400391240301c0400070071010303288844103a1080260110582a9081c020304040c41d80710b8052100d0f0040040394255030390001a989242d41848000405100f0707440020b01d14810011128580d5001040300c40501c071010985c14564007050302c3e281d50410802c4c03902c1c00c20b210076000646c0384940500101e8040351141d40710b00c000b0b8a211501c68030303258075441d00081c0781903200740540b0182c03003c7c1d1007141080001480c005805040003400d500b801c42801805459200ba070740c0d84102c2c00e2819100d8601c045040115016103440500300300701034248011003210580c0100e51400d140048540c0004e01414814110b80c121981c8400803c00d1001c40020850b00d0640024182d444c3d1041c404d1f03181400880e050321 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 453347410 1250 453346160 453346207
    0x30a110304030f0e0103090209012105011104031b050102150c0702040207080901030f2903150a0c090e040c090c3b0a08100e03040e040b0402150c0a030e0402 69
    0x4241c88500c0c0e42d0801407a00b00c3e0303031341a181058141000840161070b00055141501e0402c15041580341d4041a08003401825240281680d03003442c218404400c03c003402081541c1c068444038030151400320100740c6c40380041c498240164070500b41d28000229042455801069010180341f400d429900080c060340c00a47c4183c88464000408442a40e00352040c460203000c4114140940c1c0c4240307054159005101040c801e202d840c0c0c491402c60785e0747c1440881902100c3c0540f41c405424a040381c2e10052005101c0c11001c1a01010041104c44941050b0340c499644400070b45516410000d0340806801701c4014501804a0000c42c08807206190565076405561040700781d452a070342c0b5042104503d5198a1140146840300051244842c00b0640e54140824040c001c990401441003462443c8030f25413080300c0c4c05030071006000c100089032049a0203a03000301c80502e2540c0c0001d40c0362055205441304a0713801d42c011a034006c0028041e010108408a00800050802c4494884910602c2c1041e04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 453348660 1250 453347410 453347417
    0x2110030b0c030a14040f020f0a18050708060603240607230c040207020d061505060c1b1f0c032102041a130b070510020d02030403031a030c0105030a11030403 69
    0x200031550a084c0300d42d526001e9040c81c91801c42c1066107980410041c4c461019010300248440c070300880c0c403900340c05001460110300040f0440c420f05009002000c003501e421000904410124a041c41c10009807030250070214070408100c00c0d5070015003001c0e05021a101d4020009102c6400460311101030740d49401050060510f060728104091350a0841c1100128421441400914091f813102b44401c03e0013584604006a89510162400e4080031140c0c0002d9000300005880e03501c40c000030402410703003001590300000c07240b8802e00f04a8002141200701070a1003040c0844281580b00d00182c0c02070342d000e0304000c0b5105641340f44110f02946100c600040160b0001001c00c4003000b01c0384000043c0701d08a03415401c010b0383c41040c80c2219001e1040301810040880c0b03480602c00e051041d0820070040d8002199194414640c580c06504119020790100385001054003040d00b0903081d0080b00040200600000003011005503641d4101401c00581c0b0780d071b5074408000150a2000460055000b501d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 453349910 1250 453348660 453348667
    0x6020304110f0321031503071d1014060706090c1d011e050108100b180f031b01031112040f1202010b1c03030b0a0f050a0b2110030b0c 59
    0x1031106424900a549001e035000154491440050045400d610319010004a85da07407a00014a12103840e80c188441d80340c01681c9000644000b0366a2020038455000f64002042d80ea50410900c054054800e8080c510304400f02d0030900c1c549900141609803040000241b070150f55104c030080e000c1c1c603402122201c441031510440014000700254010a6006d04e070312050100c2000e4500e140605202e814140609440032a45201c151500f41002c3c025402c0125115810035003030586100d501d804850061410241c2c01c0981d042c081101c0815000100100081072050f6004500402c40400341410100081c41804600c90b10490114080c0d4000c9122051901e43c0b41001130003582010141000d5a1402c0c0078160b0703039142c985031080c1c51114403a41c00e90f8170f011410145c002c1d00e06a035419900441c6d0003070200c1e94020030518503055800c01d0b903060740d8007916802261202e120303101d244400d01080000c2a1000703160b4141c01584862110380044100342d880d03550386c0300d0110603902c2049264012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 453351160 1250 453349910 453349943
    0xa12020706090f0c05010905190e130f080406080703150308090103060302030102030a1b080106080c07021203032a0c0304050d050111030705120604050f131103030c030c0d03020708160c0306020304 86
    0x1c961f00f0280800710b6004102d034000d6105a040c410b030500c20500e23030a4810f00000c082c4101010300c8035006402c01c43d0b50003108050b1420256a610070302995022941a00202c3d071040d220b0300c10910200c0010560b18105030a42d100c503200c1d900001c01c090304040d2284400300060303c0030b00207580034201103c0301044004003040c40542c145071040c1c8203030802550200400401d90710005803a0007814030f004e07030b40c0c0c1e82e111400821030500486070000b01c0351000106000940b1082ca844042180040108140302000c403c11440306101e034046a0800b680107100074056498002c4002290a12980000030b520440b503c0300280c07a0022285003001c240702007442d940b0303034016410941e440201240c0070803252402602c00e40042d00c0251078400e0801248401c4400c020741c0e1483c0302003518004048985400034803a66035600d611020b45d030321a074020f618482a800c6c2c0a802036410259020340322074240a04c520500c1030410b03030b42c2400e485098100c4000408606180300441c092405401280080c9041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 453352410 1250 453351160 453351167
    0xb1206030705121b18070c020306010537051c06050f040f0308060f120a050111092407020a0906080f1c0e030c1005120c0a12020706090f0c0501 63
    0x290788000d00608102d446030f203207000041490410891081c0c400714030b58070100080343c02881220320501c0034000e1502071080f20740d00826540900c0340700f107046030300e2682c0b17500a10268480c0444044c51580da44180300100d440d5200310b00ca041c1c2c0b13083c030b0003540c400d68510005d881a50b02c011a454140604036000c01030214600a0750362041e41054144221304083e642c606170340180c810060100506034001c601540e580c4441c00002e00c81c000c16880a0254840c44a40c0700c0c60300b03402c1142c95612301840c3c01159450321095a1002030700525266044a600e404014240c81000222030102c4040019900503510000c01e4406025616400203c0a00b000f2115142101d40b9010703016540c44901c000210704041ca450087c0641189060340e040605040400d1030012400c10b1203521840c40346503091030580c08405484c0c2d01078595240142c1e030f00c6000d55000c01f0321802c5000b40003c1c100c3c1025407820040380c0c000b4105544100d40008401c48113031141142c0c8001c0103001c46112554400400c0203690 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 453353660 1250 453352410 453352423
    0x1104090819081f03082a060103030f024c0f0f0f090b06150d0203011e2106050c121602010c18051302040e070210150501050a030f02040b120603 63
    0x240c0400200303c07600b1034031410054019100764114008404a00411aa0856590161801c2040d003181c42079610381c130303025202d88103107204000144a003018030003160001f22070034241c5c0000c011101425a41d00f8078600c1511075900c02c4854221501c1e190080919954070912000c50300006000485041441141080d2100030090b5010207081603c5107006c50035011455410080460703d06260100c182044110b5000e9610180b50b21031001c000080e01c0c18803a06100001e4000c014401c200c03d03200d0038648001c900003c140130b000c2c0c1103202c04c40001401903200b00d400030036005026081034451b088070224200110381ca5580300d0140242a180e0301c3c0c0901904003004100d080001401c0f2440d40e14582280d001e12506201e0040d04c404e810000400e6412140500100d80081c4039a1402c0c1c440650742e2100f200d80600c11529240d844c220b500030078055401540d405a5505103400e00c0b03403c0850140280c9040c4030a8507508000000e048002140240760356130600d40c041d0f20743c0c58090200750034041c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 453354910 1250 453353660 453353701
    0x7150b09060901060e0d15090b0414150c0a050d09030e19080c0f1203040f150309080d0c0e0604090c0305011401020a0b0406060b1b0d020a110409081908 67
    0x2c00041c0410340e0170040000380010309507070800000207103007022844840c101c0c0900440618252644090041011100303200c1c80c0036024502c0c207041d4984813141c1c3c5440902d42080c1c16510040800c141d00e2051005003229001441d1040c00c100300c40c12458200c4010140460102c2c030782c142080d0306d5080c042d2031145060740c58560300d03020720f20703050801d5150902030081601c44d41c40c0840022181c0d4a40306c1814010b00100122030b110f640310744040e201041c2c40e009442402c014815012125882030040722902079101c86043d04100240d108240600f191032160010310104991141035038442401400003410b000d0700200310049a0b05028045480607000341d0408648040300c408540d8000540503141613024213040300766919410b182000f803550b0740003d0040c860010340d400005060314188185030002200b0f4408811075401d00781c0e070f1440c115500800080c450344840c0401d00c1c1a90148003070500807400700340761082c1a04100440c110782c50109002c28440700c20f0000d2418076007402c02082 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 453356160 1250 453354910 453354919
    0xb07030204090e1203190b040230060307170f0d030b120f07030b040f02100518010c020303070201141207020d0e09150906120604050102030a061d04060513060e060604050a06030c09050c07150b0906 86
    0x3814130402003a16041030f03001d44603682d14041c3b00000e0b4280300300500b500081c41d41c415a0010140000c00902500e00742c4140340c0318000700c80c4001841c0b24082551404000700a00411451749160f4981c50a00c1000300300345d901d0000c0c000000050380790360282204501c17065880035520412101c1a10349001680c01c110f040114041406d401030310008100c840c00c0b50242030482801020251751842031003041858480c00305100b003808001c035000140003138540030549500d0481c410325002e011840004407882190036a08240d04221418181c4041d600100040c20581ca00d910510446180c1001924200c0321694004200103032414544a400090001c0d10030601240d1125030340b0803590603004d8400380c0540c2ea0f4074045040964000b104c0101c040d07110a05002100100ca082610390328111a1980a1410940003c5500344203106080580e5070044101e4015424515000000c1800900186012508100c10004110700103020410442940d00216810841405000e2420702c00340c5002d014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 453357410 1250 453356160 453356257
    0x5040c0807061b020409120e15090f01030c110102040605031f0b071e0209010801140a0b2211120415090209040b130b07030204090e1203190b0402 64
    0x581d600c140300381d0b001c00300000c00c0110070303d681c00014020484980e005021310344050004d14096040048034481e2201111280007000070100216242e225200c001503003c49800c03005100740d8000d6118209854451401c0d07040c408610070000d0072a403058011401140012003000402000c00e09200c0c0702404000c03008482518141102d411401403071001000d455800b5a10385010030592102004940c0003480c140321542e50303088a5000381084040a2550003000e4001810903803d4014000781c1d01004d00100b4588800340d5085000601c0040c1c0c0b40c400ca0380b90102440920380f98405450103445c0704401d11410708103232a0802c0c03c1c0011400c81c0b1341041c00c088200c005a40c80c0c15080d82c0c09500042d14102c542c2e544040304000318405200200b0301c01544041c0100558145d001d002a0f508040082014084a07000e05541d40104503c6e8040d09904200040386804160806400210440030201d070824080c2c0c000350a9170848170030b816204890202d10b00b258200142070b513840c02d1481c0c0e404c01c3e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 453358660 1250 453357410 453357419
    0x6031e030f080c0903010501030b0603010b10080105154e06040228050406110613232a04021201050f0105120f060108011e06080417030a05040c0807 65
    0x358200d00c88441040c0080e041c0003816400c3c00004550903200024020021580c59181044e400e0070155000760082d868120b8441c4203041801c00d410740c03076003592902d041d40d81c80d10081008111242c1c0700e424490005000b0100000c5a4803000d100b0b1100700f242a003103943c3c509201c00d040e091001080d144c075812000399500c5520740780002607041030064070b0160b550131808062051100035000c6040c5140c2c0310380c083c0b07440103038440c000c1c00c1074803201d5541c0840900411074055070b417503003135488c00b10301e0001c0c902210000b000082da00c468000d8070844600c504c40c40c105a242080300582200e160705194034503207203048015907806911548101d80031400c000c032100001c0b402600500496000d4031520001046984c0610262981f03541c01009440302481c1c92001c8000100094031344502107000c10002081018010002009018050440512030b03403400c1422240c03100050402d0b180710f2050f50200030b814020350029440f44c29505004030b42e03403c061800041501c01a4414052508003500510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 453359910 1250 453358660 453358667
    0x50c0f04050409031e09030b0c0903120c010b190f0501051812101104090b0d02030d0c02190e060f10020a0b0a1b09091109210703060f06031e03 63
    0x80075030304150707000501c400c00d500d0140d44442507400701e0705614861000405601c2e90180000007582c2c070904d0300310403945801c0074151140c000c05404a50640241186210942c503682c05407003103900020020980484110116803d08240c000f041944d00364240d003030103402c01000300d6000410082c60580d1034840c0b5604900070070b4036100c581910079000e0070b085413034240c410490419000340c19042000349141c95458801d07594446c0c0300e80c00c1e4540c1003000004051a02c10980d441c541d40207006440c103034400650466a004003490126405088540412120b0020750b00800142c82d00d142c8400f070b02d00346902001824940b8494551040801407010008280d02180303403074038107034400c040803103540391001c440025000c0307030000300c031100384180000b4950355000b15040200c03007020208101c89031844906107664802d10b000c85400c1546a480c4030364040c40380710311900c4607610700d083d680e101d502da565401c151364070088009019030b124441482804044064400c142d83c0c00b501d07000106103960b4014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 453361160 1250 453359910 453359917
    0x120702011110020c0c0f03060402010e0d080c0a0c0501021e120a11010e07061209020d03050304020d02330c0c0f1f09090b062d0405041806050c0f 64
    0x28100140d00044103880c070350070003040e0031000c0614802e41d11248005021540d83c1c0e00e0041d424810100345101c003010b4140450301c40c1c0501d4040e510305a0368510102401f001007030035001141c1d4420204024401c90209008184010f88207456152441e4505000240303404010390b0012005000640c1410110200081440606591140301910303100b03801030a940c40035000310310594550905281e0f0718000341c0403400800751580d80d2250010b02652000000884041090003504102c0d0074160b080070134001e001442c1d00c103100504100c015061940883c080700b0700e0008503061542e80300715102c030780d1100d41e04511004800034201d60402088038038007940c891980032664040e18205100c140a5200d8428003d122040c109107014280018440107120054610451714a00c1c07074401c0615091402c10219410107092030b82c40e20b0100030340201403c08401c254805581140708001c0015181c030303603025007403c034410140c0d495203560440c2001000d550300200222050b050800c240c07540382030352a096 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 453362410 1250 453361160 453361163
    0x1706030319030f0b030f0a0b160e0d082106210a06050c13030b0901050c0f0d0b01030f060e04051006230103110301140f04060810020d060f06020f0f1207 67
    0x116001e0516040ea0001380075035440740790180200c41c074184a00f100091180420352203505c9071081c41d0703140c03200c0030664403c041d47c0100091485402402034540080429003680c010410189400d007843c1003440008443d100c1d402001d800c007010040f040c60710011000c003d03240b00b06c000e82364408202009440e980041d400504003542c0d00d0101c0c5900c1c0000c025590780d040b02003114443ea940320f00704030007540000c4508481544c20140061402218682a50a0002078505490800000c45c400c1000b4040c1c0703206203030400d5655056511101740320301440000740304214080c1a1400c0070b0511a04040240f417000d9982424504204142c919540c03000840940c107101101848420100485c0a03008a082d0000e10550200010501b8480d150080b116008201ca0f2411001141c030288400c0c0c4405111b05202a0019514800a283e041d0028100f002d143c94000a039591100043e01c1740c1d0103107801190040e4004070085110b0501007113440440b001c0c280c014002e0030340e56094070005201c2da940 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 453363660 1250 453362410 453362417
    0xc020c06040e10050d0c030c0b210612012d05010503120d150f06080a0c1407020f0d060212180c040b0415030b16050c0a03050702060c0d1706030319 65
    0x42c0701d00d22004042c0c004d0b040080078882c4058560814a0042c2601c1c002a9a10121900000b4200c050202210fa00c0e000c03104410f0850f4449d4043c003206100014582500300380c1400030303188299030138490300403800c480c10361441c41e1082c8040c0343c00301051604a540146850980180070f80e580005004c440b51002c0c0710b00c0e40d990500000d0b420040c1a00e00c8980c038a10012010100b064030110304d05609841d4260f590141540d03480c102d030402c0c0c4a1169211021840103082c40125100900c014418a1700290008402e541100c000c03070350500e20110150342035035000c41d540c00031041c5001d88a0700700000280ba0000d0046000c0466281c11030a030040d0700c603030340d182807070f154584858100a801121039109414050b58a081c20121001c00300e0303c0e429024034404040c0c480d00d0280e010340703416070704110050018021031b61b010340301a8400c030380a80e401801880071110703002007003011a61032102641e840d13200a4004030001003400e00648024800c3c4c00034040b42c084c0c82c1e081e0400f9108240c607441c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 453364910 1250 453363660 453363689
    0x1b0306050d120c1709010f0e0d111809010e01051602190c0b07030309050c04020c060f0a0204030b0709030c06030908070308060a1205060402120c01050f0705070e0a0c02010c020c0604 80
    0x15010340f03031600c1103a0300401c0c4403c604c0c00c12070101000805841041c000f81c0380d14a04075200801103075040803a00c0f80ba40d0006131170b004180400d0004148500c400006411130010103580c800601d51040203d414443c107a460742840c0b41e69900a004244d08201200465000c42400c2c00020307441d20940c040042600044128402c240101c66080000030b0410b5414241c0c0d81800382401400b030084c040782650944940d1a104002e410540300f182c08070640c030409010503883d40d0401d001d00381d1b006007294168907020301000c4041600e01d85103e0144803640c5a51020518628203504510065030042c001d040c40c1c2446000070541800848450760307890b10703011503103584520008002030055003041000401c8a103882c0c0c00c0260000f907540c0606e00803100d94500c1991002c2c801d0f41d46104001075400204180882c42280e81280007070b180319441075040d08c2c19039880b820a020410340885140780000d481b034441180071038080c440e45140e45e626101030308041030120040761481c1b189200385a081080c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 453366160 1250 453364910 453364943
    0xf03070303030c1211120c130308070809030f0d022a0f13112205060403030513091b0f03060509010b16080d0b190e071b0b07031b0306050d 61
    0x904c00e40a66400f41c090401050700908003986650304840b1040d81a00c1d00000820385980510094550b01340c41d0070a42c1c00c020707003141d807a040103411007202214009024000780c40c007980c0070701c410301e01c813141c81008003520074545400916140c010855060250004521420511624030400884070410741ea5260342164400105094020100b61840281d1400328904008003e0400806900560304121207184800c00c6117142c1c1402c083c814650302080c100f2081002a01660103082000303200442510351596038a10b01c425202804ea801410740d082821500300c0326000284100c0385140c51408100090401010804000040c000c94139510400304034900b248045440d80b0f03401540c0140b00ca5102c4041546060180801085e407912500300c402000312080e0001112034100c629a00d4201d07071680301e03003905540d4014201404c00a00070300300905008115411103050144050355000254801741c0700040800e0440c048100e0109402c18408000f140d444a840501640d0084250544407080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 453367410 1250 453366160 453366167
    0x3090d1d040e0d0e040b0a1a0c010213210209150303040b1b010c0503090d0507060b031903021b09010b0309070807030809010216260f030c0313050f03070303030c 71
    0x1000c22103510505102a03500d000c4004260842c00300c0322616040601d800e07200402003903580d681c070156001b00580108200320801c3d60420400041c0030700e02c4030b01d04518108480c0c2a03070300801d8064240315006a0410203010301188845a00108801c1210548415400910792841c050001181c10100d00134020365940d00340129001003040d8003020360b4811140500d240c0c90040b81c1142011546030810403241c3c540204101c83c42020340f60042d01c00c2d00c000d0f400c00d4410350006401503900c59610801005d55032404c000006041f010490001d20780859458024030306a9512400a5400944112000d0135168034103200e0649003a000c44503100c0d503480640500d00b24880d07200c0c02c05031007503030800001d0041600041442d07810a80c00c1d2850b160f04140c1c0c09c41040071034481d000048200401c600058411000c1c1d880711081e1640598040e00401507c052654014400c140056000001e240f408440b54000c0b000c000c1c05c0070f0f01c003000781c42007100010780c9403c00c0703210107010f05031900643d03e6924030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 453368660 1250 453367410 453367457
    0xf1312020a091b12021b0a0c0e0115030e0a0f0602030a0e0102270301090512030405010c08011a090406081614040b0105090603040302010b19030303182d0f0b16030203090d 75
    0x116040b008841040c05000513900e420741f40c0141d440d4101d060340410918a40510f445c1600c2c6010782800c036a40c40c07210114000e24030001a0b449038003c90000c84005002911000b0256004031809a2a403d1001c1c242c030488610541c00c00b0541c1c41040224803203480c3c04150306104048100c550110030056011074050040420000c060b03000d105481107070030840401460159002c0d8000b0440c080048105a80c201d00a010b4400e40c0195180803100080b038103c0240a10040504017040c00c550301c52000d4540501100e00c090f9402045500b802503040c0c40003d2001d0b18800c0720240501c0101c0703c000b90541c82403081c2c0300d02403030001000030107140c002d412100e002800545075080640d84080200344000c00d5010482c0001e0414014201c1d11b914801e0001c002c542200c040300302c00303944030720b50b806920031000c0c180ca003080f1120094010880000742400501e0040000c12058540703070300f610502c0c840c6000c8140500d44140203101c4c50080c00109006400c1d15403e20000701c41c070035400c2041068 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 453369910 1250 453368660 453368677
    0xa09030e0613050d05010204061404030b010b070f060626031606050405030f0d020702010807030e0723091003030e06130e06180702100c0207030302120f1312020a091b1202 75
    0x2450130001d42c4c02c04c80154010001c543c4942d4840c1009500081c0c40c03900ca204d80d22001c2c1c510f6941d90014041d05809400614105100303c42002d0b44920035601c0f0029200180d000c000a000c1d1145629a0495001080c2200038441e0000d9484e00c500002c140803080c45015010788815030300c00c00582004000c00444440c002d1002c1815200c17800c01308114043e40c088501240014041030100b40664003900440040410400151043ca8141081203072a00300c0e0644006002100180070156500c0c0d042982e4010010b10300700e42c01450a40c107000d1b0100707031845400d5000e404100003912501f4400d032100030981c1e41d0703819090075548510002034403000072484041d03138426108007840005500020a40003003100302070305020702c51050314280d07101d269138031019000d40c0004082a0010702144014140c2026800b046424080032841c080c41140c1d0b035401009252103180600800d6140603d90350b0010286107006202c1c600e50000c0182000130142d541e84140280c48403003101e42501f03a0103441000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 453371160 1250 453369910 453369919
    0x5030f0a0203210106120e030315040204052101060b040e160201021c050603060709080a03081b0712080604020f0d020c1e0109020114030c27030a060b090a09030e061305 74
    0x30b4400043e540010007840340601045084900c141041014020350714101c07202e501035070441d40c4d20207801c039400d10041001e45d03100b03a003044041090750342c80100c0302c121b08000b03100c041000b413041c80c61800c607881d541205810280a100411024998103119580240800e0407800c41e0310546d001640a0300401910516080300305d2442d642e0703140c0390b40c082071282c90120121170541d111480140c0b2040114042d00625030015081400828040c04181d5000002d00003880090086082c450b5095008042c0072982040700400311a41c05901c04c000d250805000c40d02180741040194560401d4401c1d40d240c01586500824220300d1182e00340803000c50110b05841519003090b1420b00700e03000700000d06040740442d905030060360205800c03a040d00c2c40741090020541c6802000c00080311010400780d02040451450101020303227031018048404124854400071841010400030421700d020300504145025141c60500004280c1c40118181c0003a03043d94140e41c7e8040e00344000800407403c0e000507400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 453372410 1250 453371160 453371197
    0x6090703230a12030203420d0501091b090608030d0c030b0a0906060f0903080403080715020c15150a0e10030c0b0c010c081509070c050604030914040905030f0a0203 72
    0xa0f1300f58009500ca200a882d04c2100417821b000381400340c4900c1c0c40d030307811950011642c81e0501c20b5807600a0b00b0020004084000e07040c01951031500b0755080702c0c0704480083e4035414074846c44c101c5a003500050a80c4640501149043c001c007180e5074041c5a000400c950380f1403111003e1640698070003030303408401800409120340c840d4103000150009201d9040015520b04032808135074440d6650b0410380b9400b240c540c4c54203141d1303141c081c9160400e842c1510b40884010030030810044520041c001c1d00b18400c041d0151851613000000c0c4888020640904055414850b44c40e42d501c644c48002500c0d4204003003460b41e1240e0411216001742500028500d000c201804201c81c03d200d800781c254011160024400c0c90380341c85003180e044000b604c2d406124103006225000c3c601c5c001c901c1e240d01c0300c01d61904110105164440519041041e00d00b074010581851081c08200500a003600c44990141d900307100b6502c45507500f550364442c1c0b4011a205071004582e00c3d9181d4402c3c8200d0790040e580c820050603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 453373660 1250 453372410 453372443
    0xb0306040b0f0a063b070903120c020d0f050c030709060807050d020d0b07020a0816030807210504051606020322030b1f091d06090703230a 61
    0x1e80007015034581000441c1c0d4000148401028090001902e010041d8852540185a10301e101003d030400200300c0400b0b0402c0300400241c40c1404140b0034152552035058951031030416403282040c002c008401c06c50b1030000b40c1c3c05600d55640550b00c41d540051500c00602e40703410058105801285240c1d454010100006100071181d00650103440900301510348260760351b01003142c8a40c42030b4000350481400c1c130400b40450081c80d01181d10542c00d0054980ca01069500c4124035071102900c003004000c0500e07148141688a82416405116800e00c2d0100d1108420b6034a000481c4a000f020115103074400501005000c2c8001010300035802d500385103587d290000613443c5d400104d00601c241e920f560602940c00320708070050f0104c0380c20460050fa10340340e11004559403656580303404104540b102c000580c4d00b4031031243e4403180c02c0b02c414581628201c0b411081c02e050014100a80c80c0d03106140a00114042024808450800e03040b000d10241d042c1810350704114991502a2150040c82c08651 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 453374910 1250 453373660 453373673
    0x90804170a08210f161416060f0c0801060801090b12010507030204061b0b0103110621100b03040c090209010c1e21120f0b0a1d090d210b030604 63
    0x201c51149610802245590303010340c00c1301c0b034101102e2100d4040c500e000d400c0c058502039068a501c5003003407000507180040020203140c03403152450f030848403140e172031084150b902540c0c4181c2640c6641441e00070040e51414800621781803041c00b82d070301000e80c0e8a424604565a011f0305000a0071150000d02062500040140003504184601000319101451ba0480320107008a46514940e00050a114076402c43e1140025621070501954014004006105030380d514903504414680c449483c6260620384040d1000ba90030702540500d008080610a003c0000c0c0503880c00820360301880d0340142c45007400001201d40508010015241903183c0003050b4403c02d000403401c12160060f0440243c41c200b103424819054090400c10001410501152140507d10f402002042c030400f00701150703140c120000290440b50f9a800100d00300c00161500192480f144d9109a001500340c000e04040714042c100035003100706600118441000522602c40141e80941c0300c15400e040c0941128110f203000c1c54100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 453376160 1250 453374910 453374947
    0x30f1103120c030a03050601030e1903021c05071403041e140906130e070b040605040f090e07060807090b0c100b040204050a0e250503150301090804170a08 68
    0x46000303008480c00c900304030040404030b41003558103034001c40c605450300c0702c210000c082c050002410151214081c030383c440c00400100c10511301b501400e040c002458034001c5d180c0150303050310001e00342c040524003d4994000701500c404540001300a00401080303100705046114a41140c22440c0e581d41201c81c0881d001c0801100703450490f43c0d2100c0d405d001c001000754078281100c545900422a07000354030f590b083c5030811102148040702301d0304440c1e11200d00607c141c0003078001c00005000858108408076480c6074070b01c01000e141da0700b08485041c084a05803a0b4525000d0346c9e0078050101d021940b0140b00e044030340014480594082c0e11450741e400c0807520f80c406001d55122140c10011120140e24241c802c0b20700301d5000610304d808c01c1d80f610001e0507480d180103007045941800001442c0f00d100c1920192840c04080350366440c2c3d240b903c40101c003600b1581d074140c280a03a240130b404500044d000e008440503030350206201032a02d2601400ca91900c0070301d0304001e060303010101c1c0d00f0641c0104004039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 453377410 1250 453376160 453376193
    0x10303021e0109080324100e0108010e0105060a200d05030103060c2109110603070806032a0105070203010f0606030204050a08011b2106060801030201030f0c08150307030f 75
    0x10155000700420103090354820140500160800c00106a584016542c4150980d88440c5c5220b20b2480d140b0026412034a1051008007013249040d4a03002580d00ca00c0d0203024050145c42c101c265414803001c682c0f54020300034a401801241300d0031a13100c80381e0012283c0070030992070481e8540c01c1000e5008205030020b2008135041402c001d001030007035000e5500441c0c0f40e41010085200c98032011701e07000191048040581c0c2c40c3c50351b2603650030541c4401c8015842a08246c03503d155900b45503061500c2e114a640c0d46010030181714555610b4140c1c205001062000246400c5031503914038000030b40100011031500c01c07071500d41000002c645070075401820456000b2a40c8900c0030360380b00c40f240e091722000011200c052001d00c0d1821000c6014100400d80d02d40e0314041513110854542d5414100e5030b00340c01c00008280404010011980d040c0912154508460002d00451503000f0000c0d02d0f080c0080c00c40c2114862240b0307501915203041204500450300041da8401c02c14a50528205800c002c601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 453378660 1250 453377410 453377443
    0x21120e030a022a0604080d020c030607080420091005040507050708042303060a0e10060501170a0e031605010606030207120c0c1211010305070801060f050706020405030601030302 78
    0x212910448008015112a80020b401612800c1d141e007160748800d0b5954082540358500c2c124000d0786030b0b242d5402402c00703404800003d16a40202000107880c00e4644400715110b58450410400001e80c81840e0304d81066001c650074944840480d030402c070705861581441c1c3c0045e0b400040011424502c8039500440e0b8094074100003a8444940031580c5129560020700021030805c400c01541005d2007011895403410070f40c86503001d10720400203041100c00d40b02e1b019566280c4030a00c12050301442401c1034951018020010075142400180081642e9100200b4a0709a18001a45040c480d04114100b4480c1010350356611411420602c0c40e40110b2020303202503103824404034403240240300f101d107519000300c100d03050b03000c103850215240341d5022404c507540d91480304e0009500c0d102800b40040148181d4680c03200d108110001800c0724070090450080111540040014a030840140708082042e46086a582c05a0b402c0c020003030b00c10f079031101c0e0f0184a401c0002050640c080781007541805640c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 453379910 1250 453378660 453378671
    0x3051e211e060d0809040204030212030d0b0d020d080d15230306010e2206020a050403110a03170d0e161707061409031618060e0906132112 61
    0x60309503440e0044421680040c0744150300c40200d07841102801740184010009494240c0341e902144111594030911032850303001040343c039000c040368040e0010040702030319452040002c80d000075030300110005018124210000f01c4900c3e07015113800c070810802a0f034103a10041035490380c1d200702025034000049060000d18060300302d249400319981d0704032110b0700c0802007a40c4030745068181e0000c00030030a0710f22000100e04100058003500140c400808540c4589440c4c0c1c1c03450a111805a000700660340c801c4000302e400340000b900d007070300d080c04110440c1001501d8051141003240140094842c840b0680b04618a8000398030140e0785900907204000d4840c00d1100e078410b6190b50300e940707500030500442c101ca240901d41d403030040c018004e00308000702201c0b083d244400704002d240016800400702e01c09203c007103044000690103400d004201032070780c3e040740d46000c4020903112180a4000c1000c46c10f61024281071004551100700103540c0c1e080340014260300b0041c0075010341448a801d0b0807990400703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 453381160 1250 453379910 453379951
    0x9060206060d17130305010c0306090912030f11030a050405010e0a05070b1c0c020705030f0c030a020f060f041409010e01030f0308070207090911040b04050403051e21 73
    0x2003a103034080c400c0904480c8044103603a546042c2ca010040310100c8030a8144044a04d851030464544015401400000345150503608000c050740d002ea04003c60103407d00c103168000540c00d800700d19011905140001c0c0552070001d42c60040c1c400001144000744010060206c02c140c10b92040d030040d88900d0080084008070000d8903101ea41501001d440340d007040342c0c10010304c150034004000400b0b4021001307001c815440d00c10011582188a80b10050744008000c1c000f0303040c208201210404044000c1c944c3c41d00c0080000d640e41225400280070b0250350300ba104041c0c23104401d6945c5090001140c5481d582c070707000a8400380e02c00394451441005d032880000f0300904101d40150503250400d001ea42034103640d8405a4650402901d030324210310403203400041804c158400c04205074421210301007d12001d604010942c0c0035198000c0c8102c0c500014040000c1d08001207881d894180700b80210f20140440703824856005044800801c1018210321208103100d56121a100310103c41d038100106241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 453382410 1250 453381160 453381163
    0x5030a11030c12071a0909091e1c050723060f0c041203031802091306051602060112060f06092301051e0d021f0807020102070203151e16090602 63
    0x412070f0346450700110300038014031136011481c100103042c4030002403405c44480042454001c046030390b82041c3d003021402051900d0900c1250a062101e10002c2100080a070580d0b01c0002c0359019800501c42c0002c0c807a4200300c0303213040c119070010704005900c1c1d0600e14842c03280c0d00c4640c12244100c00c001e0642c00241d40c4508002a242079510b0114a00c41e80075880e030301a00140317a402c640e5640101446a218016900c10f81c50b58444c0710340c0d8030030b01c00100f81460040180c41001c2c000700e4044e003441c9100d92400e6800101d050456144040291000c080f6003414002404900341003a07003241091000704005440d50813262022260f0020290032840584800c0b65482d801c0c0203a031362084510a00b1113510341900300c14040010014880c01f13080c0c000c0d90000f40790043c1d5920040903460f181001001c047d03001413140340c3c80000d50009500e043e0b0207600280c1c5920b003217502200f910825801083d0000d119120445000907a820304c1e03c3c1504140c0300310039010b4227411104000484511001c25128070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 453383660 1250 453382410 453382429
    0xe2103090d021903031a030703061e0216081e032802120414030c030c1605030718021b10060f0605070c0e13080708030109110f0a110705030a11030c 65
    0x1c1e45501183c0324140d030301200640680c40541340c101c0150507401d48103503420b0090000952103070b00005031441108200c1d250240c0d05c07040400000744188600001160003159031440e899003c004d07241c2e1000c0d14116905840c80c540051080d10a002c0100051010300c00e04010a84940e41014207400c540801d64905a01ca800300316443c40c45c07010013190005172041008603460034a5000d0345d0502c05040d11541c5541c120003d801c40d55445a030804445110070050345003d8141035010b8010b460400059a485804c0e0132000314580303a0010308141181c40120051001d844001305403402809502c1800c00a485e0501420b585601441d0001032442d00420441e41c840360301c043c0d81511246000004006070000408200315031540c1b0f007000b0001000c001c002e04481e482204441d860b035061040d01070884814429580011600704682290380942d80c1c24bc0301d4464032882c0408440b20031600031404c048840c1e001c103400d4800d1404d10f9080094003805003c007004150210340600305035500b0005e13200c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 453384910 1250 453383660 453383683
    0xd170307020c13110d15150e13050f0c070f1208060405180d03020c010b0414040507091a060304020a0b0408010e150105010c080c0309090103060606030b03010507050d0e2103090d02 79
    0x500401410342e05c00c0407504407104000081403111411340d9036001607960314400d0300340c1c1c1000402415100d05689400c128000e00f4400c5c0000801584c64031a50007001c807107014003102c0c6012004103191041110003290b00142581c001190401740c0700303407000540140307400c0d1000c0e4402d5003898000b500100d04c3e8810403000a04220041c131500a028005500a61007401d80241954981d55150400d48641c00b03a01c1c09001c0c4191a02c0040c549410190f00f080c4486c0c22503120b8500301075803668900c000d48001c1039003003000c64000d40c1d03984a6100042e0001c2c01e80e0301c41480c805001c10300083c6510b040d40840341c04c194501c1510b032100e410b00c1d0fa03903088175002d010701408120004095404074003c05c020303200c40e408980880740303003800802c002803000c42c00341d0044580e10b48580b0b050203075503810301520802e00401d82c002d20082c10030711070140550040c0c0d008201400e0b500d40e90251400e400304854031492200d410b00600300c0202e041c0110703540c0d00840c5e001c07005105800301c503214030748002519000d41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 453386160 1250 453384910 453384941
    0x10c030e06270f030a14040308040506031306050406020a020f07051305070512010b0a030b03190b0903070609050303060109081204060e150d151a030103020d170307020c13 75
    0x1030b601c00e038031009503041075100805031204810090261403001c21001c016a400500190741350300000000030a01008040800a58017081c8030400004902c1e030141c9080d0b034001c0355019102d5960f03100c550781030100d91001408990402c000e00c024441c069005042c650055800ea40d900c001022089035240c1d200c3c46401d8003c0b0302120100c0c09041c00350301943c0c00c1107040c80e14502c1d08115410b001b0090001ba004008a08000540e80740d0940d0035104480c1007080c15405404000ea12210448103544903840240034502c0d0600011a0b44800b40f04a48506510003400c0203420340d20309203507990b038004403034041c08a400b1050102e0074100010700d0034101100140564a8581845400c960301688404a217400005403002880090302c010b01030034140740301081c001203d100710546106001c41540c01034994040602d200d505040d49081141c6c152901a02c1140380600640b401658204010580303002c0708a020043c080050fa0100d50402c0e000d904071a1020701c4000c140680086501064400104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 453387410 1250 453386160 453386173
    0x501030f020901091202010201061e05010f1103160305190801090b0d0209040602091c0503120601110c01030509070b03040f12180915030209100e0c1305060d060b0417010c030e 77
    0x317649400040340000c82c810303c0003041d400d0380c50302600048030030009842800f0b220080240015640103a4104440c0344c540383c0f1501c0c504000d0205074036072145400704500b4526580e039040034580a04121003030b0559404000b001c0740409400203109080a000340034480c0e007400100300e65803038203890301c0040c2074000f400400c25442e0756540070005d502040301207810100c1c00004030350048854420030000750050020710340d98030010481000d0141d00900440c10702c03902c1422003210786400203550f040c9001c20b090028080d01c6164001d440c01d0705e00d43c441c0b81c00300000810401000324200a00468512a00c0582c000303121001d001c0c0e070340004841d000d4520390b880020400ca140c515410641e0a417155412003a49151a6000b15903440700444d4100d6000808440802c54100d01441043d0b00040d00082075040942c069210400700302d20340306041c400c0001007029400000030350700c103a0060455409107a81c0300e6031032540015100d0445001c035801d5107491040c500d40b50180c01842e2a000218001d80132 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 453388660 1250 453387410 453387419
    0x20303030f0910020a0509030f0601080d03090317090f0d05121303110a0b15010e0312030603160303120507050310090e1e06040b180601050f1302130501030f02090109 73
    0x2421000501580b070070b2080c5450300704141402d200508440055507641d9030b483e50036000303152804108210039003c0c0e910804c0104090381c3c01141045031383c881464080b81e10249400e044401881041c80194051400c100344070010301d001480c01c041000c018180d404030030044d001618580288010a0300500c0032100181a50003001709543d4400e200e4203200000c1000c400c5100d1034841030f240222488806103007401081c8100200034a80200c091908038602c0042070702003078035002000125051780c20048041140c9641c240036409010300314091819115542c0d040003441e0000d0713034003e43e0031240fa200110380560700c030f501264131465003559004001407030140d201004181c013602050640c0101c01c012185030340c1e598840740c54071a011000b80b0301420103061410f0020009406500b008801294007102250082101c60458100315810b109061394400400d001c0d00209000311082c6100040e0250100a1b00e801401a50343c20f81c0e0810031414090310f030008a204440119000c0b480c1190200f2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 453389910 1250 453388660 453388681
    0x151103090f060c0a0606050405010801091a07030605030a06150b16150609150503070506091c0804050907050d0c090803070b0c0d02031311100f050c0109080d020403050c09010302030303 81
    0x1c640300010b0011480c02401c85085400d25601c1c140c200c1d0b00503181e910400980c0b03002d0140d2400b41101e000200700c1030003150f40380454144c1903942c44407012a20760009a0b040c7c02584290000c02c00034096072011020307231911000a0005254204402030400000b1545840748000e98501c1300e09042904444e00458403205c04aa03003030358004015640302c241c0880d28480e180100880c0e5460003480c0a200f44c00c1204060500800f030300305600914050101c00d01c196104540500d50001c020401403884046041010756842140c1180d80c02660704002d01941552003c000c10b0781511642042018207465042122013200c1882809202d5105010160101d100c0c0001d01d60040d880d080210300c0c06204030603c2c400d90300b089aa030078070924500440010b026050030300850400c0c08484081e07011010181c05000500ea9103c54400c02c0350104415020341000d50000c1c0e81c080d00041c0e0251184103c545a40103035115001c1160300340102042419541041030b819416240d004003e541181d448080c8035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 453391160 1250 453389910 453389929
    0x1150905060304170f0d0f090c0308070303060308070b09010c022113050a03060c17010f09090515090705031905030a05130905160801120213050601032415110309 71
    0xd507000c08942140420742c899241c003d2681641011400e44c51341b4920711020104c41c4100740701d0042c0b85c03c00c0c110f0300003da0305000e042c2c1940d40c000840d580310f10250400724004e003c180c00080104000041e40024480c007141d449200b284400000c1c06031211010040742c60341c045400e030b40c1101f03082d082d0210b00d8004450203800704540721114401e4003a51540000c030307007518541c81524040c0d522000340780b40c1603110303000d05192080d18540440d2945490380c40700700e001280c450340d11020303580c01c190001c0010500c0000e09014004440d0030701403d020451039165030701882154828403a00b1610580100c5003402d0150081d0004040e504020590f001a42c03a80d00010000e950004070120204039084144103440c01a5940b4007050300000007a04068084081038020100004441e0514070050795a03804001c1c8002d8072410114064540c200140d003c0c14141c203c8c0b8036492503500c4e44010050100001d0021121140d4103140c800268280607904040c413a0090051500308001c07040300e600304505032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 453392410 1250 453391160 453391163
    0xf0d030f0e0d02060f03330f0109121505151305250e03010506012111090a1205060717130528120207050a03060504110603130b01150905060304 63
    0x8400030b0089500280b41d903808482091359007580441440000c18544444015862050741c4144801d03801404981c10403041070fa429101384200044440b9592049050700010048404104804442807401d41c20b09021100b07413506a91406002070b100f00320081e082400c41d000900011003102c0c0712407003d006004024207500d00654068500807082103005800c40c0c9a002503503803c81010320340001c050075031300c02906a5040000640340c00c40000043c1c90380d20301036106200c00103840050740661440a000f89410b541c0d2200c0141b9000030800b03606000c0510301c078030440542e0160740d124036040c1d9a504401c500420a40b2920000079006554100500c0185014030100d400840228208080318440c4880003901011405c0307143d000c1140d5500c0140884a10703001a04465040401052840c010381c1310182131a0303181c1c008102800074203031041b1800b0401030001a03481c6044175034130304040d17500401141c0d840c80c00b07400040c035580c140688404012050b07584c2c0d01c25615103401c000c080e4002030700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 453393660 1250 453392410 453392419
    0x60c0309030f0303240a1403010b1905090a11040501080901090c030609150c2109020310090201140301081f0222091a0303030a0c020f01060f03020f0d030f0e 69
    0x981526035404020580c2c02c2c2810781e0003182c0d030b440c103506155100700711244a8441200b00c540004255a1600b9541095a164080320303041940118000380c05000da548229400c0001d044e2602d1043c944241e401c41507a009a40c0071102e0f848515000c03044074510420528249024071003807040d90300c5202c035190042c40f52000440c2254054445e540803e0066100301c07481959400000c080220050700517400100c101010407040c00e040384d01400c5e0078064101a81e110890360020044a041035001e2000a07401030f08441204c001101100001c1c8441407040e03010984a440c0b10081c02c1a56080b00d061303a5400000d042901826038520355401009041445015002c0c007190301880141001c2800000324810004c8505290800070740407180000b02c44807101c00d00c640a00c5040e01c0001c1200e0300004500d100140d00e015500c412400c020442e10826425400d00400081c0d5001100c460340540c0e000b00c841d488e01c0b6a00b1010000030b0740c54401c004012504040601b51454010000c01e13140300340240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 453394910 1250 453393660 453393667
    0xc02071a0a230306010e010c0203210705060c030f10060c063621090b09220b011e0c022826010e06010306151205010c0e040c0e060c03 59
    0x80d000a50b1000c07070890a451107201000304007081d070748410685208003003070a01d104e100f061500400d440c3c03807803800826801089020300000c20001c160444a64070780000640e041da0030030200c1e044482d030064401d11200060741c00440c050564445a82c0c08940c8942c440300020f54042e82c4110280c918040101150142c89004560810307075003160441c4c03103620311035030403480c1c5003032900502581d1846003024042c6010007144411940280071541502c4202c2455900d4062a00c0000c01241c2803072040c241080300005401200140741d00f240420503000d0301ca2aa090152800b02e40800400c0707040d001c00110301070117510150410011019007107400180003181c240c0708c020035030140a031039440800c0c040014165541d0442c00d420075000200c1c118002400400781101e030300c90f80e940b410b000260009075140490180082a00b004900034028080b01c204a17403098140765008080d080c5400003c034a02c0801108a0702d0240b2601003c0ca00780d441d80703240190b0b030300b082c050140c0018a00c070f5403a20040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 453396160 1250 453394910 453394937
    0x608091b01030f0905100c050c03070303020c0a020a060801140402070b0609060109051c060b12030304120c0c030c0602101407050a03111803150402030a03111903080a0c02071a0a 78
    0x5000300718226005100511900024008400440c7c0710108a03008100c002c1c00303d0400031030040100ca0240781c1602d40542c03207142401200741056000b500080d40102810300000c1c040e0782015515049500703010b00203e1181000382400140d2040210040c04040c0f01310008070b251411800840e00b205040c0b40c11a5059110004140c008429420403019900c2e070321034081c00c01105006210044100b44d070450111482c0d030030710701c0c2d407408043e1008203400303481041400c1c0a8800c0040050007600162013403821a034030300303140c1541c480394041d0030014040c14a0045040e64103002d0180343c40c025007642c0d1080c0e0b03584041100d41e40c00401802040540324195299030b00f60020280c171020441b900320608006001003010b182c504481030f900d4030741425004000141e03601107110b50341c041c4c0500b0607000a1040c101114240032041a80a034840141005202807650011045c2d00c07a60a03176008000201c541740b81a80c1c5c480052180c0e28100b00140d552040d89110f5002402400029040a6400300f21a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 453397410 1250 453396160 453396191
    0x108150a09080912031e251115160c0e0703050601080601140f04140a120f031803020603090105180c1315080f010e1606271a0c06010608091b0103 64
    0xb06d003241042201d020075034844142d20381d984080c28059800c0c0b04001d08259a451721003c201030a8441c1c03164110340c2507000104c11030412200030881443c251281219a80b8066066041c00d028a003a80602d84000564060003440ba8900400c2c2c16182c1c0c5080d65101801140c500b8000c002081c0420400d0296081402c0e280c0041c002510300105000508032a072000c1c0449c80e8026441840c0c5e80ca0140300003c0402c0101400810381d64252400c1049540d00e800800504001350b0300003500908000f0400456000c1940410300590040c04000c2190158910485c0d5401c41550003030b0340016000c840c03052116070b6a200000c0c03214140b6151403c5562401104d0034420b0003107040c8050b94640f2140700b07440c00240301400d01104ca181c1c1100a2500b08032000b4040300320700704080c03042180c803407442c890b28400510040c01010b05000e680022020043d81003e150400d211001c601c2c0710b00d034008101c2500958005110f070354607000400903442c0070355000c80b00c03a03002075009060640e00c006591102c0302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 453398660 1250 453397410 453397447
    0x903020f0709050f06031606030203042603040201090f06020c060d0e0703050609100203071d1201020a0302040503120f0f0a09050a030804030b09011a12150108150a0908091203 77
    0xc0d1180058141340c020840001c4590040155100f41c111020090030031035011015001e81d01c10303240050326540c5518222401c08480184400100302c0c40804100c0c04044034020f6204e40e100381e90b0b5000c0d0aa0707595440803107012030700660016800000b80d1710302c14105040601000e60100a020545d0030004c41c0c10750070201150402e440302d1b004502048200401000350400d240d2000341e04520354500190010103403002941107200c50b0350300510110380e070703501c001188100b0010300c0002c6540c0c02d483e50003e402948a48103903400790140c07000c5402002140d50980e400e0110000e162441c0c0865901510a25485032a00c0b005000d914032000c00c81d07480f200300c59000b030752141c0d034080e82d982c4c25414544103440f801001300506a040c06802141544c8400022a5084082c0c82c000d406048250b03405080c07162900090322450107520001030148000541050305030ba408404e1101500c500521000381d421250025081000400800403c0d0a000c180b056070840200180c90a00e10440f00e400c14041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 453399910 1250 453398660 453398669
    0xc06020309060609160c0201080c0c0f0618070f05010309080705070b0d0e012d0b0303031e010501090f03020f30251404150303030e0705011b060903020f07 68
    0x2e1008080210a0628804540c0c10041041c6802203403c2c001000410a0341c050000030304000c9000003003102c101c030480c1a10000d03001c0c2d0058441c410503802110340c0d200300c221102c1000156800c2c40c010b5064002c84c011040d280c4108401c2d00190510340150060300c00c0c103404640f035400400a0b107020410910038140500301c4041c00580d0344228043c690252050760540a5450749482d9401c1c80010098540000da40000100c105c02040001d20500081c80300d400400d8250000200b04200c0c4640b40390310b40851030741452590b150b070b40c0b61070044410f030b800d501502040c0c3c08844018405032400501002080100500c0380c2c2c02200345808425442c029403880c030803100b071031f81c00005810000340020070102c5800c41c2c0f98a84441c104405070f242c05424401c0104061f11000705944d1519660841210500080442c3c11401ea80e49401401000e84a1081e0001d009054010500f50311403802e1031003240a0340030003030308108113841d208020b2030841012000e40c81500c4c1d000007442c405006810050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 453401160 1250 453399910 453399913
    0x10e090c10030b0405220b070324030b10082107080a030906050c090f1c05070602160f050f0907021e1f0510031205070f0b160201060308190c06020309 66
    0x83c40b0030b2105440014285422104140301a80c0c600044a8003014a0345d401c80d81070700c0c09440d6150290010511010100c1c4034500403201905050900c00312a800c480c800c01c0a285280e5171044a080582200e01400341d0540100302000e034446100116245407646902505141c1034565444543e29805002c0120100c1d803112805c80c00d00040748982c540c0101e4401c44980342c82c5010300000c0c0395600040c8854071504210300800358510314000c18208055008080341c44017074a488000e9980c00706156090140d903103105002c5001c18500c25558207c2d0800744c08841c4080b0400c1c100090302c0b000506903811480b401c2c8025481c2003040304212042b854a0016000e91078108186141c44c0c81030441e01c00c4d0a504000a00a80100406498040701c0d08650001105030b030f8164200c2d558461000041c111510112581003881000c694550040040030004440002d01d0300c001c1e800d88540b4071015003008400d11103407544a4000b03000141025003450030768600403040c0d07a42800c0741c02c20b60fa50000c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 453402410 1250 453401160 453401171
    0x30f0d050426030705390f0a080d23070302040614091332010504231506130b090a121e0305091e15040b03010e090c1003 53
    0xa01414111221035400d0012001c1c1091180441070b0308a44405441c2008100c1c00058012000307011841c0e01c4144003568160240d041c0813451106621801170b01c0b40e000720f0040044400c0c0c1b0305800140c841105911800c4103040c51600000c5000409039121101c4045040042c8468410410a10103200b01000d440041c1c4403030070702000600c01c2141100d0703400001001c20034a201c5a5801450780601c400710000401c940c01954072a41034a1884400120b95220703400801c5030a000e03050640f4140d64040d00c0420030b80c034541e07446510780540041f0094030302180c84081030700d401032004513550141c1c0240841d841c014050900d1490040b899110341070313028000c0f848070094603000e0b088600605aa4480c2403148409071101c150550341ca00c81d0401000b103807280340081500910548015070300040c85448401c1418a00100561380203c1480c8249817008481d001c25160320156001e44402c02c000030b0031682854000141c0c100054916440c40c4990a8168400d50300c980e011800014142d8010a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 453403660 1250 453402410 453402413
    0x1b040f0e071502030909060d03030204030f08030402030114010608060f03071d19021e090d080c0f1e0304093b0601060e09040206070204110f07020f030f12030405030f0d0504 76
    0xc2c1c4a40c1202d4040454100f041802c0d426661001c040340c1200c800c6038080d551101515003070300240b14a41c00107001c1d03484000c004044c4540c1e0400341d8400ca00a81c000e0058200d400540640d103a000d0041d48045102107002ca0424141941890021103000c0c04684400b44c45065080c2d8949003044401e01d13058030170303040001c42c1e030981140c404905101c05080d41014200c28103000010480810024400c10200e10302d1525920280b12840058010052650351564200c405441d000d9600359035446206140d0f41040e803841400300d01103401b9203040514101410a81d40c03802601d11000d07407401050b5261a00c80c20300003d05440240010382901407507031148154145420200140c2c050320500101d50b80345070054590b600041d6106074103c5165a0724907403440061700411000c0307200143c13080045845d880c85402c100042440301d000322040c010002d48132003015907980f01682481070503001140c1c2e82c1c1d5040e84800181d1340280c407803402e0301c0c20001c0d80e545400a68011805060b107880e101c0c2c00380f10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 453404910 1250 453403660 453403679
    0xb070312050906040f05070b0a050a02010507171b070506100f1508041103011808030912070c0308030705070f0606050a06020105150603130501090b06211b040f0e07 72
    0x10540010040284240e150200401d0b407510002800907100d0030458201c18108102030080c040600005623155450350260b44004005400295042c0c0c007561070403006c19206401b400740074900e080e600c2c020030b0841d0340394110200c914042441c4a58031031030074403000c03001400c02c1c04a01e100c1d003043c0c0b07140203203145000d40c1031100e40a1030780540a4030b16181203020b440c541c0a50010790003030b003000d01c140c505ea82542c017290050079135407880c03004040000740c4c00c010070040100550040d17915404a0320640006140802c403032058880040c10385d40280c004000280740000916800401800c01d5800e0240648030200c0c0c0c1d100f80c40c0100e1341ca82d51000e092245103003c0101d039003c2d05292000b04803d1500302201c11540700d0300c0407006e02c644004000122444050f002b0000d86079030100080c01344140d1494601d041a0003a00d01034442c203580c200030794441050043c0b0415113660f00e802084407200082c500303044c9602c284030840d0030546402c002e060905203030046443d0040e40c4401400000d1400403d103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 453406160 1250 453404910 453404927
    0x12060207020439090b0a0309061a0109142e03050a090302030d0b0303130b09310209041103070c14070f05060d020409110a090602030319091104060b0703 67
    0x41c480030041c00380c41002011100381a03d241d255070890494400481003c1d10818555400001021000107141d07402d954540c002d054064030480c814001542144d20f0160f014418000060004107441c800b00030142552591209a01001e050801600c461817140c1081e480c2228540ca03500010804201034685d051058a038000e1510700204042801694000d45910411000004180e00c03040041c01d00d5030203204440c00c0c181040c03c0110250f03618909203c01d40c2005042030300c5a05500c0085a082d5090b800101e000c102c1902c4001d010750300c804130f4a00941100c0102c2c0e40241d60782d03040ba210368410200a50203105c850700c59948800b45858040c01da140d080a120889402c004420802070b9680c99403a0140d400481e004c0c1c0e01d4070300c00e0b080c9400031f005039440821554100580d100d80e050202000300003111160b980d0020040d12040e040c0e039a403105484e046851003103400220340b2881540c1c001000b480c0303d85000c8048908500004050300e1140e000080c450500040040400d83c11aa51 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 453407410 1250 453406160 453406181
    0x1e0c030c0706020102030c040b181207032a0e1012030503240f15070c090b100203030709060c0501150b0a120608070e090f01050f010e01080f0d050a09120602070204 72
    0x951441c5130003803981c82c0b9030095101c0c0f04040e14000c50045480c41819125102c02c0d04050140104002f1204109590319001d00c001d640b2503000d0007442c81005210301c030100c01c03200951001440340749003080c3c05150140051062556654412010030301d00c40c1132500d19102c6d80650b0718a6200d0409000302481801004400308a0b18000f0b94010419100d000d024090a501101c5800c2001900e100c92026403081c60001490b52241c00740c003107100304007540030f03200215055541445421140005a07664403043c0c030f11002042568078204a00c0d0301c0b60f62110340440c861000460010340b100061012162035400c25410b0300d0010502920403a8411a140c80a0310a41c20601c0f0f086d2030080190b0700c500042c056069032940c0c00c8001a030b00d01003044200c0b82006550020009403a005000b03001105007801030040048d4500000070f41d45600082c2c00c10030300e00407405070090940c107000c151025800000000144580003130000b0f11020441022500c803401114090794036a40e6104004c100c5403410030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 453408660 1250 453407410 453407413
    0xf12090f08030705072102040e0109061d060a050c09131a01030204061d0a1d04020907030902100e131802190305030a030b06040504020408010f1d121e0c030c070602 72
    0x40c200410320000b000403c940d03481818129185100d2011400700301106c2c0e02035085070a0810714002800305620001a03a40144003c000d10b0794034480201406903c58044215640104081420b5103019404950020008404c00d031602c0d01820104804603110b56806004d5642d424a49100c03900c00480810400703400d00e07086140130b0901c0d8014005100d010300c00f202000c10700754807802c240c54200307890018014104500030b00900c07494007815030301d9003151704034012001c2402081e50305000340290300c100c3e80d0081070b0001540c0329003c1162007051024605a110040c065261000700c5a4880d0341c586e4050b21141580045040c014000300342c0610b0034003001c600381c8102c1080854004800d581020801d850003250031220003000900c03030300550708450360080c4006400100c004056100414464034148240949010700d01d0300c0c4401190601c2003d1141c001c04000c460501d44800100703804080701c48021403003000c020b500f100e160800049055158000510704070442c00070010840248014030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 453409910 1250 453408660 453408667
    0x29030106080708100f0b15040609060302040b04060509012c010221090118090507091d090304060e03030409060b04030203060c03190b13050a0506150301030f020d0f12090f0803 77
    0xc002a90320120021881c0c11350343d8500081e40041c50940040000100081c0713019180070a5154610160307020b88280c90104900324030019000d8080d00950301143c0341c20f81340d2400c1c2460440182c030b150340514a0f69041188015101c12901181142040300c036107042681e1005500b02400a480d00c402c04008090740001d408043e11100c00c0102103c000400a10b0500f4500c0842c45085261f81c02c5504564100390515042204103607108242400301d40c011001c014020003044980450707200150b4503a221070300b04010921056004030345008078a8400307070841c3c0c641980c40144008480654025609901e00001c2c1002546010040b242d002961043c0a51850a00d42681d0718540d070024800340301c540c0c0b01c0581a601c2d940304030000000000d8028244258a0041c402100603c812503415114403030244428800c40f0b903a800b543d05070b039403103803041100c00e84903000c01113110b0001c44100c812401140080d0001100324005240007100d90301c40c54812402c2c840006d00300c00c801c2e002079503d50f0050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 453411160 1250 453409910 453409919
    0x160f21110d0f09030501060b09010909022d04050303040308030a290120031303020102010c030b130b0a03050a0503071104050402060a03241d07030209010819290301060807 75
    0x101d403007041c4824a04000700800d08454041d41c0c1448a580050f1083d441c10800040403a4a80c0007010b02903401d03a02d0505da2074890704590128084d1450b0240022081072084c04e50148580481c4000e4140034001350030300e65a000080c2c655482900201d03030860012003880000c1d502805101c0d031014041c04a2110746564048003d08802c500000e54100300e0b03802042c0358141860320381c020520914a0075280e071a40c02403950101c41c002c7e844124010740c6400c260302400c500c01c1c41006c4421800178220641c0342410072480025103000442c1d2070340085400340c00400508208080007245100324081d546907501414a69800480c421a01d80128200801c000050743c034442102c188112905000603101e80103210700c2007514644090005810000030041514070b560944400c2980f00d10b0548100e03942c42c070104405a003d00d11300240480c4043c4081010f40f0b160511401c059120803000140341103c469070088680c1c0e40150040c00102074600d00d0a00781002e001d91405804960010505240740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 453412410 1250 453411160 453411163
    0x513120b100e1b070f030f0206010605040f120c080105040f14010606140d09060507210b360103080c1902010203030705070f0209040b16080615160f2111 67
    0x82800c00800c0d40840c00150b5070070420284d802c181d4004c450b030b0034980c0d80d91801500d040301d1030003c540503216002c00021b406200d5405c4030b09465071304100101043c50407944668100b0950000c03540700b1200140810400001d10800748694040d65146a100215003802100c0c2411044203040690400340e0601c10b207500b20821000000c440d80020740da5105100d9404d0007010a0b1000a016030705203400c0c0b0246a9000c107180d016501342c00114014040400201c00440711b58400da20740060030f0890203048800c1d0040c444040320803583d0b1050108050380c0303a046455400360000c0703560f0840403e94028140007081400c03680356441c940360300780031002e0300040e69900004100300300700140040e9460070030901c20840310035140d02a142c5c00003818a0f2401000c400d034101d988a142101850882420714801c503c041d01a410162201441b1400101c501c035840c1d010050980d4162281c9291000080e00d076844100464002c028400b00135240c449a031409010b84110031080260302e1580c031420301070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 453413660 1250 453412410 453412439
    0x190207081504060f050a02030601030b0603010e070f0c0804240e0d080903011512020439030b060d0b0f030307030e090403030e030316020111070b0f070513120b10 71
    0x21811450380680e0750307141000103040440c01362502141071405018054100d5000345000d41c0e4240c8060080429500522406000c244940700c201070f22200070a51150103210100b0300c1008a01d8801c003c00d070161113401d071320b03030040d8131004c80c1500240c00341c01e21120000404000c2415840d10289010038140025101c0d440a00050f250000c006064140d640d802d50121412000061840503100c2d5600d04410320003121400070b901890909464190b9030a078030120441903101007034010818411805407118980c01c0b04018003d0594075800d4109507650b400c06070441d9201ca0002061a01884051001100c109400d29019510601007880000e420400340d086049094030188070300d544030705088015080c800c8580ca1035002c000700340120035480181508009926030000c1c05490300684464019208440b405040c246030180400c01210516502c2c1c1c0d000081803401380d080c48500301c6181b15691041e4003c00c0da5241d004111410400713090600c036131040c000d80c0c0d0300354200d1903d40f016007000c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 453414910 1250 453413660 453413683
    0x2704030e150c0319180b03010f0b0310140102070e0f190b0a1208070204060308040306060506181207050a0609080606040209010c02060a12022a0c0102100c020703050f010219020708 79
    0x12043c0c0e4004e50220300c1040f144580d002e0b040382c0c92619542c0d078583c00109920a0003241580100410f0206024880740200c80c00b400c142e161a8901f50301c3c00304100141ea040300700f52411801411000110743c1c00e0641d00030300408a5011480c0d007420720100c416a68080e0401c80707410b2904002900d640d40d80e42021a804907100105000d921205a20303000e10745211741d000007548649400f4011007031104a40140c025203204000c02c00020740c0b42c604100b81c90282c0011320300c1561a81032501c4c0c280c1031012034145180304000844007010f40345e60008504000e1030304500c0002e884000104403090702042441d800c550155400c6160406801c0000d200200000029014010016035100428419480905044070000046403030341144040000300c01c811070314041501c038825452140381d401c0031610f62603d450580042090180381900c0b10050450300c0f4104055009140c030000224000380f005201e12a034440c00143d0f03464100b041940d0061500580c0380c11903000e8039040c4004100082c4111126 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 453416160 1250 453414910 453414937
    0xd030504261b010216090501030c0b090a03060b030118030806010e090112171c0212160903060b0402090d05060604060b0a020a08160f060603050601051804022704030e150c03 76
    0x8004440140e117405c1c0c003205400c88070040d445001943c2580c942c007541c10781c0e101c1d014800c5440d940b50000c68060103030004c002d611681d280e03410070020762075510100d0000380103800030501c00039003103180d00300603c11841980842e0001c010400b503036034010701d03801680382c08813041502c44d4103100700c20070040c1040030001e20301210f920315046030308203003070903641c0d02d0407584128009050190042c2c0003a40019081030580f05c045404590488041c6080f000284910399070401028510b85416000e4944041e0294101c0c0e801c00400e803107526a014194030072802000100464101502800704903401d6621001030fa590610051500c42c0c2c1c040760031b60b0181e401a16541e11095002c841c1303008140c926800a04402d03031001100c040050380d41000d4220b901900135138503103030303a1ba07410311481038601088110f00141c05000070340140b0306142c0103400640d05404208881942c01c0107003008403416070f0140c0114282504d80c0b08a45040c141542c1010309400c8002d0a28502441050f500d0207515500c5900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 453417266 1106 453416160 453416203
    0x9030406180b09041a04021602100309050d0e0f100c060c031e05130b040b0411151b0f01020301090204140301060812180d03050426 58
    0x1111a111000352a01a00c80100402413040c000d203a545000401d40520042c6c8031803001e46070300c2c6903414240e00c242285004110300c654800c24100704050034400034200042001c105401c104485007000842c80c0d55410018401104500a554104030701800c40070580354070038043c820311401120100a40e82c0d840004800341d40ca03503000440d0f5554582001800084558482648200380b442843c81040003540c0e0701c031005800381c4050362842510782c180800d20440580046c030007002200e425082040780c6014010074001d40c1d4260005104042003114886424806500311110105c021580c0c3e603101e41c030b90300081d0850b0050600d502408201c01101b410144160415240101c0080580c59400125541e1381c0e44240c421440202c04410358040a807909211101828820b48030607850f10b00b020f0900c6042510640c044801c00c89560703000c5542000416081c2e40c0360500240b0181 = true := by decide +kernel

theorem cover : BRFrame.Cov 453237410 453417266 := by
  have h0 := BRFrame.cov_init 453237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 453237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 453237410 ≤ n) (h2 : n < 453417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
