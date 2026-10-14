-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2745
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:36:56.70323+00:00
-- url     : https://prove2.me/submissions/41adcb0f-de08-4ec3-9b7a-669d3560b34d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 493525179 ≤ n < 493705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 493526429 1250 493525179 493525183
    0x30a090602060f0c0a020c1801170307031209111306060f020f12090a12050a030801090c020a140c10031a0619030902010e0406030f121e0509061326 65
    0x30040e0344440c0500000d4131039201000a5034030080556055110b0b4240d014455240d242c541e80c0c50885250803810650b01d8407002c1184201c18050400640c0c20800440c400a03030401e030034444400b00d1950005801c50381e032500c1d1000b44842d030300075603202100720300d44401068250404015503040ea81d07048000c890b0703c00c0c103070380d2440e00118590180d00302030080d8000310300540250035840d0340105105c81c46503491010300d82140e4054400e4889401186001c814503420519503401803030710f04c20400c80f11100030002900d56000744002002c3e80301c0b005d1034405125040101010741d005c01000700d03180d0464114094001c001c1150000b82c46604819000b80c50b203088000e9039615102c400343c0b0340c0480041c01c0110020480314100f02d05100324000140b285403610300c22403029500c110dc5280c0301d4603040c145130015001035500003041080d1100d4000c1401009034030021070f000c0c5414003c5c2c403000d000b40000e419024200001c60b500c2d41c0e4140005056640c1d04007002040490b450603c408580486515 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 493527679 1250 493526429 493526431
    0x81b0c0108070504050108040c090603080d060f0f05040c021f0606020111040f03080c0f030703030e0c0a0f090b01031407020a0201090902040b0906030901140411010e04051b030402060705010608030a09060206 91
    0x400304900b0b210422895000e00c41f02c1ea07020b80709004d00c0f0703039803900d40c1c00c204200c41c8940c00c1650b20840100e1500f040140601c9400050207440042040043c0340c00700300b44408100f0b00505000301d0310b03200e007424114001c000605880062400501c680c41c1001304007030040c01c0c4c2d485a100190f082114450805104a0468041c0c9106c00b84140c452810b5840b40d024580c42112022000d100303c2400900880b018009410703001c0c42030ba0007003031030051242c6007440c111112407602d11a11840f8010801458050240e00c121250800e020620f1340035900160300500c1203490003088104014100480168040f8a450034a4801d0f2078084944c1d840c2c0c04084100d0040b40505c000d41003040084c80154a0440055a071010303078000046a8070450fa020880602d106413022542e00880103142c031314039a080007480c0703603614044e01c040005140c4107918515941c031500704080c2420002000c1400e64441604031168075401100a0104c103030741f140456a25400154540005408000040f98241c4085802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 493528929 1250 493527679 493527691
    0x3110115030f02091015080f0903090a1a0f0d06080106080a0f0b180a05100f11090618090108071806050d1b090e011d0a0213020d0603081b0c0108 64
    0x41c140c080b50350038021031107000752940780e040544900001c1c40754203c0c0c0154062203400c2e514524642060064203a070102d0140031080030743c01c248119040c03900c400c0d0607842101c59540d50024101682c02d4030502c14420b8210003140800c00042c80300c80c0303202d540c0204089a402200030000320741d440481a8940d1240c5100500c5140f03429040c13404203070213540954000b085000c0c8542d00035050030301c1038600b0403c0001150307140c02c8214540c07031000d4a80310740c40d9030300714110381402142400c001541c00b502c20000d20508c11100851009046401004a03c41402c005000c8100319612190055994005440780c0d2034401c507000821103a0343c296000da8806c44034090182e1040d072030603a0b1491081c08501800f06240c1b42e03110000505031049004a8040380c03041c400000d83c070f440c10719100038035040c00c1071551043e900006100005031240c05030819150940c010058465a500a011020f01469407020348415000300e06400c4c6020400456581d444c4090103d80070034404000549019200301c0391 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 493530179 1250 493528929 493528943
    0xa0303090f0e07080c09041e090b16050a051b0102040b0403110a0308032a130e06090c09060f0913060e2a0d021201031410020f0a050904180311011503 66
    0x850407200505d00608100d03040200042200700e00700785990301d0407400c80401010380751100f08960500c400200c800790000d8446040504500c0201e02c090024800d1614541c03c0180004103100c0c61001e40c1e0040c261904080c000355035855441c1100720598002e03000668202d01484003c4405251003070740d140441e40c0c46040203045560f00804801e02c000b00e4032a801e20035450b15181c000342c0750000020101e007400c480340d00703c40302d04200c01c01d0b12101c0300500e01401082d072034040c484000b05660507200105411102540c0e500c1d502001044907002d10030f140c0d50403610482c5044a02802c0390894001d03102c45d9004050150703103a00300884688640c0d042e09078036100b06a0584c1c610070921005105554a00c4d8015142a54150791462200000d0340240d9071101d82c40d18600d0014418850030000c13499080056007410780e01c658001141c45800800c0c000d00c0400525442c0c2c984070b540105402038007140064070025810308010302904404c0503022007651034070105140d450340741c0c030145084d2500806 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 493531429 1250 493530179 493530181
    0xa020c04020a02100e0d021e1b0307030c03061a0f0d030302031005302a040608010f0c02070b040b031317030c0a090906030503030615090a0303090f0e0708 68
    0x82031100940c469492001140683c10494400405900840020307066031302c004c0c40482240c0303100a04103040c41034003400c400256511485a50320010716000341a0404540f20208604a800607244c800700d90700c010b000148030386000080c001d15605c006a010212820102005600390801c605860102051a403015004400c5804a1312030f0780174582c85aa03d818039a00f030b030344680024203400c146880c215446043e041304503100128400c003400c5900c82103801060002448000580c0754258002040e07068200480c0c480a10342d520340010780140074202c0208101e22515070604098003c1401800c058865a2030002d004044201140c045030030b6041c1090a64550110039284080300820945050220015072040c2c03142d150011130007040c020021950ba0364802901800c8003c140d400000c542c1d04e012400c00106402100712a4041c2c0200c449411515480310041c4c854090080182d0300a1100c0b00044201a049a8010b094076050103034403150039940c484904d660a4221552400506050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 493532679 1250 493531429 493531453
    0xe06040308222012070f180b1809010b090112030e0603071b11030609061b04030b01061209140a2105070314041a04050f030d0e0d05070e010e100b0a02 66
    0x1690001240f00002c09080050004241041c84c04842d40c03c10380510b20b49103810407000106031804154079040120901c130040325000007840d4114410200c03844005640c0c0012080d0200398414140c501001f4034020032541c44107258200702d07030940400c44c04940005182c500d1403410006403445040300340e465003e1850049040c400d5050103250440d5511049044d000c240d6900303000780361040c04980c0003002c140c80c003000042e003200001032340303140501d00411003800070a810f4100c803070540e090390400710f2411070500c00b01c10003000300b00c6002e0070700d44070700381400030302540410014035107405040700172a4181200c1c6001c081d040a018418007007a410003849000a002e0b48031016034500c440349040c1080d41d030b00900d08844040c85050350f020000060180301d680b61980b120b648006040d0b008002c01441100040d1101c86043c00d414481c524080e160402c0290400402010303002411000c000340d6560300d0fa10100c41416500315820f01d8550b0002315004a00b081644c201c0002503004203604a0f0300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 493533929 1250 493532679 493532723
    0x150402030613030203161b0f06050f0a050c0a0602030a0e0102090d030f0512010605250209060918150708090f10020307300509070b0403150e0604030822 67
    0x1020782141980000c4c0f006c1c52031a1150b80050070810f020b000c82c900340242c07000d40d9040e40200340d00600d25a507418a024050168001d054800c0c1596015245648040382e10043d16240038074041c1d00954440c00105104024040c0c000e0360244901c071030240031004000c50300314240d0041409454004000302c20f070340c3c046882217a810126052a081c010300e00070516003d4100e60609800a03001f0600c000360300e00c0f14640c10440541d003240d0b042d004641c1d04c4241c1d40040e050000140141d0302c80d205500204820b0300005815420306c121020807200040f440620349000b04104840081c041038038540002c02c142004900400790440044c041c2505200e0440c2000094101520000410145d10070105031594200c11904507110301100000740300900ea000f15080e900002c001400c3c0b03404c9104100001102d00f02a13500362503202030164040183c880b004401054441141c040d03902c103910500041c140c11510a81c015030151000e031aa4a010900d034450310401c0d0500180741c0041c02c001e074034940400d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 493535179 1250 493533929 493533961
    0x220510120b04020d0b090105070906050a0807080703110a0e120d020a24110d0614030a14010e2506020c0f10021e0f10200f1c06081504020306 62
    0x8000c1039104d0046081d19400c12041c030855001d40e0030382d075840071300009e190040081c0c00100343c1442c2141c82c004c000740c001005010040d08200a024065020a442c0d0380240c0042d0315060f91900015101c10710548001c04c42e145500303000c0c3c095251808065031f11240403e8034442418160014060840ca569401075400c0d4040d841c6051040724150544201140b401080729201300d0091080c1c58180080c292003c4038850351291b10701690440c00c0d14900c1d100032401c8a041b40e0005c0c02c04040c45420f404081c0034000c40d58250740301c1e000c2c07031041b018448500b52668000c0d4000120341d10809869500580c0c0c2d940130100003640c08180819042010f01d4241c01c42803941e41c403403061760429042d903408040746041052040d1155000700a0000e2410000c100e480304007418080e0502c0941c00048810402c50044002c3c1e109140780007030702c003084196840c2210a4204641c24401d21104121f030301100800081c05209820f001300d900f24015003540c190039500a031780003005089140c4450411281081d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 493536429 1250 493535179 493535183
    0x3060f0605090a1116030e090f1e06010e12010e0d0302041508040206040b0c1608010509010b0306010e13051507020a0b09030a080c09010e041508010b0904050a061a220510120b04 78
    0x440707d0880e003103505c894000500a032000300c1400307060304000c00ca401082001200200c00c0703000240801c4840d0703a00003103000c0340320801d442c100c412071000c0a0309800b510318000b102c02a4440c08030107050075545517004000304d6000b02c0601c0299003404004460600c01624003a40c882000d100c244544420f240c01810b40d14414400c0742c41d06500658004810581036208008a0759030b0010003802040030f006080c003a61049003d85080c2d07040400024600303030060201c50902c1c51107141042041010003070358034248545030280034146850000207580d4850302504071130381019400400e00801c0d002040c1c4410305000c1e140e03101c20b503032107030042c04aa8100300c2c40541000281e9041032a1600c60384520030840e002c00c0864804c103400d00c14040d007944d0600c2d084c42c2c0a41c14010412010400100e10403111691218010071400140c0300c00c000840c0d54021850f5020550100c00101581510100c0d0a07414440300e0500a80c0d075900d01c0104030481c1031084c0580203441d06810000983da503403c3e198424 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 493537679 1250 493536429 493536437
    0xb031b1c1e1a180a150308130902040b190e18010915060f0509270f01080d0c060509032a070503030f2203060f0605090a111603 56
    0x822a519401035481c00a114078520110741d451058120351805102440103001c00120226051000810b220099000301281c040b0401c0e0080fa01c1c54280e608085401c0201c00d02e030000654407410251455440101e02e050a0f07600c0002c00620b01009009030307000c50703181c50565030810355170451812041c4186020101001801048441c0b60364615201c1011440c10040111003981006660811500c408070030554002c3d403180204400c65100307001d15a5001c1c1490b103161281c0051006c501c1c40c8150716a160b80119401304550300c2c401070034540501c506001d884444050b641c030241140ca0301003554142c1e0010760121030b50404078842d9041117810442c050116440d010300e00d446500c800b40121183c4102100e5404082c0f400c0000300b1400001d4031080b0050f61070f0118000311410310340b10384080190184c02141000705140c80303c588840046030800000d01040103000c0c2c0800040440d401254445c014900120300081e90030300c17620158516540410349460a4a00d401c035440c0c0c0c0f1080110100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 493538929 1250 493537679 493537717
    0x150102210306011e0f02300c07030819020606010918020c070f0f1503140f06060702040c050903160e010e0603100207030822051b030f01061409010b031b 67
    0x6038244004c60309071007010707903500d080d5804610009050900a0450f20444400075640ca144040f6400c00c980314141d070000f40a5a440d0981e01e103600302000c1d6403000c4d00840010400c054000300c0e90b0910f02d013000d103503030943d00117594580055408414a0244489649210942c8204c1225980c02082042410303805c591000e80e482240d4510040709801200701c40001c40001c101100f40d50b8a484444155403c0070b001200f500e00c140d0081c0d200007003840e900e008004010420035168001121040ca4000d007040c40a443e1a500107422a0300840c420780c0a4419101d101e4081291403a41200703a4810006448080c0d03c1d004100740c0440c00644403651501400c421808000000d1000740b51170303407082d181c1a4031850044206841000d80e242e8500400d130b9483e207100d0009801080311b035881451320000700701c1c0c1c481c11004030b481c00c00340380c02c000203640c40c003180825010001d80071003880d80d0048507003080ca1383c1ca484a00c030f05404166080e080102d480110340089802c208041e080c1d42805424810380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 493540179 1250 493538929 493538957
    0x20a020d080406020f030c0d0c03140a0305090f010c080a0c0e10080f07050f0a08070311040806040501050c0921100f0b0102010b03160b0f0d0603050615010221030601 73
    0x11103410520100c0d408600000c0821001c1e8040c40f400100c5031a10018605080c510828240c55000b9641031104228003400365004160180da014240030040d5002c03103407500c0740399101034002e0a0070b954880040c811040c0c0b80d81d0035441402a0880350308195a41c101c01d48600392402c014000c900c800b6001c1c000d80000b006400d032200c0d151a0300d0821340340e403071014908140340808a4200050504000c2000400944110703400b131034200c4803281480c0c900340e0308642d641201103000380b0a0f848100070208000500140b0342c01700082083c040c0e40281c000304100d403a40c0c440d4880034462820030f0f03600841e2130b10804680740c2444013440d100c3c1e10868280c4030350243c0e08089408031010702001c00f040b075580b0b401c00b14603960b0900c2400e04043c1d06400409141c102286112118902441012001c000014040960350b07a4142940c0e000c07540100144503031078803031030401e4443d00b080341d40649070a0f20800411443d840050381080c6504007040c0303100860b02d8082d0014066000905c6a81440a021000c003d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 493541429 1250 493540179 493540189
    0xe040e030a02160905010b070807240204030c0f030c050904060f0c0c112d060405060c0102031e040206070f02030a140f12030c03010501030e0a060203090c040501082407020a02 77
    0x7042400700e601400c0c4524032845110180c1c841c0360000d03603016103008014000e140d01d0350100e624860700318414a40b52040c074908050400040b00c4814402010071644050707480058001c3c0c0162803040303100081881d00e490b01801c07944035902c4050031002e0440d000308460308100e1413042c0c002c4e028600115020301e91401c0d020a90329603145641c005074418817484280300e41c00d282c90303041e81411030b80034270440c4808822090280c0c900003c1440b1628645912145540d0502214010b00014101c15211010b00c0c40c2076000b5042164840e80e502d4003c0c442078081500c03003c00511940d0700424160811a564403005466a004007049070036105581e96500850302080c11000d002407000010a8084821001e0074184031403015443c0c0224024000e0001000d51740c01a24151782c800e02e00003071200781564089207040c8040309c0180003d840013052103e0580041468039880c4403d0300c080c007290f60f884804950391b00102c580350928044413102c02c20301c81c001e844801d41208040c8103da440310f4403500014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 493542679 1250 493541429 493541437
    0x509032505040c050307140c070e01240801080a06020d180b0a061202131808040e060102071706160e100504030213020c070b0c0111040801020d1d0a030e040e03 70
    0x8503818411041008107280500030710409422528025095060444000d0003400d0910b1001903180c001141115102508121650003801004c404c21841e581d15004643c010f01c40762113101d01e8040c541c1d401d55020b8007800f1180d0488503114001e00504000c0d46441d4000c4d0010802c0c1740c1035136190107000302e0000e10004800040c43c003884545025041000300c0404569856018800285480e4800c00250365400602440c4220032007011030039800041c220044800300f4100180220030100340461842d1918035807501c5902c080c2c0840b514561560800c144503a000c455100300c2d80e2200001885c00000386401711020030250901d000903005100020f40e550340c1043c0d40c0e17000144042420025450161151042901f1820b411480d041c0000d540035100c0c0700b0350003020005e5a0008407a00c04030002d5100303800204045514545940d00da0f69068003035400154031024050410b05c154404d05011400100c41900c500c0c000c0400035007075034054800c003009561790340d8071960350b20205880400c240024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 493543929 1250 493542679 493542733
    0x507050f031c0509130c08101802030901060306020a0906020d170408160210030e06150a0b181306080d0816110304050307030f1a0103030905011b050f070512010b06030601050903 78
    0x70031606ca0f030301c0b001441c07110010070b088811241e443d400c10060320074038500100300300d80810242c0d581e030f951003496000d042f0b954001001c0f28400a043ea410a50041115054440d80c0e801c1d070705802d2250300c080700c680072401c621084100100001c60002030355000200084030221460525040080c0c001450b0005031400d0803000c03a03141c0303c800181460500030f56030f1110b0000c402d04107070680c0ba40407a005441d00d00400220600026894040c2115107048000407980100440202024009210081c00307035031041d107100348145403d0404180c0122148c901c10454502425041c0b81c0c1c44104840040c5544903102c041d0004210200d1241c03800d2121001440c06429054100030a80c90408161880c0035040c0424a6140c001440001d40c0840c00f00b044036001d20b00314003d1900010904880d44e43c081d401825440342c1012560003e102180101c101c1d0784c1182c1820480ca0b41e210a03600ba030350703850440d13680804204001180c030360080000d401806406000c035440c1c00c2022041c422002110030074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 493545179 1250 493543929 493543931
    0x121e01050115030615080601180308070209090c0d061d030c03030114180a0f1103100302040c090e04020909120c0c0f0402040b0a03090602090a0e040507050f031c050913 74
    0x42c404a0070381c4000c9040c1001914041021a01c2d10781030303904001c00321005008106011021580d01d17881042c1050781c0840b01050707000d003d40c0d24036144415601c005c03000c90042154800140c130003100031401c03030709a400160082d055400b03261341c3c0100504141882429034016200d16201e0150204042c0211041e44d00003995294100480301321402ca44502c410b1042c401c102c4a4282012081e401580144000d00003150b104003d810040150084540c80d009191002c010003084180c5c000303002084900a460801201c4640c15040741c1c80e450300d0141c141c1005045010900606240604a62014500040c0d40845414800707c110b5039000e40d035040c5695000c1c847e8400d07a8500034121042e900011a001c42c80c0528060000100340a4161072405069980c000315080c0100c0783c0403a580320300010403440c03840f5129601c3d810740c41c106480070b640303610481c1d01c04141418809030100301358034001d00900d491307900d032503c9a607038003c4c00074070f9002c006062009412070385502c00d000b04844030781a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 493546429 1250 493545179 493545181
    0x5040201140714060105030a0f110f0d0501051b03090d0503041a040b011703310b03010b1b0a052d01060e06100f092303060f061309050606121e0105 65
    0x1200f01d03e8070006811003446900b103400390400252202c900300e80c1d45035001303103a0b0200b010990005060f0542c188403141e040b8210b50b2682c020840d06520440c403c0180f00000b901c0f40ea2680000c0c4664042100c1d034181903800380074441d81c1240a07002543e0b000b48154032064003c000c60850127402041070f14212403641c7c12800501c942005000f181d085a00c4200045003030003070303d50303101160440c2c251102462150316440610025110b1040c030703010b001803402056a0356911a25612244c2c000780038581d03901204010000b15120101f03a5001c603a8226004010f00183c004036001d10101490800e03401c0802d210518401d8442070080b90001e02c1072401d080e190385409024064850482442e140c204510350340324401d415003154903403050742c100f102040c004c1c070302d100b00c40790350500445c80160b4107116075000c009411113400e5903903200b29000d490401403030300020341304810f95040500040803a003100000460605011018803000e01b0b0182c01c980ba0813864220f8465403041c220400320040c0d4443d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 493547679 1250 493546429 493546463
    0x16060603300302070f02010804050c19080106080c030d081305010c1d06030603120a0c0507080105011a03070203030127020d050901060f06021c0306050306071107140d0204050402011407 81
    0x103032a001c0300c0c2a420305501c0c0c4142030352101c000d0901004000d040c000f000010805200381001651010311000d072020a490040c0d040b10a8640d585100d80c80a81d070a00e000450305d61404035407141d40880c080d00030502d401d2902c200740e909840007414510110500401c61021900034001c04031202415146d403514100c6200c408150501402d800a000d400d00700280503213614001001500545000203654446050050860740c068200c00081c01600c01d10301c010a81c104c040d40180d04071118100d03151402ca017803600c404000c1c00101e4071100560070034801000071984000b20b071940000050158600c0d6030360301082004907080003411024403a5558104114200d0034030030070020703042c02e4000581051510300d0096560903002d0288101a07244240507051741d0203034201c4005010002c050780d40902d00060700402c08040144441014410b0b81d1000035021080602d07000108030240c5403c07204811502400090a4050f100301d042056114281010042010160407024418114407901a41c19 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 493548929 1250 493547679 493547753
    0x130213060516060c050d150f080f0d05180a150908010203090a060b06070f15061401050421021c06050105120d08101a030412030e0316060603 62
    0xd0308040300303102080080d00e12030b800760898000c02c90f50001002c100301c020081c045566010710719007034042c10304008004005040841040d000e94402c0303180c0d070024556400c0c80e240d40d05494519083d440d04866003140d1103611440040403900300700c80c043c40c030902848001c02d80c60314155202013280f10585d00d41d40d048540c400b0b0120020070020300254114105500a2601d400d10030800901c02caa58070812402d64035208160b1b80d405401c48040c0c2004485810107026892200380c40360074041c600341c00800ca4100c910f0403600840c6041e510241040d0420a0028001503500350f0489001a845400300042e91359040425101e1000e00059030580e407607161050030b6440c103070031241c4508003030201c4c080300361000146071858451601c5e02501d41e454440b10310400c0495034001e000700b404184a0500e2502440c80114021882009a058000c03060740084086801010743c0c0c03507042c1c01c00c00c590081d2000c00700342c1181150040b90005071266076540e640d1006580c0041c07413500d8410600200250a100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 493550179 1250 493548929 493548967
    0xf07170606011d04021608070303020306150403030f080414250b070503070f020a0906091e09020114181306030201020609070b070618060203090c0f10021b030c1302 72
    0x800c0c02d1201c81011080b2081d83e102149000c00c038080e0b5408203002d03500c4040d90b810401d003942c01c800104da9409286c03c00070065442121440e001d140307854004800c4080080456003100d404d0340d14502d401c01c81030300486080b800500141d824542002d801ca0f41003406022100b01010070030410580258001100340340c051080c0d12040003940203004171000302e6004012a40c015522a90101c08600c02d4800900c0300d14450f0072281890b49815004140c0d8001781e4090302400c1000b40d842e4000c0c111024a040c1174404202d030090020b0885142041140e1014018005960403c02e007041c00031019030121340c1d40214003607118130031604c0d01400c00a550b01840016080a080c1003e041c0c00c0e410441107aa02e41306441d0024280ca550b55103103041103160460302d1110550181e000d5540342441c0b010141c6c0d601e01918080d110b4540f550003061580742141c0300091084940d00684070b100744a2103890302e201d403a041e03140d0b0140202440420f0681e50a001c1e810b42e9040c00300016243c0307560b02038181e4648a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 493551429 1250 493550179 493550191
    0x50907030c050906090a0b12010e0a060501021903021c022103090a0f050102070804030f020a08060105100c0204090b04050a03031a0604030b090a08180312090a170f071706 75
    0x125011499442503801000c503480020140c804941c0c3d485040b0200e0006c03031540d440590b0148010030030168010b980f20189041b10100508103140b40c41e680c50707003011107000d8440d45d80540c3c40324084240003548803c50007240c50190040c0c401c03e0121140030210b400c0b04030350400040e04200da0140c4001d04601803940510002e052642c21890150701c065a00e03241c101014020f00b00c0e0941c0003040200c00d4045481060344a02c141d41c44a03641d240c0541d5031480b00c40224840c0d07240c0d52003c038142c000040e541e0b04071400244000c03d000711581081d208090844416038100c2d44880a4501007001c5426880c0110320070401002d210705603040007005c6130b022540172040d4505102aa240d01d50340d01080c0d030140e0f40c104460318a0341c0c850104143c40c0400ca090000c01e800e40220340d0300d162000810603140c5080098055070b0464070308040c2c00c40207100e17486000768410720b4840280b00e0580100064070541c040340e0100c400700040340c01c4d4103140c0240d80d4000d070b40070002c0803034603004081c09110b8170b50402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 493552679 1250 493551429 493551431
    0x302031005060306010605030405010e1e0d0804020901140402130608180c0d0b09010e0a03050d06050406030f0f03090b030a02030a0c0f02100e071706040b0106090b1218061005090703 80
    0x81040702c0001e84a00040c07080c1c108000000c004501405020351059540c4104441115800801038200c03907143d001c2c2007401881406030b80107401c1c409000320200c600c142d500509081c0540c0c28070407080200c240c203000e030390f8116600340001002100701902200240403251078510051400104441146408002c0b428031904902103c01ea1030b16111150b2509540c010300395001940d41d00080c034010a031120703000071244030318520385092640080c001d0181c11203403a03080c01144e4881042c0820b652061000600d03101c2e80d52800d134040317100700032443da44a01c64036005007081d55070701d150f07171468106655920b0082e600009220044186115400da030150f28100121031042e41500603456014107220b908030700340c648010184200003404102d0242800700c14211000d8020640a5680c0504590032546210141d001080e100d000308034079070884440c82c102500e0952010180b84c00040d001c1e00408180410700500112440e042c41070608c107162801c01001c05a14081c1084001c610280800d8149 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 493553929 1250 493552679 493552681
    0x7060f0c02060d091e08180f100801051905011202090402090a1e050f010e09040c050d05060a14010b04030f020f090a022a100902060706090312060503121804060e0705040302031005 79
    0x15440300545148020307204001107c65040008980c0740a4048007041c2e00c50343c071b41205c480e00c1c0c0d0000381d0681618015140101b11f891000d16a0500c05a0790007083e000c100c91b4076100e070264540741c0041112071000b500250a060101c00400c02111064202020000c550302c1100030303124403e81c071040108000c0750700c01203805a1400280102941500e400d000f1580d500001c0c00707011200e0071007001000042c00c019201c9480c1c0c14030795268107054400007001402d05401790005800601c2e6607050310003000806180a29640d2130402c0c0d124900f50807138000e0150081c03049150f4880c0301046c8a91817000f005030341d031101c801c11208960b6200400226844c240c4022940980c800642c14004160321200041d00d18114000690a03000710b0070300034040c5042c49010010564443e0581d900365401d40f42c140b0003183c58000305500c0300b002e06903403032410205215202c0d100c10b03c0c8414101181002d0400200541c03607881400035030300c00325102001b0903400141002141000c00c420080401590010042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 493555179 1250 493553929 493553933
    0x8150402010e01080a150b130e0f160207051c03030c02070b1912090f1b032004021327020c0303010b0a1418090601080907060f0c02060d091e 62
    0x8500c0c0c1c03000d2030b60411800e40c0c00100b00e620740d0f5200800344c0030110035415540b41d440c0d002091540c0f03d000300d0040b00da0f025038000350740e03400035075014000c0b0015220b000c1c550303032440e281c003103100303604281c90701140b15040c4002099110302e42c0b807100144c041400c42c4001c0503241405001e58040d840100d04651140c1010044580c2c0301d4103440b1118180a484901000c401004481103080203c0203080d0500d80201c10081100c400c440b0000607102d00141c0c6445011403000c0504450310344000342060100c00c4565200d41c00307240d45101c101800520045c00c2419000304002000301640201013098008d9141e0f9403204c648603003c60140c01440410b5140c1400f000d1401d440f40010300c5520601800820352840680c041c4242100a000380001952102d011100c84000c0c40100c140c59070003880008080303801948101c420a104000310001802881e1504408480052204103641d0401a40020381d40c016512100180420308602d1804102410b146c186526003030704103852170303202501c140e0034600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 493556429 1250 493555179 493555187
    0x418061505040c2c1825140a03020d060b0304050106080c060408190302010207020909160e071e020c060705100e0307210302070609030305163906060e010815040201 72
    0x104607100c021100005202c10200c0c01c601a0518482000100d080c10010000c86c40000c20700f13408500200c91781d17441079140e000c4d9140c02c420044403281c40c904018101e1072078001c0d0001d1040c55203240b40010b2090b0307a24406410742c0c00a641c1200c00fa519a034003042070131010089004c0d40716007210058034041c50040c1050356485c0811804040d102021151002d060003075040d41c0c0da4a0f009005000e040ca04142c055803224a00448d401c00081144400b04d16a80e00c050054892002a00c1d1b0302c5c0f41c0c03082100a84030400b440030b1044114810580030940545070003010700381d0980b1540040220650030712202d82034403080380d40d102465006219040100e0022180107143c0d80b45040301030b02c40b982030782044000c0e01c144640549603030308140c002e50805030f060b8000c6206041e03680d4254074520400c0c104803965064461441d0070218002011400c541424054490009840307020640b5580c0c3c555685060344c0a0383e0240f11704401080040040300c1c0c00740082c200c0e001c800402d04015203029400a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 493557679 1250 493556429 493556477
    0x5040b090c0f210307120306080105060f04050612010e010c090806070906200109080c0613170a0e0a0801050907060c0b01060c02010c0c030503030612011a0418061505040c 75
    0xa803141003041e43d0301d0381d00c88869007020503080e24070082d00e07030b110310341c2c1411440c602014804034002450068001800d001c1842805c0c0a800700815490b156103012080101074000a00b24651100f1000b41034140113109105102d081c0d501c1e100081002000d48402811500c3d0700d6124440a8000740b04000b807035640100702000b624030500380482210851f401440310f1030030240001007550b10300001d620501c29250041c103c01c04504007200c040390b691400825000040140040c0000c840018850b4080313000e10141500b43d0103480c050b01d4400c0f81c01e000428a24559000440c165524400e00150440c180008404cd000e80d01b4498036111266441441c001c40511411040114a05180c0d0440e0300c104010a001e40c0c00810401c040c075242e0501ca0f859a0003540e61a12804c0046000700007020180141c030a0703503052643e160310f05620350080c480034294084d00d01030035128425001c40000d44030b105484004907034441040041d0f0901c2c00703210882d14149c0403a000e01c05821345400401900e40d85032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 493558929 1250 493557679 493557709
    0x90503060606161a161b020402090301092901170307030c0c1508070906030e070e0403030b060d23060907140f0a0c060b01171308090a0905040b090c 65
    0x10750340c884950850102155400e000100000351413a849503036220190341190090030b9041580001c5035911005590304e01c40c2c1e000c03a041c1991126102005490141c3c0a046c1032103000d4000b0605c400c80380d617040700c1caa0141d0200b04182d084080104905c0d42840440c0c2d007d425400d02d807804801441c005241d0368040c50500404002401c0005800c0140340c841d110014118083c21083c0881c2c4ac180c0501310b80c0d81140d480c400100d6071840094124442d0040300c10a1021102410340716042246c04066440000c2c01607050540302d40f41c0e00480d0b21142c00502100c3c0e450440041c0031220011203551040010f02c8600300c040c84501805001d40c2c030240041d800008500f00450f12040300550801c00d801150001000d117078010402c0301714030303030428500b11505116523001c201003004503005640c48180741001e000a0520035001988040991280c0a211402040e0141c02c0200131000130301c00c82143e0f04621500fa40b00c3c2c0c240010404581c10309038105403114013408440e003401000c151060000046 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 493560179 1250 493558929 493558939
    0xc0a0306050a0b120c030f0316060e0a140a03081014060a2c13050702150705040504050403050405041b1e03060503010e0f1209061c0f2405010905030606 67
    0x1042c0c5508041e48002905400509101c2503202945001138494100c0c00c0c0e99030003070080794190341203501c012040b68403203145c2111320310303403103600b500c0d22401800600303094080c1d80300e10b6403c800400e0a155140030a41c1500c4010000f0090600e001826014080c004c1000750011100078042242007400c05c1088240c10f072001c0e0b072940b04290046807490402200004c009400c1c40d55429004450b8036590b884030025136045d410001d84001c0c0c80d0441e50101e807100c2c0160040b01e10846403800801c00340c3d070401b6803880c02c1806c10342c072400041c080301d8055030100c020900c0024104041d0030302d40500c000c020680240c032441c00c042c145014000714504407120700c10f182c0110200540034041d03841b030405814050001c1004604201220340d461081440500081c4204c41d40c80c00100d10204c200c48081102801190801134048640c403429205000560f10198030341d01c1540c02c441d4544942c0d101275003500107410b0650745810081c401c0d01c00c1608010304000f20780c8000c2c400da85000809030741010095803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 493561429 1250 493560179 493560181
    0x3210807120f1d100c05090d0b040203030c030d05071b03170c120a020a020f03070c140619030903110313051915030c030f0603320703050307060e0c0a030605 69
    0x10711040205282111034400807030340066030a0202c00004c1581d0640e0002c0c80402003404491010350380c0c0c0c0683c8000c0e40d0721000c4042103030002903490f04800d4120384041c00300e9041c140b41310009401c64000f6168404001d81c0c81003000720140d4061111101c0030540b41c141e40718078800c0e490042150f0700034104004010b0341280822001c41c2c640c000c0360300a4440c01c410340e000c1d080c0116114080e501c40101d80d17005201d03081b08800e80f40ca0201c102c6944a03440302c074030281146000030f064590700007815113642c019130510003440303010114804596160340942e0001041c035120310b4042c0c2001e012000c41141640b052207000038080c5002d00d40001d42c0c0007151a4581c0700c0603650301200d034000300c2d0000e0002620980340400b140b5015000701501c080152070030302a400031005640f04a074464400501103522070400390107000c2c02021095660440d2a1800200b280c40c510f01504c1c01520344d1044a0700d600c00600241404002e1040c016000703000b40203000021141000503420b2205400041d1030180d13158 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 493562679 1250 493561429 493561451
    0xf09060c060518120301031527050a140f0607021f1d1606030501080604020108010506070c091e1a100f09030b0a06180902090a02130f0321080712 64
    0x3090b01114003c141e04845a034007100c01c0c0c881c1e2941081c44110b600348214510a03805500c2c1c2e002d03088182880f5014881400c0021018400006a1401c25201c500404409101181900203030b075940b4a000401040c52030f658040d00e40c074003000200145d046400a1041c2d0101c1220033980d44001a1148400300b014194000400440d907011060301c4818880d03110501c103003500980200c4225040c030b89003080140c1e610417025494080032a0000e000500ca900148003525101c006400c41c94010900350700910384440381c20003120811100d4400b0404840021400201140112254015001c20181c00141164045040c1608a0440e9020700401400c80e4501c03d2288103820000c6410040400107030802c401035000415203030182803030f40004005042d000f143c4a010318200d45a001d000c10606070745001c0041d00940101d12100c100007002100080c5080004400e24083e5004081c1c150800c40902c180c82032000e800b260710300600105004000206401181e804002c4004010200d00b081d412 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 493563929 1250 493562679 493562701
    0x91e0d030e0f0d0f11070b0a1412010609050324061203130b1305100207030201030b040e0601090b03010c11191a0709090623060901030e060405060402010f09060c0605 73
    0x405000640c0c483e034807500204a0344000e002e4000241d540f1061207040030204000d1320389916000d01643e454080104c2041d4903c6801d40070010031207152030600b040080c81240000324001e074018400181d10b4030084c8283c3c6014080200c208202102e0307800c800c116081d20072550903005142030f1042c02500000440078038240101e8200074449030300e00d540f542c0c490400342016001201d100e401800340300000f081034140555280090b41b0b85070014092545564011406030105901290301b1548408000000540411085020385290600811901d800a05260844000c181c1d4201003280c00d0004c08000640490b2a49907d1070300c290303800145c64141401c5641c01c400340040214610840c0030006a02e92000041054801413072043c000300d0360f00d125052030701507040c201d0250b5281c50403164006280990040061100605021860518120385942840030854040e54113401240801046607840048441c121105040c800c800741d041c01c2004289100400307000380101c0c8c0e120040703a000702d20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 493565179 1250 493563929 493563943
    0xc0615010c0b16080c04060834020105180c060d050a0207020a060c050f062211101107052b1a011d01080106050f09070302160605091e0d030e 62
    0x12a66880c0b240c00c045401c01c0c0380042880c4407038001020400840c4a4615034003c550032141300d5a02d04003162284800150924071443c980300d41d22040d0320381c01402c80402a07640c03c10807240d8000040f6403900e84454032242040c140c60400a42040d044c07444035035100010341d8071031480712000190356a64050440700920031a44040d522404540c400030b003c0b940110120b5005109006807001401c19003031041d40d0350700645841209500041c5045055040e40e00703070713400300b41c003521000c040007076008041000c00418143c030200044200a140c4841d110800000b00184015614003904106040080c815800d1403144c0030520801451003805110040c1d00402c0c0400004040501b0395a403200640c03800c107047d0304407540c10a0500c000161005062081c40d086400203031000c910038808004206c01000020105403d2560a100280b0703500c141065012038648112800111f50a1450015140c41d070304900b00e000c1ca07504440c80c14120307030b0f002c100090905070600b0007241e5520a0030800c1d0401207 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 493566429 1250 493565179 493565183
    0x1503060f0311030c0f0a05060f070804060206090d020a0308010909080705060708060a1403030d0c02031201090c08011e091e110301030c062d11010f0504020301110c0615010c 76
    0x203a40e14020052101e0740d292518604021402c480c0c0000780002400488042e100b12154454080c44040241342482c40c01400d02e40409481c440c03401c80c1c20b40d0b414400e81c00603007018006038040000c01c21003060401101107040c4890001744240b0016079401441d400050168401d9152a40c480d00308118482040e10340c220703400000d4505034a040c0701c00410422044405600c1114075002c00200f51501c122480a103210180c0514507002e407222004d0003421034440000114030080040320b11401042c40020f0103010b0800001c10700a8040c3c0d001410154181c110180c010541d503503500d60321003500040c1742255480003020964100c00040011400c1c0201182c6c0744841c00d01c90710600c2001d40b13000440c10303640714070486203006848120841e25818561441d18060a80071604c02c0c5221542c01c46091082051925003411a50f82c400c26003034a800300c81c00c503072168541003408110b2800303016010802d83e181380140d0600c10151b041300d54030380c000ba241002104592030321034042d0b44220b0b081b8048076 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 493567679 1250 493566429 493566449
    0x2c0115080a150f0f020a0201090201080604020a020c0f010e0d050307060c0f05220b0a0824010c0305160c0e07020601080c13090215120103150b010c03080603070512030a0206100b04150306 82
    0x34503a41b401901034008403200301c0c001002040041c80d00d1030a07200b0b4558441040d0f00800100c2c07000c10038407103140709420081d414001c07034541e503010b03544d60b450014814034841c1001d07580f22121840c1c00b02c1516a02c484603818000800214042a517000007903450b048103111014140d00c115842d02c002c80c01c003c0e003145201100010381e0980b85604103004500449100c059081c04144040c01504180f603000045400119088000e0010a00c05d0340a40003009441c400c0c034061940c940d036018103071651940101c210b41261000c1185280c6c043c0a120300400081d170140c00c24002107000034281110101082c1101e0365280c500b0381c15900c4000351031030082c0c4c1244189a80b904807420400109000344401c5908459500220341d0250346806960252103068607032007203c12165030156a1000024030650b01449103a00005140d40c441e200842100c003100040c40d5200b502600007401d10702c0050000e03408924002003000a010030004403000ca550b0003c0104821400440480c0640f03540e50099901d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 493568929 1250 493567679 493567687
    0xf1c020406030512090f0d020a0512030d050a1b0f0203030a0e01110c01140a020f04050f1212030a0c110a0305032508060108070c05070303032c0115080a150f0f02 71
    0x131030b03031244c02420030610442d60044850803000800118010000c07000f5000f00d03e0903410051803c00d03400443c0040c1c40d0001b50381c1401c03100c100c1e60085490886c0e034070321150346070700c42d102d40c0304400d000c102c3c8409000d20703208800005540020350341c3c1c0300c054001c104c0142d8481030300403180400c0d4450b000504009000581da08062a107a034081d105041c4207051510409011071580741032132003203800001324500d44500f410700c0c20081040b254056200e00390041c4001d2032060105174180628048003c90301d049035100d0801602c280202c4400000351000c1c4101144a903980190024844034495413602c0c000d5074945d103019140040291818000c8038411800c404c8103801c07a0003c0d02a48110f07401c3e41c905a0990b1603d0040b43c5650392620003808a4000341070500100c0c0c881e0300036608030703c1c107400b00c200b080d0039505003c0f07001641600c14a0042e5540c0a0140c080024031340000001c000440082c04003c00944030541000215007080e0700d80e40d926803030074921a24503007001401c1442401c0854807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 493570179 1250 493568929 493568953
    0x7050d0510061508060105070c09050708090d020a080d05070c0503191b081c23100e09030d0c0912150c02010606050a0507080f0f0c06060f1c0204060305 67
    0x40c66020901d00d668603400c05030b020a10040c003806420354070710250744003c403548911006540c160720086003503400390800700011540000ca802200e01451142d99a00440d01c2c10441c2a8200180c80f619401150007802e07100020a1841054504c004c000520008242d11001c20a68403100b030b40d00018498000031805103c40d04440c1c03c05c0715001c242c1e46440ba8078800d8222680000f80039040000c000e0380003888840d003030402141c125148200c4910300041d40007803881112500100c241c402c450721800340000c00010303c941d2441c0d9401410b070240985814103001040f507449004a403260385242c2c0c0d881000591041c42110150000c0a0010f0703281c0301781465040c20301c02c03800500e03d0200114100071140e0003c2d841446144101c035016500c90342000d04401080f01e69a000410580d40c0391000d0003200304a21810b40108240c40c4804441a40c0701c0314040c0c1681800d000411652042154545040d0b0548683c030b0701a4880d01c807006515035002075440003c0081c900d607040074203944201c00f4a501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 493571429 1250 493570179 493570183
    0x6020303040506010e04020d120e041a0111010c090b03040f1208150d02090a020903120a0309020307060e030607120f05040507082109090403090e1509060906030a0209070207050d05 79
    0x4040c1c0d00030403c0c0c1d0307503580c0c0341c40d01c981022101340c40c0250000340380241e00b40030132883c1c1d242060801403480c0c0b071604848a0750000d030654048010144030145a41c03c04075043da0041c0010b968650139800910040c04948005001ca14451260f54105600000003808101720005480311280e03028101d403110500303500c0001d20300d18040342c8070b030140304040c800d219092404d00140402190b000308800d0303080c0d4844003414042d4010501d41ea41501c5030800b0349640d0261503016100b0b480e9190b40018030718041e401018a004a20392052040c418014010801c50310042049903200e2494103080400081e03018440c0010300805800c0d1000348d1074a0140020000049446411260690100c840241c491280080140d000c00c210000540e02080385294504040e02c0c5103034400d0003824004000c5a44640124a00c4021034410006c281c01440910451600c070242070f030000000d0f200041103140c2600403d544880025010344140245000501524400c0040602800c00035005100130031091803c02d03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 493572679 1250 493571429 493571431
    0x50a050d021f09151b06152d120503040918020603040606090509010c090e09030909010906080105151c02060c12041706090d181d0601090f0f06140c010606020303 71
    0x10001d1035120420f0100e1501c1821101c903134240c0c0e0307030b1182800a402d6590f017005040702d0f2a42c20080122000000340440c09641c4042e120682c076183c2490180900121040ca06c2d882c1c00103007000f0354420030310300850030002c190707000d881d00014002400f8403e400c403b800c00403207110003540600300104000400030b42c0c5e040141117800e200024005501d40c2585903003a107890413081c00020310f04600c2004130a4522180030382211941054914100c242004202c0d46002600564060b0b51600401c1104010900c9007940c40900ca040c0c00744c0c04e21407040003880c04520940140c0b0348080004c40e140a5549140803a8200580c0304125054003192150b01c0400d5001031040013003022034803100200310000450341134411900070380502603182004405490314100c0a80d05202c0c940c58250100700c40001e501c0700044512090211682450010f000500380c85840e004201980e8448400300300301a0000c50000a560417420200c00c0003000e00d90f030700414003401c0d9a417041d030b40c200341000500c10380200c021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 493573929 1250 493572679 493572689
    0x615030e16300602030f071403131101020106180b040f02090d0f03030905070e01030227070c0317010b03270316030e090925050a050d021f09 62
    0x1481c84a4024a00c180c15041184506a640c091000c000a07003022418400c81c01c403954081000c0300d089058540004a8204858200961500300244074505402502d059201c1e0320000b5030620f140b41aa9071941006141030b0300814207031304c040705901103a00130340141c0302070040300e030380d20318207140c0e040007140034052940b6007500440c40e01040d12182e44841c000c60b2000761024009641400340c41c1d8a005410501907810340c1010340e50b02c903680004406011540c001d0809240044495056004000c0f012a030b0400e0381e0101d007030341440841c0c442401001d042d4032116500784884401c40c0c03803c1c2a04d66000c01548010b41c400010004140c0c500203002860140442e81c074003070320310784825a40050114020703040c2c5500b03600500c5401c2e007500b420386007101954440d143c0b14440201c82d07404540e002c1d0f02640c402c041a00b01505201b241d100c000d102d049100d2011030b50030001c520741000f1584503034540c060517000350203c4043c00c0a545946690184a4071200800407906030050302c0207020f18814060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 493575179 1250 493573929 493573933
    0x4020a0219121704020f010c03140d02030f0c090906040506130e0709060b0a02060c07030903050a0c030b06010c0b01050d020307030804060503150a03020315061c1407120c0605030702010615030e 85
    0x200700b140400003614184950b070b014203070900342d0011b0401510a43e00c2e8210171410032020300801307240106104003610500c90002000341c2c4a0034070f0100c5195240000b44408036201c0d040c020196203645210010790041070984001450307480d4400403840c0711410780b0340f135440715003014421052074000080c808100d030b06003202040f00700d03218402c910803481a0681e207030059104101003052840e42030020885c5030312a0a141304202e55a64445040001003d4140c800102104041086c040800e85140e400107091030250014001543c0c1e803c00087c040c01414012050b6160160854604010101c091600701c8042510340d5074070900140650b0040741d8100e10365000150001240c2401041d100560303500901811110100e8003c1c45041e00d00145410b80c45034035500070051100d074100540400d5405406c0c4481014440141e080c60310110390b02c9298038040d0075001c0c6002c04c16144000041c0c030701c14545680c1d01d450b24442240581030b181c000325251b0002c0b0200c00b0015406901a250f82e0301c064007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 493576429 1250 493575179 493575197
    0x2090d210509030d122304030f09150c080919140103020415030519020a0c06060503060108120d060f14031005090712020612040b010812040b0904020a021912 69
    0x46440d40502c0503500d4059001c4030751411901e0040140000da05140728000405180408031030722100c1e20b40e1036031070380746040506000c1030540c0315002c20790142c15410b0400026162515881c0151031010707600c401c1103484203024041003604400c032801668003d2a0103240c3c02034983c0c003980408144100740c540355641380030b14015400b90007900d0803604821000c903180764649a003a800751000400d9840055440041c0070241c400d81c1c40903180e00d4040356202003402206191420850b400c6070051882503115400412035080001422400e40038a0078505884030306a1105070003802c00354000c07481c61006464049002103003001620103010085040790300703104e5a40b0010089540540c2c2107001600101d4060011500f802e400700121032002e8641031034020702c914410b011190036901150f00e406201c2c0100a81a000c002c0c81c40503400d013994507440d040c54020450503d20074115100d000e80c0d004504890214024001d01c1d128147c084007488128056241240f004885900001c010407200350f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 493577679 1250 493576429 493576493
    0x90501260c030604030c11040509011a1801060e01050408060702031c090201090302091803190e0102070821070b040506061201060e0c1806070503040303122d02090d 72
    0x41c0c8210301d040050007a10403600e55860842d03c1000b40c03030056615032401c800140350317a00c840c800c040c400c2003030700000610703020103442c0407607040203000c50144941e030a410002c0003100407080c8181110b00746d04000000701e0074480142c41d02e010350f0344049a20b00822081011907600031008003030407111801c4011010940b50812800c030340286401a00080a004060005080000b075254202c424a02c0401035021120303c03442c6954001e40d07103441292900b15101d1403040d08070001004600007400074000c101d00749880c0903590464540031072460070b150300c4c4105400c9060821070b074065400142001981c038050078074940c7c500040d0b0784a030103000d8005110050810610481c01a0b803d000581c1c1d01c1906c5000064909400c054200411404101110600c954809004100070380c410405940c03078524506010b044a16204103041441d410311002091000c00c00070840e400303c1402c03800c500b000520180d04c0d8000d0041c4c64840741c01c0300803e60b090b01400505c600031380c00801c1e032180715820359040b1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 493578929 1250 493577679 493577683
    0x2403080301080c01051603030504080f0a021b0909100c14070807170412060e01022a0d0206010605031303020a1211060c04030308220c0b0d0506010f02101509050126 72
    0x1002da480c0d00c021b10981d40000a4880d800c001d42190090b40c84a04000e01585d203040c440d80015010300c0983e00018054502524042e10502c10759011140311056107880001a510b85d5800b04a014240d07940b40002c00603a8012980a84d00c1e00403140001d89442903031400707200380d0344400010f54402448506c0c0400507140c803c03c890075034880700c4003828a02c1041e501c1c9005491603504d00704495400b8400c036903504a11101c0060395000001070028040a0400740c0c0e42040400c203070101c110740080b001406010f030031004a03504804071112003503045003103081c22400d2080d151002413201d80f6249290094550002c580c4000c0300440e03041d1800342c2c403000440c003040d20880c40014080f441c45000589584a08481810104100f074941d07c420361103a511072411954540050b080c1070b90200300303585151101d2081d00e81c481400e0a002c6c5203004028800b80d540c034a000340c8036004a0b11841070780c040030258400240245446d0005200c50358650134544001c01c0c5442c0110084c040d1074003912084400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 493580179 1250 493578929 493578937
    0x140f0a08060d02010210092409120203030609180f012901020a050c040519090308270703150b060d240f1a04030b0a060501030e030901080a2403080301080c0105 70
    0xc145c00070112001c11410810140c070010301c0a4880105107481807415410180c410301d80c9466031100040c2e221100c2c41c0c40c07070400152407607040440d4400e00c00c0050f5034545d0b034031030703600000c0c501e012102504210b8030742460f120b0f541c040c0c0c00c0c20754208564007100340518030342240c0c500341c001641c40100b5906401240d850f00031701005420359002c03107000358190500c1c4c0d0242d50419030900e2108034003001d4151a10030341e4140c03e0201c0008404501308031001081617010b01440351000940351001205540e03480c2e0300c8201e0700015181000c42e206001e204003ea0f44140075001c4060145521030f00460009030040a803098900d919000f15407582c0c2269088450315001e44207000c0c0e002c4510380c1413a005080b0034007010304061206000300300c048046401204040d10030b500307121010034010f044c0300004041d0b5100d40244150755100340710300d0b0800e0307810641c2c59a205405910014001c00311008980c400e9185100748500c0c03104503180802485440d0000b141685c84034030450305170224440c0110390500c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 493581429 1250 493580179 493580183
    0x703021311091512090303060a0e0402011e05090d0803100f0602030a0c050a06091b0f06210b0d05060405060108060c25060e010903110a0c15140f0a08060d 68
    0x78041240e012640f03080c04454101256400849040c9080845180d141d1030094070145066800482003080a103070074020304010308080f541c110014100b540c0040c06584080c2107070220741e51058041d91003684600107035200f04030020160018004142005038a0f5482503809120740c1460590105244d0703049400041200c00642c01186011010003088500c40540b40080b606406040321080200780240076152424ac002d503c0c5c840c0e03100e501d44000034144500d90048071454040300013000000c5c4c1100e0009043c6041000f01900c0d8040303000c3c404c00502000030b155511082c0040f01d201030020000d100e52085120308129510780e601c0759004c651307804085032601070120007041117010b140b0007140c6813a842e210042546103002815a580302c203a94001441002c2607568500752000e01d1350101c004a14101100054861150782d41c4031242ca01440d170056040c3c0840b94480304000078860010600240c0d41202501d172603064224001c2c0c8142d0003501c5410001e03400700d012989515203076140c094415 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 493582679 1250 493581429 493581461
    0x10b0415150207090c030209100306080c060f0f0403050a020a081f02070602190302090310050411091812090111030a0c1209210320030702010c080906070507030213 72
    0x5107803020000108041c4901d0300118015200d0003c0c00c441c0501a036418400107840140e2148941d03014056008501c4001c0700c10141051400c104104020480c0818400305945403a540c01084405910a02c039000d0f140d41900000540042400030100d0240d442c6e501c200c84c00440c460b03850541c01e6427031140c031080719822541c1c042c0407a60106264020020f040c840c0b200513052184a907000740350380040703419040111b60006050300d510704e0140681902003141c04020401801c058030385031000045103429602403800180880c00c540130304040c05c800c03c0301e000212440560b50102c1311503503410901c800e501042900046503400074010054076502c40055440d28804205601d076200304500440441050240c12600484d0301d02c6000d04a150035507045180c0c0240800c2440d00170005004071100e64040c6a0304200404902004030445410f07540920313141c0f03506115400d0103103c510980b0b03030352079200f0000030b00310040000100300e80003142c0c002c032610409008030310340b0f00342034a1103901020b10701 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 493583929 1250 493582679 493582721
    0x2070212070f062607020f0d02010c021b0604050d060605040b121b0103060f0b04080f0708030d0f140a05060102120306030a06110d06081501080d09060521070c0203010b04 75
    0x684102c1043c0407014900c01c0e1801c02c084c0d10b900c0b00345550702c00e030380c0c54005030400e8203001d5450781c00300204504034020384005c2020003004140251948030000b903500e1100c10540c880e407102e07500e0350141ca028010040000080034528a4514014201807113114041ca06180d000c960b2803030b01d100682c100036080b00150a4095143e01502c00d6030a1141500b4140341d034489010400400070010000600320741e50400380d4071820b0611030b919040440e000c1040682c841c101c01c2c02402c0001c0140d60b44c03a15000800304001440c0350082000c0c0c290130340c00550451a500400c1907900d40354201074080c8200307809079400c0c03040d0b039540360300244003c88440d6050b61010b0610350001382e13a81d00c0301c200d604004e50341e1130509190300c01c07250a80301241e101c80c00300d074880025081c0d42c2a0000c0607a006107080802031034207480e90080039200c06114071920b002d001d0042284184601e40941c6501e12825071a191031607460000006840c0040314a001ea01135032802e2030310103150502d03110b40c00ca5401d00300040001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 493585179 1250 493583929 493583939
    0x6010807290301060503060307091b020601050d0c0b25030e01110c0603061306031502030906100501020a08030916060513230d02190815090a03210e0307050102070212070f 75
    0x4942d0025190f648c00d817044810002c0d24051522541c1c00880850300354445610491a00078641074041c1c01c10b6200704855400d20001500c5130002c641142e105a03e10b907202c01c80385880444c0e41343d0000c111461414400f01540030180e21000140c07004200762500c0d09072110900007242d4520500c00402e0b00a40c04101040061400c122000d04018004801040d110b440703984008014100c0e18103000e0442e000b20900454070f20502c038580d40b042c225003840010500d4140000c3d600d000c1980050004c03400000401e0100005200c040d000f10486902521116900e0000030104d5114200060203000798000c040b5540c4240c0b6526484404c1d5a0340e01c60a160341d0301c0805c090001034502c100d9005400c40d0000d03074105000d01ca01001804014003401103045400d407040c484450041034030a060f004211710f8000207070843d29039480c4524100c0e0b203804c110351655403100100a0301e4981c0314180700c0071a00d8810400150000c0c009a80b0a0318404080310030780c04082d60382e00d414041c45c0280351040d101444 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 493586429 1250 493585179 493585187
    0x3080904020c0a11041815090204061d0a0501050609030a17090d080405030c1f0e030f100509120403030903030f030f02040308090f011814060c0601080729030106 71
    0xa141000910040c034244140c40042d02c1c00c0241141100c0480c0302c82a00b080710714191046600f01c031043c801800241074295a6041a00d00990b4442d01c2241c0d110060000d54039507510040140401310884404907808030080520b07140221003401c40350741081c0011501c5d0503c08103440a01d6400b4005001c0f10720250b03920036a802c2c2500c00d00414038002e0003003003803903541d03000380d030b021503005007445a0758905003800c0c1801e19200c40041030007004011510895460302901070b10080c0c40d0303441c003003096149500000707040c10f6080d4040c00b11441074048a94400c503056200300d00910740c0700211345c590799400c410381c00300f40034a00c4068045061400d0800120b8050b60b0700c0c0080707464a190010f08183c6000c003442c100d82054005541f40c8201080b8503005041c01100c0071052642420100d9000b0311001d1406240010b0703009100a6002a26140801e602c8500942c1c0c81c450036941074403800d43e1111211552052503108800741c01c20b9050070180740c00c0d928003002c9541010303184d20354610380c00c0c800241c7d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 493587679 1250 493586429 493586437
    0x421020c040b1e060d0f0504080a12090804120f0206030709050f0d021f0e030a0c090c1107062001020415020607080c030f0910150f0504050603031912090312060b12010308 75
    0x2545d1344503c400c02415040e44101c2c1d03c50703442010b002c2d4035031421240003803489140d954a100c1d081e2406100c4400b06a000043c0c400300c2c0c000445610300c500d59490c2840140643e00402508140e02000740f210007500b2081e40c0003940c400b500c41403c4000000c00308581032441c4400a9008820060702480c55101200240790300c10f16130901041041c4604086407030030f07109003000d13504400d5911003030091100a0013904100c5806107000c03001200c554030840c1d159100c42c4980001e0010b4017182040c0a006019100c803031985010003192501ea84d840c405121064082c3d02e100180100400a0305c04e134090490540034400d4148420b0070b56450b06150308515030060032101061240313a0b1001c0341198580580f1001c51424a4406060742c80e0070307000013442e030303032070300601c0c451802c050800c20b580d24008213481ea241e080d02c0c00c4103a1202a10400d41da0224040c8001008504003141c4406054128450700e81410b2141e40402c0304680e141144c20b014020303410301c020a04450b000400118001402074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 493588929 1250 493587679 493587697
    0xa050c1f0b0a1410181511030316030221040803040c0501050a050301031b0e07020d200c040b010e09070914090f0412050f1c0e070806010b030421020c040b1e06 70
    0x4001782015001040004400f180d1104c981c14009042c51410131f68082240302e0741802c0d50b001582141405c441040000301103c120108059021513007200994071203103046100b8a801c94090140c1c14241040e00d00c2e03510499040d280402e260b1800aa103511480848001c501d103965a81e05503401e540c0e60a80741c04901005041d0f0346495070780400c90b0100945a640201c2041d0001c2c000300049440c0902503072030201d185a03500003047e8480c1c2002e400070a420444160854000454440c0107006807001d501d41040f0039000034044040288440d00703c044617080d0b4203074540c2e0301a0080a8410400c80300c3c021500518466003020200b03001402114684950714110705041d400e003001c01069070040d13008000c0401c0c0d60f000101d402c20034030321280715440500f5480405060b61030b04008110f49c9d81e02c0184581c02400400000080a004101044031903c8551242e44204810740c0000250741c0c044940c000d91180380381c108001042d15145425040244840d000030042208072410006607402020305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 493590179 1250 493588929 493588937
    0x4080a050d0c0221030112031404031b0303030b150d0207020f101706040c1e020c0402030a0b1804051207020f121608030405060405060a050c1f0b0a1410 67
    0x70301078002003409001c015407072690007490082244469441e6903180800340c43c081d42c80810061008040140c03c000d18030343c143c1041c0c0300242d80b810b101c4207a0300c22640b0142c070744007000742c101c0710154050b642d2104682c0265820f120501c400800c01081502441956040000400244410b5903ca80151801e903000500d135180b140c5042c40030810f415019030500f80010f02c2c03040e407100821450003202d07411081c2902e007008840c0f03004001030b2440340d11150380066031440010a003100c520820421340d80d080042c2c810b43d1203007018842d981c0588006801d0074030079964a5a940f50345030078040c03800c0c8116000300c010580b0506440780d140b410740c05070b0030a030703081017214106c140c064031110115038681d20008005c01000d040a000071150f507a40d5040741032507030400c020400c299501c0300c2c01e640c1590400c9560302d580e05803c002c140c03030911841c001580d0034010301400111582014801211101d01601c0a210f41c0304003004101032424607004a0900740b8041507190035504020000012030101424 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 493591429 1250 493590179 493590187
    0xf0312120f05061c050a06110c1515010c03020705090703020408011806050c030f040305090103090b0f060a050303040807090924091b030b0414210d0501120b04080a05 73
    0x414401540e007840c45a0001c6601c0300180030403420b180d40c0012041e00d640700d041c8844442ca581d040e4880c0c034104005001c0503240d40c290404820f40c6011204140d00f504e045a0307a00d8604e9000400303400c42101c801c900a0030303807110360209500800840d030245605502509030b4074100000c014011402400c01707020194244001314134400248528290300c4051100d0200000c0c00b454200c09540000f45811900a000c2c41803110102c01010a076400c40c2e8103050441d00c5018400040b401000c652300e014081e0117218040c018200c90030b91005000e441c042c0d802c00d101079240e03014180d492140b03114152036135005800401040d1500d80c000f11010b8800d000d08030041c03260003020301012900c80c208409465407420302000b0810804d4985c002d0008260b50080018903546a0103c031f102c0040003d080d1480249002840031000e214603020400d100d2200041600215518078540c1c0041115103c01e6180000114500900b0002480320f21303408004624981c0d60f40d950300d82c094000501480900c030044c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 493592679 1250 493591429 493591457
    0xe0c03010204080606130207120309050a020a030f050d08160c0204020f031608060a0609090203070306030b010b0a02060a111c0e060a02030603160303050d1505100305011d010f0312 79
    0xc0014070040081000a10b00c1d42085c2c1d04104440400c50042c640052041102d000058141c04070190301180074280052030350031604060382459503905000f50f1040e0709071004000c000030025100490740c0510100c50441ca0501c90039a001c4034207807205132881d4400c01110341c00e9031040b840c00300130f14405800076003440d6446d0202e071084e40050310549650316815200c1d507030282c1d1000800d54489411128070b080c8910b8002d000e0406480340c0141080b56800100240701203010b5004140256032040301c03200c80390b946002003c010b401c9040141c0c010300414004c200c400d00c150291880f4034001da0301d158a020310700da90510403038040e140181d9440d80c03540c88100c10308034280f00481c41481c80380c0300940d43c1d1130a842014100302070030103072840341e003041042480030903841401d80740c8050750101d00040a1226043d000d041c54820b601040c0d000130030740c2040204070390680200d41220229240c01103d41c0d40f654000c24410000d001d0210031240410003000030807107050700c4807880986c42c284a2004c000c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 493593929 1250 493592679 493592681
    0xd09090b010212120711031303060b0d140d0e0303131502160f0f06080426091c06291e0607050106140f0a09020322060e061b0d0e0c0301 60
    0x2134100840420040b0810000e40d801041000403105e1820283d8030304140d000c240c054100380c034007028200a036038120707881594031500d0300c05003503075003003071a18848035816100340b940e0304031600c40d81c00000c040151880950a000040d2204e0840100c10302c155941072002c4001c1e9120308100c40e900718840c00c0205030807045e5411418026082640c02540103d06100011030707800c281b64896020450940d01700300128480c02c0700c07040241814490107400203c0383d0304680781e5004d0740385903da124810400050b03541942515401c0190300c0303200c0511010b00d01c404400040612945401050031084100100741c2c034125806044482e05007400790400c00200c3d01089960704110b0003156035a42d22101444821629080050054800c039001090082e246d4040341c1c810b4810f00c01d80b1070302a00807011411914041001380c20307071100e0142c002039082c050305124020744044900700200e4000c010210b00c401da400411080c10000c0150000e00d00b0220080a10003003800b41c181c80901d0041018820499500b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 493595179 1250 493593929 493593937
    0x61a160206030a06060f08070206070c02011e08040605010503030f07060504061d030c0f010509030a12060504020a0c0b071704080a14040b07060608070305070b1303080f0415020d09090b010212 84
    0x1d03030080080e00d85c2c10304c0c5000c1c3c658050203000a081c403544500f041031280e03002515661117021450300100c0d40006100603111241d24065410668095a804942c06648034182c54819405a00107202990381c03541810f84910070f4045107101442d0070440f150204215420150304240300c1d210000b11500d0480b0048000c485896050381d11340c00c00145441d61250421407000700300d16502c0200500e007060008240d84e0300c921241c040070700010015442e14010345900c44002032034007400940d607940c02000000c21040a045040b1045030600700421003403482041c9142c09030903808205509a1a142c44221050f04041c00c848100b000c211079081038440b03a00c01500c0217000c03c075006a1607000e01d142c06402e448003034220b042c6c6075000315000c0011a80021b6054200e41140d100160348400c1500a4011046aa0000f03000b048000424055141401c802001140d40d407014090002101810032a03c6403400d98400c0e00203000d194003880710008542c854041c1080c1401100c2c402c40020b1015502500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 493596429 1250 493595179 493595191
    0x20618030714040b0306151c0c06030914030310060309050a140607020f0604020a0509250e0a150c0809061e0406020c1903120e13060503070504061a16020603 69
    0x216140c0d41e060a0f003024061034076811000c03000f9011034600000c0901c40c6102d424901d074400e4481d44a0700e4000000c00b5000509240c00403c07018800d41c40c1c3e074001e00034098480c0c0c2261600510000d02c1e46025011040c0ca028141c9110400810f03445d003001240940f40b101c0b01510140241c07000030740041c610400c40c8280805034000b80c1010304d0804c201905250505c00314980315000001008010f80d1603101e4901680c4040316007052580341c0c15880c2c00c0980c90165040d0120811104944566402c5120441140001c44900352a191079452090141443d040b1500204098650b448002107480d0080c11500f04003800c840c0c20419881262002c205401e8015100914002020720080c0d42c148540c030202441503500008448034003640320001c08951001421038188507070f2200d2071510848030610030302d13030007001011003201c210009001810355106192284c030550f00001854181401800d003100c003004144401103030a40f00c1d080b1154401d01e985049170050070f0668006030b0310300e009140102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 493597679 1250 493596429 493596449
    0x10e01140a15081b0703080412110a08090a0b0903060402010e151303020901090c0f08040615080d030c031109040e0a0c0b030a060e2401110706020102090f100206040206180307 77
    0x824070200801c60500045107050510030300300171400109402c040343c0740c0c00651018000000c3c1c441e03064120fa460f24001e840790940e0044a5110062101201c0074040700f40317040f20100f606075960032000505100c0c20789401d400d60040e01c0000c002d980111228003400301d010304811007018140b06800c00603445041d9030314060340860340a10660402603001800f4000212080040c00b64041d000f4003c04603000c40401004415400101045480d4102480203200e18001e0500a615141801d480701420082d00300040c1c41c0c080760000c1c06200e40074940d400140c0554a914040300201840064444440000311512030011003100042d0300c0070481d801000c10130081512400d00280b203100352211944200356003c003003000c2c44841844044442400324a605c400c408441c986401039440d2120304814288034003401000050003074040d0000c080d449000c840c0c0c01407042c1c020080007501d00346c013400e050050380030400080041c2000c0005000b050764503c0890100c226060001e031510f45940c010207009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 493598929 1250 493597679 493597681
    0x7050111030c0c01060e0c0f0d020c03121e1005011808190b07030b09011520030301060311030405070905090708010e0d030609180b130819090b03010e01140a1508 71
    0x60f0020300c04c01c3c0c0a003d5402200c011402c4c1015002c503207000380c4c2100c2c49000000594210000c0c02c40e4115000b00002100f52529001c0019034010004000c0781d81d10244109207400c0e900388280003003814441c5014415041c8501c4c2484011115440c034540c0c02050412030040126020604103c07901060103e82454410020f062034801c51003803000d402882407506000d4603526558440048605407902d201000c80800c04000045441040c48003241000f640610030b205100a0040000d41c10303101c10b40c50610580300305480d13002a5100444014201e034105d4001400340c440d0f1034000b0750b0000410401c03501c0c4603171501d240c1400c444007540c40c43c4a0f54400040d888006030580290b90003010070610030820100610310407456104002002411851181d002480c480d085441808042c4e0300002d0183d00d40281401d201c0419030014407140204041c1a4001050b4041c0021030703040e07900f0100303080c200d64648924030443d21104555580d00410600303002c51103e1046881c0c84240960386c3c2d0310811 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 493600179 1250 493598929 493598947
    0x1020702031e0c15040906330c0b040b01080615060306060702010c02060a030f05130f0b09030d06120b06120d0c0f0206180910080c22140708150f0607050111030c 71
    0x890301b50341c0c042003101c0b2450008c9030644001c0c4214152004c10100008110302c0e0b040c000b1a0340340a405e400134211a0054284004d0141c4203049505075110710b0200c5202e51200c0b05066014006040d8a591204040000405a043c148041c05013984181002c0b500656280c0c00525940c010241c401c0010350364a641408141c0e081c01460b400280c18070b1500d801c070100e6101c0c0b01e03100c045904042c0013420304101080c0d940c00204115032a907080003400b04007a94a61100e40c154464008003035452620101c045801451303c4502003442a00c9400101000d244414094451030f0740340c40256240f40308540100c0142c1c0301c0300002c080d403501c8103254002034095803080021604002c4e104000602c1d9041080c444c901002a206042680484001d001603d29404c155030880c1900e0b01c0711201d5080c2071a411200103280721f00c600030302154803100801d42e0362000b451802110780001c141e004030b009415155a0801c18000c00c44113000d0000480e600405040316031241c5d00a40d4008100c0400081c1c1c0e8031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 493601429 1250 493600179 493600181
    0x4051c02270415090c05240406020d02011a01081603110d0509061302130f0608010e010e06151c03030e06011710090b06040b0d1e060b0301020702031e0c150409 70
    0x180b04032007102c04c010850003600c0d0304124071018000c00780591107134203602038000000c07511141c000000b00803403552951500c030300a4a0741d0001d1011009507003080103000f0440881e462504003450181d6170107480b5501c50640400c98100d0148807401d041d80e600340303507200e0045000240340d10a002d000105442c1132140b41c151900c80c4c0100894580054581c0c0c40e0300507a6400c8201e00202c8441c00d0200391540d26074000e82c001d101590062800e5844c10560f003c500c0e00641100368140241030560760240d0f952601c000311420500d411543c8610801c0d41091015202c0c82c01c101c40d54064500021003108041c15503140080a030440301e0403c0c45040002002801005007400c00404117000f40244c1030305640d004c200c00c0001d00034a1080380c407044000323315161030106502903a00810801400d20064110261400e1094030035a255800c00c0c03240045401c0500860b103240380c2c0a4010628150b0740c0f03409101828139050000c10034000c0e80c0ca5081290340b0310214401061058809995491920780d40e08 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 493602679 1250 493601429 493601453
    0xd05071e09051302040e0705120105040c0524160605040c0f12020901140d020d081215010206060f040b0303070303050a0e1c05070f08030903090a090204051c022704 72
    0x28050700b04403c001024600011109080da416100403400c9080d041015043c408150412604180b1950a0b1701c030003841500514090f41c041c000d049480d903100c070180003c05941c840f400700014000074155a220262200502171140c4c55400d2144c081c04558940e030540350152401ea406d500810001e12443e0101c0b64250000c003000b2196801c401d006038013051a00905118904d502034403072a54050648408000944090b4010720034143d0b1b03201c03450b0039400b0741c12034541c01a401400c58000b503803103100e84c000098010780580003045555aa82c08102d544441400142d400c00d4a0b2003a102c0a5281040517111040c803e84002c2098984202c0c074804030b078025050000300b076220b911002544100001c0c800d40c2c1d0070036450724030b80e1144503040c409103101048800802c9142c0010401510100c0807010740341810088500310205565803082606900890141c00e1b03101054512010300a007540440c0309106c2c0c809080c642005000d414001c13040000342201c91290180300d4200b20803c15105410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 493603929 1250 493602679 493602689
    0xc1908120903030112060b031005101706040201140306040f020f0418020f0909090f070303030504050c01081501050912070311011103040303050d0515040903050c1e100b0d05071e 78
    0x118195854800812441c405d01e120190242c0d603220030240c4c0c00d8078144a461640c2c400083c09004504049940100030100d41c49460724010b00341501c24800341010500c00e0040e03405039a185036494440c00711800c039600140c10140d1050351030496040e0581c4900107003211a00e0b03400c1c0540c40d50b00d41a10034250018010052440c1c43c410001c2d4200301d0a12020781b00d00300310513a500d980741d985281d02c5d0307490700e00d004441d401c851043c118000704050f4560070862007144600140c4280700c600d4401525201400d4070000c8240388141281c0d4034551141c0003800c400c840003009008011000340f5000d092071484d40051720070902c1030b40043c6070755803c01294482e40b89510015441e1528648000b0101d0050341980c15001307031a00089001065040710140304036034020300c10090840c9515019020782d00000200070280903c880c407401920f10356201d1002ca4020b10003030845a4210088200100700114219900c40100400702c0003140c810000a17020b0102d940c0d49003446050348850444800a941c80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 493605179 1250 493603929 493603933
    0x3091605030d080c0417030301050411070b01060e030328080c0a09060e0409140d081509010e040602120703090615080d08061c05100c020a050604080c19081209 70
    0x1003000580c4000840c10101102403034811041d8075442c6603001030b03208680c007502031062820101c140100700440294120340d0112000c00100e04042c8681c0940d0240c805c0180c44004010010419580640511005d003240203003035a00d0203500c01320808011341c81e01405542204103400d58980940c20400c000c0e00012012105824482850340040100700c80d40520300401083c4820549a41c1b2603400882d40164814510541e5520044103141d9130818a03e801c000180c43c0c0001c0340c10450381c1c00700c1203007400019240360144c2c0c5c01c205003001a900c001e00101c031955804c11500602c5100804914040e48480d94041401a05801c001e804d58100507482e40c41a070800070100610540022010038805031130411010740d94550740000c03a1440b00c807562844d151890348140c420441c0106d96002d4880030701204000c11089280120780e60010120020425404140840c0200d81c280020703001c00191881250030050351003001c214150b20080049807800c001054a03032500010901c11a842840c0c100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 493606429 1250 493605179 493605223
    0x30906100302030a1b032f04050c12090a0c1d06010801060813050109050709140a05041a09070302100e0126010b0d150e01170105060924030d050309 65
    0xd072900c4c07280c4801040306910000c152030300c0d00c3d030306981001140c1124150400314100d01c0f40c110500181c5090807a4450000d100c28401d26261241c03d0203034949221441c141a1054200d00c1003100107004541207120340e5280324005485001c030800600244410900c407061403103802da203000c1c0054403243c10310800e107006000b29940407054561200700c007880c80880c44140e080c520b00400e08600042c0c031a010320b0130b0102d0b08005a03009103460110404507005c5959440300c0c800c0403a5415500244090400043d60299918241c0ca0980004002040c0c460069917540010344540c001070300da03008100e140102c1405036812044085001418143d030703280c10706150000400c03000301400303903480d09800898041c90350860b0354803050700caa8030304242110080e251901e06421070407d10810849100c007c1200c500312034180545405190090100c00b280d48507800100700b4030701e000e21601c4012545854034503040e50200f08101c001c800b00e880711a56800c002080034100380f204c80e007041c855100e00c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 493607679 1250 493606429 493606433
    0x2060417100b0906010c030e090f0907050118060c020a0906080106030b0c0a140d020f0c060a150e040204050c09041d0613050307200901141e010507300201020309061003 74
    0x43c030000e52000d42460015600b00b960314094444401704040240c1200660303007040048400881c900340150f0418084603100d40c2d9442c011103841c8142188406070400000040141c14020f40c0c000c05494402411111000d4640217141c04031420341e40701d040c81c0e039162401082840f404c1c0714400c1d001070104040034580800288050496901045d0024542900085442800c10700e0b50549080a41e1821086d030755581020106588880598000c40321324075094039121100f518603a084115910085a504187e440b41c0810008001c01820003540b245e08010a602d81d0f038861080199031415002c581180510481030308c0d15000009007801c800b07d1200c840ca50100744004244c0d02c1d81c99010182c0e50a030702a0002600c0400e10101c001a006490040046100022803559000b03000c0182c8070038030034820300780031060741c902c02204007800700b0010845000480c2c013104c2061040f40241c19000440e450b6001004006005070806400503503000c42440701e05202405025009030050028104e40750550b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 493608929 1250 493607679 493607689
    0x602071211370b040b0c030412050f0405040e011514060414040209091303080703140105010c0614070e0a050a030803070516080304060906151a09010c02060417100b 72
    0x4441c800301c0c41d40d40d40c40c614441c541198030501c0082000280918035070052400c0001040281d8003202c1750702c2650300140c41003882d0390680c0c1c403803a00304101204901c0094403c0c0c0d2180d0100c0314180f00795400300404201c940f036502074251905408070000644054404241554807115006010301c049aa01c800040d552080151003e4484240d49a1070001108000038020300c108120b858214180d20100320001c40844050b40d502802600e5901c41a5030340f150071003c41c6c6a1040000c5000d0b905001448194400e000854045104000000c0c000d800510301d2068904c044401800003501c0707580203105401c2c840f081c1001018180c424080250030b40d40d47d44407034000100b000e030401c540841e10501010100051040c803940111006640381030a040050182207000c0f0180d545605107506942c880300c2d452101811034076a5440300340000107941c1e070780c034140d40000100303410024043c0d00b550250756108001d0000701107030320b507001142c0c0414001c2400c003001c80d00790f04159490b20390101c102c0d8880f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 493610179 1250 493608929 493608943
    0x908060a020904090c0f0501021006050927010515010e15040306050c16050309180403020d21050108030408070e0c07020607230105091c02070b0a09030206070602071211 74
    0x220142c0c54000c0b10703001c0780050500c03080103040c00010340380008000c200391740b0603030603580c0a80c00d44099440310341c0100151482407043c0d0703400103158000150301d000030b511020303420030341000c0c1d0042c42410980742c282075031010b03144c3c50455960100c80110035a0403966004440f44c0507149603015411192a45040c0d02a034440a04030503204c03800211000d2200e0225551101d5621002141c03c1d03031414030756620b030041c442003801450b4007403543d01118141891903100704da040d07005080c0c103106034008031005c59803100491003200341600c1c0e0420295103400703070038082e00001000b1500c031450244814941310f2075070310503400c0f04489000c0c408030900d901c0c2115181a01500c49070380c2c0d00c1c0d05107410f06c00b107860748041142c642d14030a03410b0b1454a06420442c0030f02c0d0100120b507010710442d1185144400700040c02c0d8096401203804002c01d1b1800400340044c84010704001506c42d40e2030300410398503449424100d488941c00a4013004101980003d48108c0302d052400110850340c2040043e5201030b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 493611429 1250 493610179 493610191
    0x9160f080318040e03070b041a0c0901110f190b07050f16032109050106060f0e0103050a090209010f08160b16060902120f010b040e060f13050105070915090806 70
    0x282c00954058591907a40201070f00591001c212a80c0307800ca0f0a08900c0c0c03040c2560121b03500342560700510108043e4208903801140e010303094500d4030107044010b440b280e2050380c8a00e101e0041480da0900104140000506070f4409040845455101d04d82070b5054240140b80c601400010304c034001812106205495803c0e2802c3d24940d981415414140c070145000160800310a8031080312800a503095004854894444e0000340007864940e003040d500200390780000c0d00002d449210703100c04d41d031094100035000302460000049410150b000300f00c2242098000012547d400308040081501c108414802880d00d031b40305080032814050303c1c141b03510910303000140b201c076224058418881c9940c000c81206600a0249484808154030300c2d8440b041071900c40e5a1f5407818440310b5a034207284c020084040071010103885140da83c1d80b0b04000610002e04005a00d4041400080000f00e0034401d01e0300400e00307a204e103814646006103d40f1813440b84155101009103260302001040000540150800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 493612679 1250 493611429 493611457
    0x90f04140f07050408010216030f020105090d03090f120f0f08010302130507031503120f08010e16020f06090105041e0507181e0905061e0601141209160f0803 69
    0x3480b10a0100d0700d81c06a40c1012044e948000380090700c0490103c20103906500c6500d03003400d002800541079003210002c90303812103a5007003c1d83d50b00b5513074403940c00094014070510400150466030786824800d0b54003030710380d1004180f60002e603400d40c94000762001d01e042210b02d440d9659604640c081444850030064404180b81c81d0310100344201e0080e000110204140006003071680d40d24280f030021480d010100c4800302e01c031200c2044041d032162501c141039500c0309440c18601d0712181031161140354113700400450040ca5510002460140281409419048004103070381c141414200013000201200d007240e42951820f500c002078010800ba8200c80c207030201c43c1840c1c042540340801803c42644900a202c442001d8051008201d90080d21147d0040d8101e03400e56454004048100d801c0806203148034145a0029580d07620415401e5502d900c190f5041c1e040010303000001481ea081900d2044d008e0b001584410b0192502480c800020284050fa2030f00152426990325224803600c0c50b8a40c0342c3c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 493613929 1250 493612679 493612681
    0x80303060a050d150c09271505030604200907090503010f060e0a0b0a0b07061b0e0102072706080109050d0302031512031605030a02011803050f090103060e010902090f04140f 76
    0x124003540f5282c00510a0074168502c4422147e0150b060034100c50140c08024035040e5082d050304041d03840c0314203403500500280502d840355200e0030038074501b41401c0441009880000d00b0f090702c0f0440c04034015891911070300c84460405040500b5946144c529042c0300b0b14001d002c000380b850002285402c42c45401c000245408600d011402940c0b568206121b070341301c0040c6043c2009510b6010006c0a10b40302c40000a48145180c101c40b03803d0060820f81c01644182e1081c880e086084880c144c07000400c3c0321480c894000901c15005030380c65988440120f95580b00b840781400750034400010321000b14542103245151012100c1c07900c28a8801c1140100030034050311003078a000700200e407442141591819180002403800d19500e50200b0304000055003008030540c008000c02c15404106545501c60600740041c00168401c1d40d080042d4050415884e680005850005594824041c061070040540d0790200041400921106646824011381c03510144a1180746041c02190300504448900340030307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 493615179 1250 493613929 493613951
    0x304080c06070c051c06230f094b010c0206041e0c0503060a02030402181308030702011e1a0909060708040206070b09070e0c27010c0507080303060a050d15 68
    0x40b40301c445c00018070403842c04a641c02c1809003100b04c8400014404410082c0e941c40c5241d50038a40b41c04e4034803900c141d100310300c031210070403000603e403800b22618844c8050300282c1c50f0144c00d8031a0100303100030b1084500645002441028002c0381c3c0f07040c1490009110600b420340d11140d0118459040708100300b40440000e04016840890b000105030050032241d2500340004600029441a9030072803191844961560710080144501031064124000304810810705880300081030340002d00804c115589c820b8013513108015074000c010303488580100020b0035421a01090310070712102d00c24511441402e002c111441d5000944150f0113865450105015192440810554098448003c102d05a03403010011640300001e41241240c001106000960320340c02e902c040c080c422600701c03502d60404d03400e840c980d2003000c3c1005541c0c03540616101c500d001803034071424105002504543c14503000042400800e180141d182c50140c48110f40303186101c0d2030365440203204940100014002610b43c0c2108070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 493616429 1250 493615179 493615219
    0x71101021314310506010903050312061c0609030908070302130c05041208120109270c09020d0203010f0f210204390801060207050d02040e0f0304080c06070c05 70
    0x102d11000030300c0b0801000311608110300d07030802410306003c2d03107031401000815942c0b06540030001c513070704100514940b2a4480e0f520172040402850310b60000050785024003103030f40009823020403c0c0183d2000a06000c0d900e0000c003500d9240d0b0110b081030380000001d0026a9030415140c50503603e04000161038180c400b0309490602a550010003903d04d07480943d012b100c24003004040c00e101c0d110001d2803980e01c86208104031741d10b0344810808800030701a4050014080d50249c102031780100f0001e00701903515441c2c80103980c480b21092807138a401000421500d03800c004440050006c840b8420291400c04000d20481540d04810b030f10101a040c0283d41551150351140c81e20007d030b110000351259546040c02d501c5454110b045400c1400e095091100c0fa10541045058a80c0b0b603002e07100d100c1c646001c010400c45007001c1070b0780c441e80c0c54090860601d130410500f000c0c0d8007140051038503503207003034840c5080820b06240c0364004e2000300031120000f10900da00b81c050b21409c880300d0306011030000b0520 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 493617679 1250 493616429 493616449
    0x11e150b07122712020a15050c060c0306280f030b04050615060a0e04141509071d06030c0702040e3007080705030705010501030b071101021314 63
    0x9100380500081003000d00c03000e540941440e010b151224041018084111264282c840041103000354100405000381c01d02c41c0c500c0c0c059540020f040c50002c41d110103a06880e0410f0740c0c0f22002042d4000740c484a108011b001c0c1036403209503000003e0035071400e4408503801c0810486200411500000c0021020440e105100c01928950361411180754032460510744100c410794013500d20344180300001c3d840340c10354103101c0c1400b08060082402c14100003400e44180311065100e80c1d115031600d100308a004003224506c0c0c4a03074422048480072510380d40900c401c40d003010703204000b0841146032889803001c0901103001005000d444050342e0b07503602d400b090002c0c080c66000960182c02c08400112294001075600302c83e030380c900400e050002980d0b801c2c0f188854021105806420b00f401090081403051014043c03003800350007034038130304042a40c03032030b086480980003110005d1901060000483d0b10080061103698260000c44c600315850491462129003440f60041d04800c1081600d80c0e07031103c00c415 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 493618929 1250 493617679 493617689
    0x3190917030903280f150e1b10051612030e060c040e040f0b040b060405010504020703090306090204060f06090801050703020c1e07080706021b0a0617060f1503070206010503011e15 79
    0xd4058961a28121b40035030703030020000600030300706014032480700300100702a030f000d4820050914030030481009200a080c0c2c0081000f00f0310005020302408035404c43c6880c144030b4402c3c400001800701140c000b40c12100e402c0c02030304480c2c1c4000204803003400c0c04000c840c15a4009802c1c800c050341c85140c03640507403910b240001d110740580010703c0100007407100b040d030040c40101c1e018415a80c82d00c0c1800124041c040019000602480707040010850310b9200d211854005071000c684a5103c0d03a15503140440355114200054010340704100c640828451942c20501d507241c00c0d85440c0c80407000036500c01d561128100a0400070030610040c20041000341c00501003441030702e01807540e03400301a458180862444c070340882c0e943d96080142c940b00c9070120945440744c0b28040c56503074611040c07882040061540c2d401c6201300c1d00140d034039640c4000f19402424171a0349150741c3c1c50103403030080c245031040c1e01481c066810b001c50300340355034130040661040032151180014010202c140a0100f84516404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 493620179 1250 493618929 493618943
    0x60503010e25080a050114061209070302060f0a1b0f0221101e05010602060c0309010f021c1b05031303020c0901120c06080115110319091703090328 65
    0x42d042c505811014080c410003040030100104d80ea1003c000040700300e044d413881e600c5501001952180c00445190b42e412420a40480e42d0950f1a40d02141040c4c0c807021140200140200b5804605544401c5100c0031500000607051501c40950301c4410300000c0c0c0500910038070a05d85644082c1041c42000a808440304048844400000c1c4034140202400071a400803a1110345010120344100d0056134121003032540103085544da40203454003150809061004195243e001420340541e082c0007034408100ae6860350343e4056030b030740100811a07000901001908000541a0725455041019a42d112100e4a0a203064134001d1404a00301003c0d51400c50b40f01000754000710b20450f5038199248201c0c0308240f4650600d8540c1c1007034407940d2003441070807071001141d0707140c0e00210710405010982013000d008030b03030404c0301c041a21041c1d100c110301d00b02d0000354006800c01403a030b80558110790310307200d500165160040b1400481d40f18080d11300207490801520903500c01c04a01d00d800c20b10400c1c0c016070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 493621429 1250 493620179 493620241
    0x40c02010b1302030601140708220347041b030b01030f02040b1206060d0c031e03030605150f0f070f0602070c0e090c190f0621020301060503010e 64
    0x3540742c025007041d0b407a01e0024045c4072243c8645240082120811034100400e503007021660001103c2a00007038200c3c5a040004940000002c3c42807498500001903c41301e0200341c66026a03411001c0034504402415680480500c2c0750040b0010040c2d034000b03410000440c8804204c03041600181e02d207501c020a81600e040001081c08090030a41c14030030300c00c45c0c0034000401d00c1d40c100001c1d0003400c401d51204c0d801000c00f0078050b1805049800c01c6038410203481100c26039176261004023140e04400c0c40112645440340c07400b05070b0b240c42001c0c05441d04680c01c2c0590b40056000c581307140606a0f0404283c1e400041880407100800c0070794040562200c684180c82c100e501d09800039422201701100da011095038046040074000c0300941c4035400c00d800400900b000e220800c40e00c01102c20080b00d051140a002186d41c40b031109401010302004e0701c808080d100c040c1083e20182d01e8054014000b02e105000500174140e00404807411941c1c002420b02e1540c486290710844205602140940350032a22 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 493622679 1250 493621429 493621459
    0x6080a150f0602011505010806030619140f0709060503010b1b0f250b040506190c021e12030901140c0c0904060506030d031e0923060405161202040c02010b 68
    0x14000701005405c031381c030301c0822961700c00055400324000d84445606400030310010360592108014a520100200c40c040f83c07011005020410300c0c4026560108050314180c20081c409030480e01c0d400c003e02a52501515640c545100b40300c40740201c201b030f4010b48017101699030712020300304410b50804d140b0100380d610017100e241c0314224980e414031800d0900a040000014801c403120b007030f5002c40e0030150000d441c0030000580c81e820940090410410f0100c0d0040c280c001da00d03408c82001c8007429030102058104104e0301040301c1d860300460301901980c000c00048038aa41e0004c124109a0418599540c0301c08403038510505010071311460a400418100411040c0015038120a0045006034243d5010100c40c0b01c040b0159100d5104c0111440186208402c084031198401003400303000da030307485c09110a00d950307000810022200c03003440c2ea44883c0502c01804403d100e41012207480b0921080c3c1c03d45041c500904502101d81d019100701c1d0350b01d00039107201d0300030b40213840e51020081204601020701 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 493623929 1250 493622679 493622681
    0x4230f030a05032202030a02060d15080105061c0203190c0b031609080f0c1507050102040b07020a060f0f0f140307200304030b061203070803100311010906080a150f060201 75
    0x2c84d20400e0080c1000d03440180d6030000d0400002d02500a13028211a029503001d00023298411503069240c03a9071681d882e4501001c80e00041c0140200c80004035140c10090200007607046102c0042c1046401e603080319006940016004180e10a403040a400b50802824140720010003a03203c0d000302800001040589da5041044140e4aa10760312140020358490401c950340d05440700780400a64007800880e1000d141078a0072a81c0d0300c5105986034500003031940c0709804c1e0307042984225005072010800e042180383c00b4268001604840c03602d0302d0b816011402c014407502110120400f4801307000103001007944290150b100d2a03051002d0300b517983c105030800030b12092885c0d4250b108542c100505052201021044400f00e0340c0001264419403182c0c1c08101450b82001c4011040f44800c010490000f0350100c09588200d003841d04008040f072a50030021240036501da411810000034100502c00507400c501641d40081c20990005030b46801d028030842e18804a40002e40341c42c004643c0055500c2e41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 493625179 1250 493623929 493623931
    0xc031407090f23040905030c01020414040b060f0307050306040902181605040f1e0905251b0b0603010908160311011515020a060204260604230f030a0503 67
    0x418012a942180d0365051906001c40e40b40b02009540c04591070007100d4139068205002c1640544191f82c54043c416844908a9015a20004c2c0200d04800350800c0d42c82c092003442c61410702a10250f00e081d0584011010509c0010702c80e805104021000c90341c1c58580e50701405c20035034003502401a00c00010110b580c41042102e07802680401501c540c600603101d98182c5003101d01c0501c90209940c107019101040da0006a1034140c8142d00080c00581c1c0c88803801140d0081c56000c0c500d4849002c5020004058a1501d4040c4c00b8008010301e00308404001485000070141c009240560139254080080d0242c0b14040d0042c00b4460301040150751440203102c80308146200791680d0900c0c00c8903855480c02e803007030381400101c03070800e100703040050070790300041c0307505c0314500744151210640c3c5595807078200d0b08550069041c00002d0841c0c88405503081041401c80b914601c0140454034007503132003813a03600d0002250780c0383c42d00084a0226610003003040407030307808007441907a4440030398139401440c0e508 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 493626429 1250 493625179 493625189
    0xc11030a0b06131a132301031403030402030a11220507090e0402030c04090c09020d02071104180809180f1e0f0403050a0504051e01022503060c03140709 67
    0x58036841016814400d44540c452109440410700055626042002925502405c1400c030740c41c4ca41c0804c0694920a06841c200040888102c040759411810103041006c4254072020b169401082440090b913000190311036260362100c40d8a00150080707000c04c960118184090a04022060301c003140c003030480d04460f114200613900c2c1c41500c3d81d1145d0541035080c094901070f4042d000740504040505180d0000316005020700030319000329a0310800c90b022a4050200c2c8585243c2c041003000412030314480344158244121010300c6206200c020110100482c03050061110000044001c4240c032842c52461005168114607601482c00c01c1d40c44034800c10442d0b4480500380240c0301c0344544150700c007060b0700034004c50b034682100e5900d81e40c00b91240d5010307070407003014424180b100049a0384c0b68525036005006480a00002d20500d0002914001d1300c0041102c0e17014840c8803401c9008410003c250440360440c034003007000d00d10f980c0305030001d0034003072034400f0f0300b11400c2c00b0000b40d9a000b404040440b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 493627679 1250 493626429 493626439
    0xd02010507081509060f0a050d031101060b030906160e03030f0d060803160b0601090527221b030803010b031e07050307030903170709181b0c11030a0b06 67
    0x55186088401c000315034000d03184d88920782602040113820016400740c900c410182c5131031203660310f410003e91101c4d03203483c1c200c0008046000b0150560300070700500c002010200c140c5411814944002e54981e03100030014240008100c061000c0d0754840c03a480c030079070780003d0709403503880160100c408465030040742041d046504108000800e582c000049030200c103808031100032500a02d55038480051000342c511030402000c0700700410260f81c0d20340c4400303070401a2959000644085c00148105800041c02049600b807103201042c0f490303550200b4520b0b07265000d00c0b41c5102000001c502c0810138803580000d00f0600022001003003c648100049d40501c40700e070341408444082140c1402d0f90709045035031000140b002c2c008111924001d801c44400710b4403074200302040d480c40e001c0801c0c2502048501030001000c42c078041014885485101c056a05403040c240624001c0e020290011112461a44c2c20000115044410b000b084002c0320015540141668160b06041c100071188001c00e0710602d00ca0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 493628929 1250 493627679 493627681
    0x310150602120f2205041103041b050109050411220512030a050f0d09050f010f0c140307200a030206040b1e010303081e01030606080601060c08090f0a080d0201050708 73
    0x2012141e42628030f100d901040003480c0c0702500c008940e040d60b40c1075040001c4000058045480d680e5409201520098540c1482e2a8540350900c699802a825000a04204809000c2c4050399210035007c0a480c0140e401140300e02d4a40c404135182d00c01c00640240511440d0f20300f10101010758024022100210307902d6a03004900507030503490784900c0301c8040104008100c99504110355070b0244c4544441c5000001c1c84a405031136903410a5645052178920745d6403280c00c4141c0d02607600c41e5041610003440d21030400031030030b180c21405200203807183d01800216400e0031068a1703503c003008803641c035400a03942d401540346806951602c00350350032506201e4480008a08403181110010b84c6d407460701c0042c505920715201981d1007031000e420205444120f1040d99045035100704028000c51188000103007041c64420705d2824124107070403800070400d44184443c00704040009940900f00704461210107a0407100000c1c241c1115503024650b03038003424850418054040d4803061088990740c680380c4803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 493630179 1250 493628929 493628953
    0x3160b010503120f0d0b0a0305030d0f060602010b010e0d140d05120a0902010c110a09090803060414040210030c1724030d050a0516140f120a1d0310150602 68
    0x19801142c4450000752405d1010001c800700303680000e00d0490029040040349a1642c50302c5055510540c55003006548601007480106010300c240402010603100800003400310100080640c401115914464542c0324081f40034011909043c10924403440c088604e402400e100140c502e4002403800540c07400e6001c00580e0200646c054901d24a07030595a9806444007130b520105018124041c082c5c1018140350041031685141c0b00c2c0305d81650046003807603100c0c6400010002525410b18044196101400c107100050311484034084a01e0100d05003c6021030744080e044a652410402c8017001480800034000c1c2c001c4014101000e8148070b101a071452995407062613928a0403134600c0000600800c0907801140c8140041c01d50f0035461403604100381e4181e1903110412500a0100d80103810000e04400c3e449401c10118a0800050341407608201c800c00c4041c2900098020082c0b088100841002042c2c1c1c0038400c038100000030301e4007000b8401d000010040000c8190061201510642d10700d00d074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 493631429 1250 493630179 493630213
    0x501080d03150f05012007060c0b100501140d1b08060916050d0e010605030f03030f10080c0f0d0b010905070e0301020f0d0c1205040b0601030b06090114030903160b010503 75
    0x1060b40c9207203200c0107900e85130800441e0710a2440c0c6408101c096108144440361030140b00703444c02007001c4d81e980c000505482c280310100200c00307080f46030444040c0204010300d907008044030306280c00071480b0545810200030440042e042e05010142c1e800b10b0081032940c0b058000325680d0041c20196400901540c840307141d1589000c0300c2e000c09011540501003101d00c030300c2c80e0b000445900d80410011901c10307920030200e40b0b401030740c20081400e50408000c009501aa800072560300028240c038807503440b442c1049594403044088015030090001c14107582c0a9140ca070307500300c112513004003906817a42c1c6d80c642040040509840c804c00040110344d00c03821610301402518030305050303500e1551811b2520900000240780d11205001408401c0110120038141071107190f10a602a00c01c3c40e13000e00d0010001001c980340c0c095134038440d02040c000c0080c00d076070240175240ca941150314103903034a48903640010724500660010200111013181701004001d402807145040743c1041c1c04645150780f020507000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 493632679 1250 493631429 493631471
    0x30f1103071413030b040f051903141812070302010e06070b0115020f070f090f021809040c261504210c230d020606030d0518040501080d03 61
    0x58001041025001191078034100104284070420f0280030f00c1c00e82d01e9540400000041320191600c0b8907842055040c480203020b9582c00d10f0a10360100f040341020342d0050405030302c24901c2c15581c140402c90350740e081d02070300c0c90942c8a0001070010a11004001c011692072200f4041240096450580130a00e801c090082d9154503501400990703d0f603080c0070710f6401031005152004114411440c49602a241c240030003006022443d01ca0314030300c0d0802500c6c1003910160a01c0b0909503204024000c00e50380000701c10050320504441010042e1124285074064a6190708140445a480c0000038518201200007401340400072069070b05011070b525024090220448000d84490701c402000c4200e581c001c0d80c0070005c4002c505040b18056495140c01190941710221160080851101e000e841d00040000b094841c5580c03005106500d0030002082e250092041d42c2b5061041c00b007580030700550a0a00c595842c071010b00100650340c0e41b011803590b1203c0711805580841e2402000400204001d9004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 493633929 1250 493632679 493632691
    0x40b090a081f091502031906050102031903050603100e0a0c0e040507050127171905030d0c03090501020a05030f18070314010902120f0d0306081c0c0c0303030f1103 72
    0x2d00300c4400004450250010003c101ca0f0100520034141c1103078901e20155010b40f58030714101c0c40041c25010500100c44907904014190350013480403d00400752400496000d102c58600420103488410100c0d1602458503d03200c2218200350017020886000070350200d9450043c80600c82c495911104000340b505c050302e01400d0b6402a40e4180000e500582c0e01c4580300301c0c04480400003148886500b100d440c040d07045100b02010a09002c4100b01c010003a40007220b589450480c0821001c0d9502c40d41c82c428072085694040e101c2e61603400b0240254030034042d00d6000030095669075000310004015910440b44c5004440682c0f0110340c09070710840d445c12540c40c05400414107141503841b40c00d110103a8860402040d925440d0542c0103849a00340e000201d01441c005050315098407640a0914841011840030503140000c2000700002c0000c6900015423080d0780c43c6403d0000b140201c7e100b2140c110080c0440040141c000101545076210300580f044c0c80b03d00700981404040f0f1007a05102c180d1300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 493635179 1250 493633929 493633963
    0x10503070e1f080a021e0102060f18010906020406080112081e0405030d021b04020c0a0b250509030709020307050306010e120d05130906051f030f02040b090a08 70
    0x303000555a0314000780e0041d1082c2d224030010800ca00944800110b181c0140b640c60700480c940c4400c6052a401c20131036884c40c1e010404050f24204c00007950b550008110080c0001c1c0c00340411100c190300b003a52103441490380004c0c4840c00b03842c204035010f0346c0036226107000150400e000007141d010031010002100c4d403111115103041c0754881c40540c400f290640314003c2400420000901d6a41003080010f5089150054030030030064140fa00300603407100558600541c0100301d0080c6c0c2900229001552942c800d20030040ca0b2120112207260503503a04046540d10301ea042c22001e03050300003000d0001c10008034100e85d8550b40350704c600d00682c00203a5142021030024408900158000c0c208c1d200f6031745010700312580e541381410760700e4680f03051300681c18042900002c40f51309104000c0c582c18003130102401d080c03240c1454000405c5283c40c0d915840071030402504070116180384a9084810f000d48000401e44d01d0b280c9842e14402030381d0140300c10034468000d2480000c2c400e400810001104d00503020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 493636429 1250 493635179 493635193
    0x20c0319020c061c02190309020112021c0e0102070506040308151009360f0e06101221080702010e07291303030302040e0702030c0303160c0f05031e03010503 69
    0x20215521440004d914441a8081c0070741c804c1518512562406040541c1e0086200c000600014041011b03504510b03a100380100201510a011240a00c1103500358810000701c0080400140c2d0081c0203c80000346540144402e00042c1360303100c0311090240d44010140c00884491300c041100c001840e80c0c4010104030351807420040c02c1990a03a83c0784415203000c90b441442400000910b18548818440714080c1e40d800c0e400b00c01581d54414000c1d214048002068503040078003c514400c1c0080c415442e8450000026108100e411305d012000c030340c10244d01c04860780c69007101405003407048400c10012343ca400011002580300113400021501c41d02c0b284012920a0a40291424a9110600050a010010084004007400d04e00380218001e580050321a410080b91202c400e401425130402c651083c4851500301d035020048075000214500801c0441860b24000d9803200b5140fa0702034030800c0d50805c2041030081c00b20040140020880e000c1d0b480c0b800d40c4445046a00080c0507064155220079 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 493637679 1250 493636429 493636447
    0x10e06030f0607021b0f100306080c0604050604260316030e04050417030a0608190311030f0901030b04060503100e06070c08091516030507030e0f0f0d0213020c0319020c06 75
    0x17040b0041e19603002d000c0425452083c0080303800c5805808056001a90700c45c0108590401406503d0000808450441c5861300e00380000d171490286c0d001d4a0010a010ba603020000f41d410708004420150761000d41751a001000440c03043c2034241081031f400302c1c1900c0c4001c01c81c2d203014441c641c452075000b6060380c8080300c80d2a1400080d0002402d4003000382e90354030080f4010b03004000000c4906180c0e02140c04004487c60300070701420002d041c900d400d90040c0021025110940c042e201c00c1002803900052130b012040000e0302030400d503809550980640d5603601480007485c0c2040d82000d840d03200b11034003526000401c449031018000060300307140c0300b4410240e42d4a84075954410b035190410445050800d516021500f4210300002100802c00000d1400c08041d04a05040c0030a00b0849904c6403400d0240040f924013595130560900c95106021180110f5845080010002840b158115182c2480b103a10716a07a0340301c2c408251801922805c10041141f001032102503200015200c40c0c1410014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 493638929 1250 493637679 493637713
    0x1507050304051e0f100926030a0b030115090c1404050105070b0640050f0c0702040e070b04050306010b041d04170729161115010e06030f060702 63
    0xc4540092070b005118450130610000c0216140c0c0b00c210403000224400e1514020300c0c02c180541402c038100321134140d60a540c0f110740007035039806071402e100410201410000031380100100d0420003240a0b00e100042030010090340901d40c00c030f84580750441c140b00c4144425501d4000d038852540090300030040e07800022100866103401803805407d20410707104540c25801e12121401404076081d014290400a07a00c2461190900b0310740400100801e0038800304078083d1020081085a00d0200021703000210340303503640f20a040d101031030182c40d50b59858003c80c403aa541301e0710a580c400d21071000003107142c0d40c01400301e800701c6001c180f011000c21071a2a0072032006070020000d595900341025030b68450107600000b007510718450141c9807101841d81c003202c01c2e8480c001040d102c040c00c01c8401c0100c1d03031611989000d1507140030f00f400c065084410501615280ca01250302000c1c04c101000041e991814400043c002e400c210243e44403851014001a5545800c40b40071006038000118040d240c122 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 493640179 1250 493638929 493638973
    0x91501030f02190807050a02060103330b0a06030e1b0604150f351b07080714030a0c02090402010302070b04050c09010f03080d0f060314150705030405 66
    0x6040c0440c1c204041c0340c94900720f800c40e120300504041e05403c4840e1560b4000b42465001040741003403030500ca443c1600940c0e54605000040803008000c05d601408101c045081c02000c80c1c0b100c2c0c01e0015011021540d0240201d0410b0382d006848c00c0c0400305406029001d41c4c0075407050100144030102e0344007410512084210301154002400300004540b6491003071240820303400035101c40b201413010310700060070300701269420141100b40c0c200c10a04a070481c528030003500442030340451152a44030300700607403070b18450a1100c083c100003861b404009010019040c018041c0c525a01c0d143c1c25440e00d1b5849204044151000035101c14010005141094110307402600601d001820250b155075101d1001c00140d41c00d80c2c5541c0f266a45a440d40f42c100112030140c11400c8003403024519595407041203012710644401e04648410440081c1c08a40c1d110038001e58000c10300c0c151592815010179100e40c900903001c00002c07207080020f20002c0c056001c8034040d0340c0c4640207144426804480310780541c0c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 493641429 1250 493640179 493640221
    0x911130b18061804021c020a15020705041407020319120203040b04060501060306061709011404081201050105190e0118090c0207090509060402120a02030604080a1d09 73
    0x95980c841000395160a0300c944003084926800d0011800c021003000002142025a018030041020030000142c468480402e40e02c01840400324400300c0c1840000c85080e00d680182010285004011074507507070018400c81141c0080d2002c006104803c050414454411110200513904c02c203d82120440c00401280080c840c524102d0b1a000040c0400c00c141c2c0e00c00d580a54110762207000b4041880700c00c1c4509801020a4101040308901d2716601410f11903900075a05400360202c1d001621946080d08124200c1c2c00c1c0004003001e600d403030b18215032260032010212006221000010946e035018004603002c901010748102454882c00300125581c4540d460064100240ea1a1700b40d403000002011102404680c0c01c041004450404002d213058160350007500824200340510800b0780000c5289074000b42c06030380011103488129500b81c0b9040d040d640080d0180704410401042c081c3c41d001910090201e5910312423141e1160070070310303030386086080381e10303400000c2c0b0b408108070072013000d0b460903100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 493642679 1250 493641429 493641431
    0x40b0405070b040603050105040c090f051e120d0f09030c030204050405030d050403050406021b060f0a0522050f19060305060a08070e010f050603100e0402010c080c01060501020709091113 82
    0x542c0368408010309030490340c40b540c0800e484d9801401607140c140922072501c480791809001c050b140400000a0303c0c3e1900c521030280e10b20801103d20704440f41021036103040084d00d080a11510031130740d5035035807142420200c001190000040c0e2414800c07918001141d401002d011012070864080200402018000300e4013403004000003401c1000303a00940d8811030090316029201e520b0000013a0404000c585071842ba0320524801517502c2d51500d05072640b0944022080f2b44406950308280c4042c030804403d0032000c1c40b0b600c11401703014942070a500c00e440090f42d11001c81c01c594030a0050034090030b00c402103100c1100e0411b02900d4465032145074803207001000005001da8807698036040c0101c90b0052042c0c888420f0042c030851001401a50041100f5611b56103941351002810505141a01900f20b49201400100f000d684c42100c42e41e100c0c0b0307000900203599031068501940240740310310402d0b01601414800003851800c43c4a410071860308440d6445150b4901802c201480206001c140d00c51 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 493643929 1250 493642679 493642693
    0x3120f0309120e0406061103041203171306150e0a0e120a120c0f0903120e1305040b0a0b032d030a0f020c0a1202240d02071e020108040b0405 62
    0x104a08402e0300d68100103685610903204080010b100590b034194000805001c54054503903248080001101d049411a500400e9020128501115142e05e070580c0a20804204001e100400d030100035515901c920072101000500d104020640e844056886655100e00024000174005c1c1d07401d400c0404004034076410b4645c050a4031900b20301d1504500c00e68000255a45203030070400d449807007070400071802c40c2400d0400c4401e8502c02010b418290000a0000b50703034481d07d0400398003400c1e130480304140040c40c45628401010001000307000440341034500001c0a4082034400c00c052240c25110130001d40a085a01c02c01149041040d400b00c10808051300e000320031700075144050014141005040c0d550107000c0c0c10301c50009141c941c034800b081d4450042500100030300581d614600314901c2d419100026241c14800301c030002c0721403004401c2e05056000458131148000e0364010320380b41d8401c00100040c2561100061612002404000d011030f81a102050101c0d1001c80c0d410781c401e00c0b031070856a113 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 493645179 1250 493643929 493643933
    0xc020d020604090f050a0506090c0a02160306020c010b01170c07230c011403061f050c070803030601090b04030807030c080714070e060402030f06010f030207080c100b0a03120f0309 79
    0x2032503202d944070220840d43c0d00510312500f12180145034012845281c24490783c10200005445000084d04001c240f200008280c80c64074020710141003200701c242c040f40120755580c14124007039172003010442e03465440c180144030310358003407220018140880e2550444a070b4925501e40f00c076500c008001c0d142d078650035510540041400c46001060700b4040003034030b007540035100090036210b20015004403144061081040d81c2c1c552805031742c05901000618108903034428420740f481c1c4200380300c0d1741c082d0003407070780c0440d000300000020350040c90280e07500b0030111307030394a1f18038800c0c019400014040841002803401081c407811554000600500b03401d4501003003507581041c0110560841411508810010804420400b0076150f01220030b940961461606400707511441070000d141a060052803802d450f10300d882a4180c2e940a503002541c41ea45580460318995901c001501200085082088400e110b007000145141100c1c1c0c008000388a41090700c400b61059244502c1000800d0303620250100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 493646429 1250 493645179 493645189
    0x111801030f18060902150406050a120e0322090c0c0b090304170606040506040225171201080712080406081e040b040228140a08010509031801080c0a0c020d02 69
    0x60303024400e51002801114501c14000c0e1b5488400d05240800d5040c841080301540000031680701740280d01c1c103106002075801401d001400e003518400c2040c4400b16011042d000c40040d42101e544401c0b82c55180e881d41e4180890584004004c001c4c002440682100d001614074051660080c926806a03420302c1e80301c000c646101c485c009180c1d4615070080b014003045c2c2c02c1038418107810810980c0d0940c0b07000c4418440d54820103090442e110203041c1741100e4001e00160030b14001400d0391a00e0b03c07558410300034000c0301000c5002c0c00350462034040c0040c000f17419441d1002c0d101100c1d5100301114109490914262a420401820000c04d43d035065045c66000380c83c042d0542c400c61103850030501d20b0506006210600b2440040d414503407a081192412580d85500007604403262603869842c280020408112204a20b500002040d0b003401d051140359400030003d40a1144210303410b02441000c0401140c100005540345440b40741c0c200181d40301036209030a06c06000380054001c44000d00f9507400b01d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 493647679 1250 493646429 493646471
    0x40501030e070806331e030114090106030309050d170c280b0604061a0c0a0206040f06141903020a030209030a0c0906080a11061b120d111801030f 64
    0x46400722615804003d06a0141c40054546162070b40080c00034142c2d0205110281c0921b1000001d00c01d00c1c4226a90355094101860340140d900e00002c00b81840d0303070392901a016078042207010940d121404038890030614031600c9600d400100c8880100b558051401c1c2da64008041450b281c00f0342c8800752422118100e89c21070070301400300c11b61102650350619441e00c03d0042c1c0103511450070b2800c2000081c2c14031469140c8010140e4016a031440e1451400780f07880d8038140020340285011070005600b054244c60001240c8807a21a4440c2032262071a0320128454401d203880702540c0d9902d0607101078829406001840c0242c100145806203280020f840c04c0e1106400700e0740d00d00040c00a010610403130003040c0080c07004000500f1020016a928151001c3d209545801500003142c00040c0c520200900b070710207214603007a10b400245411302c00a5503400240d9014015042143c030382c4140c216041140c9103045c05440c1896007074000c100440c064000c070b400300042207440310010184040d02100030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 493648929 1250 493647679 493647691
    0x503030f01150c03090506090103090606080c040c05190e0d050609010b031614090604021c0b010e0d110909010213080601030c080c0108040308040501140a05060a08070b040501030e070806 82
    0x28080307600d040781c032211030301d88044900b04011034242c420340041d03009954a019503004403070007500c03140030381c0c0100c3c014054568040c0005081c50360010754800007060f48040070300b00b5241400022012007054a26101d16100348041004002000c4c0740c1500c15050a90110001000b4844882c8107440e00c5140a409503014180c596407105859107514042220000000d02000e858009620700703200f01810910070380c05039014201e00400204165034a9049806002d0040030f540d01d00f03880703d650032008285414182c0d0107e007058518458902d800d110f500e52036a40088982900501081440f10703800c805001070b409513400b4450341240075030340998240a0102880205440d6156041070848150198480055a080b2560205059034000c1800343c1c0507400d8149003035503403201d00d41030b801007080c0c1035505800c81c0702c50f080c04010b911a40025020304412150300802c0f90b1074000241e200e080c184a4001c043d00b04200400a43d40250441400d40c441d50090f03a1794a90b4902d0080d0400d0340480e24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 493650179 1250 493648929 493648951
    0x1c110705101508070308030919031106010506090f01050703020a02270604020705070b03070504150302070204050f0c0d09020a0e01120201020f0d02060a0b0607120908150f0a02090d050303 82
    0x200c0520950107104140300b41124a00c0802c1c0d940c685410507456807078a0202500510000000801400003042020385024050380000c40034102820002d01c0c4001241201070140911400040d0a18001060b40d4110200400c55040c10450900545803648180d00807429030280c10902405a50740081c2090090200c5c001c2d10503800710f6a504600b940b070003c00030f500c01d40c4140300d01c02c0400c0340018003a065407007003035031242d80c0d464003841660306005540c0314a1211242032014406150305401501d8400c0c400d031010b0001352103a52018107221400c69136404840c1040c4204100c0d08419042108c0c25800540080c031096165400d5207030343e403800d810000601c1d081642e91400c6503410080d0218030126840544030b020481e400007501e42c9070283c07942c2312082e194400d114941c1e8510701210502c43c0c0c40813043d1250070b42c6c210003400083d160f201b01340c0f40c0d005052a02c401814030402032481a100c801c0343c0c69450303845145240c000d402c1043c4031508889046200400900c0420003503015001c6202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 493651429 1250 493650179 493650193
    0xf150906011401021b1c0b0a23040210050c1614010f020c041a0402070c0611150408030c1c090303060803041d0408070b04110a15020303040f060f0f141003081c110705 73
    0x180081640c5c1c52400300c2c9c0381940c1c03802181c00b024000c4c50a864000760f04685006403800440e00071107841c001d00c8075061490040145013404102070458900465021b5010708070340c414210019a0f5200c0c81c2032115025810207820001585040e90000d0b142d4150300301c407104001906008501240c0240004880000300d4200500c070880d0000481d0783c480c41a0002040022801c0c001c0c002e100d00041c200614020010011811903141c403010b0300c640c903485c0c0c0300c82000245004083e501a00300004241c001c01d1401401240306400401154290b850031280046082030500f444004080020819520030b407041c4900c50025081c2200240a14000c140182c1d40500210401c1052187c960041d03120900048824240680101c04d40f507005400280d110755144840c14954003030302424040702d55030b81c60a00d0017a0303511020380c81301c070707400070510101d81260707580402880c2d0301d503e54003003c0c000100038270031611180002d20b0342c40c0c1810b42e8001c001c503450440c0b48090780340360030103c4200c0315504149 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 493652679 1250 493651429 493651441
    0xa0302010f140c0708030304110a03080712140a171609060c0f0804081609060e18010f0513060509010506060306190503030406080a0b04050114060a020f150906011401021b1c0b 77
    0x1114500701d0715080f03410012035491541c90a40034071800d040248400222402e0143b1580101d40c0d803482c180261607903954407108030388028800c85484a542d4030411440011401420145910388100b220782d40310070328a242441c0c029904025807810440d080c50f8a9200c480000d1081c80c00f401c000c00c900001007046000c1200d041818110540141c1e1009141c030070100208000c08407401c0e00a40348070344006480000103d250301400310b000900310030b142044107204141480d451020b42003401342c2003c0195840c3d02c540c4e50309803003041e90030560200042c400300c0d80b1480c2544041c1d03001045002e001990980c1c40c3d02003402c54205078801804601c031503007013204080450054018030348084808011940c1009160140c40c407080d2900d0740290000320701c0c0f150303513030003000b825411a030f100088600744103555a24400000c412190070040e80100d400020309098102000c1404100c141c010780681a4204c5078550030300843c0081c291700a0240040120341008020012191030240c0009501427802c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 493653929 1250 493652679 493652693
    0x5030f01090c0e06180d140c01080405120a18090213120c06030b030c1c020103061203050a05030705040e07020a05012007020411040314010b0a050a0302010f140c0708030304 76
    0x507409484924100382601188a6000101c00e007200d204507510b64895500b2004e051041c88001807440d00a00c0284d41380c0c060012034003407010301c103016104913a149402c0000440300e068003034900508541c01060204180ea441e4405815152000e00d070000d00c0244650058a00c003000c0c0d0b11125100d41d00262040900c0c4d4004c1c848009070019100d031840c16210b40da1408152611032040740f040569420064582c0d03a418071110782c00601c020301c806020403640b004010466000c4004074003003031902c0c100040c842c00100c01000440c2e01512142c1c14004650710943d440d070b00080c4030a003004010440402d0700040305080702c4c041c0416600815030303e0b80a150583c216801c0321840d20300201f086d20600d00c03c041c5041103400180c3c1c10748011039004002003000d03140c0e014580008148035440c003407622403100152f0204150610484144d603040303594005202404c021408003074001a80c480c200c6205500902c10f8001102441c5011454082080001410100d03550000d441541001003480144482 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 493655179 1250 493653929 493653931
    0xf092f21070b07081b071e18050106020322030605090a05010e16090b1807110d03050c070b0405210403110907021f14040c062003090d080906040605030f 67
    0x552070b84928041013501e0f000003a00903000c0b0001c8070805101c900c210000d003481803400900415010011a120360076520b105082c1e0360041c081d8140521301200a013998900400f812640103801075480d04982c5440e40500002e0004061051080042d00000207031807403185900c102c004801900e003520003840e080e030a64140b00b40140c8203034408400c201058100031502821124402c600107101c5130700c1808034101c8030b402d15154440c40607110821800365000002d9400d82e0182d0f07000c2d84c10300f2111000590889405903104042d9403000d00114002a80b425100f54100d40a81c1c2160709504a000c0d00309a02c0506106000f50402d02280420070030800707031520320030740e04102c030541260314120700001c1d6101e1010f8400c1440d40580840c00e01c25032919404101c04544118038101c091505091141450b90033b4450f10300022515181010001082e004001c9109550009135243c030a1400400110010328501036903101002c016803025039944000900c000c1c2410f4881c0c0f600c900c2d04a031103075a0424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 493656429 1250 493655179 493655189
    0xd03050a0806010c03080c13170705120d0509130f06090f0c0306150521011d07020a0b1f0503100504031b08030c13150804060f092f2107 60
    0x4c4403050142c0000d4100c101503500010350181c01d511551800014103c82c3e09540c0005118180280a500100380100344042560001d46a10f11003800000c801c9684000b040d120350002101802082114035042c1030105851208c0400070030a2501165200100c2d80d856100c3d4281c15030301c2454020807183c80c000ca0903005014203082000a2074640c001c102090321307450303c5041000001d02c042101100725040440c9140754150b8092030368544840c1e00852145060018510103003200080fa50740c40010340420150340010600000c1c0c42d00145400c0d1007041030032904004114080101e001d03102000300300c056140042000c00c00342080d040c00f5000d8407248100040e8090030b2941c1d20040b600c00c2d4101e90f0040180c000040d0344061424290070b000045810654001c81c1110380500380c55444100c0300e0140340210170070401050302d43c1d0154111006a0802400501e400307001980c0d60390401c200507481243d00c5510240440c02d100000c00c01040c05030291031258205201c01c40c00c890030400000030302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 493657679 1250 493656429 493656437
    0x120306140312030414030c060c21011202040e070503100204090513030804030f0c0215070506090c0d02010c051e030a020d05182205072304030f080d0207020d03050a080601 75
    0x3a0030318581c0a00c00104050500d40410b10311703904c4132400704102e6000c01204026074000307080c002c482146545c442103440c00f203881c068122a0700c4c1c610124100d4101c0c0e01c00c52210800a00c0ca41c01e000140100ca00500709a001e0480d0010707060702c050120700383d130305400900113907500e0070240040d01f1940003a05400500550801c40000281c024070380d20f4200c1d0300360074002c9103060400822a03c000704280002c3d0070034041142e492407407026002901e902071150003910b40c941e1760080c550360b4408541c01a181e200c084c403400c050155000b14410b010a502810030350b501c080907010060000102d11014110a40c0b002a500403000c1e8103201c0c4456014142c036104d85030200e00c0c043c40d101c3e0707100707603d50520130000000282c82d03011043c0501070103400d03d03080501031841c0c0701d42e02800200c1107032900607110b00700e02c010094624a8004a40950b0750284110401e014541c0300e40050390810044200c405a08000c2000560b80305040f69000c40d00c0b03aa14a65500c002803002000503030054a81c1d4180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 493658929 1250 493657679 493657693
    0x31602041107031b0f0206160b090d0806010f0212070804050a0e0c1b0a020909010c200a030e0102030f13060e0103150e060316090c110601061205131203061403 70
    0x80e4024504c01c0303400c40e020000e40003016181400c01c0d81ea55101e0f0000e600c241d0011341d8002100594080c0c0301c0c0640a104500840d40c3c0711a1070a88581a900344031000614610002d14690b008818180e0b0524492041310400545d540c0d1711440f9611812060700c074060080790810240c60030205c140040d01d641ca040c800c45040c0300c03a0100b901e02403804607400f41340c651741d190111240200803228101d0740003081d800c21303814034016903402000c40c2000180003e120790207008103075a42e0403203008004500c1008010341400c0340c4007111075110040449045020800000c000f400b10540030780054644a501215864030300080600f00610312100e05d4103150400e0705c031882d108070742c0c0f0b041421a81c03401a00340c85035403a4400281041c0b14440e0030b9a03005000040820000e44541c052403806070b8549400c2c103140c01600409503030742006d10610001900800c0300c40c0304020140c20030b982103005402802c100c00348954416035056809003510b170010b641c40308100000503980c01d440c00008002e4001d8921 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 493660179 1250 493658929 493658933
    0xa38012d0f030215070210081503010e0616020a080304051f05060607060b01050d11070506060d0221030f0708030a110a0207140a0b03040302210a0c02091305031602041107 75
    0x200c0003440c48040e21421107504001010070039013089031030f1103034010180e0000c10354200000e00f00c00e0301515030b0080e40c03240351080b40030360505104548030340b402d6100400315541c0300508581040c0300b0704400002c6014a80ea104002816074020b0340c0618402c1002c0d2260f600c00c11076a8100404982c0c081c800c0303505003001d0094075103480d0101c0c0d070041d030002d0340820340d06a0000180e44907c100b08019140c00e2601c006801400300c01c43c00b820302148240b050751140e460324001c0080c600070341030000e94000c000548140801c03c03a084140d014000d4441580d0501e90134015440580e040f8500681e19210004100601640640324600b68903002400c030301c1c100355040308002e548004034052040b00c2118104541c0780c960381d02000c80001c040f940000d903501d01d40b5150082d02e800100781c140035010000000c10103040744020942d100090a40c0c4ca090402001e40c08100317501c0405000d401126118082c540042403043c00208050400c40d19003a0b1310384142d106101c215200c4105041030000d0621080e00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 493661429 1250 493660179 493660199
    0xf0d090303030207060b060c1005091513030c02060708070201080f09120c07090e01020408070b040e0a0f020706050f18010213260304060305010e0105030a38012d 71
    0x81a65010300c0c00507190070081c90318100511000151960080000c6041c81e1000720000341050000007820b41071215454500f40d130381c0c0d58003090040021040759600007820701c980303825401401d14024504810030041640202c3c005510076103007969040300028128080d540c20600d45030b041b64094524150a180a4280c1c034ac4843c41099003440c0c5003800034148001c600100305407030180140f00c2d000c10a0008100c7c500d4001d51180c03251180500070f8000010701c030800d4038180da084401c2100300c000b0503992610f180b00100451030f0440103103507080c00017130003041e21880780b20b00c546c451008803003581c2021034004042100c119644d65250303004101035100d01d6642020202207650a07414054401080c200c645501410313410704c0c61141c840440c0001e486589a00005e0403140440c000800c0741e604c640c03d16890b02062000a414180302610001e03003c0c00d00f90208480080803650b03100041e403030020f4816088001c2e4081104400000094006410200c0e246007401c4103c40800c00190f1914800f40c3c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 493662679 1250 493661429 493661447
    0x1a060121140a0f0b01050c0309040203070c06020c0706030605121507021e07230904020d08041701020415020a0c1205070b0307030905070905011805040813080f0f0d 72
    0x20405a04405100a522401e0704488240c002021000c0361910b0030408040042007010f080d07007036140c00c040a503501035000e4022600102c00860266280180791000e200c080d500141200302040101d4484d6004500759201422201c864030016240c420310302000202038400302e0700082c1c030072031250f522840d1100d00015007103d500a819207008860303072008030076814080105420850700c03403030064006030f05a010600b08103441d0301902a0124454000107007450282000301d45401131294000b03c3c01516104002140452040389540c1c6007135140d050141d00b40d0504da24100250790082420f214502ca04843c6800410303545c8020700700c010301034a90341808d03245032040150f0090700b15036100c01e000d814000d85000d08250305426941e41400030303000b0001c181801c0207560600492502062070900d81c010a8100d5050f002c1c002034202485004000a0001410440d040c480812058024482c03d00c4104000c0032044c000d0003126070402e42d000e0030202c040d0f200c2d04842d040030881e81c481d250030042c14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 493663929 1250 493662679 493662707
    0x10f050418050a050307050d1e050d0b120703050c1e0108070c06180203061b04060e01020c102c0303041401020f010603211103040b091c0f1a0601 64
    0xc079100007008024840c400c25004058028000c041e1120140a00040144049807145c2d0445e882001c40e0f48044070f810880c0b400000da520411040800014891406070560211994000450358002000140000e1850440034016000f9030750402c24010103100380c12041000b9140e440d01c031906908522003a45038061814180115040812040e80c80358a100030501d81c0124200004014a400c1110408409030228803d03c18003000501e04d0041e580401070040d080707000141450306260b0265003004105168074110f100710890445150760300011003013500b620ba242c605041241441c0c0e15034100072401c1908109003600031042140d1400000c43c2c089641070303150a41060103601c0100e0400c85101e18007001903023000300104c10300140c1c021a48060710014030003030000c40d42103000d4038010201100603005070018041001650340184c01800700800c000d011000441500e080b0200780502c1010036901c00c0d5117805004200051042140d514410441903c1c0c01072800c2d03800280042842500c1d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 493665179 1250 493663929 493663931
    0x70201050a0504030c0305010b130b03060f07051c05070e030a030512060111060708060f010c0c0b0f0c03040807051804020919020d0e030c19080a031a0a09020904060503010203010f0504 81
    0x52690042c440c400740e80c00755a019440692644e0382c0e08100340030382003007201d45110b242c44041485a1813101d01c50758020a8000d0060003e99a80c1d101c0e100a2000042008083c0f050070005005c0080f03030082c002500c1103a00030002117900b418440144680c4e18140c07618043d9210400c1b540120707800c1000e4880030343e21042500d4107541d40302c0c0121004c0303540c007110b80814401d031002e2088103034109005034847c41003500c00d031800b40c60100c0111064680d01c00060042c510420082c05030b030f0400d03c01815050762148005142c00000c20105166901a900a102541101d1001e106614060103407551003000c0d142d0300011030415400140360701c0c20151240d07569000402d0040c034020030b1501940c00c2035410b08010800c102125040703c1d126400418030302050301800d03420141e100703240191007600b01d0700410340504200704410281d0040000c84455011802403048140380c0d42d0701d503400000517041d901c20142e11881040b0a000569501d600850305c203900500c01403103101140b40040003210001c8134 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 493666429 1250 493665179 493665187
    0x30708090406030f0f15020310050405130803040506071101061d18071d010510020a170d060f090c02060906160c0b0f2a0901030f1b11010b1507020105 66
    0x140c002e084641c4010020010001e500061101901c214804640a0a80c2c50483d4500b0820001280b204035100071a44403812070500040c00d00d03601c056808000c00e008006804103580300c82506800845048410b603100b10100192075a100c481300d070100c40c82ca4002e01c030650a2040c1500c04d940c04458588020040100041001c0741400590780880308800649035120346403800302030760031002d641960314480514000180b6051400003a540512554080c05a0399410f98400c1401801350000d480010414064512003a19921400004000280824100e186072012105c02d40f6013031009201550004010400542c4d000b14925520103003003800b43da141ca00c0e201c0241e900d2400c3e11405070240d005e5000300a40d8585400555008188065407641305901c2c0050520010f0b00210301e0780c1e0892802d108140d2294040e41104c1307025100c6940210341d100740c001190a84105001c0c5001c0055000048881e50718000c1c40b40203403081c003c3d06c04a02d480b803175903120502840342080003810400005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 493667679 1250 493666429 493666447
    0x22110020f040603050c070c0801052d04021c060c02010501090f050f01050f0a09020d05220812060a0801020c0a030e03160e090115170606012a0302010f09080d1a03030708 75
    0x1e040302c81c42a40444030740611a25001c0c2765000f41800c46100307410b84004a054848107a15100141640c0d580041840c030380d549542c01d021b9100c0c0703a030010a03400c0c50041d8801d00040d5107402081d1266100e54000141503141207403c0e415640111020032103079161205025500b09245105030540f04252606052072040360041288005182d200082c428404550108010720702d8203e0303030103444090302d100d060494a11130703c030307840e406c0e54002004c00c00300300902e100e1640a05103c40c1c0c80b40e801071107402d166030f681c03207200c0c2a07900c66021012035801000145080640080503041c420100307600a00c1e150600c004402074520860089401001c0400b0004113850001d41024008400e9500c0700b00d03c241c3d0340d103050781c9204560074800344035004800020b0029482803560000003520013170f82205200c000e907001034a0f0203410720309400315504c5001c601c3c2032180702e000c2c80c001c0600c40d4030343d80c1d50303445201224002c40d288940030f5100c200102c40450110f540c00070076521400e8002c1a050340d01d40c0700c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 493668929 1250 493667679 493667701
    0x2152203051b0106050f060f0412060603060509100e01540c14060412060b0306150a0b04030f02100314041a0601090f15030207022110020f04060305 65
    0x2142d0304408040c248003180222100641011044030425104003e000c940740301004554000c0c1da080c201d0941090204120610220403482280c60044800064440d22603c0b01401d071641115000030540c0a01c4821251080d40e20518440082c10002041151354140e031b50301a90403a80e078000e1044407030760010f2603000c00d60b108500041c02002c013491000828554460314811040c4029502e5038204d80b40003510b8118400004080e03580201403902d41820070794461400108604e090312415600d01c61400e1a0314108501c038090000217918031445002442042040e820b42d410441807200f040c4810000584886509040907030b040b075140140c0d10100300c048004040390320340c140381c440342c10041c417060290307884c48481c4065546880c0c03013080e0743d0b500040d1400c18191169031200e02d0f0562080002c1e10700144001e000003110316000d4508807054002407031440303400c01082c0c0811802e51607041120b40070000ca04062018001c2035045c400d01c3d41d0410001e00542c4102c405041d241c00000d400c080342 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 493670179 1250 493668929 493668937
    0x50415030605030c15220510230a030f0606120b120c0904080c010216060f2c070803031806090a030c020409030302160516050303091e1f0206070215220305 68
    0x11b00c860000d0001d002241c0e032003480400d114a9006000d000b2181c54904e1242003680d40f981090344910007802c01c405a248102d40c40007504500b0141e4880140e10003d21078003c40004000e40d079518210300000b201c1030400c0b81c3c1c096010754844c035840350480c0951040402d401605103411140903041d69a54103020700984101e511011955100040304640c0d44d03000105c400c156130141030100080f40c201620700c005c075038400700602055141c07040000c1c02c0e218181c9400742864950800c1e10401d607654080240740d5041580c0c034030101010440b4003855040304104182e482048280142518002601e007e40703c0160b101c8007901640d260942c40b4203050207501101c1c071525010171140304400241c2402900c49042c0140c0c02c1c00c00d048004005202e00d0004240c502080008002c00c04401c841300707810060001010300c0c141c1004090100411188a04a124259209680180840f450000c0d8003e04184040301c400000d01c0c420310a2000c081602c000f02c1011042038040c2214040302030070b0a03103144c06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 493671429 1250 493670179 493670197
    0x150207050a12030f05010b07030e120705031504062703030b010923120606060a030510051002210f04090e12040b070507080c030307020d0c08060403050415030605030c15 74
    0x40502c407445440e6066124164042c0d00d00c0007080682d0320340b0348045080c0306409002d000900326401450607454500c8504004015840880e990b8980c1c65002c2400c00417105240c1031042c2c0028104000e001140c09070161410a5000c0e10300030715440d0028032910310085901900305603541c9500b20703840c0d0084441401510701480202001c1000750040408030305003202d043e0058128003040703040307070780b001894901400005081d5410b00c469000200d00614000301024001c10350300d24005aa42c8030b0310329183c44240554054180c00004c4a09001031003070109401500c51020851031022070380b81c005880c00d944060340c000c40c07041d680d04c1c201841c00100d20721080c4400000100040c0c00804c035030040200038810000c1d00c00d116070b5a03000341d407030724112405260981c0007008024014a80040c001c035449104040401d82c0070b8031000158074085c0d089404401084002a042c0440c1e000c80482c0740031103545180902100d8101780101e9291104480c0d120b000b400104801218403415070142e800d020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 493672679 1250 493671429 493671443
    0x10b1018030c0b030411030705091506040e070804021c050c04022206020c0103060602061e0c0712021501050603092a030a0804030b06010912030f031413030219150207050a 75
    0x280c5880c68200c3c664416242100e0003800304c82200d2207400c02180c00001c8500042210401d5510079541076140c64240244c280e000f4002c010100d08080b0013144070340204855915580f003803802e40b0512403c4029051151020607075813040c0d20001d40c00040c001e4000c04140c40c0980c407000030907098400035450141c543c00740c01031560b0110b0201e6002401c107c000600748d03401c2c4841955060141d0300d504050318060000d05803e00302015806881e45c0180e0049c2c440d000c8145410340a46855000410b00e082c5940140c01111086006507040c005850161004841803481e40c14148005070743c2e1480d03c42030400c21420f08000e01c4000c02e4882490742090800f81c03d9400815032031802d00500c3e48240002c580c3e400e910004100d05504c121070b80410b07101100d1540a200042ea101070750b804c0710b400ca55504043d280c134503114418002501440c007842c02c010100703c00c1e15061402a003010f06000301840102c2002040a0214031108021060900386820050340c8000ba420070a00744100001d01405031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 493673929 1250 493672679 493672703
    0x90f1104060b090f040b03030906030403110d0e01020303070e010e03070339030f02060d18020102070b030c091c1a0708010603060b0a050a090e090a0b09010b101803 72
    0x8026020420188000111020404591500d50007000390090101940e00301d050810071000900785940420700192000341120708145242000420030f03030080302c0440018001c095130041243c02041070110071040e50412000581d40035000235901c0c013008185604001e28560b03900003d9008450071850300c08041e05442072241c49080c01e80d0900308040c80d0150310100413050032030603260426030020800d110103607410389602d1511040d2425442c400180c0c5d000000b0006129a03032041d1250085d800036540c0d008a40c58410700019082c4a0164090303016004200b081141d50030381d40d012680c5d002c80c00c6820300d40090501d45544005100286c1c020070484406500c600686c800c048c4840c4149600d958201d0160780303851080303098840c240b040070074440b01072040200c4540650083c08601c3c135940b5080740501da03540e4203103c103180266403252090b0043c0341114180010600445c0c5d01070b007900002c0c8039101c50407020404020740c1e01c1e41c2000b00000500310380507203803400c0c07290710046810080100c02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 493675179 1250 493673929 493673933
    0x7080f0904200c1501050d0201050a050f1813060b0d110706090c081e12090f10030203270316150c090e1303081803040e01030c0f0f030c1503090f 64
    0x49910101c1c001e4280e1081000d520716005000506070305030f91001d1f151501c8608030703500560303c0d038000d58a0401800740c203220107004070700150040c0076032130b008100710900d118007541030002050504031540c84440c24135070140f0241000e441202d0f02030780c1005c4001558081c030316214440380100c4000074541428140d041d001d000104140c1300980d6100d0080ea4800c100700710701c5d10705011060301c82c585150803030300f520908130120704007030000d4240103490030300746d45207210001c1c100036054020100405d17808024040006c1403400403c407884080e13180e140b40209140d4805a40c0c0c0908007003001c144c801d6030740305810800804560158450390302418000c1c400b500201420410b000e0040c0b480d01c50004001031581801c420b00d44801d2074040d04d8000030703034841c2c460440c1c40c03075100040858240f104003c0000c54100c100c03078442c0258010384a101c0054200407064205880e181d110708103040e142801070020070600c0103030310b0440e110040504001d0741e030200d05038080d25102e403014014859903404681 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 493676429 1250 493675179 493675241
    0xe1e06070c0e0606180d020d020303160303050108010e030403140c06030c0403021c1101030911030a11101e03022a0c031005090d0c08120106050a110307080f0904 71
    0x15518542490748a0742c0e555424009a4000da17916003010085208209880d03051070034030036000ea800640000c03141d42081d0086407940c2d02003c50310f804100313400545814107505101c5c5a0142c2950b000a20086010803510ba68901460002415640d1003e081c05540b400c104450f0303600380303006885640c0b41d02e040440d05045420a1100b640900c401001741c0e1310801a43e120800b2181c0e008550203030700031111004500501e00d100d4102c6199100d00340da151159002c110f083d42807441001c0030740c1c40c40d01c03030824411000e103221200310038860f1520020f4000c584640703a84000c2015841c1c0143c441800314412030304a1000f41c068012031007000180c600c00d56012074003054408042d011100c541c0c0d10050600d0882e0000c4614402d607030851094104220b119142c814840385c010046241420010350185112003002c2e48803070b000c204009080d51005030804811908000c0f00d0024505061458407107000a1207443c004411601e4005042441540ca60f400441000c520503500700d0403c0101441f07031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 493677679 1250 493676429 493676453
    0x100c08251407050108010513020c1e01060305010b18010611030f0a0e040c0c170a12060801090b070810090b061b07051302130b0a0207030b04050309040f0c0e1e0607 72
    0x91030044160108482d4060085c132812517001520f0008503171010301c49480250001c3c0340c180d402d400741001d910005064841000444032407030f000000d0042c990b2500c1400c441c4800500c5004285508418008079110180c0a0440f072160401c8941031090450392400c520900c0354040c9120f0021400d494a5540905134404000c000d44c0c0421800007509020f0b50104044800200203100c0342000781c1c5100d00c03d070b0240514a1284c02d0424a000411250b40c040d200590803500803a9518400202070002d54011140c1280180c2080c0d400c0d4105280391b034801d640a07010308015542ca486031030035192681c008413217041c8a0101c0e44614000d03400785143d01d4621030f2180e10b01c07400031401ca400014200b88202d0300c002e1803208030071411074644864210107030404a88203045d8050294000046601e11030000e10032441800a1680c80c0d004001b088100c03010710341304403a100d1410f042c00482503007101d11213200380b50440713404020402da42400d205821111010680144005c140b82d81080010b0300c040b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 493678929 1250 493677679 493677713
    0x61c030903061a0a05040209040609091202010c0f0f1b08032701110715110c03030a05070f020d08100911040315020a05160804050d120905100c0825 65
    0xb40304643d64101c40b651120709a822044d40b02ea032801e000c010300c0c6850fa00074000280d0107400440c2c11903840e050b1400722004d640058038000d10f0541d106112507030a116007034100025040c0038501a0b40350000510100d080d4001c00140041c0c0c0c07411440069180c2c840d449c281c2c0e40710359000d03581d1801c0904244604c0e01c0114048107207a00c810f106d00c038181c060040d4502c0500845102d0700740b070059112003020b80d11201c4628192991070420340d00c00c01040b0000c00300040c194000b940e8030b04180690f80200d4031700070812000c21a560400c0b5114982c0440c140444011030300d0b000e510358682041c100310000c0d00e5882195120300e41004494074030f001d40058411a0b0140301800b18030400881103005034825807010f04000340c01004407041d0b8544580e0b07040e02090150440341c1c00c06449402140381116884410340c1c51034003988141c0740d03103503011040b98003408098621302500c81102c04060224081d1540c018070600c00824280940d515000f285003580146648038111401c00d41003600003007983d5090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 493680179 1250 493678929 493678931
    0x703080f0a0e151c020c01060b0a0f0912060957060815040c0c060f06080d050a0c06110406080108030a050403110301021201030606260c0108061c03090306 68
    0xb19900d0310307000a4606a100c03030140744920301590041310900603480c80040d454056428003d5100701c500900c503507005480d0716502c684d0703a09444040500f000c00242c2d00c4404003c102d80080c446070803920000c4411503400715010071103554a00e010400740d0b116040d44144064400300e4101040d1000010400c42113849614410942000e4003400e1000c01e0480303184511221464100324407482422610350040541c0c440c407280700c250b18002400d0350031010030341c0000b464584a1100f80000ca1181401c40c540c5110108155464606055100c0799103d03400070a000011582c854060300404010183e0307613102d9410000c10070643e46e42105da8200c0d005034000207082c41c0001c50444400000c8a1440101d5100c1e642400e140d940e4100300303609961001d80c1c141d50203211001484600e0300456010350701c52180890507604041d8017070f041c004002450071440b03080514100014001080b010103811003881c0c8079095130340b8040414441d08080c1c1c1c44102d040c44102c0c480050540c8040130f007050301e00c1898 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 493681429 1250 493680179 493680197
    0xa1e02210405030406090801110315031501091d010c080c09010504030804080724080c07060e012d0204050a05060c070e0403020d09090603240605040c1d10050301170703080f0a 77
    0x801d81c0d080727034005c50030084000410408650b2103150184545c8480c1c000030201c2d02d90f100e5165446031400b03003c0e8007180b01c40d42c541440d0345400b90358401002c00313405200020820800d05550041002078040c0103011140000a017480d110b0b403091080b2030281d60811b0107203580c2ea42c3c843c03e10360f8424051040090441311092400f098144035016000c0c00d5402d40e41d00c9105885144400c60036610400044424694440c100404a01d080c041d5480d910300c101050003141e010403e40d1031045000d411a10041481080103014a5681d96980b905a030802e0316420b40300c0d0a292011031800003a60050080c00c0d03880f0303007007008242d4009906810750107555200314485a440e00c85030103450741c0e408014240071036000c0d14140084546407200300e40c100380001203482c0303541e080800c0860f580900c4550003d41c06003440420303080c281c00b0550170120155001500700c0082d150043c56804103016601760300704c2c0150580383ca99170800041025540102411740e450032110301043e1a0350103a100d503408503143c4a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 493682679 1250 493681429 493681439
    0x1b040b1204060c08060907030e0313030b1501050c192604031a0f060907020a0b0106170115050714010605030d030506101713032105010e0a1e0221040503040609 70
    0x102c00140141d002130100e06847d03c8091042d005000100d005481c0e51200303100e0140c4081341c1e141c81c13a0046001b015012150304000c1c0b000c504104101000034107001d420081c8a5a881c1c0c0091804031303100d07400c2075a0030100c0c190f152112090404150402503800302d010210041c19034500248102da1140d84001518480703101d45500b080d00071a49040d001c150f50000490034100700f6100c0b6444415441030f02d174420b03820303615950725903001e8100c0c0f0300003000c2c0000411035000c20380d02030303024101314282c5040c3c006403450014144e2007a12070003080d02c988006600007241d000d400c201e02500f80101541ca05205404c1d0040040004480180c8550581c0b003a240705035005070b20b0355040c21001c80400c03040e41d07a4152500312010b1041c2e022000c00c0001a0f08502d00f00c0a916000c4100d4000300c00410254502000080c103202c2c041c200c40f418a140030550203044106071b10349000c00010000160722007000091280c540e252603901c1c00101e508400c01c00c000c105e004001042900c88946402404585030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 493683929 1250 493682679 493682687
    0x604030605070f02011509050a0e060c0c010c0c0203060c07170d0f060509191802090a1d070806040f03120c030f0513080405130923120306091b040b1204060c 69
    0x680c00080300300c00c6c204003071182c1c0c0556007240350f00419031038011030700c0c4200e5040d040c40d14804a41c032152844000c079055004c080e0070f0042d00c004440d10324002c050518590006034031004081d01134030401038001a60010407461003c450600005080040e441e0586824600007900c070f10700302c0d000140d1a00b60040303610b241460f045030145611000840d00f40fa80440f804008140300c203031a50110159000c0c640041c0c0e02c282c20303c1d20800f080000071881840740001c80f52007070075144035011150841d402c14084d01c0b0380080c0d01944183c016850f2030480007075040a403000589544062060350405406040e541d40603000301103a203040c2d090410513070799142c1380c01c1030b2064880130080c050181040100014501841111404491414009551074555030307206c2c40599441080001d0410305c08841c0e0340e4030b0381130180c2c010242100240e20314520781100018803003240104003081c440c01092200e070540d079241c000d503005096880314059a410141c0883c07610074100f114112191030510407200e40715445 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 493685179 1250 493683929 493683941
    0x70c210b132307180c050319151214010606020d03180b010b22081e072706060f211b0201150f03120c0611210a05070504090c0e0604030605070f0201 65
    0x5c19a10a03055880c0c1d000100d0b0200c00200c03440e103043e5100c1510700500d00b0500103100081c0010812450030440e140b50000101c04208540f5102c6c0e45402c100700070b0141c000c07035035007540413080c40c00081003910500604904070110350060315022058002151086020f002090349056074007440e840100383c0340003501d209580d405041c030150455040782503809964444000c2009505040c0da401076110352400e03000402400d0481c0d0a00100103503810030f506a8450280a0107a074540860003103811007029103004150b02920100d01d40054003040303501c0c10b40e070101c80c004c403003885507091503581140000c2c060004d110b111140e100a00030000780070a405448c1d1000c40713a00c944841400440c0f4003080e10a00890305080e503005480300c6010466003020401840030003010042d28042131a000b40301e4600f000c0082ca600801d078035007020701007d41d4006055404030f4203000c13400302e62880c1d40c0c00111445c2c004402c0c0700b5004280803030041304200b507580009210701d4190780c0e4180041e00703828049090b641 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 493686429 1250 493685179 493685201
    0xc160f05150907140d1b260c060309030705010603120e0108060a050904050f0a030f030b01021f0f02090d0c031109100b0906040803070c210b13230718 66
    0x3c0020410000c040c013070382100c00c00403002015029800050b456817041c01000b40c1d0009042c0c40b80d910309000341041030380c4c00c079441c01d10b03082c0c03c0a940c071808118594910307528150324898040130000031300341035042007211903095008001780720040e80c901d0154403000c100041000490303091510010203501c0713034088520815000782490045031601e41403102044000d40705890301c0c0582402015031200800c61070a040d88282c1e0f81c180500c0c214080201103c0002c81d030581150405540c250300b03000070100e401c1d03880c0290f500000d8400d007041042e200a01c50f901d84130381c0001c80d0302884801d10480580d04c00c22a030007160506449800c0e4010020304a80450755541104c00b40300061044840c0300018041407440904054500780e1520030403031840d0404001100c0f031036280c10080c080c02141c0c0107a1803204030300d82d40d40d6056840b40d58801c020070070010841203220110790300c60303401c1c0070300b404c0c454005060140880c1e00340400300c07106030381750f4003140241500a9058030710101e0100c601d10456200413 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 493687679 1250 493686429 493686433
    0xc021c05060f0606070209090f070e0105090a0c09050a0b03010504050a02070803151c05010515060a02071404320915010909030207030203030a111204030b040b0c160f051509 76
    0x40d48400c0c2c440c800003405086180c03c20800d0103400d0058440e450614040d0f141440180236203903241d003049280c0318403a00122580000040100626103ca1082d140c000302c1c0860042580c660f5154202c2d2180800d46c0810342c400d07908040003130412a08802503042c1d44040c4c0c2c0a001075075031407400005038072900ca4010525802000014003d9240821300e8007004802056514415450180e40c00c0c2c2098104042d10581d5480f800c1c0800442c030002d164140a41c1554114140420144040d4550100c0d105000c108076044a15a40503959544220044a0381c00105500070140d00c60407402d91600c40b18410881d42100017241d4240c1c400180841c00c440f0b1906c84941581c00c100c0300c0006041010b400300c00f035203e00342c80440140c0d13081c4050020b04010756103641e9509024a10140351074001143c900c1c441004102c1440840c00c0150342d187c0c8160031141008550f00c0d98865400648242e040c00100c001d44e0340c020320100b02c6414010305e085800740003118002550790407554103503001620310314019 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 493688929 1250 493687679 493687681
    0x207020111060c0915040305010911010305070f050406030e011e0902120c06180301020d0e010b030d0c080a030203100f0303030906050705091e0f12070512070b030105010507060b060a0c021c0506 85
    0x607180c00302040b9420520920258100747c0d507561414203580c100c0c0340c11a084070585070760b1740030b55070305104056100d031403440d2801c41c191050a01605900c51409240304040d1603030010141c4000135045a2013001c01540c02c1007814a01e180f000004022506040b0310a44682ca00306e04010000905107511190040c8054074211030325540c040309410030001250955028801440b507140070784140e400030741c0710708004260b841409081508052071007103103c0c2400a500d0f1180c000c83c90000075078190f4103a5050041e81c0351070780c909065141800c1d5101e01483d00c0d03001c80c04820035500d40c100303402251003004240990b0b240c682082c0c41c0342c000ca0002c260462400c8400c00c0041c64402c49500706203e024007001d8400c000000400e440000804401c14641c9c481d0804025a0620420640340070b0140c401030001c01d401d000703031415184010303c42c2c98104000419510148401136002e800c00311001002980d40d901c10440180ca45507010005130f205420704054056a03600b07007803405a4a80d0310034060032039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 493690179 1250 493688929 493688947
    0x106030c14041503111602030d02030a14030603070b04150305010e04020d021306180614010309081902070509040b1b0901210e01020304050307060e15070e0111010606030207020111060c 81
    0x9075082400c040684a100c8000a40500e80c0281b12204441748000c020880c9801070510f40300c104000002158020407505030303e16804418032821000703000000d41d031f0340c803072100281c131700099504551403d800c006000690303005040845c6004405ca9103007805030b41c0c0d170b610700c2c0628240c00300d4002c0c0d00083e0315101c44005151244014180c911002c6000031030340d886221145d01101400b600120065503207000b8810300d107200c0b1070510b40b11400d203014000c102842c1d584881078006d074150a11207070031503900506d50038024001d48019020280500e61a032a0500740401035440070b880b44c41d201e601d0300004e08000c10b00c500444001d5103045e102e00443c800c43ea1100008000360440d42100340d070b56150505c523195070a0004500a600407402161a000d203801c1c00e004403038001e006546c0c564804034401583e080c1d001d8000f1b078000460f080191080d03030307680016110b0b113181340c100000039403a1402c00305443d50103501604459000781c0e04c4168010740101000d988000542d1aa80045c00c1800b440305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 493691429 1250 493690179 493690199
    0x605010c0f03021606050c0111040f0b18130b180c0f0a0201090804081c0801080d030c1b06051b0408032d0a0306090e06060117090106031a0106030c1404 67
    0x50018401d20454080c084d808261540100c3c0b01d40140d800902c1c0040d40305a980c030240500321100c4c142d03041480c0707807500d0b005d440b0302e05207403d200304444000c01182c1c00784018100c102400001101901407441007036407500e800018907102006500c10f4181c90215070b514400803002910a20001040d14640a110b0030100300540108420204540d03d5214503800a4000000b40006200d003400500c00716940100160040c02404400410000b004004000c16400020700d0121805c880c10000380c403203a010811960880803c16000c803098060360820304012590b031080788549020900c61202c0e08112004044501c0f032446450721540c41031103401c1c031150f0f903107070341a400900c0031004d200c095024620841d0300750484403104012a43e614820094103400e03005414806c8143c40c094009450420700203400b40c50100220040c0a00309000900c1e410801d41c1300d08003440e004046040703444000421034140c58800d004d2100041e040c60485050540aa5101d0401d00d4443c1142070074242881e500c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 493692679 1250 493691429 493691453
    0x105040612170309070f08010c080c0a0e01050304020a230102060717040209150a0f0f050a06080a0f020c2a010905031f0908030f0402030111041404050907050402031e07030605010c 79
    0x504c0340c0540c1900140304490301140b140101800e074004a06003600031006004041d00500e907001d80d0a0802030008010790003038200c6103110090905545944560010508214103900042c0d6a04d44c680542c685100c68050503800041c000d030b084480c6a070b00e16108803100410707030400c1000440c0c3e24021800502d04002056031208000d1142140d40354100e0005d005248036501c21540d00380c0c40785040c80041008041d05024110a51315803000c00d00d000c40080c6048401854100810396030141c407000046290116001c43c040d00381101c0d4001d0f8600b00007946c110202c54100b0603103020400300130a65020702c803050f0440c1c400502400c00011600704113902e02c40c0d003182c900c9000707a80340c5001000564641c095070003100088074110503450144145401c5503a084030610103103005000c20040400700306140c40c1c0c0100140c5000c115500c43c407903000c0c075020003070300f0135030f170050010003000b40380758010401c0b010300082d03000000195100d641e41034040340d00130300a031400a5024100c0801040c0000031071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 493693929 1250 493692679 493692691
    0xa051c11120604021e040602011a090408031302130b01090f0510050c0a0203070f0303081f15030e03030f0609130201020a0303091b0b0d060f18090807051501050406121703 75
    0x1500c1c5c00a41d001180240300000304507213032407a0104040c001240d0911540000ca00400642003c00c0c054000203074a0304c80041c0300401d1110000009a80200419120702c0b9007035005e0300d51501c8211903100b05c400b4004102c44d290008454a000151007038000f035441007294000b50040103071802112044546030b0160404802c80c0c81104d03c0c1500580781040408014440200c200030300c03a0661600402c080f03406401001814060003035613216201007038264080b41c201d0103500c0d05403021418254090072101450038120301000c020080101c1c0e880c1707080c40c4611011030350a800c658490700020300b04520401c010780140c2c0700c0c644010000340641e00020300341e0700449002854010384816680c80480c0380d000114180404650303200f2500030750286034040c001140003180149d0900101da0300036030300b000c000708820f44c441400105106000301100c41d02500501545e112255201031040e01403401c1c8035242c051440d04d4800030300304048510003401240d00c012555210b1030300307400c241c5154101a1030307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 493695179 1250 493693929 493693931
    0xc04030219030b0903090901060e0f100c1415070c080403080304110306071e05180d0f08041202030c09011d18190c170a030c0510020a051c11120604 65
    0x1c04008100002c000d11302c500a500000e581e903424502c14004c3c08481070303204e02c052200c030200c542019074078884885c4019400b511190320000e0418030880e4464030104010b86800b02c00d103d81c070b0385000041911004219030701a81140f98584d801c04072050242d160010b0800b0105000901c00194805c00442d002401805914092915000000c5c203012003681d0401c045194202c00e060b01c1d04021201700105c0001b070612a04119150014a943c00d0b009103031780d40310301ca040b9071841c200074091003521440c50b0002030054680c1c2d21f4010071ba01d0640441000e038031921801407052441e2078085c0055040e240610b5005e082d200d0044418115030401401c2d038050310600300c01c40065100c0c10070480c040c004080b07000810f0340450381040c1d4614003054001d8044a62004003200c0d030042d0009110441590506d414014506030381442400e000044c0040e2003140d00001d040c2088039488405400000d6251244184120703501428200300e80d40100360065544082c880f003000c078800c0990b10781e031042c00600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 493696429 1250 493695179 493695229
    0x60106090315051b04061d09060d021507050d02160909120305090a05061005090606040b030f090115060809060a1a040b01120513140c0d1104090f03051804050c040302 73
    0x210110350017940041c0c000480c002c08070811040c481c001482009003d135581ca00600784140811610000114043e00981e0090384515441d00b194040ba000180c00c00c3c1669140b401041d0001d4a5950010f40c40d03041c10118080400c030000e407403040120156018508034820110040c06801800c0300400c1c030b4180d0b00800d8070300760200b0401c0c880d00744941030b920210884a42054104101482d0141415006180030b1000384038210300031088a8003c081068101c04556a00c944203000d010182d001c054160745440f0002003180e0407030015400358901e24241c80c900d47c0c409800400319170301490340c054490201080c0e8841803c20f41d010f00b101e220107160107070300d0024213150002a60700998500c06484e02800c80c07541441000203080c00010080c00c041d001c1d1400350300001e5002d00d0145400341240c0c0d82e0000403e05039443e40c4c1301559240c1e1160340c1c201800c83c40c4c107003c0c0c82c6801c403c401d141c00c607030f004035102c106103020b03c10b40d44120b40805050382014119020320a51801c030710f9110301c400c0360f814 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 493697679 1250 493696429 493696471
    0x114042307060306090e03160605040f0614150420310306140c070b0a06050d11010f020c03030d02030702010b0a09021305060a170c041a090306010609031505 69
    0x20006001600b502d49022a036240b0742480b00040f40c44035800e44125400c28000400304440d40b031780c00c0044a8120710049815102ea0134022400003000c20020b003400d00e00247d5051110003211018440c040814001c0546180c54090000340c404120588401800201d42035580c03101c09030140141080c1140740c0c0310020b04500682c01c88562513107051940380c3c1041c1c07040040180034010071070303000105c2c1300d01034a5040c0500d41607054066064000e000100010000d00003d43d147c0c840070003024010703c00d4842d08010b040c6000104081028107001030005041c0d101a10b000280410429001400540c80c0c902d19400c4003001750009451003045548409400c00b0a0340ca801c3e42c40054644120010b0356204400015481030401c3d600c02409810207019599a179600096810040003500148050f16a84d040381c4c2007043c03149800c8443c1d00d0b455501d041c245011405d003d04504003042c1d04807440c91340c8489058032450040e200043c5214500108260288429001141c125074800d8500b2070100c0d0319 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 493698929 1250 493697679 493697683
    0x30f1602030c040c08011505090402031e0c030108340602160f05091303090503031c11070b1801090b0117061b092223010801140423 58
    0x118058181449a511108190715040c080c84003a090115810040c13500c1c51034000d00383d03690520550740d8580264440709441800703181100c41c11070000340115070340c0c600400d2110001480c0c003090804070105c0c80020740c440c3c0450088a042e074000030028046c0b182500c4c0047c8030712411004a0050400010030550711040045514015151540242c03500368054030414030b0501c2140d0048156038001c0200f0025a12031107034242d08124900489260b80255050a030394540c01c83e03008a4251000051159072100004140c0402040c01e6a050150307d0000c0b450081c18090103001a1410341804042840814002000c542d4020b02600114041d00d16468400200d0400d9100005a0389500400105104c0901c80580d00c004003040c11064003402d20040450740c011001118003440d4415900c000081600343c0d40005040909810b2280c040c404050300322050000c1d0240b0300e202c0d980c2d00041007a01c1c040c001d070350742e0301e402401701d164940c0d4503160304102d4904001084200e144011500c003030b6400c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 493700179 1250 493698929 493698937
    0xf0b040f0e120313020108060d12050306120c0907031812021501090e0601090e070f090204030302060609070509090408090603040b06030715050304080c0f100515010306080a0303050702030f 83
    0x103180000416003181c10180c0e082521266450300c000000300704202842407054601d030411034081c40c02c5100380d80c4100100d400c0d034024490150260040349101414940c0c0000214401c4a0988100111404080c04265160681c4800a030f0003111000040c01e4548207902c18155695810005445ca280988402585002d02104400107800507100d60405500b01c425107401003040b85010080700e054061003544680b01030045420450719080002d020090400850000e0010100031604240c1e441515070020b5100d88411009401188002005443d011241521810207174030b49502d080b81040c20418802c000a00c22a184040bd01000c0204e0305c03840c0c0554869445840030886a05014042618015403075120703500c4031014107001c018690303200e000daa0300709038842d00e070fa81c9500c0c481241504111070603c00441500c0748a00322100c41840307400050040e012400700084800c1000011001da0700e0b14024016964440d101400010b8400c2c0e001d10390107400352040d2400c0403204003490102e544 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 493701429 1250 493700179 493700201
    0xd0203010e06060705060a1109040608031c05061e13110319110a050304021206040c090c0e15092b02040b04050708010510020c0a3003120f0b04 63
    0x540400144070740c40640c200c01d0b821440c200c82c21401c02d1101d580710355440b48020a40551542c95030b950001500c2d01100340c0304100c400600074060903443d0700e00c4c2950b98010348560004452940801216000c061055500031078025201e60103854040714015080441c41807041d8000b0000e807585884415140706825003010700300c02c03440d500e00788110455045003001d140041c1140c90a01d0a184508402d421075100d0285c4d4103000b07441e0380d600d0000480b101507c9c103044415003d500200030030018801504410380308030600800080745007038400c03615104000c21094205c040180800c103104484d20190046040081601e80354540b0300002c0382c065800070390011008110721305043c01f1031400b4000c1c020401c0d01900c0c1042545032148000b00003442c1803103668000c202840707110380030302d100b40b0001c2e403909005041680301c0c59645424501d60707980d0111043d40310f0307030001c4c00c7c122400310800240701f8190941c0d83c070010380205211080007000102d0241d4891547e55134103101544960103404001c5d0703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 493702679 1250 493701429 493701431
    0x61e060c071d0711160909050f070303030b0307092c0c0d060e070b12010509060d0602031e060d1505060d061506030b0916081905040b070e0103020403150b0a05060d 72
    0x304102e2009001144d030354a07801519003107180a651060041009042103802035400071448185a0805508044440741020303000d0003162000b10615403d904500c0d24404203400b2100300ca0307a140581c20880b80c401e080c003482c64060012400005841d0040c002c22540480259209a8145400542000c01d00c0307400329100381d1030f5500c441041070244046001428070080442c6018606201c01080c95014040c00c2c2c4150041004625152034000f41100306940c001c60440d541c2c00e00c45041190840300182c0410070300080c90000340b8908003149010640c6611020703100320321034800c00903c00b4040003005c860f0132800c10016000800e005010741c12034034a600441c0da149600f02a001015140e81e502043e001e60b08079820b0028071348282200351214601440d202000d40c44643e032900740d004440b51030f40d10321810102484207202d44070080d02d0041040e42c035000c101c48650401501a4029480050070407003002c0c83c401c1032a003a64000b480d0f8200020a034668458035100010026004809099001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 493703929 1250 493702679 493702681
    0x10c20030711062b060605130b0c070810050609181e1f0515090606070305091507050d02010507030e0d0815030109050f0c01020a170d1b0314061e060c071d 68
    0x94031540c8228009041e50346020b0b0308c0c0280c1d2100c084464400b9100b0406c1c83c07440040c4050200000b48a104090019101650449110b40307030140c01604e425201d003403143c0d08050200702c0100c6007100c0100035001c00405880c417403032028000d500b25140c10414202c0c41c0580c2c000c42c80e410403002c010100701da16804000440e0b040c54286d000d4052005c9a546018810100621049607245c109a40300c5990620340b02d035480c010000818400400b6032003c0511120100303800041040102d0740f2030b1100c00c40d6000304072564071200120290f8203403110320003003034110907928502c0030301c2050710716030004118041300311036008800840d08460002d0304c145c4468014038401c0051450a11030581070200900c020320401429403180442d2a2840300f9058604800080c1248510300c01e4001c400910809107000d40c50010303680300a0040d00140d500640c201501c14001001490f0844c4003000e103c04122000b420800803070244043d80e030003680940789074071489000155218007488290720403504c1e03d580c0301003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 493705035 1106 493703929 493704007
    0x909041401021c0e060408090d0204060b03091c11030301170c10020f070b030423030d020c2b230f0408010c2003071106 53
    0x103154004102c00b24240781c84690103080145141e810f001c01350440f245562190002c50340103004c04c1d01072091f5000c2d4105031055011407440038100040c815102c0c0410601c0380c104403203542c05940038a507185c0301c1040c20760710b000510300756040c00c101c90b1110710549a104c0c08140108480c050301d682c8802d469580402841d00300c80c5d4060321034030b80d8041d00440203444100d4107412090350701c82c01000103103001300041181d11480e0461310203a40d2890111445e4030541d1114406403841c442070240c1e03415a80c0311710050000340c10440007003600003802c00b60b40e41403010b0300f8038a402ca84440c0084c1e034011504942150795503c0300307225207582c2d84602c1d0403000190141000c1d182c11014042008104110154010700c0c80c112262110044001401e1080046441d406840c01182c2c00901c490f50004100001c0f81c0c0c1000c000401c00303401d0000402d0000c8103a0541e1404201504110441a0f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 493525179 493705035 := by
  have h0 := BRFrame.cov_init 493525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 493525179 ≤ n) (h2 : n < 493705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
