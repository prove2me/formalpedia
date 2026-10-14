-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:14:11.440359+00:00
-- url     : https://prove2.me/submissions/c2efd682-cd78-47f1-ac1a-8dd7256b0af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 197482014 ≤ n < 197661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 197483264 1250 197482014 197482057
    0x706141b0106080a1a060d02060d0b0316081b0315010b180d0605060f090c0a050705101815020f0306040e1f0b090f060607033603030e010201090206 65
    0xd401004160301119161280e40c94034400c100c441c24000c008028650b585042503035492042c8035014030301e43e0000750302807010010030b88018050b601c060408500038041356100310104882055000894204c90025400b20600560400f030280a0020005c802d030050610803c0c2c003011880030103010b0107143c0030420b0106144124000d00a04500c242c0300003003042034800400d0410400a007401d84065006103446d807013581113401c1c00001103000394250507000e8074105e12001d080720b0b65003150b081101d1314050440c04c2c200c001613500440500342c810b0409506c003480d41d480c2c5140c506c208010342c4c4007818010310841010000d0328003030302d2f032250054802060307843c010043c060070910307103a14040c148500040d0171400520f01ea80540c7c2c4070380e03058441001c04d4546058040c15210f0481c2d055511280c20410000080e109900c481901da40c1300385424000003051050841044148140a44140c528901003083c15441590300c101c0310001c1c0000c000b1aa4281c0114140c0d120f20400d0b90b8085402c0f0291 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 197484514 1250 197483264 197483317
    0x3120a0801061115010f0503010b01030b030c0f040b030a050303071101060302030706140d0507050a140306030d140d11070c12020a1509080f0d08010501141204060908030a0509070614 80
    0xc20503495041c0070408643e10340b0311380c0c1b080c60400e00030680070350718008005030194002d10078003589201c0100240405030304d1a0410243d401c0e100d41013608030b6140c80c18030704640c07010070002101a110b400516180c0c81c200b84000c00c10710b0340f5500d01701c460381041c1d420800360b10045600b03019030328140b400480070406458800c80c04e00c104c0c5803600d00c90349030408000500d42e21202a128908181d80c0d2001c0d2007100e000e68116600050300c0700c940c107410009400b24240e0040081201c51400341030124102010400c045040721941105990f0b001d000141039001c01404042e8035010b071a12101c403401d00322841e00407442500b01070081d00d03094070100d20010011801040a400141515812541c1e205512109151100307241c1c94401c010800c2000041a1503014288105a040319038040d41d0510002d80004400b01d0000740054985030b81d40c409200200381d141008520070240c4801c040f0b01820164286441d000d90781e44480d041100c1c03502c5003003030742d40304100703c40c140c8081051020303804001016 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 197485764 1250 197484514 197484523
    0x91a01170a0f14040c03021002030c15130c0902040e060406081f020903070f0504150605030a09080403020a03080309120a02150a0e06160306091806090c0308030901090203120a08010611 81
    0x143d080c460b2103014104002c000d071480c040030a0b240709880d142d040c00d013101401d0740c0e60f00541081808a4000e10805081003148035492640084030620107101145280c680b68030242c0b664100320000d580000e400d00c02403a94210040d000b01064504100c81da1030107120a032122000b47d811002002c0c20f00741141d003010315030169050400300a040c0e5405960f22840301044c01c04502c41c4902032401e100c03c0710703c241e1844034403008036400b036100c0360300e16038a000c4040010102ca00003240d100030103200200c056121021100b002d184500455552402e009000c145444d11200d035216280108000d142911f0f030340440c1e000d0051200e001705820980ba001541009442e440c02c2101a9204038803c0003c1810f11240072006032800d901c0411409481d40e00c10b400b541c01c41c80b68074061801090400c0009102540620405070080803400390355603d070fa44000c1161700596400645030746401e4400203500d8203010741b56003034941310400c51610880150240c80b00405202da141070110450003811040300500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 197487014 1250 197485764 197485781
    0x50a05030703060e150f03060f1f090c090302030c040e0712150c0203070209070c0201020d0c2120060609010e130f0309150503040b040b07020a0606091a01170a0f 71
    0x503a11341071490409100b41ca4181d0450b0054890740034528140e20a05002c6420b5001c1c0b11034a0902009580ba04400421104030000648800780100d10014601c9181e10842c59056110340d039000c442c5103035004144c40d0140701103a16106a01e4890b091418003000a41001182c0b060b1248510301c06003801c2c2002c0c10402c03030b06d41e06a0107092007100d1008603404002810214070860301c03100d00740c0f2084411202d00c60780100003030150b030100c1064107015010381072050a46208103201c000c0410544196418a200748607004007007651850280715034090078100c0d4100d00c800c43c0080109207492000030f00050010b115015041c0c0240001c500341101600c030b514902904418200c210070b00a00e00100302c0318152041000000c07414500c102a103124204890003503810504002d60780d292500d42d070201c9880036081070150f00c28100000002041401050010117403c1000a5944280f200c91408007090420050420000128880c2c0c04000025445e030400c0285400160703420000781c1c00b400a05215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 197488264 1250 197487014 197487029
    0xc0302090d0510060b0a090605030a02090d0c050a0801020a0206040f0804050306010b03040614070c1401150b03010e0c0304031b0206041a09120118020904020f040504050708010507050a050a0503070306 88
    0x50106082c4103000603e4280107501490070001e01d41c0c0c2e0b845210f0a401008030050005000d07900c2041b02d2486040a9508083d008000514154000c400600c180300a10400c4030103a1100c2e0040110307240c120039440007403500c44001d524203480d03000b000791100001800109510b172108034000900200307206032009004061308075001035855483c2040903030002c84080322070504181d655150000c4e070040b6103000322843d8859405c85a060754440380101f00c00080d075000396581d0b400620b090b4122040140041c421200000c0c2c0c0c1c1d504104201070a0b01d4010140b602d00102002130200003a4089a50112013222485c000d0070380300d0500c0001c3d41c9200c1c1d47d01442e054501c0c403103600b401f48802c400503c0d01c8102168815a000d40300d4503c107003030315a0b4020741031090b05100c001e0805070401c0c0729181d90140c8000c200d40130301106100002c0460f28203850035a80c590045000f80800c2409101c0c92b0780121040c01c09074141046e20000500300d103c0c40f0350031001c1000120100c1c08003070181e00314030042d00c0e14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 197489514 1250 197488264 197488279
    0x5030c0601080703061506050f091f11010e010c0e1306080a0c060806090114040f0b040207080403022803110f0409030201150e0f04020d15020309160602010c120c030209 74
    0x120040c0710b0343c8035070a001c01d070ba80c1c030b2a006001605641902e01e60003150956200d20b4104000b500e640e01d000d400285c5400e030001601d10301000c4507241142000c944641c070f030703d412a29000a007162400c60703440c68912049a850185540c050b144c201000b000a12400c50b803010012400721440b8001e019a6401b0710b98034425010520200300c00c884460f41590380c55507a25200fa60307000204a5004008c4c450810003004608825405083c180c1080c00d00d03025081c00410040d40701c0c00030074200c0e80040d50654003814045000d20440ca4142e2011354810340d0541028066544000c208000383c400f0311008010040c0d120301c0d0b0141da20f600c004009121001007040150f241c050402034003804000d8001c03141d00a800002240811050002c0ca0146151068020039555a039083c0701c5d01700f030060005d950006440000080d182020b0000714440d0111401801401404a0559245210340d8001c501503905161002c2040d5510200480024003a20000b00e101440c140080c0c8c001d02c207090900303030003018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 197490764 1250 197489514 197489519
    0x60f0706060f060f080f180a1e0c0b0a021506120a06060311040e030f031e15030705061801030911060c010605120c090403030f020d0c030b011103041208030405030c0601 74
    0x80720581c074801c881c9951034101c05a00e0040301202c80aa0031034041b4041c9107403201040345041030061005c40c106180c81106c4c0414050b03180d9601c4003800b25442c0414184a190210401941c00d00000041c26000304040c1410034400010307440c0e400a01c1645a480264400110555512440741d040d20380e09909844440f00c0c1e905110001d4400390006071141405075080841034200761061100c004640b001850a1043c1e0210602e01984040c0600307020710800042100104000085180900505040b10030040040800d00d418807000e9400140b0510003480090b100f01c001ca10340903070179082481c00049103107541c680703034030a150704a00d090b800090101c0d1000383c0c072005601100a864040710341c00b00343d0720400f50156407407100d24400d94100c1d10840c040b40020340281c10008020201e5403000d030821070b1940c00002145c080900500000b03840780c0c0b02e150349503000304501d0811f0341d040c809940303040d090642c00042000c1e4084014014400000003030240a8240280c90805041d00e00f03540403540d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 197492014 1250 197490764 197490779
    0x408090a24020f16030f0809150a030e030421031101021602040b030a0203150c04030206070c05010f0905300609070807080f060f040f0501051f080c090105060f070606 73
    0x14140c420040075104450203600e0200380011400e410104204d1404551429035403a80405920004100d80503030040c0020280340d522150000c0d103081003901926150008c09c10001c061b200594482c40c0ca6400410041c80035403d2100c0006e00b8078003072880030141100c00d01c2c080710301c2c00c1c20414005d8a54030114070018021220002807107100d000f00c0c1d0500c030201010341090b444548061009501d980728080300f441b4104020119544490078641c0d00d41813940d81e402190460744980000c5030a00d0821000713001070342c0c100c0180b6010a00d41e1800310140750502002c02c0c81f54651030003110071506107843c9c1601044011003540c8111085400341e81841c00c081d034180303a684510780181c0085005103a0085400301c800078100c0640403d000080c2443e0700c03121061810b48001906c1985c007080f04181c0c04022032001d00806010320b00364000000704468110340840119540d82040c40306810103e180c91241d681d0340081410742d041120000d0b0350340c5d2501c01107000c2c1d108843c40208240d00300340c0006600b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 197493264 1250 197492014 197492069
    0x2d1005090a03110f01090806181f1b110a17070c080307031112180d12080609070f090b1317070e0c04080a1101091806050a0905010e0408090a 62
    0x107010130b80b86021260300c1400150f40350042401005920340c4000005500a100300302194120b40100041c1c03502d0320728039486c041c0c942003c072000035035283d1501c001880144000c4410440031005180c100030130340302e050169440b40d10f0200c000d8004086a20f00c103801c00c5000301160740041d44130303900d41182680c540d80c1540f80d4200c401c080d40815504080c1800d41000807a00341e440641610b080c0d85440a1440e81903e0082c104c1c50ba1500001035550510014458209001c841d10003901c40ca4994a042e030104002848004c044034100310794030000010468003c1c48480030784610760b182c1901c400090003010481d070500d0380845100d164181d24401400800304114003078445000c680c0106075113a602400e52481144a07070181c1d90700001d80f90b404102c4050311844014814901101c40b035035501109001d180404a0680e00b150351120100080c0c5000705011000f4007030000240b28542c940301c120001d040d8000c2011305144000512200a0b96913800c44901a046500d8190110110007030b080000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 197494514 1250 197493264 197493293
    0x10030605030c04090803130f02040207110915030d1103071a0115030504150504030e03160612230408090402040306020a11070f050f0301090506152d1005090a03 70
    0xa070041c542c030040c0d81d00385800b40309420b0303800100361851519141111a40321020403400d4800c5001d070502c08006960f0345c0002c24902d8020001d801c2e1603540760007040741c007120140400050740d407040840d04544d1804580084a070302281003203580040c0ca0001c0390304511800030007e000341441074a041540d100d110026041c0da15511501036a071940c1007059084400c19540507041220200e41c2d103036a40800d400140e48288170b40b46c00b402100c0c150000c01e19240303d4a004c07003001c00e4071010a1103080e600c00c02001c0c6416142d03c0602c040c1103c202d0800c6000c41010450702030884c204001420b00c04020102d80188801400455985680c1c0c10700c14002d400c440c000303030001822310310303c0300a007040000c05105070791383d00000c0500d81e031420081000840300c684409400d5503d0b078940c130303011070001c3c0000c03841552018010050031401c00200181d0400c3c01b201d41488401111040080ea48608503045030001d0690341001c00005410050701c0718040c0c02c100c940d101940300000301c204500607440208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 197495764 1250 197494514 197494519
    0x301060f020f0a081603030b090a050703240e1b0c030306040e0f060c0313021c0308090312060907111b1e0108060607140d02010203090c0d0f0605041110030605 70
    0x469090b2880320b261a001c52a002034a02881401340840361720384c596210560390311a040004500c1a28808100010300c01c41c1d50540003517546003000b103455014002c19124803c0d82020f18100c036001030782e0b203d040200b401200020080000086c0200080c042c5480c845981005130b20b80310021011a03075501e600813141c0f07602407420b1640c0e82c0c0e80c400300050f800518120030809006240d907503040962883d00300805401c0700c0712805203000e01580380c0c0000410007c0400031001448581414081d01c2c215001e01386c40082e92081040c1182d02d18000900c90300118220303100416920350304800ca88180c80440b640000d409100c100c0c0d255007800302900e41c016003040c0c0c1c1001404520541c11606219035008450104900500040a07442d040d8014003003148500703ca000154040a107071490450031392401000760390b0000c01c2c0304a4480801c400700765028112403500c6546141d5840e010b90516a45000300555162004902004100c0115800d54480600420004046000d004001d045213208050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 197497014 1250 197495764 197495773
    0x803040c0f0b07390801020c01061d04060e1507020a0201170907060e06040308030106020601090b0a0303090e3408090613080a050d050403050903010c08010302030d0c030c080301060f02 81
    0x5035000d400e80550b0000f9403c2440c243c80001c40d510054032902d03140c2190034a02004201c407204400244a00801400850000680b688001046942106d000307410165000c0015000b0b21940c003c107070f5110703520a030b0010000c220030000c156170504d0840001e071244413624540d020001201e5000840d00b6032a4005d036107a0105c692881a160300c07100e8155880802a001100c003400824052a4038200b01c03100580494a0070390349840c0c004803a0400c4c1c1100d0010703004080100008001c03401240700d8460112665280c0e00e01c0c44e54043c1c83da107914802c2c0340300043c1942c0090840e4494009080080c00c1030440f03200003454441005070000a1210042c000c112410003007109680e00003030003403003082600c95902e00700700e160f2907000ca21f410003400c1d081040702c20840c1003928045802418011840f03901c50507100c448e00b40c109402d407828030500c80c0810950400400150340c1c00180010541d00c103061410f159881c50404462035655140007400211000000003622030b4401600d603260300d616426907 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 197498264 1250 197497014 197497019
    0xf03280206040b12132105070b101a090d0303231602010f0501120308042f0f0d0b04110303070803150f030a080d020f0d0c03091403131503090803040c0f 67
    0x85c5443d0000000250118008011040940144040c5030f02800f0b03050510740c0c2006090703a42e881b24040219411403620003082820862501090001c00c407454652410908080d0a800414103088074070802408250300c41d4584c3c0702e02d015840044c1414071003600e42e5000c13442d021448500071200214203100562070a00d0020007047c1c5445110305850b15401e002d00c5669090320708407407640c80540203030340f595071000c00c0f80c0c1c0d40010714880a00c0040e80e4126a809040d00d0700800c101d0400240e4441d0040c90782c103491600103225010100d901592010810110550040c00f20789103001d8540c004145c644c0c00018000c82da19055126130403a101125610b00760000c9000303042d116810110010301c600c00074481000400000c1d0041c0050011301921141404070f120718000030360700c0407028440826907500c03092041c49184105030751a81d040e40000c1d0b1a0260656040312440d8884c030500c1b00e520701001140380300038440d80040080c0c5422522080e180e06181c1409244d140c100c1c81111340750100c10100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 197499514 1250 197498264 197498281
    0x30e1006182706022107090f030506070807030b13090b01141f030f05010308031008011109010309050c040921021b01080405010605220b0f03280206040b12 68
    0x30815101030400201c540c1000035482c801d0201001002242c640d60240030390800d0888010301d0000c0740744002d07a80034150400c0040607081c0003c0f500922288a034000050010a50001c2e409402038654a41014036681e140ea0440040805520b0603a10910300c01c0d0592041c809608100c1c2000c1c000d040c514440d03641c4040703a006110817000000d800c100d002880f15103410b44084810040305c0c0c0381c180401c0c0f0504108102c805c48100740c20896004130701200380410310007402ca840020b0038a0340020805008051560784182c0904407010303041503141d00003002000350030300c0303070f0540440f0260043c00b9000319441e101821203010224117034210101301c01d41070203601c000f800704507048108149240340c0c03e40c0f600454ac400030042050302e03a992622000181c94540c11300e002d541e100e40c941d210080398410340e54031064910780c03400b03d8031681410120121550340400c130110802c51078103062081d1000e1020328100c1e80d5000c1d070040c0d0700c004003003000100c90070136000402030008a24490002a0f4032050f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 197500764 1250 197499514 197499521
    0xf320d060b040f050607061b0c050c040b010905130207060c020c2d060f1903051801091e17160606080d0c0615030f050c010809060403020a060c030e100618 68
    0xf2203a500d5003507501044036080500007040d80390b02541012880a0010400d4400c191941c5d264000150898114005208051007a003032856400c660a0026410b1240000c140c05d810307001c2d8903c05c2e0f01461840d80c00840c83d0b811611031a90140050080c01060710019440b0301c0e5081545000e186008212149114070318195101c0403140e5454003842a10380c4140005a00f085109804a040400200070703c01c20301c4003100f20b124503030750780481c0c0d6180c1441441120445000d4006150f814030145000013801d0348905208034800b6444007000141604099156403400d48140c25410760020b906121000101200c41485001d00ca090203000d60319191250303110f2007408544005a00ca500ca60b00181c81c2c4d070054889044114000b0b80c0d21030322625a0507a08208a10440782541f002100b22990358012032450790051041014000c50b00c2c1170307240607445004812000701b0840c0d031554090b101c903019500000304107800b01c044036014114034941e4402008640280035800c0070f00140081076161900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 197502014 1250 197500764 197500769
    0x6091b0b030703090c0305010203270a030c060b0102011418070611061503010e160f0e010b0a11071205060403110d020d11070506070c0e07020d0f320d060b04 69
    0x40d85a14540c0d98031412801403403001d1007220080360314000000460024000346009201c0d84a00e0170104000c54080f48a811100c24694160f41160641d030700802d8104214080103074100d02d0114405540d000100d00500810f40071100300645842882482c01c4613000010000648100b150700301a00c400090340c283c020981c07010166441400012114408000010f01490001c0c0000c1039200100b00c0305410300100555401034400c40e0801013003c1c6110401c2480104440d000c000c800d54109114000c041c45204045410300600071142005084104241002030410001142800b405450309030713200c0009540c1600021490100f2010b28440456501c800401507001000c0b25050040151869003172950038516900039405c1c00101d944440b00100855840b84042541c107c1c201a00300900c54400740142c011540101451800c040d040100c0340c0701542e850605014400d00804100030304040300018201910701c044000071000d6504000c0d01d41489003640510002c1d8650311007503c01d00462 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 197503264 1250 197502014 197502029
    0x110f010603120c03021006140f060708160c030204110319151503060906121505060105030a09020d060c0203130503060f070f05070611030103030e010309020d020112090f06091b 77
    0x2d03200403507000d40780c0219114828010707200300807004101d184c1200c1c03035507009562007540980700760b0a80c40c4c01556604c914100301c0700c85e8100036490722030341d6203401382403400e08449100300401801d2221040324140159402001407204904007058080d039600103950782010451143c0403001c0d040c005010b0391510b03400c1c0a10b1441e40c00c0c5084000350300495071901680070f25903200e1002c6a0724034540614406004802640c104808a03481c3c0f2080080d4041410030015140109000c3d03e82c1e4004220ba400029900003c210b81d20309000088414030700c050024103951070100c0c400c2101e42c012015050703004e46841c583e400c0550b502c05040e216031040703070101d0600c240000050800c0d8016140402400030b189400ca091030200d64840f81120304102c091450900040010000c0547c8072007551580d06082c42c05202d0300c0305560106100f031600440082c1802804500e540007084580d00140003150045811400b401c80340c1003401c02090805410f403036840c681502400801c842105c40022150603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 197504514 1250 197503264 197503283
    0x20c01030209060c0a080408060121081b010903080901060803250303090c0905010312090303020d080c1e0301170c13090206090d0305031015020307020103050c07060c110f010603 78
    0x100114029071103141116803240082c465801c02d0f40b000c00400212911811002d9980c5043c803441506d440c0050340900708c0e0b800b25040c447d0100b0034910105426980c465102502e4112417804c1e0003680404803070b098019031901c000f1802f4582c2c000c0c141c80c001c02400000708006619140155200c0c4030344a0032040ca801300380c407a403004220303250700300d0810b5010345800070302c21031656641242e940041d481801e60548400c0184140300d030040c0e00000b581c2c0a420040b05c4c10703107036076800b07512082a12100704c01c2c411000700045140c4170b8002110b5420f1030080f0f021400c15074050810406400c01e0044010080c00404000c400349000030b610034070007800400d024400000c0304000009400d0702141240c00501c24004010b503910344c0c5d05142003503032290b00c1306501c91034502c00350300b55803984e5440650044400565000308035008001c8a143c9602071a01090b0740d40c074000320300f195200b824801022145001e0180c0d003000c0d070100783e400703140c10300c00c00707481403080c6060543e426641540005800b9440c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 197505764 1250 197504514 197504533
    0x140603030f250f03030f0c140705011e150503030a09030209091c0e011706060f0a0201020421031808060a0b01110703050c0102070603020f030708182a0f0102 69
    0x6140010300b000c0c6082081004025641c1440018409241501161801e4400649208242e018000e20403c035030402d104000380c245c0d687d8010000c030410254804400c10024001040c0a000e421120b04002c04104500000c03400748000001002941c000030088855840003048600d0080102c0301c02e20030700e6494581c00d60864081100d050701c06800092a4890215041151980c030140b400344440141c951600310a00a40094000d070329010550804a14440070440956640020303070780e1410403098015110910084140e00910840e08000018003140911204105c1c10002410320f5600c40e98900000352410316400101212501645407503801080c0002c991300138503401056820014900115074032118064582885019002550b00e40c000c92420041543c040124000500d03543c81d007146482c0e02428085407601028104100b004005008507030001c100c120712a1042d001d4a055582c050003110340c1c0c1d10305514045148096542c40c1c60312420324a0710b00b918140c0b41c0d0068015024454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 197507014 1250 197505764 197505787
    0x30c03040501030e072d090903120f0b061b0c0901080703020105030613050907080715020a0b0402012303070818061314070e090c04020705070b030901020d050c0a0314060303 76
    0x1c407030701d400203d5110741c14000810101503c5100c001c44c040f02c140c90304a004e0f00075840d1748000c140e0400300d902420000230600190380640c442498003050480051051085500000502000800550300c141e0100c1c03005441c0d014005501100c0f03031004100d0b0715151000013403046070b04003445400d0f8948c002002c100007550203640103560120008000c42004440491810b0450b40e081c0c80c02480d60340704a070203010034001048010007508a504110a00c074075041300080d9180980400205070000030000300c0d04590165400c3c0315080c0100031600302d0703449410300140d280d0300211602800503980c03c000c00c0765130f811000040c41821314400507004650343d01c4000003890304100c4044481080810f42c42c2e000d1901841714002409078410b0705a000c0c10004503103850003800b02c00c60361069104001c500000340001507107030111404c251040f82c80390764401103d40280140102810083c1c2010304104010b00d10b02c1c0240101d8080d62400c101c1d0190b11108605041c500b107a00681543c0b08012008540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 197508264 1250 197507014 197507021
    0x14010210050901060b07060b01110316060b03100513030206010b030103170a020f0f031c02090f1e0307030308061315092706062102060304080d150b0a030e030c0304050103 75
    0x40281c2c000420103941d1400000042c4e4842c079415107100b41e41e000800302c0356910042440030b428600d0f000354201028441d184010182c200c0c8001c01030703079448114104c5502d0510188400b4503020310100030f103241103103565030b1074042d85a0840040c0186000442c40081d01d000ba0782c140c075000503d036070890800302c0708203a81c0e62010301940250301c03403000f81c1d20003207508001816001c51800c0103140c903025911000700085d0a00c0c86000c1e40e903401400605000c1d1503001d044030354014101d03540881d010b80c45880e482032240f4104a0b6400d4001c3c03690101c00d25802050441c0514401d540c044e03039506407520500d00b1200307040d41a41a0f90703010b040400c00c0740500e0704804020b52070641c1c02004916042110310481d1483c0a013102c81d140c454404003d81240714007200c541514428801540201560000c0d1880c4402040217100c10804036440c11100541e0b44040c90051000ca0503480d00c41d21104d2420781c64101048590004c0d0510324000d0361110003002351031014100314004d60030035040c40010b4014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 197509514 1250 197508264 197508271
    0x180b130b0f0a08091e300d0506010c06050a050411010206040201080402040c0909050a050a05060102070f05090a090212062d190e160311040203010608070806030111070302161401021005 81
    0x1140710711201d100025110170035a11074074070b0031030091000201c120b40450740031070544105001004003a649200e144004411900d82d0340221200003410342d903400040e036410b59400c0c80588058a80410003d0040e015070200d030040780684107002c1500c401c50012641c4060844009000548920200c2d00609068105003261422420b03d080155101c080141c125030301255400207035038848090000a0301544500381d00700e80300307201408810b410a807c50242c1c0d0704500c80e50340142440c04c000741540a42c0c0d440035010b1a40142051211800e1008107a59000203a810025400d4204a07080e900d2201021002102858841c196025a07503c004146844071021403c5c0c6126201e40d80104424014840c802403c4900c00c042109103045040031700300382d0150900d890003640b0410051003859008502d45074450080d1030f00c040c155803000042070140480803620b0101040c0854810200340d004641012040d10b49461900c04541c4c2c0d4000c5c440300c20b0760140490158004401d00b050048280d004240e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 197510764 1250 197509514 197509531
    0x2180411040b07051b0f0108010614070c0306140a0621020310050405060f010902180d030e0a090b011d060405010c0303090c0605091806030303130201180b130b0f0a08 73
    0x90681d01d001c08181544403c100321250b4101002c1e62010080c00e080005140505031000380d90f0407800c02c0082c1018606003d1f034401c2c040961090115481400e0441c0c110b02d50008501e940ea60380c07071030b2603400b91420200818a509980000800c242d00901c6400221500021104c0d4040c1c000180307202a1410b19200341d0b0580103039201802a510240078072809680b08030002c204a1070a0316003e88800c8041c0c0005d19101d0042265904003480c01c814001c048804440b0f02e00d00201070315066510109081c1c04540101030804001185911544001c038050b6007030301d401d103802c052404412060310540c000740e1b42c40082400288981e5104207412000781713207e4100010461901e032103002074507019500120005000140c0146203082c07903010398004070906404a50710781840d00000c1c0d101c1c0030050a201e040d12001030210103580c403a5046003e1000702c188101c407015200ca0100005038408024541315220a00001480700e1020046071143d401d0522178a00f00300c180d02d0200c450000c082d06550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 197512014 1250 197510764 197510767
    0xf120506011b110d0c05010807080606040e0606090907120b03070807030609080d0e0a02041103060102071a0d14010f120c0306050c0c100906061203020303130302070e01030f0501050a02180411 84
    0x71180e00c5185074080c6850189000300301c6280b501b000142900301c024004020411039000703101d41a150030b400d4600f0703940603641040f01a59408085a61802418029548410b541c014840140d800c0116810078000c0e048040c058600b0020038035544440d280b01c4e00d11554018141040400c0c013507030014400c180324908162034614500d010800b90340c6600414441c0e50009000c090440c0b515100d80d43c031103226030404c80c0c250312b0700c0000030307450b60740790b1080c07007800c10b0b6801811060400010481e030002c0b40113078003000403100c40304148055020900a1070401c1411440c00f0407c00d15445082800b01c0c0d110b1152040e090840d9544009000080c010b11407954007400030040b841c02c1404210032050090030005034203105410031308140d035845e921450050b1400035840c40400e40c04412a0350040641d40449102c0e00c0700d140c1207107401c0c12075011510030043e190021003000104505103002c0341c000d50092103603445848031101244a0290380c4e02600303080e000b074039045003040c0d0840c510301c64220508a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 197513264 1250 197512014 197512043
    0xf1225030c090501080d0903080a03050702010f021201140105121306090206030c03100e0907120f051e0d031e0e0f01051503070801050105180a0e0703030f120506011b 73
    0x50301601c96420041841d500c0b10010f00512074200514011840549451525645036850f91111442044041810192204005a0300d01e000350031011004008110855132040d000460403000c06080c014810095800c0b41c0c000c00d9580300d4001e403100d09260b00c0b440348980d1030f0300640d01540d00b284002102c045454210320030142e41d0310707000366210b2014485815503902d81340420402401c0190055180d004080301407000c0950300117805030a45084a050621003a4a0705103401c5008180d803004000e40309101e205c020f4060300c00304011165084200712140307480d450718150181c514258050340a0200c1e600780200d5040c1c15040400b458120304182c4454400622942e03003580c0d41150140d080c2c1d061148161030b14202080000000c145d030350001c0100f541800700043c9070780d105280303d0441840d2480401c1c018482580f1001442024600b01c84807035641e0726000e0014100e00344428003084040b9445000000300740550303032144030165116210400540000c0c40700c0c101d5520b05030b4420f02d404080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 197514514 1250 197513264 197513273
    0x90a0b01060302041403070b09010e04090204020304081c060303020a0308070314010e0601020f0a0b01050103051008010608010b04051503150c040b03190507020d0509060d0e03180f122503 82
    0x14a001e0500c0d40c1d0701684e207a00f0700e0825501c20403110903103406a409030008110118802003510402102403a255000d04a0080054094115544041d600c6440001400b042003000300007441d00060802589a00e0b407201c0e80d051084440d03903c000b0b0096080041101c0002e4401c000c4960310044905000451010b01c90400320701c600c2c241c00041b0301400c1c85061106540c0c0400a0720600e03108000240307040800c83d9156080a00b040c0f0489040c1616100818201001d01a070607010307182040080003415036540803180a04581030b0706900807441c02000c01d0f07400c1051200d00e17001c0c440203801480c0044018526800440000300300801e050400d12011034580d000f00c0003140a0b4810b8400901306214069109045a4004e4142c606551000a0703d0143c1c4c1e8104054030700804007250710544030020207155074060000c102d14245c0d54000000c0d031140c008640d07001c5002400b030503502e5040d041900c00c03d001007001044a01c86035035200d20001c103100c42c40244925420300a440c0f010865030307030300d030789 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 197515764 1250 197514514 197514533
    0x507090501090b1e070f0317010503071a0c030909070923010203030615041d0a060602010b030d0e010e090a1517100e240906100b040303030218151b03030915090a 71
    0x8101c001a003403004081508c0041c00c1034a024050880c0907040e01440c114070756204950b4100200303101b000c04210000009014010780d020b91101900405a51411040040850300d0360700440b00e089170044410008030070220744010211006030003c518649800c41040031080e007a40c86440c3d044c8040001241c0c0b5800550038030b850300301c2441c4d141401c1c101510400c040e80d03038079000b40b011680b60040c07425980d90009100303082080c680c1440f001000044c001250341080e00c484440d0040c415070705000c0f0080140d408120400e00c80b0360f00ca01d400707448500c039006100705600a040c090303000c0c0304140d00c1c204181c0c0c40b80d21200034032003c4480c2c100350064200c031110811100c0003100301c108002c000c21020140a00780d4070130070100103000000d0810480e400c241c02a0b0002130101640403400c2d080b0b50705644d50340480410000c20041032621400000b80150b4080c0104000c3e00304082c0c0200e020b1100041030303034001c82e00b902c0500544040d0b81030a01000c2401400d1040d00e104d03a80244010410481 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 197517014 1250 197515764 197515793
    0x6090804090228021f150b0304150e101a0418050601060f021f150803190e0f040c020715120b01020c0d0b060301021c0507090501090b1e07 61
    0x10056150481d003003091040440b07003030f5980703c42140c0f6602c0224556011804045d24100c40d00c042000401c541d070318400805200c0c6511180110f0102d01148400045003e544903903c6401c42400140798107582d40192080d00c0601c0382141c1c480014079805034481d800c140180c200a41081c0c01120152000800b40c030403d0380c0400d0002500d20119003402020300140c1d015220300c2c14124040341b26180001d42e5509012401c40040c0b82202c0d804409640316009141c99148411580780c4071510303013414030b03125440a0344910702090840751030303843c0600558484042c0c00009150040501c192001c1c84003600c28624000d046002c4c026000c00d0109414904ea80120702c541d44a503070400001403d04100e4052204a074150342c8031800d04d546654440c04101611a801041c24111b61902c401085c007a002c0c0e08080504841d1802c08900314040ba0f60107a841254a079444d0030300250349100548040c01907014076000400c0400c00e2003400c03d01642070880e024031150b0410310344120340d140e0f5160a039041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 197518264 1250 197517014 197517029
    0x6040b0301060306050f010b0307050a0309030c0f0b242d220c0e060307030c14071b051219020a050d060e010501140d021203070c0602150901060b04030f06090804 71
    0x320141b000c080c12425260307001d0207549021a1070750504e00409810303401041d0048082549521b420f6082600c104171181c066544a070070007110040614184602900440c0d00400c58046019903c128422003400c1900303c1202600c17a6861010030103240420741c00007000f00b10011404a10b50f0100e4882c03280c07074885d104e0341c03120445000b09500d4640c426100380b05c40000800440070000d448903581c601c101c81d085444c49c1400120340000d04016a400380d6050f5901074042c80c081500c40500442010b404400303805100c0084070952140304004600c0b0700d000401549503c0709800505890801074214101c0340010500113900741c0d20800500b141c2400303c4116030382a01c0700c0303961303000c11000d000d503e0141c000c904e0314658030681c403004a8551501d01e1400703440303a01c0004251407a00000d204680d05250888400280c41e604c51101070350f40c0001d142d0608404102200050030401e040c030804c41511006282240b600d40307551605103541c110020242ca120303540b450300342c0c00543c41c41d00810003002c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 197519514 1250 197518264 197518271
    0x2a021519050d0c020109020f0f0406030803160201150806071211041d073b1305040210050f1b1903021606050405131e06031a2d06040b0301060306 64
    0x40c03031450b000340ea0046040340107582c100390740d1100590350711186504043c02a5024020070211800040140c50345034400b40001c00008180188008120b60308010454150003d10502600d850f0703180381e503840e900c148252030b00120702040c0c0440c817504a00c0c004136500f89002c50074078100410101030741d010303600c455414541c0510141c0b100a40c450307203135445101800d001d00c00041d040c9809841c001e580020148010186068042d424461f0b60014020bc07400786c0042e5500f000304070702034000c0406440685c81104c6079050704000700c0c80b85c0c045804c42c02c010f0024900345405107500d0f4882e09541d81000045020300f0785543e000e2000b900300141c40307501a0707005080704075045030392110340400d03504a03004205080000384020b4541c00303480f2406103010b100c0003c4840340f0785440a5918212061281014204040007043c02013041c03a0b01c12103104a04a00001e0b100c2d100722540701d02d501400e5242c80c6120202d00d04081e0143c40304168030220280010820904880009085650541088514954 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 197520764 1250 197519514 197519527
    0x2404090c0503090c01120f11070c0b0f090d0212030c101503020a1205070b1206010801060e010c0201080c040503010f060e090a0b1f05040e06072a02151905 68
    0x94080c4200c85149400c2151542c2000608107883d080d00d070382071a041c02804101090031583c0b560015a200200750b0003000400c80051881107e41d104010a0300d015864080108491000c0300c00c440d000000151124600300182c000d10807440030309a000d982c000c1403401103c90000050008220200050010702400001e117101942161500c447c589100c2800510500050700c03000140340945251002c0c2c03c950949501d0207502c3c0407150f82002002a070003086070f070a4450100c4040b40a130354240c868134400c4c0c0e290101114801d00d52030026001a402d01518009075010300002501f1550b14100d40d45090340300d00c082421b4504030010061342d2951580200460050105040d810121a1003d426000c1c2c16445800b405603000d88074458a0142a031180c0c2016a2014024020100900140441c10a14031403d8941400716171803408107262203144030700103035546214541c00344030544121001e4116000e200e4001e44001e4403002c0c1c01400c010a81c503061480740418620f8403940d175540c1d518813 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 197522014 1250 197520764 197520779
    0x24040516080f0f06010f0509090102090a15030e0109030c0209091c020a0209090d050406080a0612140606120714010507080d0516030501180e0c090c1317030301090b2404 74
    0x4068000b00801c0c4e41003040144007001042c44108100c840031110000d0030388450015070700a204500405a00c94050800020600e91107070315021034403d140c404000c00b11310740319020300383c80c00c6020081c0025298005040145840420700d034100d0007c03421503d0360050b450320303090340071041c2c07040c1405a0702c8820650114500301541c690b22261510241142281e07002c07001d4201d000f94040c04084c82a900f002920b0070b511980044003c001c0c2e2000c0e182c0180360f07070900c1c002111314281007900714040d04001503082d05044482d404209030450080099614100100c02130b04a00e00302181000810001000444c014001030090341e081c2d140009043d0501c103a001e44080007005505091500384001040280c031040340103101d141e6814400300d0040c5c03100100a0501050300030080e03202d0809003d124091075008007614505240c58210f044150f01c070b04814014200c054001180c5034400c100521561785190020060180040d11401c18183c0000c803007121081c071004d04142c0d80c1800303e81040b011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 197523264 1250 197522014 197522023
    0x150905010812070b070c03020a05030d020a09080c10030b0a050d12020606010206073515010e04090203070b16050601060f03270f0302120d02031824040516080f 70
    0xc4188115440c030f002404c1d83d982d001e55000400013414021403001a4003498024082c4a5031250f21005a80e9074402c0300722040b0003900b041704d44000040b48050042115007000400c18024040100b044041000c9254118064600a801d050304031840680009654803130007407021110f44252552440c0c1102002c0c001e181520040085046601c40410f0180d0766400c182410040201109660898480380e000b664886010120300031040d459107080080d091094400c004504200340c0c0c07130075148d8500c8010081590f0101d5000303903160300403840404c949030050700100107244144002c80941aa01d85403c0e0178608242d025074040307211040452103065040c41070805c507d4910318511164612a05880c0d64440d4040c401444130800a40c14010b0500030841c0589003190305480955a0103c200d5502c041d4005807030a03900040640d01000d0342400c04100d40441c11021140705121400080d88181c5088004d801079440f070040c1c1c0d0340d8108080c5100b101c400903028140080c419134040043d000c1c40d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 197524514 1250 197523264 197523283
    0x1e0c0f09040b010b030c070b090303070917030417010b0402040e090105010905130f031e030915020403121d030a200a08030f07060b090103050d090915060507061509050108 75
    0x280e4420301004000b644060080d8150741183d0404d64580d50b800c0a021094400c081c030251100d01c40004000c03200f0800001035100d004a550384e40b4099a6a05040c0c40160140c0c0e0600c1050b04144010f01c094000d05d50400d142400703032000810f000b40072070701003412a48503411200c450380d0044e04104406000340591801002021001c010520744402e00030650140000010301da480e2424018090500c10420000071005602030800107039146a0301030001d00c000541184d491002214a140705410380c801d5504581c0c1185603840300019902c030869110a8100392540e51040448448607035440801c0a9540b00d440f0323695100f031055541d0950704e0441002031203a40316903048107041c81000004025169070aa0301009240c03507081d41c0c42d06502034900e204106412052140c000002d215001030440640300442e1648520a1b40700c0e405041507a00941006840e85a1060308110b40c0f48104010300045001d180b00141026072142900c2d092000c1c7d501080301c140d214001402070050030b0007100130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 197525764 1250 197524514 197524519
    0x30a180b0f0304050607020f0c01030506042310080102030408090904030c0807030503250e090c0d090b01030618110f130f0f060501050c060a0b040207080304050f070e010605070209091e0c0f 83
    0xd18a5230004580e5984244185c414100340c1c80c0c03408904551116000070384140c5c80006042c125008100145c014420200d80c000d080132900e40300025841e10610031607004580009046140004410522003400c401400c00c4003040300500540c0c0c08a96040054120310f0702c695982c8d55030303081c8030b503c58035044c0601b1340e006080c04220b01c0064045410088805d2083c20546070604140d80d40c3d03034840c000e4054021801196420401545c0400c00c06c404590b040e00d00c0f40204100054001d0103407082c9a6280e039006069031000f1075244201e14084170341140c00000180f484400140e6035004006541854450565a42d01c4603142e07207c00c13000d400f440d40a0107081c41e146041141d00e0450036940c01c0040e0802d10903580d10040b1030500d483e00e80450310440e4020418994900f0246442e540d83c00403485460040e00840030003144059034540418125040e80c0d803941d060003820f8082000c0034001400301d000382d10030312224080c0442c3c02900800c2c82c60300715014161142c469001d128480e10f1343c520091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 197527014 1250 197525764 197525773
    0x10905060406021e0f0d020303040611090d15020d020a021b01051c05040807170a0e031515011e0e1206070507030f1404141809030a180b0f030405060702 67
    0x300650380080c0e0115080d640410343c1310b01c252403695080c100403c0c1382c1c0380000f50260081001113240c00000440c000ea1044c60f04000c200102103921442e8015070701c0490380542c0807100040400c617203003810306041d001c0d0b9000503d0240c03000d14400480c0d1207986400b0250f0040195203a40b0001036203d00400407082c20072501c2c00304009041c14141e46200b6214199955500100301404101c0b401e540c0841e6101204c000707083e10102100445070000340f000400254207520000e013a04011032221456030010080341c03015201d078000048149514641c20707040181343e25940703402c0100134448002c1d44000b42c07100040302555209206900d003030320409039126407000e0b00780050540d0220884100301c1e01843c2200c040d001c020b90840c0c2c404d040c50502c0c0041180401c1c08280913080e400c0241c2503481c01c8810a402882510b40c07212281403c80e007564060300103002820746076010f038189200e0b40c1d56500240d0341c01d6444405030807094020559070141581d010080004201c81040560703000310741d81c002403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 197528264 1250 197527014 197527019
    0x10060e0d110d030c06020403051c17010603020318060106050301061d100e180a0515030604152c0a0201090503060f07030f0f0903020a0c090b130e0309120c0109050604 73
    0x1090340208884903540103007180c00e19034040c5813040b1400a50700398481d005541e1a9540d00f031040c3c1e41c1101c0500c000e0b501302c00c017a034210180d000c0c242c1400c4030284c920401805030718005060300203410090a82d0480038a00c102300d1301c208000d00981e4042c01c00364899903181d505140004040794140000c01a00b119651340d840182d07078588d42c0c040711481092905440b40c42520700480c80369400e4600030403002d0f0800060080e6240c0c0c0340c00691160040941a48500b04420201603490304166405050b4042c04203041d180300300c190304100440e60b12a6001c14046040001d06113444500c00c0d51036107a0741054042100310340e8020f81843c002c2908030300170300c018186500261071070a80030340034209040e61100c6081244010344c0062100003102c410802031030109060181d00e40b02a600d0031a00c2d44980c1c4400701d66002c07184908050041c0240c00d40c215150603240550050803c071580c840700c3c0c44107011201c15582d03094880b01003000c2d08000381c0800082e20001400a4050b500450321440c02400700303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 197529514 1250 197528264 197528273
    0x7060c080705070c03231e16060e01030b0105190210200d05060d0c1212020303010609090b030a0605010605071109060906092a270105190201060e10060e0d 68
    0x1100b003506d800000c00011180301003044003441520600743e007070600500031400020719047d0501240c0714480e0042d0740c03c131420004840340d01261030041e800030609140c8442d409504c243e01030074942106052603072820390f4201c0e10100c040c01303d1308407034016070005007210500600c50240140b0a182d011085401321400c441071001c130300421144402d401c1d550390000e00e4603903440004e0694103400c88400064240c56210580c102110b0100c00d540f40715071355100c140090710002c1280d049452a60354480c6060801e001c58029040700580d8550602c2100f1174840030502620031340d1300820b1583c484566480ea1072400c0e4800a4031140e0b114030031441e00d000c01045803198051070b50700c420200d13004e00f050303501d540000d040d60b10030300c4032154410003107043c0750b26051350a0000d200c6030260101501007090f9482d01e1540c1842500d01171400504240305500b4840c82d4000b51082628a5000201c0c00d10313121150542440021101c030004800291010841c03030780c10035104020024161001413409810f6103c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 197530764 1250 197529514 197529533
    0xc03070f0302090402090a061a031602161a1201270204030203060106110307150b0109080a17280207060e03162102030f010603030e0d1709060d0207060c08070507 71
    0x1301901551400001070b80051203035001c00082d0020325015181d81064200e40020380d0000c48000304503940780418001c041c2e000240415400d0100b0340404034080c2402d8021030240c0d280342910040714014002c02c80b80703240102c0210301803c28402002c04042d059403840c02503401310b0100320f14840c810402480940c40100303401f81502e00d41c0c00c002c1c01395030300c0c2450140b45100d00c15018128407020f40b001c108160003504031200c40d1100b681e0300200940c071560352a0b01d61401000061110f80081d00680080d907000c0c024066054403d040051441445001d00841e03030008446000142c1042105000c0a9000702900c180500c00b60010055259802040c264000250003540700c0200b0320502d00920118845c4044041079010b010350b02c00094014070307540a070441c2e0201310045261540e046a9030701304034000203102031700b101d803012514403c0940c1803c1e9510185600d504248100034a10345441d1a0001341107540c40b0302c00002c0c0890314a00c00600c0e00101a0092040240c200000d074040303140c0c00f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 197532014 1250 197530764 197530771
    0xd1b03020d0e0111030d09290109050705040503190501050a1a13060801020715050c070b0c18090414100510031104020d061203030c020a0803010e0403020f0f0c03070f030209 76
    0x10850002c401e900e006896110645101c6090752000090b128521300207900f00c02900d920460042c2c50180c0c2c400300f10886c59103e038054104003112240104031049058010726044501804e2051400780c507200440d0070406006000d64000312404092410010f091050551004402408020426407001951001c9213502c943c42e2040f41242c1c28004811100e5009000400fa02e0f0000c40d52000640342038000c40341c110318041c4145150000044c0c40d0090b000c100c8002c60f40c002204140c2d642e0301d10502205802401c50348111b074190b4040800e0b41d444845a4034000c40c091100d10000c5c110300302841d0702e000303010041c0441e00c50400d0b0501c4506034003528140d05032980100e08002000f0503e0100d00240075080105810604010380091050740001d140042c190095805010b5842944820f9130f4030f8510440040940500f0801040200c0c610045103400510910544924000d907141c01890407100412454090f000140f2017089441c0801119005084100300e04002c640f4580004400f00c0004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 197533264 1250 197532014 197532017
    0x3020a140a030f05010f03022d1905060406031b0c02030d030f110f090a1a0304081c0e0609010605091e06061603020703030e0108040209190902040207050d1b03020d 72
    0x324040c11403a000380c00c041614801407600700f20940c2e560306950b401501ea440141d01a1200446502d000da006401c0c9604070b01c1c1b274000340c8030301c40030402c284200f010b00c2c285401102c85080038049503550701c540003400240440d9901264800440e40722300b150884005400d0180902180740d200143c501041e4040c03103c2e00380c01c00003030b05901c0300b0740d1102400d5242050821000700040c0d00c1d5400c1500c00292216800c1942c8050310382c0d4071902e4031141002a040114240b18090000800252110006000c5c143c1c051045019008504010740d081e61507514a03540260040c0c8100003c120b030910501d0000c00040301d0360b204600700240f1703562882889202c0f0050488c0070000241040d1104801c03610640c109070f4200c825141641002901e034042ca010460006901c503000035659807044a88601035a001400021603032601424a5600004102400e1006403616040c8000da41c2c0d510261041d075024602034000e80c83c0044000340b0310030405007920301c801c64071080200400d600182822403211135 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 197534514 1250 197533264 197533267
    0x603090705120708010e030c011b0203070210171510020109030e0409030c0506010b070b01050603040203030a0c02040f020c06150916030507050f0a030b010306151b1e05061603020a14 80
    0x15645040c3c20100180c10404603136080000c5102004000070041c201000280000c00c00c9985917400c841c81602d0244102c00107038800e005000151920003080b2000303a41c0e0f07040c00702500c00d802c40c0d6152111803c80e15000400c104400d03028150030180b00036907910b04184000c00c95181c4659021b80898075403100b0170b00842c2c0da114490100340c020390704080d450f504a0f040f0762081d0380d04d00c15284160b101080c102e07142609007000164904202c01503d0123140c2c018003071418500311200c2100c075003480c20300581c1c0c810780b10303180c40c02a42b4913440102030f000c02940141c1068900b40f02a41d00311940c46209a0094100108006483c05103070b8540034032988900c1c0c081880d888240c405c659070300070440302809000340003603850074042e0554014010324400380c03401d00c00720340e41d0350b0001132860358040c6d1080410420764200700c04a0041240d09415882031745026108070050310802000c0b61244000c49641e400001031007000d0040c03a400d40314130500c524041d0315040141c50300a1030301d00600640840081c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 197535764 1250 197534514 197534539
    0x915080903040302040203040b0a061a1c060902030903070302060915010e04030c0209070e040c093006020c03030603100b0303040e04110d031d0103021e1e030103060504020f0603090705 81
    0x34002c80b0b000b07540041007552a1300301801c0207040414140c80900d081840e1050003d000303144004000309900b201d01c94a81000d604012003480d003500c20000c41541552401d0225040909201450242c81510002c40c1c440f286803801078a48180540182c89590100c1068511582258040c40c103451000310340d025103494a1400303540c88010000c2c003d50001d040c908126010b5484142d41d0b02650048400b480071194625068841e400d0318090000d002800e03441051003240c01010350100b0700d40030400e0400b20700c040e48030310003241c07c08c1843e103200c1c1e0400000d10219203003c20800c1c1c1d40101501c010042d1090340c3c40002c1d139178800d91113040200c0c0340c0900000e080c0001d0000042c0d0409002d09030111054040c40d000704508680c1180400c804940011009113510074401e807004124102d181c49264070015148050780c1c4c11034070609079124030714044d5034041c24a03140a0b6000310300c100340c0819541003034030402003040089075406004d00000d01c1080101e0f400040c10a08591003074031000000711 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 197537014 1250 197535764 197535781
    0x308070203030c03071a0f130308060f090a0518031602040510050405040b0108012409051f06021501140d0b040309080a03110d020601030b011a040e07030b010f091508 73
    0x40c4015164003400702049030024010b803014146c10040c12000900c807503a031880072143c580e01056034003d501011020300880040c0c0030b6002c142c5c01180c010b11341c80301d80c90038000242880b58100c5640c0c982c40c0e2600c0900070b0350b44c1c1100408445000700340156042c410700c128201d005081c2036034041c0c440c40d1203d0208042c0d080740d4441c03d01510018000b40503501d020704106480080030b200f176050542c603008414000c840c1e440d2560061101c40510f080090f4580044400a1305c805401e642440c04181c0810007020306000b035200040060340c01510f0040201644c840600005078005080200c040e850b01e11250b88940301103882e43e03403200707241a0039140d03810200c80100d550b800007020341c07042540c49403d254102000c2e050016182d012640504000c240890310b8034000c0c40014205c0c41501c0040c069500c2030188100380e45090541d00e814690f845c0d00b00140c000c0261030010100f80d8500d130b4104956400102c0f042c581119007040180c043c5401c081e03040282030941094100418200401d5948 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 197538264 1250 197537014 197537017
    0x606030415110d090c090605060405130219020a03030c020604150f06171005061c08220609170a050309010e040204121112160303051b0f0d14090604030807020303 71
    0x60222407095250034000714014020544c01d0b0301502c5401030030000140c8110140110801e4a90180c080c60405240400344581c0d040406034204444d50248038002c0d0110701c0f107094049065159004050300a040d0030090b040b503a003158808210f410100811000c108a08a82403045d615032000190180328100340c036005001607000042d0100f1501044d01c2031010001303190503207004181c41045680c42d101d00700012240b00000c5020b11107550701580b030101ea03420001d01480c03940e000c0342180b41c150450404a020b0038503004600400c124250500c40041d010f403c0329828600c402c02040008a95240c01d580d0307004070301d9580d0400c0345040c502c159a0315190142c400401c5542c142580d88007461810100c10074103042143d0090000300c582c4c00c0402400103030840b649210a2500a010b0300f5510111a035500c8456000c40707014a00c41d04c0c8000800c208041003c01c1c0c1290098130015000100052015040a00e002241281400802803960318501110100d030f511400c660340e22090340c400309055 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 197539514 1250 197538264 197538281
    0x150c2c03070f090b0f0a0303081306020c1516020705040b0d0b0108031810120b01030605030d020c03010c050909061c0b0106030c0f0305092a0d1103060f0606030415 72
    0x50007800c03400103812100040c00310a49a50000900074054038009100360b4070301101c0015400724944c882000440d01074000140c101c4036586455081d800c427516807100345c0e1b0042da41078071907510286040035001220b805203500405080070f003420152009200035500c03017250140a11841d41c85400d0569a603844081d2240c880e84800d002001d50303074840c1c1c40e6840340c1124003107201403041003e409180d807070141c0801194001a440d00c4d010030b1003c014100080c82d5000e9030505160b035800010030613070340822225085081d075600411030501000c01b40740c250b0f0790f042c510300207010091017900c03010f5460072001644514260790300003100080034100326502c00c0d80c840c05046010f1417400440e00d5640364200851000068540311304040c843d000407011503c0c00c980491164200107403d840f0045400c00c0b11080401d402c0340c000680c0039140c00207024080009080b104122401102c00301030070103210b200c1e4002c0d10a02208850b141003c080796403807000600c01400c41318094807040da009030300e5000c50301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 197540764 1250 197539514 197539519
    0x12030b0906130f06090f06051002030a050708130b07210806030a0609080706020a170609041a0a0b060c010c0e1806010503190908031906060f110f030f07150c2c 70
    0x6c0980c02e11130780008043c5400391038003502c98820500c0080f40000115100c601440d40d80520702505070f200d500994010791007403c0c0c013074a550000203403085c3e401d0181c245640512028a904c2c803580c4d02c554400e081c0c01c09100e0901104804110207a03501146110407140c00c01c070b021035030007036078540b007006072003400070003002c0c0c0d0300c08074618143c00d5001040751040d8130702800c0c4920780d495003810400340c41e03003c41c1c000b48400c185180f4484142c00e00d980080d003103084c8080201f40f0170540c100141142d00702c402c140b00c550b2740d1038100f903800700d50145030142107aa0546a80c5440032003000c2a80000710001d044905000002010460449211000305601c60804070100112985803401e2029075100365042611031405030303440c184016642c8a80c03005c54a0030b842e0204150400b0300141d45808985d00f40c00450302070703900007850700a41403000340b8081c4080100140d0f986d65901d0911191704c4a01603041d221440d1400050740c681c1c000c445812070080e152040145511012030001815020f110300a8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 197542014 1250 197540764 197540771
    0x10170906060a0b030c1602060d050718060e06030601030c05040f0303080f0a050f0f0603030403060513060e0a080a050f04180c0206090d0203030a0905150412030b0906130f0609 77
    0x1810440450254000d040844510071990750f68454840280070030350382c1c2d407901d113420441c00c540605501c0c0305525042c805030602d810f081d2100e10131000c5071387c01c4842802140c1c05092900080c11b80a0b41d1002810041c28114044074004001c5101c81c0002000366052507600c0b500481c0090090b4259001058881c1d110300465813640340c01840e40b801503031507200100c144030110b100c0f94810702400788a05100e034101e511994550303410030001c2c400130300a160540810071001c8085140c9014140c81840202c0301041340780c8440c6030a04c12920362021300c0b412a000513441e00000343c25401140c11a8059280075500d0b04000040006c081c4102d5100301c4c403000720042c4298130035066420418604079a03400f954466a0340f01c0140c0d456500142078400103030001c0001a5003241c3c107030f20416010f070294049030300c0d808220540c02c1b00d8010586080c2e480030320030480c283c050383c0c0c180204841b02c001a5041030446c14048046128840b5441042d040f45441d10b200c0107100100b43d0040b0000c080da42d0003070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 197543264 1250 197542014 197542021
    0xa021306020102120c18210109060e0c06120a0504061b03090b0c0f0a03050a18080403200109060309060f050106050c070b03090a02091503030d050718060e1017 70
    0x80c2c004e61000300300140084c5024000f40b010f40c41c541c00c2c1ca010125420490307460408200810506074141954503070700c0c100c405028403200320300344281c0245502c00c800c005421a440c5031080e140140091002d4401e910404c40c00c480390461003a095008441c0480c085900e4039546404000b4000e10044102e16221f40490000d03c40d62580086108600585000445031940718280980e4414140c1502080c08100320400c10f0900c00d602095211015880004491031140800d65000d180000c06403840340c0d002c6002e00902c4045002d10006503106112484450003840001e01489820701c908000d00d59190180002d205181d00b143c480940b01d580108015a129440a0210307080180e1019140c850541c0106074100340104480c000c03a071000c0100801c180950800801c81001890b03c0d02949010b00b40b4030040e00c0405c050705001c40c40c0c1401160a00d402000108005038040380072044044d601c0d000c010003034100025400e17080082d204060205548541698543c580400310b030001984ca8081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 197544514 1250 197543264 197543267
    0x18010f0914221406280b0a0b07020103020c07030507050108070503010e130516080d030b040207051908070c0b090f030109020109031b1e0501020105100f23030a030206010806130c0b030a021306 84
    0x45c0e0501500301a8481604030403000c2032044030b820040894000c4480c080030700c190400130001c1c1040c10f10514016251440090100c1d00340b02056104466030350100d10180321560300000202d62060709450306070306540c5000001c1d41144400390091103040c0004150205000040c46021201d8005c020308403411a981c8a240e6610703841810300d080007078500305101180c0e280038001c031403071107400c4801440c0b040d0401c0304000504070001412903c00e0b1041020100050302c11281400801d03255008949986c0000203000c0300141c641c04051099141c41c054800507030b0020312a2095039008070101c40305030003902c004c1d0300070b68180e001840c085d50752080001481e908007020380144d80c0b0a0b40240050340b070300300040b403080c80907004a610702c0c5801c031014003501c00d401c0d1400d5151030589400f2511080c00784013190401d26000c8080d0300581002c4014028103a0410919800074404901d0070240f40307007501c5181e00503d0a004074a0310600000100e002e1681c42d8042c1c4061000e08402501c07916601c140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 197545764 1250 197544514 197544541
    0x30a0c05120916120305090f0103060f06022512110f210d030e101509021b010c0e060f03180f100e0a020f0f18010f0914221406 56
    0x9a051140f60f480b1400b082c139003e440180c89050340e26484440c2442c441b43c04000d840d00030441e107941090b59a13400081c40d05038040c1000d006050940140141a02030441120341a01d019400c80895921841c100406102218071700e07002c81d0081010140307154498002003025001c1c41c051a40071020f01da18040ea840480c0180c094200300400b100d2241d030010a054058aa118000b48129045201000c3d40c1a0598024142e00c86490720a2106030f074403681001d0480e0000e0b4001c1c4000c505215012000403030904c5820540041030414004210001c1c2c0000e1052080c40d85103c0100004070116001035056a0120a4002c544040d40d42a252030228640d070382b280c01610040090900110f0003204030042900d41d50290064001d400751001c4000344840321350400e4882c4d8101400000c9031041200c10110315000c0c010010091203400d2500b210b54041c1c64284092104100554091005030072641380f50070b9041110380d282e0300303801046041a0002201180c1f80b4681c82c082d80d01041400c2c3e11060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 197547014 1250 197545764 197545783
    0xa060c14031305010813030e13060305010c03091203060f050d0c05090103050a02010f08090a080c031b071401090f05210303070314150102070314070305160e0601080903030a0c051209 80
    0x90b6041c1c03181e40c6906c071112a003c1e071044041c01207105000b4060b01c074281420050540344120401041c0960b407507840302d084403007002c0d540000030f079a0781402d07040260450361100c813101945400d0140b541448691500b88103a4070441c1d00c14564a000c403800c00150055940080c140180102c80742e6079a1704003d9101c40c3d003448120f0000d5041e00491040600030707106103016166000051100b03542c503a40d035403021340c400c00c8003804510042c44100c2c6403c2e048008202030310600c10213007a100345031860b0006443c200c0610181484080311040c001c3c08103250559080b10f1089030b1100301e5102040c400e9031140010036945c180c9002c00001c118040390140c2040012040366481c0701c0305950b4000d0702c481d02700c0d841e00030540142c0003030404001055900600d0064100b182c81070302e45050f074a6440074541030541203030403680301d000da0301002165440c0b04400d0780b001c401c3c248a6a0703450901c4005440c2d00c802804c0d0703a03001d5640c0d22008140e61007070b000e4441400e41080c1910342400c0241d116640c030401e40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 197548264 1250 197547014 197547017
    0x306060f0b0306090709350106051f171f0b030115030c020f03070b040c05120715090b0f030f0c09030a0b1f060906020601060903020a060c1403130501 66
    0x10400545540d100c0000411034244101c40d9096450310701c00c1011001c8044c20017000c010f00c880e401b0a030200356201c1e13007050010300d07203681003140f40d880b41051092a4060403034035a0303490a141044692150303860200c40c131100240300c00f4030740701d031a40558117900c1305512144c100401c0820003480c0741444041c51200d40c030084c200f80625a4030905402c4a100c24001c2c04200200f801208040a02a802c00d004c1c03c00d503401a10404080000c0d0246960041901038465008803400d0005100f0010111409490141e81e13004c469108050030b1640c0302514450a5400e01d40b200458015521a01c07420b400f40844001c3c250750b030405401000700c1900290740340550701111781e02140c8003454103012941c1075070380036014000c24001d9481d1030091f2003000300240e4807e00c2c40203803401c48400c4500c0142c0a884103455841c4800c0c107040c8002d01c2d11805803c208248000d5520600141c0d0703480e8603410860340f0502d0701003c00307403240c42d1646010191020003d00340c0310220f00c0e0400e0003540d42003501600c000303 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 197549514 1250 197548264 197548271
    0xc0604060b04090c05010e040618020d0609060b070201051b03030403030b092a0a1106070906021204030302120315030d0503150f13020307020a0b0f07080604050f010605090a0b0c070306 81
    0x50400c00c003c4a600c0d0000030003404050b401040039500619480c0c104280051000890079130700d280c44601d0001407941c0d002c2c590341c002001c026818007881414080c0c01e07844020403241d4101681e8140520030844064107014000c0350340700070ba4040d286c6900d0703a44d032902d09a0751282010b146c081d0186c414804014030501205002805c2d80c0e54462420b0100a10b0104040d07001d62010a0120b140c2e1221614504120ba2003502001c0072404200e109c0c007032980b99540d211081d1800c000207050401040000c030050904000400200780c3c002020404112044003c03666919024a80c8405c5005500b040f034050003050390002440c0d0b0018040e510540101d80401c1c0008900c40820100308552154242d1002d0880e4020040c201c40e60b0203598048c1041c0101c400382c168584070030104800071109000c14240c00da04105203981d11100840d01718605071024000360503e1084048414014040c43c030400c0800b1580369200d035904007018004083c5070708220b9450004244c15a01c0e0505c0340070588010f401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 197550764 1250 197549514 197549531
    0x120708070e0a06141f02011127060a050f1b1e0706020d021005090312040b0103020f09060f01080c2a06010503030c0706051e03092b0c080702060f0c060406 68
    0x7240e0924a444600103281e4440c000b004d10304c1c5440d00032485c01240440d940d40400b4041201054020408545031054980708120a1509000e044107042d40d01da024540601111180383d030810240c4034040c10920760f450b1150700c1034205035190411142038240c1b51003450b44503c0c2450751030807100c40410500d000d0b190b44030703140c1c3c4050b03981d110038900410041e0302140000c0c00904965002c19003140b041c40540c1c0c901000404241002c00c0c0c151b400b62103848803a0010401c515141e0064400890f080e6000d4915281040000303800c00e9065081d00e05110030305000802d842d0200003101c505d0480b280164140d809180e0050414068080446015105100020a0130714000051341c1c0303007824540c014041c0e18101f4000711202c2c1c01241d00034460301c001050115100f11440003640c820540715004181030039104c2d1000401c0450b070741d28890101000e0352000211940074251411458007d020300d50b45d074a0620210340070b44503000915140c00c0b804290001101c402003001030265004880c01e0100c0803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 197552014 1250 197550764 197550779
    0x20d0b03010614060d0f0204180e01050408030a0c0e0316030317060307171216051b0306010b160c09051611070504050603160308031008010603050309120708070e0a06 73
    0x5816000e03039280c0c00c524250029882c41d201000300f11072428400c010506d40741c0a29607809a800c16089090700c075001c0f11304904902d00b030348590700d24126a48000c1c00503091030b8441100368400a000c0d0507485e5100c030100555140503001a62206c4000340882d2a104142c543ca1288030344640002c800151041c01524038001d003c010140c00340300c000f00a807030110300e03200980042900c42040005940910b82c40c8600d013011102c0030f1f0a41e0454445068006103c1d8035010341000a9a044211940c1c000d01c607a9aa940740060121f042d1050714400301d070f60301c0c116411240301304440e03940140071550305000410f002071141c00542c05100c0c002c03004030001501a105942d19624103014410950004004003c54602500000e800c01c201509071406004902221152290b40750010746040d480042800000c1038640c0856004220000081100c141181c2e42d0a84a11030f40c00c0300d030311645000010b0648400244450001844100c0440e04042e030364501c507500080d411507000342d0040c5404030004414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 197553264 1250 197552014 197552021
    0x206010302030d03020c070b070f0b0c160b06030a0b0109060602060c0c2e0f0b0112020a053405010b010f030b0906010f201b100210020304170d020d0b0301 68
    0xc030350080290860841d514012002900482242d83d0036104c1c800b00000c402d00100e005091482c0100c0d01c40c010300d2498100b080c500f12024040c890042c03010802c2c900c0030303860b00c10750019080d841421800c803501c2d43c0700046c0c64a01d0084018100611b818000140300c81c0d142e1006044034015020344500340e9070340084105901030011807030016080817404c000740820043c0820482203040302030b01c1c1000d10011032602110300610081d50859503030030b0000013941e005043c43c8071074100c00206500d080c02c0c40200074254001c111308001c2d00d6407455040c0f40000c4860143c86d1203802c854108005120050034a5400380c0b02c00140f19010842d02d1402440b0729100c1d0141c1d115216015051a0880c0c440c5001160001c03021100c64042021407840942c180e05001d048100d54a02030300280b03402071140000c0f0071612202005280306540319100c40010540110798203955440004005849035101d01704046000202030121106c1100010301c026180d0091b070142c0700d5506031900810030340c0e00d01001d0500305d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 197554514 1250 197553264 197553269
    0x402041d0a0501210618110307050907120b060724050a02090607020d03020a12031d070806060d03021011041e030506060d0c090c0503090607050412020f0d150615020601 74
    0x130009015410f0580810b00350700141d205101e07807000115040c140c83c03001800d094031036085490034001c912441003480d04018140140000300c9891815050540f8050840780318004440001601e03100d80840a948000513590000d40000c0e600c0c40c0b40221030f84441d00a650300118030480d03031402d004620340000501c00d554075414043d000500d400815002c2008800340345000300c0440c410003001e0fa000901c2020141c074001c80c0c42d140400c3e80300001810104900d8008101d800560007020704020a110003e107594104006032030380c103483d20007803d00700c1c00c3c005441c96070200a400d107900306c020403860358028070403902c600d05400034890f045802e503061100c42d4800a060780c0c0c003144c00f08119203480445511854032462041a20550341c40960046c0c0c1d90500c20400464000700401c0031003002841030300d0f407110083c074046181a0070881007205d5100001070290080700e11075800481c03510344030000c81c1c5154100140d2018500781c40e1030382000d03001038000d0340266101d07400100440780c000600c0605 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 197555764 1250 197554514 197554529
    0x10b070203030a030b0f0406030b01090b0603190b03030c010509060703060602010209010c120e0d0f02010f050304050604080a3b010e011202070602070b040605060117040308070f05090402041d0a0501 87
    0x42d03d041510102c000d001e4046000b0b03805034809400701c039607554038030942e0001c40c4251681e10143d032410140c0401ca41c041542c5a004560030010045071500d114011010203001104c005085003072076010a20358000d50b160130f4281d620701003e10048140000707445c1e210300040c1e68244a151b4454004909078014940350034007107403411100900207424244070002003451840c21203154040d00c40040c0075515000010782d10a00007980010641d42d100b90142000d46050412074038508150b90b50743d554400080c00030380301c1d00020400807481d601c40d200b01080d05100522380c40d40c0c44154101c108005054403a0b00701c0070000480c0300f600300e50294074a0307001c600b01610b60440300c1c507154610704065404180205c8a0f00d81c204404000103400c108070702c0c0103e0203103c000600e132030420009094a03404d040e403103100c50076a00c10400060b030300c208101d40c8441285004c0e43d0700d181418060b9a1401003201059002d07001240101c0d0300d0071440c601901451400440f86450340700c4d00d20140480b41c084c0501f50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 197557014 1250 197555764 197555767
    0x6040305060a0c111006140d0507060f05070f05010506030d080c0d05040501060302280e01030c18150b070312020901052205100e031b03100c09030503040f030506010b07020303 77
    0x30310180b6a9400b0f0f00010226040c15010304090254260a18180a41d041d60040d582d510a0140e000c69080140e200308050f110b10701607003502d85403a5501c0e903280c400d41d000c1011038001100c1051240e026100c625604c100160110a064a00700f030203401c01716151406403282d4648003c8251003070b1102c0380210030308481c1902e04100c0050380760203890010700507181503480d0040000140c807081d040c03030a0264490304c100c080c41d071100c0c1000059210381e404211040110401400410b00e0380d107558049076140e40d4050502070107110360102401036480100391803510300700b00184614007200101406442661060307681209003440030200e0042d01e80c6203000541c00d0166061404080a818a0b82804203251030803856440f000640516000c0150070300040e10b800b6543c030b2a090401c965141030424500840c00c500142c000b1a98444030701c0c8a00f1125510380b6090104c0c5801082c0d4800510742107001d4a6440d034903207140300301c00344003840102c03030324801c1800001d4003202040544401550050145 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 197558264 1250 197557014 197557021
    0xb0d0f061404080a11030906030a0204050112020403170a0e0307090203010501030b092a130801060302010908010c080c030a0902181e100e07050c010e0f06060301020f0d020c072705060604030506 85
    0x110340000c9105c0389920680310410a0b1601561014040c621600352882c0140c0d0300e50403c800104540e00080c0d1190080740148010701c001040003034002c8503210701c80e4025803184021442180c2c0d045c1c910507015018011201d003c10680301d41c1d001181070301c0081c0c07010322000d40044180004940121070303016050042c3d040f01e40b18903001f408008841e2001d0700e4401d080c10328850783c0416408103980310690980d55003a0070030455030080003000c02404114020864840311980203000e544005104000d42070000002641e1581d80e503102011240d006810200e06007030a0780007490500043d203d40c00e036520035145c6220f0400396120f800c0e103e221040711240303103289017803846005c80c480a031103c030030700100344190141440c092098150408621000b810703d00c035140744080c107104019207a42d000340d004022003282080117000b10750100344108001640d4019250055042800303607044012051f000349030010f030829480b00040d034103000391003082085407103520821486200d5448028007039004072000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 197559514 1250 197558264 197558267
    0x1e0201050a111804020c0f030a0c020f06071109040206040b070804030c0e1009092d0b01080f1e0307020907050c060702010203041a040f1b030525030b0a0b0d0f061404080a 75
    0x11b854400c0c210b00440e001c4030651306040d400c6801501000380012407581510056140c10f24081c1610361003078130603c0c0340001d15180c00071011105849140a418100089001c5442c0d40080702c0041041c0200542c54407807602d448a0a42c1c403912007a01c502c13010200101c0c0680103180d01c14000d0079000107964aa0307140a180740040c18a400702034440000c242038503201d4600c0c02d040c19101500e0300340c1611100d07032a0300e0302e403140b401c040e08042000d9020311030790880100005411a00c40d40b10b0880f0ba2600c5041c04e0340ca618521404400030342088806050140880d006400b406404d555a0f007503c1081d074a5540480c02c0780412580903040c0d2101c10340942c10036207000002c85d04a40108800100f0312543e03210341030000c040304400401c440492000304144441400390803000c0c104000e01814100359501d204452560500010301049416008185070800c00d51103160a04805081c0b018980d0b031a080c8040d083d050400305860341414240c0310702600300c282c0401440780c0d5116031005e0414800d94070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 197560764 1250 197559514 197559517
    0x120926032704020a0305061e01090611070305100203010305190506040b33030c090c0912100911010305071803120201090206070f0c0e04150b011e0201050a11180402 72
    0x4410700390303480034158aa129101c42c002450154640e4401181c142070110511801c0c0185090101800040440300c00d4147c0c3e00404100c00c48e1030a10f032022000054806031403c09e54261310083c500e202d14201541c000c0174076000b441c1244c0c01641514404100201c6601150a0071000142150840d81c00500018107012031250000007072404c13218910380408140c01743c40780c4a02444284190010440351618041143c003050b85c0055401240c9801c281c0d4065445000701c140d0184101219010030403400000c000100c1034000ca000103005c510300504100715900184c2510034000707800c0a00140e1a00d010314400b6405118940c1840005840c0d07480703141c40380e82c40e1400c18046540700c6034420003503550350b03011f46012401528500c40517a003600c0c240701c807203141c1d9000c8052914588100310200e1048000b00d5214104241e000c54040c20500040301c0c0715500b56038a48183c0c29240346031024a60542c0414418194028200071a012044c0c24844030b00400361030400501140480e0341803404e1640 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 197562014 1250 197560764 197560807
    0x1202100807091e0e0403020c120312040f03020a021012140121020102031e03060a080601030302061603090c170105240f0d0f05062a0a0c0f12092603 65
    0x3c07a008126160302c0b15a02c0082d05980c01d80041e40012802c4180d403818101c11030502204100942c07505004241c00082d082d00204058840c2c17503003526040905009200c90200c0383da0050018006c4020701602406007030070700342c2e06102c0c41c0c0740028051f40107800c61b0015041c2c85001d01410008042d0b8070060f0f80031480035404030b0450009002802c8262004029400004405482552240b500b9000d02c0100e030b40c682d0107110316601007801000480d4000c605182c028004038a0003030950788588040d0060600080028502440000d00141000c6460b10101c44482400024880390b100c050ba0034440d8820b10700c0040000e0510340d070344400361402c80111001d44c08040c00503041c02d1000d840d01f0362030314240e203c00c0d1025000001004104a42410419400f06440c14078104c50201440e10880030300941c01c0c000107000480d588001808441240480942d07070080c502c035200341031184001d01259903880384c403903511151030b583c80340f50a003c403170b01d0644080c240045082400d4a005000303011f1a81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 197563264 1250 197562014 197562059
    0x40c1e0305010204080c01020f0102030f0705132112090531050901091b0b0301090902060904110a090b0418110c0d09031208040f0204050702010f06120210080709 71
    0x94100100007072003070024000a00c002c902503e41240d40d000060304050556200890070392040040140c620106010503800101d1407901d19240c051008000400060507082922000c2011200854a111642d840407010388110018201c180d45c0541c2640d040c0142d0003901c1d40100b40340446403112041c1c2e03641d00788001c40c0040b0841c60a6103c4260740403030700151100030303082e51504201d20511494600401c009490324034240000c1d441d181c4030006a00060180c0d400054035546036805540d05d00d07007683d1034020020010000030109178116050741d44071003131000101d444420000380b1100500c0640d0f08585003650f403400305840750105c150080000c030803000c4038458107100b01c562602040015142031081621285526415401c0500c40d95121145840c20821504d04210008081c3d4a250341400d45c10344000c1200d403504802a40541404c10103c030381c05143c10320000788030420352142c9139024004d070380303824000c140e01408070f0381c0c400d0454205000c2603444000304003040c40c248000e07403001c207103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 197564514 1250 197563264 197563319
    0x5120d1403130b0f1608010e0106030f060306140603060108070b0d022503050a0e09070c02040b03011e06031203090c0e1302060c030c01051609030f0c05040507020d0f0206040c 77
    0xa40e03030f9645400d40300fa1869a0840341d6102040756542440d141420300000d40d040050391907241500f8215840014000c1e0000c0607103035291000101d405070844005103500050912440c404594440100d0340c4c21030b54184284207840c00050103c034040760020a0351210450185010107a400c680040d51020017110b44105400500d0507030b030041c0c1048020300301d10a070748550381d42654940c01844c950348a60401e2160300074606201405070044a141c04050f03040c2e1300441d903101003100081c01407064a02c103205002c0d800c01c504650200c9a030000c03040d42d10408001c0c00c000d0b1580800c5044808c0000000c043d00d07082d44080c00640d04801d2440e600003c07109141018958550110b0810b07004446016007940c40420b6403d0111400c1c02207076808003945040007681101c04c0401003010a2510003d07044200b18005c89003807028480c1c000000d4900500b09010030f00341070000035031720241005080005414400f101c039100b031010501a0046421502d810b07446400d1403224804440212111905044d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 197565764 1250 197564514 197564551
    0x20c03180613060c0302060601171f0b042603030c1b03070f1401050702060912091903031e05160b0705090d0302061e22020604030501020d020405120d1403 68
    0x41010b5005808140e42e034a6807200c0900e0003070725182018008a0601403154694500344c1c2c89545a240e00120120302a04000808002c50264401541041410003c00200480c250220818003071075908840124a601c90130000483d0702d0740010f545040340303080100311112010101c2c08040078000d84200c1a43e1400d075150395401b0301d8110b0740d0000c40f8507241e14170180605a0082c807402c0e51100c00390014003001c2c5441c00d0b100341c076502d0f492040d400c110008284c3c0300d040d8617642805581c0e04a88000701860300d4070fa04001e0300d80051502182004503200020445d0f1901c500251008100e01c0d1a0142c0340404966403880c80900c02880c08003001b0b8140580c3d0000d540361568a80340c079000e50094966070400380c40c600404003914a0308580118060f080c00141311060340303062410740040e5810300d018240e500c0010700c2e900c00d1ba4000f900760741c0081005e041d604039a138000c1007150811034143c3c181e000341c50300198446c05580e0a040104407103c0201c0102c0440d5002140d100301100415140e001c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 197567014 1250 197565764 197565787
    0x702010908010203040f14010b01080a020d06050a170d0c0c0605030703140412090803091e030f1b0f010c0f030f0513060302070b060303030103240207080f030a0c03020c031806 77
    0x1308200c800b40e400349580d030320010910036100c11441090035078200901401550b040041c1c05182c0c054108803100e81d0000703695804a050f82c0c8004082d000c018003120720541d43c3ea04007a81c0c03000104100e03140b070013040c60401d222030044030300600055000c40000710003803404205940c0b50b04000e11010925032a0140540080d6800d10054400d40c85110f11000707034045044001c0051515401c94506a401040108070964071070f440460600c03082900c1c046902404c2d00402d04080d0080740c080000c0c031940c25030045610141e28860140d00d0150361780038048104800464600c5a814006400c1c441300c0312900d400310b0720944400303141d1080f904190b46001c5a83c0c046d80511740c4964002c40000b40c1c04210b81e404c011582209540148040740151b085504545411030613844011003c440c0307114182a9941c41130494041d81c00c2a81c020040325241e81e003151030400300b64001c071501042146001101150240240309964001404c60015428070030300070f160051007100300020356481507092141482d81c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 197568264 1250 197567014 197567017
    0x50715060305030a020705041a040203181e010b010203040f03030315180b03010b0a151b08030709030201080609010b03060607080c0729070503180f0a0f15020303010503070b07020109080102 83
    0x2184070780300541d644d03a20b00340000d0800750140c000302d11580c102950000840d80c0200503004080003110016582d072181e1002401d82a002c150206d4180940c4903104581810421100d4800005600a000f200c1c20100120307140e1180e40190005074000d4601400864801e07031100006036076182041803a2619810fa42c12481d101040c1e4a03c45038a0f0440d070300d002d00b400c1c01101c15099003a00c0c44e00b5141d06140d84180e100c0e166409040810000070140c0c002c012605110000554214448540e03a0414030801003400d581c0d0702090b804244041d0201c0c500341481424103040b5102c00e1000c50440d00c80c1e0040103015441150705460040c000c0c004030354000c0741400801c0050908004c5120034069181000f403082034a2011448130322414022000031070004001c07640c0e10b1485081582c0fa034481d81d40000c1c020302a040203030350030480b00d00c00803800044090f840310a0b01c460b8190717110b100001000490b6030344024061280c2503000742c4410044558000f000d0a28207105040c090030307094030380d001b003402c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 197569514 1250 197568264 197568269
    0x304060522050f0709061211030709020f1b1f0c050c030c0c0405091605040b130221130c0315061805040c0b0c0a0b15040c080406050f040308040305071506 68
    0x220b0300b2802d00b810580108100e90001005100028410700b07281c80d102441180340010040c02003020008038070049e075814010707440603002c0003404546651500c500b00070140c001c00c1660300a0b07844413545c84000c1c6070004446141c04401c1c04890322058a50100307a000d0030154000205004043c00070002000c001c3c0040c00d03074000e1401c020010018040c04000940e58050401820790300002111088815900002015500103031004581b00c114500800d9a407090b82c00000c070302610204500a6179456020749000c0861a01076003100354035440110040a841420000c0951309001b1080000402e4901040019091100b000560380d0b038802540101070740440b041484a5903c0b0200b0003007014001402c2c000c0c040241c00745003044510800380c1e550745001500603081028080014880000c0420403000f5440c010f042031002a20907070307003d4280b0310150350890b4010b0514002074807406030101181e01c51070300b6680d090f0302030b20749071420b0701d06510071003040d6901316107000c140501c0101801000d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 197570764 1250 197569514 197569523
    0x13090506061c031d0d021503190204050a050f0427051213180b0a0b090111030a14210c040512211605060f040b0f04080304060522 57
    0x4140c5007100030412180e80340700034041c080300c82c002500046075002c081604507841410500c8111079441002880004283c0360003580318a146101c1d814002c0001c0155000e075411b2681004040d8421001e04281d018501880d9006410310340e0030030061030403404100009401030000078440d640c2c01001e0f170700f2050040080000c01d031000c605a040200800c04d6016404020894504102c1004072061001d840c0d441218120050030f00007002c03d102e20f60054041040042c804041c090365500c4031203498000c0151903001ca940c100c103000d02e40e60080115090059a41d4a4000040303c0e801500520b0b0000d00a01030090032a195100d80085420f8010340a40b070300402c81070311540b03070504001241c2c1502c0a01420380e0041090485405039403040c42c82c0c85400d0078411500d441c1c0040c0018400051940090481d01c5803000740302c18110707000e26840c016400750b40d507075041e1b98508030700003124803081d40c00500c0d07039a00304001000324500c1c3e0b04c01504444844040710117030346101d0500801448400e0b0568 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 197572014 1250 197570764 197570773
    0xf0c0306020406080c03040b0105040903020c0d120f030e0303130c0905070c200a3f05010b0d0503030103020f0604080609010e0609070506040b0a03020909040c03060b011d0f130905 79
    0x20858004c468184d04c2080815000d10b103107402c0e500c40d091203006100311406903445240301420107000f480744990b0700a01402c2d406400700b0f0360504030442015010403c011032003d284650000d803180c0500d021000c1200015032031519080c0085c4c050000022041e94251031302072000c103016003a4040ca5000c0c04030b90348d684038203203101d00741820b039410140e2085040d8070306c0c04a505955102d01c2220021a000100341c0c00000500020ba04803c080e845280d00c0d0381484903425100c640000004800c81da80540020410081d00d10b00b8041c1b00210354801a24030b0340f0500041006190104e20586c601c1809041c1506090b074480c18545094003d5442944c540d4540c0400031070007a081120551042000c0c0c0203180e05841e05000c100e4501c0390703008040e94200000b807080d00040c001c3d0100c41c0c0d0024043c202080b10301e81420001d000c030b01c4030301046840900b0302c1203400980d0301c90b0800006c41c08804818051402c080000c02c80c100700a0002642c01c1008058113161042c501e109141c40b9a00030406030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 197573264 1250 197572014 197572019
    0x1203061703040f0e04020d0201080a0f020a0c2a120201120e1020070b0a06080a05070812030c03060f0409050610030215030103080a0c030216060c2f0d0f0c03060204 72
    0x5143c0a4082d8000302c42444511003000003603941c48141c2d0380203980a08044500f922008185009007108400f4080c2142c000520301035040d922030000700f06e15010701c040309008040400220003c2c812030600340305a03d0000001d2040c1000b80101d40b220314414148108006503c00c0c005064404500141100d0f41080089003200b0060380141c03000c0c05a809014000f0502c4492429018091050f01910410041002405412882d8451030141c0352180440384429210310f8856a590450b005880003801002c2c1e130304003050025021b40703010740103030340d58141190340d81c81c00d2000c3c488040980541c0a40c1340c4112102050b801d01c4224010b50341c200091140508500520484034499580c1c044800000c00040020074440c00030f8941041f002d02d0241144d8144d42400c0b1302d45001540300c0103400b2480d8000051b419005161540c4092160082128002401c00104500c6400700780e03000031300548400b91365071840c000d80030b000c517144900385000b150801c1351900c03600d123030740ca0b081201d400380d0000e800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 197574514 1250 197573264 197573279
    0xe030d08060f0a0303050a031104030507090b010f020604020a060e010c061b11060f0a020f070507060833040221010f050f03061b03070e0402070f0b09070f03120306170304 75
    0x5101c0594015115000f019242da60300900720310503900300c10708050755007078240c464016003421a0001d58100080700c0069840c0e046420091059a81c4540407640c01030880988500214249108640007050790b40040c2c46d22101713a0f101104680018100251071454400054a0303210380084013a4141d101d900103840040c028200040d0b0a89049065011404000d0a0154850440d40c0a41e004c0805600c441a00700d94003080c1c0211480149540200301001c01e00c154002841f520982e9581118010703e40c0c5502c250502c4041c40619010311440041140c0040c00d1a800800c40c85600707014241d41c004540155a0702c001d000c1e0080100b11110202c2040302e131070200400f02891801303d0240000b0700713001c41128024207915075003040805000c4000340d1064011840158090006001075568070f4103860451a000c5076210102c0d42100304c500402c15590b0002000c00a0310701301a40c0300c00103411078075519142c0c080d0300700c910105504c60342d010130101c0000180d1040404040f00454403142420b06 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 197575764 1250 197574514 197574529
    0x2304020901050a18020703020307080301030b0a050a0209100e03030d060e0912270a03060f02030a0c0e0105070b060301090f0f1502092b0c171005041208070e030d0806 73
    0x2c40c5109624070403040c46052044002d01c086542118030050380c6414070303c1c00382d00314015210082c1c0a1207020000109124401401c58807940350414108070341e0350707000300c5101280920032446411038980c0710300042d810301805820840210090442b410045094010410f4844a800024000444400380b00c00c0341810800c41a01b0034040100504069000c511840c480c000c400c4d5003200b041014034030f104242c40e01e4006c0e501941d0000303000d0200039191190003000c1c0d401540c1b0500f585141003922104180700303207100c00024005950b254900321060700e036121400d00c003a0070941c2c103560300c0111b240090300e621040d40350584100c0c0320741c0003030f0264100540070f10514080b03210700e41e004005040103541d82034007813a641c083c508003040e00a88900411505c072220400010300c0209800c00c042000401446410407501c01181210018503001000d0016200300b910700a08180d082c0070401407443c06803140341d52244151509001900035000000c0c980051010700c0130206030050148075507401c0680c3c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 197577014 1250 197575764 197575769
    0x109060303080a060302030d120e03030f04140601031e0203010e0d030b010f03381e030c0a0b03010b07080f1303061d060c0a090b0d02120f010320042304020901 70
    0x801000864511b80120b6125155406201c00f048403105c3d8900184c2015842007042e07402900880f03860740380010030309590b00400d030b40580d00540c541041c5d0320468400150103050303035800388240f4480c5002101401c100d084021080743d15549805004c48000800c00918400662654000c00c9a18162001400c0e184001980c1001c260a000d07269504940c047c05005034403545108040a00e8864036540c80d0300158501c0342a40900341c2200000055403918404510a0040b01030341c00014030402040101c000034400c608880c4010310041106051001c00b8104250040c40349600d402040c2091000c281d00031281c007c41c1d4089904280184040d61040d0802d62300701e8218007074a2480c04002c0e683e1000014030107108440c0c001080c42020b403080c5940d0303004207043c44007113440365074850b084006034120102d00600c11f5400c00000713800c2e0108040300e60407690008003281c06c2d840c00c2000c2c0700441400387c80c102c0d040f42d00c2d4440c00360900e401e024900760301103842207592928105441000340c2c859069 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 197578264 1250 197577014 197577031
    0x804030b06150418140f040210090612110903070b0d0507050403050a0f051e0307050606040501061202030c090d060902030d083105060708100906060c020f0d0b010906030308 76
    0x484107440701c80003800b154142e82089003000b0150030030259a2004e03207106804117212041c40001d028054101134115402140300300d80401500010f6582101d1141c05031207030100046d44c1b0a0409065001c96010410040c01202c010b07140c02c00d0308010a07c1e220813640700b5404040c001624400504443c03080035082400b524003179280c00c1c5141c0782e4076078a68240b100031b00080305607941344c0200442002140d042880015499101c03460300e011880e26a00301e28001e5503107000d00f2001442034600b9114460590b501500c981c50b0110000084800942004001208242080040c11501d03903407004aa11110b02c40c07039010071400c03541e105150512a04000c6c441c01e200400007403050b12402001020601d010580120011008011008514003101c0780040c2c014005e003010300c034160b40d1160101d44a2083e455010b42c02c2c070f5a0313120442c1211998450360000607a21112200189444401030300c140303e0007081b42c0d080d54100e03114404603805c00ea11000819130b813900304104050b0008800340c1e0003d640e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 197579514 1250 197578264 197578279
    0x12010501151205070906051c05070201090b09160303081918031e050421080c0f120c0d110a061b02010b010c0c050f06070b10050a1509170106030f0804030b06 69
    0x1080019004143d10b0054006015010032074920368440003210301d230441c48140c018442c0381001c2102134024034003900165642041c400010320b800c0000070700c8c180b80003500ca01031048a481c41e1800c589898024210840c81468181c0344c824681033401500340c808004610035910781150320b40036184501d041c1c1c1d0b2030300201d504d09420441540207002e50f404c581c02e4131501002e081c02c190501540d00030741200100070010209804a02840000320f481144c000796044548011040100754a10b00501c103005480d03078008401441514403c0035001c242800318003c80301e24140c84c0d41e030b44040e0345401d0403804001c00007986009141d80d090240b41e100210030708200c5404c0e01c0a0710350281000880c0503540c0208907080740501e1039202d0a003122080d82d04800107490714201461841400c04d15442020720841d4150004101441d190032140d060728016240e40f81c180f03160091001001c40420450720841d580d42d040040410304005601403294810000203a64a0a5107041d00c030050003e02a0b0780640314 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 197580764 1250 197579514 197579521
    0x14060708070815150c010906240e130c08100f061505070f0c03080309030301060201050144070303030608101803080c0f040608070e240912010501151205 67
    0x85400744004598165111070308021048101101c1d84124138096940d51f103405218414404035030702c5515102840384241c0d041012500401c0c40c030301024000e0b408070000140104d00240380c000e40010b8110301c1205020806581e8080d45420543c00042122015450701d1040c81103429610509001d03005e40458801056031680c1c000b40140070742503000b0305006c00d54107c1800d0000b4501c0c00c0d402035511452840c0d4a142181000c0c1c5c40e40c00a02ca410095070901c0c0c004640c20260060640c514466181c0c140150f00180c1e0010240302c020455000e1030210303d01060024000c2444560051806602d0104885203402c01141c6007410643d001802a0300d02028282d10b03a9091820b0000c054061801300e41e0750b00c034003201c40c0d00340c89002c2e99001e02400010740068000d421003a0184101c0c0103445000303401e0000d40900403400c40c1d55420f11141e0800003801d8618240803005019100005070802800c1b00889448500710340013a013020f05410704032002c00c0843d641c009810440031555603400e0002c7e08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 197582014 1250 197580764 197580781
    0x3070807020f0c0111070b0a0915030b0f0402030402040905030a05070b0105150a051305040606080f0a060b0a11010902030a030e09070201090305092107060f17040803010918140607080708 82
    0x140f440504a040050684448000442c100140c5001c1e00d9118041d0755516031810010304075107014418401880310754041d061019000f8810300250b1200949042050200402004004e50000b401241d105035902c03030300300219208001402c2c010606807074150342c030203550410004420059004078468501851650480082d220a40b0045070ee141009a01ea0480a000c10b055018a401030394209280500029400758007903240340c0643d12400c21350b1490b8581e40302c0d090a407141070240c40c00302c0b00204011186184a20701e03940d060f0b9450030001500c3c000c02d900090a00e8400e140560010303544000110341450710820903030700140140020070034005980e034041c0250050396545c40c8202c100888034140801c80c14181c072840499a402d0b41c1d0410b0305d03560054440b0398200c0100700003171aa0045030703c2e60940003040501984e0005149401d41c2e03c0d22601001800080340081c1e400e02540f918000020142518450b5050703030f403c040c1280d443d080c080200003140c000e10345410841520141b20401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 197583264 1250 197582014 197582023
    0x403110f03090f0405130f03051b06090a0206090102030d1103060a06171b161b140108010513020f0a0801031a1e180f0703110103111b0109020904030503070807020f 72
    0x3d0342c1035401060903503c440c0e011701500217140300031f44400324100380c8404050b840002400058034a070000004240c61203c0c042c0c7e5400c0032222280e207a800048400c0151034600302500950780148112450004c005200c00c1c10740d041c0802080e640d600200c00e0103058901082050041c05035450881e250014000c40f042c034030381c0064006011a4880300b07504500d1a0f05508690419024400b01100c14006162030810712003000720310005140e40000104220240c0d143d58182908165034140d9541d0802c001c001d5000f8138400600700c000d030f00304004054a904a00a40002501622111650741c51424158450110300c0440015548400c0400500d940800e45402c101045428050410741e0761940b5003079a60500d108080707007407048000810303c0e0080011034009580c444c40b800c202140140d8010f500f600c0103500c01304c40420040c0012008a0040b1007004683e144010002c180b4650607000b048041d4801c0d90700f500040c800004100d40180c01c0031106811142a20060104c44101401c080d00d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 197584514 1250 197583264 197583289
    0xe07090c053c07080a030c080c070b0a0e0114160c20040f06300b010510030b040f02042102030717030904060b04050a0b0f1c020c060403110f0309 64
    0x205038a481c09801c000c40102c1e94041208805902ea038a54072402d004460350030050b9950300007030408880c0071940e0b00c1004003030b000c0e50120540c2c80c1011000c0d81e521115002c018100303181c0d0380c1e8401410170041000d000b6030301d4503902802c80d003000741407103a8500102a00d148911050085000c821710003c0d1145040904284051400208541e85c8500043c06060341e04550207803103007807031400b04a0a00050b80480090303800340400300c08a030854180071130810240000343c20f01c590f510042000d030400380d0345030b0415005850005502922800082d0131a07071019030302c03071001e940814180a0892a0300b0000510901c80a003210004c00e075600003071392500f540c05030040010800429080040c1e08009441c4841d03c024000d00c841500c0708071b140d0305034101c2d1041c188600141e50700010145002402c40f83e0b90700d074195211f40390130071001c04505880010000100816404c1080303544080007400181d0103240710b586c52610b46103403210f44518000880300c0c0088503400402803843d4660b500c42c4880030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 197585764 1250 197584514 197584567
    0xc0d03110a080a140c090a0501021b040b130504030509010f1106010b09061b03120c0c120a120c120e010b032a030604080a17010302030a020d0606090e07090c05 70
    0x840b561030f1407065016046401d0b000400c003c005040c409465004c40c0902050f20090311001c50850fa01c200480e0b450790038102c403001803090310102e04c1c1c190400780c0040c1980c102c080c04040d107881411407007204445003200d098002070b00100e1510354943e40b29800010b00e011918001440900350b0140710b49466061084207041c05c0001210781c283d44401c402d48510364103002500846c0d0800c00d15a5881e40d210410001d81c01900301c000030700e20114801a6030001c00300c58010440c03a8a41c010054596104400b0141407180282c481e108054030b40c02801c150401c5036075802d4040c00324403031b40b9041e9040940d180d030240c1d04002405100c0d071800941e8915009018074008815003444102ca03030090440800c058040c000d0400b0041401301600040a000c0c40e1540c0d400c1e40c04002011075000c0c0c0100b07000096160300b1031a019405840c4c64580225110301516001070556642c205407000c41d02640f090021541003c6400c001c1405284038240782240c0e075003005440d201c40b250344001c02ca60800c00400c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 197587014 1250 197585764 197585777
    0x90f0d09150e03070f0e0a0609021e0904020d0c0e0109150f050f04080307030206010f2102120c040606020a0308011d0103031110061202040c0201060b0a050c0f060a020c0d03110a 78
    0x1043d680400000005010b03546070310310070075100d04401460b100c040340c41070305003410040d0005204902d8400c980c8001030500c03620800303021042140140354410600c450707006400744002c1700320030752910801c01a482c5944511424a8030100050030480c8503030b01082a101070a10b449244540089000b0b10f41c440d070f450441e030b41e01d06036403408000d4080e0750495061480081070040805400240c07a0381130300c03840081c40c41856581c0c100811018100f101c0c0081803448a041903005041418842e61188110030a0724003001e001c80201d42160003551001c80140cac01a414542030603044050300e8094003801c0c515452445d9414408074403802c06100003020480341d505110543c80090110000c00c080740e2a05000450341c91941c41c51190715907600764400e130b10340020409040d00500c1208226603002a0341410a42d80020a6603240c124102685a0340611641c0c0c14100350f01703020701c40c4105c80b5010700585905121b03641f149000c1c280c8540c4400d051802070100e041100e41410b8400e00301044c80c044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 197588264 1250 197587014 197587037
    0xa0e152203051e03060312072409060908090f04090f1101090e010e0a11030423030c030c01050901050f0c160c120303090605060411040312090b03090f0d0915 69
    0x4941501c1102c0c40035200d895900803c038200c0808030b004600504040b41180c1c5603108003000c00c41e503131182500040c551000c01000c5800e45480e03004a0f024440070b0040080e4a40707030703621048159811408116000100010b0052103840d00031528505508140d40130007920b030841c0e4960b1215041200090030281c1d12011802d180e0f0310481034a000b420050714943c000796034411041501101c1030720347e600c035903081400220300007a0210641c0e10998114a84088006000440b168200450000407600340003c12a003404500204002e0496030040c80c0005142d00d41218150308460001d8214026029540c0902c01680c40c3c0c002501c840d8540c40041c00d901c402685040c4100e80e00710391041c010380101c80d002c182072503099800103240c1d40c041c10080c040c0b030351808200022200c8001082d910070740184000c4c8007103030241c0014200d1000c141400410b10740c41d1113004661781c00031034426850354441505081c4421003070126260000c500d0801c15002c6041c45010b60340381d0488580d6504111040004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 197589514 1250 197588264 197588267
    0x80304020622060201060501020c0402031e0c040b070506010e10080a03080717070804020108090c0a140a080316060605010c03050708030411090705040602071502070b1c050a0e152203 80
    0x3842141d0300341c0310ba001c2030780e0b00c12029020708001c0c0b0425003d8011400354815505003030088921400d24180302013445004500101c5891101400c0c541c40b40c9002d0202140c01c1c4520002004458011002040f266142421515030310b038000303122981c100c0c4601410080c120001612840c1d5941c1030410282d075035a41c1d8001c4498107030b00104455001c2026090183d019008034032940558000c0c6e0300e40d405541c84078519640c030a8801c40d456040070f04840c04019070030751404a140580f000904c0501c05c1c607070b1007030f203d807a5030418100105591402e44100d001c00c4800c1c440c20008082c00c0c2030062146a03143c0300501140030358000644011400800a0704110481010b940d24001c0146034240c24200620000c1150b001802201d000d03205850010035807005071107114070865890780c0246552828800c040320942c00405240d114840403821040c0c4000b000d005080c0302d4003a10200003050007821403284e1402201c60340f0b0f15902c00c00e08040c045a0303c01c441d025101c04a240780070b68075045140c40e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 197590764 1250 197589514 197589547
    0x8070e070f120504060b090601020c011b051c032708030a020c0c0918010606020a080d110c010c02030d1802010c02060f0f070b040302070b03010b041505040302031506010810030803040206 82
    0x3600000b901d0b20040004028556100f020076010990b03881101c0c2c0c0e00d1000681c1c2c3d81404000d0740d400b05100b640c12101c0d400a80f01c400000500c594191004003101003000ea402849220440011949a00c0040780f09144c1d43d20192030340100f10702c109011051901c030341d2501c4c840030700840030741600012000c5426400708000d6103011006814900145010304c0760200140d4541840b1607036500b0548000341080c070000da210f07440c0f41c004010324a415022410000106001091001c0d021828044044e4022080c803070200403240540156540d003184241072403c40b1408a44442150a200342c0300000d40d81c005003580000c0c0d4151080c9076103010798a4800d010b405592030104540000040da9000c0041042c40107004d18403036005c803030303050740c5640300e110043c002405102424941888100300d1107a4160044201842e903050880c0346c540c494022904111800100ca08039982c0501800350702c0d6800301c0210307400192042650500ea0442e6120902031002610280c800c4a01045140c12b8100c0c950 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 197592014 1250 197590764 197590787
    0x3080313140d1830020f0d0f060c050c0613140a1103060a02070f060c180803070c080102030903160c090608060108060a020a08010e100b0309030405040608070e070f 72
    0x4048610440c802c0b48010301c0304540c0f00150307890800072000010031290400039141004a040c0009440914100410600191444007aa8002d00002006055480d20855500b542c2d018050782d40003081941482400c3d24140307200b040c00c01200308040003221102042c9241c01a21000104480103081e007020750031071864120301901d5003c2c5800c08801c104000c0d000b0440c1c1d000c10703010ba41c07595496075407081c200d025a0ba0003505a09c46a103140c400200b5a900c0414000308034200f521440920f10301740341c82c030190754200c250140c1c0009a00c00504c80c2c10a80b80f002000048000d500d5443d200e100c03583c40f8050101d0144100d0200520a0100140c010112000d0301c8d501c54100011961b980a03d50342d60028030031a03849004000c08a030030b682042c0200d0700201c44c1901d41d40c1280e4641411254503003402001101c41c2110641c000c140d4001840056010f10700190066844a04040422045445650146200340e00030070040110103d0000701651110003810412041440b03e103066503e4620380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 197593264 1250 197592014 197592053
    0x2070f0b07020a05060a0c1b1d060102060a06080c0607050118120801080703020f120f01090503210f0c0a02210403120804020904020405190203042a03080313 69
    0xa5000c18152a03000c06441864000c0314000e10442c1c3c1d68080c00014800c000320100014801807003000407030400d00100c42001d05060421143c0c540d1003066041c2d0400750100745940000480902c801981e04001f000d41100ea01f81c0100300c40751a0280450b03403a4658500c0f903000d88004900300080c08400e5200100350011030183e4141d000342e51501c40300126107101e680010680040010a882c8400603d100903642d024180c1c2d20803403158020885a0102000a1821032140d04800c50120000f030003640703280c5104400541e10396080c1d903100f05d41106a84d43c1c8140d801c0f003400c2000012082c02140e545c004030010b69480d610b12000608030f0404881d18007c2c420001800c1300d15003034143c0d07031004000300c031300442444510b04c1c80000200e40150301964041c2d400000000410b02614040e80300c680c01c1045405a0351100c0d05104440302030382c000b00c80c1620030585a81982c0780d1034001e014810041c14035504241d445505590702d000c0140009400d5021740310a10742c4d508104101d450310402d056865 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 197594514 1250 197593264 197593289
    0xf0a02040e10030c0e0f06130906021b07090b09040f02010e090106090603060501031e0c0e0a090f050a0902060406030e07090e0102031006020d020c040513060207050303070315061e0207 81
    0x111440a04403a0144001c440095244c28001000c403032204001e401001c039041010785a80781e060800181e1540d4040d2a40c0d0140d032a9461000194184001c05000407803a180b2a41d10751a0320465040c40c04541c4200401400c0c41d1008465075141060350f94056030151030119001194001240c6158001c0c80c0c0039004501c400001c103096420039103500499099540921225456800450940f1030948100a11441e080b28003d14001942c0140640c8000c42c0741500c104a21100040c1c0c110b23401c2e90011130301700d586001681c1c03410740c640a00b942c0720075890024440300c0308036801700d0075520951040707204055079a43c80c2c2c481c149047c845000101141c02052010051220800d4000d60080d613003011000f0791600002040350000c82d44450209030750700070300f031005580801e200150a00400b44550036440d0300200c2c0004000c1e20207014424054001151030786480040981101d000c220201c0c3c054100c90810040e03141c1c048110350f10524040c204028034184000c0c1a45001106d8201c900f85410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 197595764 1250 197594514 197594521
    0x308130e0f0906090706140c150a09060e03030105151e0d0228020304060f0504080106030c0807270c18150e0604080607030b0310230f0f0f0a02040e 65
    0x10100280035602d040c0c15506191203011a4039520041d030303c102d802140c3c1e100d910000c0b55072000040e04444003c0d9051341c035443e0320b0f05102d291140c4101e0356040d130640c0d58030020090000c21300c102c0118a008400544c61941007100013110399201c0807042008100c0041c0012a001440b5030403040d804074101b616499420140e2100040e401c0010350341020f107485a604100c43d04d43c02c180c161901c10b19005140307014106113007141c0307117217194a0303200500170204400560403609200d00c000540c0149414000c2c94280707000725040c41102e9001000390552901242120f89404014044d001e841e00300000317030424451800d64809411082044095520f010300040c13440c1e00208202280a80f40d131004940e042031350070885280654020f480c259172047c2c000601003802680030760301080000301210382200110711120b054404a000308511606003143d070112820f0488000b54001110002808051070322483c1000100700043c030101e0110605008180c180d40c0316811140604403544d0715031103501d07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 197597014 1250 197595764 197595781
    0xb0403120b030307030807030c03060302030f07091407052b1427250b0307020d0206180606040c0306080a141b03070b1c06090f0c08100308130e 63
    0x20403003151403100350510407140d001e407801100301d414969041c5c5440c480c0b6151540200c0081804800031414140c0e40d82c404005603408000302e140340c1103440d008054942c2082184070a94441260707100c448141030301404035040c0c10000b5141c2052401d006502d01400010711481030308403550040c2000ca11706241030720701e10700110740d940c032a09200c0fa01c814190b00c0c02c000c07541921042c4404688540160382201030216400809103150f1502d21400320016031214020415540152000d2015038031a42014500d42d8051190719800541c240105400642c0000c0484e00d4030700050103184920f959054659050340280c0c054006010a00202c500c0801146090440c03c00e00600d000818420082900c03c01854805038401280000e409407038018600030381512140c1011100001d4100003104042e4038001c1842034200405880320042620510380d00400f045842c1d0101c88800c220480b010815049488448032040340d40c821042b5541300c0107a100781c000b0245540060008d071501005020095 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 197598264 1250 197597014 197597027
    0xc06110301080f15190e030c032125050a2d030506040b03070e1305060a0b090702060705030705090f0405150a0b041215020904050403092d210b0403 65
    0xc18810300310740d00082001c0001e8091007013240e0340500c9020001744854410a140c001801e6076105408903400d0982d014074482c2550000b03403008030302892103481035581c400f2506020307401010080d20140d1840440c022450741c03004009142d81440400a5441c0d40369201f04085403040302031003524460300c1c0e20034040030b00f0b0310101548413000a05000100c1c001b89858482c4451145000300200281444d001e0340040301c0200501c20940540d2010716040411004e000e464420b502c51030000a11720040000c002214030054817000440d44500c04001c0c6c02d5420008a80e04540e0701e082c1503440b0740c1b452001400210544401e01c2d000390808052102c101007074000d11501d540c00300c8443c200c00c2e46510504a40340620b124180040044070014000f0030003020032500500e600c080e0251804448801060941d44c040d0303000c80c00500c42600c00c20108590308003150558040c054600144c1c5d1030400b0100441050380036140c15041c5151880c0110101c004091100d03c0d0b01c1001452140b40504010742030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 197599514 1250 197598264 197598283
    0xd0f2a0c0303051806040b072604030b0601090e040f110f030a0501050603070605120112110402070b01090e0f061906151805040606050a0804020307050d060219110604030c0611030108 80
    0x101c121a21307000258502202501d003a03644a41d819410031000d0340b5040c8125940010021f00d0201818160315072066001c000c00166000d886c456a0904004000400e0120994002c21a11811005000c0010102d0300d00d00d90694218120316543d40e2a0b0340096290b01510044591500c00c9418484c104003040d000076101c0c00c8201c054840c000c1c1e5802c000c0d140361151031860018621510010302c1965200030010104130700440c1e0403a0501c0d80000070401303d83c000381c02a1041040e20740100070003441030044150201840c4042c29200e0140900d40e0b0383d605c8050b1038804050030041c3e03484078504055110900500d2044030003400c8540a01c4050502d8546100c4140905000507001c182d604040c042d42c3d04490302d642d5000c2c540310360108100c0b0380e2000540b00300c0e41405501800140e650302d151030129042d00030f40e40141e9848201c500c060b140c19000358240d040c0400701ca0200104039011401075071064250400118141043c540f03100180300040c9816040c3d0400f0001040039440054031055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 197600764 1250 197599514 197599537
    0xe03070515180601090c051c020717090a060e0d02030316150507080c16061506030f050106020604240603030504090c02150a020f0715020c0d0f2a0c030305 68
    0x202619201c060480310700c2c290980c1642c5500034001041803042d5940500d0380d050051a0a508180e013060722901c82d901e1444401580c950007080c20418400005640f82718001c00b108403e107400e503d00c2c0416011342c410700c101000d0101400c010501a00c1d6200501034903580101980d585840c081c1c0d07080d10303035030011106803542440100c0f1003659420390312406010f5606512070200c43d644450800041750301658048101d00b107190054000076040f4015071320f00724138a011080c442414800024111440c40301c0320b1400703d04110041000d80c1c3c02161954001d40c00c41144c00d03041c050320103408540b000f003010f1441d04602c0e2900010501d40e00001800503201c84a0081c0201580c150080382d50b80005428010115142c40c00300d0800ca185078010484550f40c4040c1e242011001c0d21141d0303441d4205030b88580340d070f50001a00c0d500c01c1e8091040a0342c041403070070003401c211201040108046104547c1a00307a158403110315015070b95210500704140e9002d030f07546005a440307140040c8a500940c41443c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 197602014 1250 197600764 197600803
    0x1b01020a09060219140a021306090b040204050a03020906060708030702070302040c1e050903010f051008010b0603012121030e010b121002030c09030613021005040302220e030705 78
    0x24025201080c8803507040e019005013010f52001da1500d10320b000c061610100075104440e69040140c850304180c0390030071070300c660000c2c003940f80038114415a2500358120744558070400c000d0210342e03580e8040e142501d0301590000c0040e543c15021441602c07404e2002350800c20003008000030301e075001400f441500c2c0700765000e014502c2e00005c1a1008844070880510304050450034049251117000901031a000003000031846014054a800484000365164201c41e05401d0090200e44000d00880c0e03400d100c1035601916640c0b41a90400d10504507900c0281254003d04d10401446a5249109050b041030030340340604100241000d00101806c040f089815420541d06404901e0546402001d0307075280742c003400c1c1032070383c8900c003030002e500007031060840e40c0043c80b00903c035131010001e0510407100c0342c142d001e810b0158010000e100c600c42081b0713420800e0800c0140016114502c0b000031007080b91850340d86a00c444500d4102038105002c05071400c0c4400310b003080a011000543c089003074002003548 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 197603264 1250 197602014 197602019
    0x605010f030e03030f19020c070f17150901091a0f09030c070506031321031505061c0b060a0513091b0c060621140a051e01021b01020a09 60
    0x2a0140d5281c9407a0780700503041440042c282d45d450b00342c415884200c1800b4070400c4036200a1200032600484074650283c0d00004040c81710444481405024050003102141c000180c0c400180d613408441d1076500c40c8502e20008607030f80c103409411004001d5405440d0100402078440703104400700c8101c40c0880101c2065004c600d000c02e01000b140c2c007820000c40035050540c200340a009a9600142180713500f8410014a500480e600390341001b001a6400f40203c0c6086ea240360003001c2c0d81c004200e00400041041c002c1100c0e45e80c45048070001525401c103030100103154000030703006040c8444144d4005200094070340b2a280e0100c0180143c494940e45401d0382a1542299011984000031001901c0f0f907805005035004e0052070196041e81c800c01c00410b202d520b413405030703133070072420080d41c1c00302c507540301c444d1042015140c100008105c0e501d004000c0d0005540f920743e0740700301081040c8003d544965640340669429012500c0241c0810750286408a8002d2000d0007035020041250000d151044003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 197604514 1250 197603264 197603267
    0x40219030b011409191809121b12180806061201020f0301092c0312010501080403091e12080c010c08010f090b0d0b070306030203121204110301021c0605010f 69
    0x302c007003010914003403400d1804e580180f03c04122045c0380521100312031200010700300710000e46800c003a041c180020840101034900700b030080808028080500c00d0300248140c845042000480200703030052036281d5200d0000d00b090701c2c80180d440c0d0f103074055084428033181042000403518019402500d011541c101c21002042c01c07405031410540a81c8810801007081840a03000391070b44258020403842041366103218860100c074016940400c0342c00100b014880406842c0e10280180f80a003030101007460310740d4000340208030601665160905949123986d521030359690343c0000d40700880c54021405001e052441e110b402540040f1100d60805c11051000d03807040709858102d400780103a10340c131345080504d002c0141103501e4545421205c42d220080106400b0000c03107005000603200010780904600500d8289013001062a508140400c051303940d07441d1860714150711a03089a80e265080340308800084c0a485004111035002d029420600c0c140c500a9010000b01c8109072681d0050400c9180b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 197605764 1250 197604514 197604527
    0x6010e010614030c0309150a050109180201051e09100203032a180114030c09030d02190201030b15040303020d2304031407170a140303040507061b02040219030b01 71
    0x40c0a2220441800070440e0f440c00a03010750b4001b075000044d90500d640808507010449001c0b00c51143c0c160715040100b100c3c00c1ca1f8030030307a180000d0305a101808140c10b0340000c3d103188211448005001035001c02c0c0d4080c40c02c0035082c1c1d042c0810062150f2103003100288000c0d43e81d001620000020401c650718010031050160410303070702c00e08021005e41400c0149030740d00311080c02103100341d042c04032443e0800301c51020180110322600d5407801454552000ca020b05280c80010403403941507500030101d01c60701300030207000ca9900c40e0742407a0101da030111207000705407604548852039520f280c1c0840e011042540100305106444440d94840c12804da40001210210402c006901e103080d004020500c0800d14002e2038490a429090860b088030380d80b00000000c82c1d070b80d40031640440c0c0001c1c8031a0100070070081c1049151202e100210b0450816855a07900c03400e41d4884c210500c00042440c0e080300b00c000c099189169001002151142403007061b0b259020403003c100400640741106400c160b600070803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 197607014 1250 197605764 197605787
    0x1713030b13170c03040f0f060f1403220203010c020109051b0a0314010b030f07060f0323061302180406151205060f03010905030409110f1e1b06010e0106 67
    0xa1510424190030b10b4101d100d0303115400ca56070381e0008000228140c40303042c10803802008802003518082d482c1050003052030843d004200100007081d80c99000341c010b00e0003500e41250640540c0d442c8181403011240302e062005200135015401d00c04450520360301940440507080c00340e02a00c3c3d0494910b422041c03c40d03200407503a50300141c0003600340081225580c4a188281035003000003810807aa00010389081060f81c07200c02c90354040c0b1414403560fa40000110200709803400c041c400c0003000841d080a201ca4400e1525420f4107581c002015035454a1100e40e14a24940c3d027199102c00480032480d070350300180c48083c0924102400000c0c0c010b1000e60300108040265102803201c81000d95078000b801c0301901103940600002c0c51419182c2c2c0c00e00c40c490b000c2c1e00c00d000941d541c502d07081100b420f690f920110300710f0b420002d0102e417a21580d0710b411101c1010200500381c034a0600d100b0060480d01491004040ca500d044e0f10241180708002800d0b8142d4807100c0030201103a80e40d500880340c43d045d030b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 197608264 1250 197607014 197607023
    0xb0910050c0c0a0602070f050114071103040f0909110613080705010e1e0312131a0a050a050c0a0c0e0411030607050a0e240a110a080301121713030b13 66
    0x303854643c0410143d41c050007415103d0400009105c10f543c4600d0f09580c0d02d103200c0c1c1c100c025050b042c810910b822615612602824202850402d447c1c14041c0e00c8140700c5105208900d500d8000210800402c0c20129409500091865448041c110302ca0300b0b100c50f40f8081c60617240f14403400414590702410048150070402008048000d05c20961031540144880c1a160580700d81c0e2405600721040002404c031000311a85400b540904c2c0c81484401406410a0403d0040003044106012a4000b04070781e02e00c2c1d20390500766030300d103512030b40707246421a00440600100f01d1201c0104800320100c001e140110300440350b803451000000201926100161a07410114030100b1601c0f490a01a50503807001c1217004260340d51114501e8541c240804000c0c546452241c00024005039454100510640c03000e08a0000c108240b5580d8a00038a0303c410b0103030000402201e8041c80c00c1100c8282e0310a642c988000e0f1254443d40080ac015003c00094003048503c00c1c6803000148002004003e10358400b03401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 197609514 1250 197608264 197608273
    0x40306150b0a0c050c0603090c0901051c0318270e06012706090509060106170403080f09031c0614090606040501080c0f040303020a030f02060f071b0b0910050c0c 71
    0xd070800b82c40b6048098011913542c000d50010640d6542d0b9440a1849a1061006072664200707010802c0035100b0705802ca00d03c18213000740c0d06800d5009800f8040081c56150070846091025510031200b0000345501c0407034420310400c580308119516602500c501ea02c2d0890a02c1a48070b0217004030784541c400d0081e1140b080c0701050304250051701d070342c2c0542c0c0301510742c0e4002065500c800c0b40300d0541d1b03011101c1c0e503110351010780100031040c0d0000564191040d901000441c50402d65002000d81001a25003120303102c20b480840c3c240103007882100c80700c035420360390380c0c1000303000182d014094800340c0300b1112106c2d0070480d00c041504141004a10450b0300800c0149080d081c880199403041c00685841100001440b203003007400e048000820103140130b90018138141c8114a0000d05642480d9501c2c000c45d00b0a01c10302400c0d948440803d500406a03061245c10380f8074801c0315440603000c030307600135000d803d002051091a00c1d01203040141d00c1d005600600c41c035650244400114452021000000e611 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 197610764 1250 197609514 197609527
    0x3021f020d1b0b010308030402030705010c0f03082707030506060103061d0a110d020c070506090102030904050903091905100302090105121e0106030b01110c030c0f0d0501050c040306150b 82
    0x104001c8842150164035041140071455190780c0080301c3c0c01d030811548800000280000c1d03140800000004060074a0308140d81200c82e0384091280100d410b004081c401d128012403506d081144040b00d101c2e4031a40c984811000140ca00b0342d0700c10035848241c503a80100e00214501c0c1d44a8043c0350280c81c0610300b64504031101c00111880f8450041c006150142e88420005c04800140d00401004004070340141c0c031183c22551050034948680c0c0b00522411041004a4050340c0200c00c1d0750b010001142d0020b040d43e140c48190742140f084119182d80300d00d12039519064040800380c0302e0140c80c400e40326913040ad24050401e60880c0b1440e400c090216405012800103009280c1d9500d621441144044507101001c000f0580c10341f2003070300820042611118440c03110f5034440903040c01d5000d018000d0411090820100f51201145140385000e01142c8903456410780f9600290042164410005c22240ca41100107192503003090008030303a81410031290081d000103e000450640315241c030517910300030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 197612014 1250 197610764 197610767
    0x1803010c0c1b05030d0237020d03030f050a021b070305210903070e0906060a0e01060c020103020c0304090c11060f15220204050a0902070503040b070213060f03021f020d 74
    0x56982c1110160038800700108070b5413010710650f1450350355500102a02d2441c0040441d08000c552840302c4030052502403011192240200b100c442a010b6074101448200d9082c00c40c083c1000c2e200c07410600341410144151001d440d0f000746801d04010401c143c2d400b4000f90810344408862001a040d50302c0100802a4810600c0421103014227a4101134944901f18012a00f0f110059014000048111042010400c002e0040c9a4440000c8604800031802d010902d120072006004110402c107401d0040c100310790080d8111022041ca200842e40c80d00d60701c42001c3c1c0075040034146d03000083e04c1c14040e050308a00c00119903000e50501c051030491641d68800b000703854a00054010750203903041c2c0f208800c034a011996009600d16111015944904217014401480c085a210b808074034810805440428404415501651780078081150b980c2c01a00002c2c1000b19104090b81c0464a003120000c0d031181c0c080e84a02c1228400c0c0c8070710402c0100c40305841c0030038000701e60359000f582040c0790042055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 197613264 1250 197612014 197612033
    0xb0d0b0411010c15050103060b091006050c0304170f0d0804030806090615070b010e090c13020d2403151803082e08070e041505040203070b0f1803010c0c 67
    0x300d07818035010840c143ca0b0344650030780c10811404008010340d564014001d01c40305010300b096841003513940164900b04101345e0a04072440b84a250704009010504488240c024011074004103810b02ca0b41032100040c6c2d125503259070101c00c03902c0040c814041c40004c018099541e10784129010784551420b569a0717001e0240040d8000c10b00ca60200a03009000707203400c1004080e10190b4003860100d00903604003d4444500c0380041d083c1240c0e81e0000c0d0301c010040c1d4440c02c0f03082d16003649290240e1180d03c0400c82c100640500030240109070021200b04189192041940d801c80c1d004a142500d0b04503480901400c540e4001c6085090038014040c0802080c000d03c402030708801102d0000720304c545600c0741c480314072103420005049141250700c2000301c10030402c80740c07002d80000c15030696181000d0b6151448a5185185100d100740c585001505541e02406104001e218440c0c815958840c00c0000c4056580292580d4641501d501c2000007281014821240b2a250b15251041d20201a0302e410400f0f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 197614514 1250 197613264 197613293
    0x3010b03071a0f04240806060f0d0209061306110c15030604181209050f0a080c090a020712050306040f060e0c070f020406060203040503101107150b09010611010b0d0b04 74
    0xb10f00302004001650506482c1c01e00320803900c0d0502d460079080e034810040034040050003262080c50240700c43e100c08001902202c0304190440030060f0340f00d4903070012400314040c2c02000c0da0740d0701d00084d0000e1203e401600741500d90f001c0d072080d501902c0b1900c0420442c290641904201c09a0a100180080c105a44200c0c4021580104185480d05542c1c03006842aa0b50040c60001503640504000c50300349111003040000301261502110750038480155074400d80b840500e441000d200c00420341000b02c5604075800986c0011f0105d14101002d0303809062544107480c55030046107002d6100601e104a40b140a060b11075000c02002d03140c0380c40ca8090a150421902030303070000481d601e244016a1548103520080c6034035005162501e04d070104040c2841384180044412a05101c0d00d001d068074020111005180e000405100c1000c5410052000303210081032150401d00480001c1031803500210041d600c031601c00700038040c02d0945428005180710007480200049500b001160005500c001242103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 197615764 1250 197614514 197614537
    0x50114090a0b0d0e0319030c18081509010207050a02061305130605030f0d0906050d02040b03090601031707030e0d050309061204020406050f1f03020405150903010b03071a 75
    0x822508030300150340c8045690003250725001c00140120690b000307005075403108a480003d076007040807007078400c12150b20b44900074080603640e1400140080c011070100c9070b8501d100700380d01048d03622010510b0b52014600041416400040c1c0040d039900014001c13141c0d01036014014080300c804942c2400030b0344c1c00110000e2201da00003040842c0645401c007c0560100e0111030108601c0d1500050600348036005034101450b4001c2079281183c0e40e0807801d80d108030341540c40d146a41c0e4030643c030843d00a0089030020040c44200000340b03c0104000981281601c1c09140500c00c008402c01030141c0520031104028081030085203594058a040054a6103450044059031316005045000400c036901c50010640214032400911066007084d1103410054181075445082450300c0800186450910410004034003114208080c2500e202c2c0d0151070090a025040502421903d07600e010290030a5a00c14041d41c82c1c803a00329428600000c41c030089440001d40d072040103803014030381c03a4560b00404141c034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 197617014 1250 197615764 197615767
    0x5090c2106040b04020c060f071404140112050112050f031306080c0903030304030917010606051902151501120b0901120f0503031e06010f1e090314061008010501030c050114 76
    0x40f480d03e482c0005c021118654010340364500d06a6207800080b240505000c080141842950440c3c07118001154261030f041e12200c0d1030384414200403140c0d0202d035058042c1c910b00301000010403884140041c00c44603c07410644041c420a07101c0d4039500d020309240c24510b845190b20411030140a1401243c012461500c1e1070300d081c141e000030924640c42900c08070001480d49500b000250703254119181c81c18005402400385510b007150052040c010041900c0640d0501030200c20058000c00000d00392201980b20440140307001d03003515601255455405001c20619415522800d5451090b00c002c03190081180710180d00f4030622200c0d40700f81880480c1c01d03112802030200812000c20140d48a2841d901001c42500c620000e82d0403481c07009080310b814424056443d101c81c1d90000c2c2000c40758032020800213144002224200c48404c03059202400038140411003058100011a1051180ca050280c2030501070351020ac0a089640c00d202c085c0440b0740c00b9400340820f40c4114071112500001d4140c03d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 197618264 1250 197617014 197617031
    0xd0503040902070c080607020f0c040b0f03070f150c05120705071e03030905031b0f0a17010207050708060403080402010507081b10200403110a081605090c210604 71
    0x24000c0781d22495050703038807501380b50080040690801c8000c5d48440d4601c05803107102d9101c01d041c1d59911075072021910032078450303450071000e484034400716102c1e0703000a00f259144c0da50b68880c00707260076032806050007010189080b0303140b09001d407201c078100541c803400030044451403a02e050440e4001020171503007030080540002c5e037000f40d001c007001040340c01040c2072903061662401a180d4500c81c1d000500942100350010302c0389413004290324520b50191200b034030ba081070300c0c0000c2d2a20419081840d11807108a01061403020540c043c242c0c0a1192045071540b0791078400351a9100d00440d401030004190070000f8005501c00c0d809820f109204043e054100901d1039805820f007408000503810941c0004504090003403180603494200d00000080070030880341101d124003e20990001400c41c000c440000036440d1180f003a280002c00b0560261030084120000840740e4170000c2c4100c601c21030700c11010890181c0c10504841d42240304c02400260b90031a111403028940c4001c010952150703490110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 197619514 1250 197618264 197618279
    0xe06010c050312100509010305030a0c03020304050307030606090e15011a120f190e101104030b040f1718010e0307170109030206130c052b080304052a0d050304 70
    0x140414a005601040007440d00d4104242d008004d82c0c0214440c00c0290010004a2000710403103007010b00320328041d48011036a0906070319600c19a80256014410014004180f04841d40000e0035a1036214003440780c40200c00010390f0b10079082c16445189801c140c010492001c0d00c0c00040a013090382c0342e9490400e400d05c514041c44180480d80e20030800807175801c10012004480350740f48440b101201c204038034030040f18050360311101daa900202d803650310a0700e601503254400c00d6400075903116034009000d15044c40d19030804022060111512442c050051404403071040988140308080c1d0709906100c1d801000441707410540c10341260f094001c070742d00400c081c154200d138940010341c840300108a4140c94500286031410082c2000b1450000012050016101c01500801c403070046920108210445070f061400601c10b10351101903500d100c8119003048420005984140d020740182c1d0700648035040940d80440141010f0141c40d40306015800040c600a00c2c8600054003880459003401e40381c0f0b40c0f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 197620764 1250 197619514 197619517
    0x503042105061006110d0801051002010e1b0a06021b04090f05011b180e0c0307050c06070903020a08030a0c0b0901090611041707060807031a22050703060506040e06010c0503 76
    0x14001c1c1843e041200030b2044580052000e0980c201d00742c028a50a100118010a6403006000350782c0704600e4040c4080c2807901c02d400425180b40c0400030f840c8245040f51140744070400c038448440c0035030710101c000209540089651075117844160080c071505444141048004c0481070421601000b5003c0c234200031401c24404c078103142004003400031100c0b015a4001d070001021001e00203114081100c10310200e104d5054898108000940e0355450b600d0f002c100ba01c450081050048180c881c0c10f007000b045c81e500021040860b0300994040c00810b407680c600a40b68801c00a0301008034000c9548840003490801d1030651020104000040c0c2e00d590340d44107412760b40a404120207031900450305012400304086031090f122094002013440368603082000d80041030081882d4181940c540380f10030f210071641005c15010340c00420103405103844007240c06981a11105d6802494501000504500d00074403419058030b0000301050300782441d0001c81c243c4408006e10203410010205c030303140c1c0012420070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 197622014 1250 197620764 197620771
    0x207060c0f0909060f050d0303060503120703090b0c0307140313180c081b0306040605060c010507030606050a09140402040b0c07080f06060109060f0207030803180c060403050304210506 81
    0x50340d031107001101100c010582400c5401001c0c020b40b03480b50410070555030102c0c1c0c070101c820940b02c00340701c0802070600f0f0340213016585c0a41c0c1c050258042070142c040040c401040c039980309403070700d034209601c6003290742480c001c0c000c141010750700070403031400440d40ba118141000c0c8a044200c91500400201e00c803400801548050b036010b00f8824103100803212401410342003601c51078402c00c00d00e060014404005135030b208500f080b81c2c001010915503220303608205d002d001c000d4025550f51080100843c000c0a00b1561103002071720744074011984900c100129900c006081e580c50545506003203071003074000701141e03085910076070800c80003641014213000b402c44000803030050555540390044040c1041c0005102d221581c110b4000c01400b607800206005c00e0307a541d0301d0421450f25446405914000701c81d00040c0605902204200c5819004d1005505900c0698266880c0c0c1481c2410301100740030f03502000704281c000344420b1142005081d004a02c40d5a500a4600440159200c840c101041074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 197623264 1250 197622014 197622017
    0x12010f060f08070b0703022109060a050306100306030221150c04170309150a050c0a110a05061608031b040e06090609041203051906090605030f0706080114040207060c 73
    0x402044621024043c6000030810b0200c6203281c200d2030382c0d000752a52028048200300b01510580ca541c1d01c06400203075010940094202d07a40d40704107210142154000305c070014820781d0b2a1140000c914464020310f4200d0740d020b0710b55819280e0060b020446002f10340c000c0300c01e5115500c2c414200c01c6522240038050b500350583e41e5917a40c10302c1c3c1c00b400301040d80c600300c4060742e000b040f41040940303650845000b83ca64000045840344680e14044515100300d00d06800346109441202c0284441d405207120804002c40d5100600d603914002c3c807100e80541e42411841c12501c05a080100f00c5103c0210b83c80300c0f80d6101400c001c00b00c6500c059194000781c02a40708515180c0c100100c9040c00d020b51600510200ca0600861400d913542c01c2e114036070000b88070b0070942c850380843d11154204003d055010010f010030701c00d581d122000c1400400745445040d01c00d10030410030350b60190000c10002e0a9440740d85c2c03094400e86c00d100e40030149000e046109030b0801e508000400c0071030b126224412160949 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 197624514 1250 197623264 197623289
    0x80c18150702031c0c020d02040608010c03150909021509011404030f150203040f0204150512010203100b0909011710020f030f060103230c0706020301030f03030e010203010e0612010f06 81
    0x22801454a403010031003504d01c80341005898240c4003030b084600119550703812640c0446815140c4046409000146e200f110b084d820305440d0302c1956010b4100d4090395184900c0405031a6a681c000c80070380d0301090010390016640300c400c203d0304242e500101030b041c0041c144448003520100001c4000d910517401500d40c0c160403006002005808080410301400214056045003425110360403032038070070400207100710394540b884014445043e0703000c0020440149103000d032000403049203010390310449044860030450b03280031610304403500585101e8a00030b07107030744150707801c1c40301c40c06000040041402c120311030070100c030003130300d0b440d00041403a060007c0425032282070640303a0b500c4c10704024003554141402c220460700b0066641e40c030b00b0300d5442200046e090540300c000d082c550b10300c540703207024100600000c004030a211066407880e0807140310359000c000500c050b540681c01c074002070181120810004000c10f030b00c1e107042c6000707100c190f02c3d0100000d5455038103101441100e8469021207100325a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 197625764 1250 197624514 197624527
    0x111011506120e07180504050c130b090105040c170403020102071b05010813050d0e0d05010c08061e06090111031c0506011103071119080a03080f011203080c1815 71
    0x56030140c032103480f8801d0002c0c0b8004d401d00380d170240f20310700410310014000c2c1d80d03078002420f11900b00000020800040c00300740080c42c3c03c501803405440d9205c0c0180c0100b801600009a9081900c1071105034945c0b40e9688d581031000c005444410751000d04180e0456409000c6200802e045011005078091004443d414440c030300780c00940354a50040c0403200f404e24111805d4003090011034a2842c030902407a1a002021100b00028403c0c00c0401020381150720303203402030044981000700140640f404858101c80c0c81030284026049040d407900e00ca4000c242444114050b5000f80c4007804d02e20041ca050702d0810180200b448820044020045044ad4941c3e0600075256040962100540d07a070380c000e5440e10701251640058020410b40c0e0300e00541c0c24200340340300429240c240002400790003042d103425104c1e504008140d000d0036149020240c1c25040009181520764502c802c6450389a1103502d030330382e00c158101103035402043c12a2040d041c00002c9903403e945081d01f1b403110172044e03035200b601c0d41c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 197627014 1250 197625764 197625797
    0x16030e011412150126061309020f2119030306081f050402060702120a1502071a07051303060212010605091e0a21050114070221070c060c03110c06090111011506 70
    0x503018880e01c1f1040303160141c4613000da1540117094083c22000c1d5940902980c1c0c5807660704511034825001026405200b80201c40f000c50000d541110311b001c0e64080c0300c09a1145a5280c40710118000c500c00881001105406500e10340c105960250005000074206000354000c141c0d242e841c0300340d040c959044600003208000d444182c0044900706c0d50811402c0c0038150f41c840c40001c00702010000c090351814000340ca400c2c421030440c0d100e600300c3c400302c4d0a526a646403882c082c0d0031002d007110074540d0740c200110f411031082c0300742d81c854180200b013107402c2030044400c07800d0b0035000c0c1c041035000403003904d02050410800036049009a203001812544110b6410480c2c00c5a03001e5480e007000800c45070a111044e9400200c81d80d0148040410720b907011164084490944101c140040041c5203200000a5454005402e410028001d40381c10a500e15000c1c05e2030b40320100c802240e0b03480351741405411065482602d9076000344030020000a03810700002050007070403105520076400503040582d1031043e0f4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 197628264 1250 197627014 197627029
    0x1e0106060909200c0f06012c0405030c12040306050610080a02180307080c0109170d0f03140a0c021c05160c091103100e0402060a0c060216030e01141215012606 70
    0x1881d031a80f040d00240c082c00c1d418818107144c00c8c90440d052104da40402c041c0712060040711112031140b17045900700d0503012101581a000352000740e41c928940380000e04075081442c515100b000741a41d500c10075584050300c0300c0c002d401020841c1c4002c030440c00100c525407010001c51000c5c08200c401855142510000144145101c0d040721030783c00c0704c07a9428608a82c1c0081c591a40441d030b810610300e10712085200301c4c002d2020480c5503900e04e40e240709000301201c09070300c40314a14549071709888091210003d84490800d085050100180c0e040081c840c40616000405110750302c00c0e1001d00020360340e0501d55083d1100721500002260700001031103010702c8108400341c01044100003242451a054000620031b01031445020103100303001c1c088204000c219812a102c1c0c0810703940713a660a0300d190600800701340404a200780030a1204403081e44944916050b281c2071500c1d01c1c40c0207c282d55501e030a0303080915500030f40d07050280081121100b038580483c040c6d18090801d5100c10709180103010001203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 197629514 1250 197628264 197628269
    0xd0c0c0807062f040303031805070e0c0c010608030d0e0a0f08091c030207050301050601020703050703120c12111207150b060d0204081e0106060909200c0f0601 70
    0x2400115646140010a10400d40700311582003800000e29140700c84154607120f220900c0803102c042e1154926143d181d0f06000361060300e00a550400c040601d40311503115141c0c80400140082d403000c00c04000001601007559400711100c80c0043c10003e80700355013800e441c01c6411000340c68002056040500c0325500c00d01d1140c064510041c144460031b500d440040160400016045110014003030302aa124459080815100d4a01c0d8181e000340a00b1700070b45500c1c040c000d452280d402c120104685610005140381a00c0d007190242c45640c0ca141e40d0907014441c149202014880004103200216680b209400f0a8494541300c00071030325909018182442681800c0e1480d40c207080c4020000b14003000c4036840e9540c608240001c2e4200d00c01c00094080c01440200c00c591400020081403605000c0b0b46084550010100101c81494086401e400d03590980135480c00610007580070000c058264012500c11000d50b0780380701824441d401402542d80c8104088a220350040740480410300703042001a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 197630764 1250 197629514 197629517
    0x304022404050418120c02130b06091c0209060609060a05092106040506160819060305010c2703020d0201080a0b030601030309030213050c031801110711091b0706020328020d0c 77
    0x1341b070010307400109020b10170703100f0460591759144400d88c0798454404840b04564004c001c041d840110007181d41c0524210078080340159500c401240c46400c0034015200e0303481c0000c020500385540e00301e00311b40c140c0280305115440607140b080108940a181842c44d00004c00c000038240d02e00c1e203801d04924060024120040b0510f00c18a84004680e010003420307081400c3d40b03202401040b0005d442c0003e03010300e800150080d483d041c500d0f169035401006c190140090440c0c606000b06848440302480a803912010790043d00c0144020015842036880750b520160f44000000e9640940000c2072600c03009070000c030301080e0303c4c220510035407a14840d1403003000d091000034001032504c4980b15846010113000611024111890000300d26401e4120110111061241c90707103800e11070410002501d00c89001c2405114520041607400d28850156202d46511415440c50803242d9520000207520051000b4051180f20034103105105040d003180740c032034480e158050b03204e81032066128200d42d0020100350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 197632014 1250 197630764 197630777
    0x4120506010b0c03030114030307140d0e030c03150601090306020307030203040b0a050402011d0102030c030f1b0f120711030105090607080105182e090e070902030402240405041812 79
    0x1a815001013140c6c1510840e20690b0200201d4a000c03d2075409640401040150582c2211903214000200c1c41c1840200b239584245160078141410703241c034000080d141c1c254005001c0040220720101040d500f05406140c146c10141d9240c8a01d400c90300141c1e8820300007a000401d001c10301c0034040701e8a41010b01c85078200482c2c201a80003800c007050004000949070361071110003000342c0c001e0081e80d100da0603035020f0342d41d50320606038005e40c15400b4003000c075404104500428440940080d00c0010401c04500400d000031086001042c0d540103200c04a84000c1089800303c4191020300402d400758501c10028919420007003000703031550340140c02160203100400d03032015130f00d04034144107a0851911004080c1510412102103074a0040e80312002e140070f840c10000840d070150758082c245020300700056406107500d903107080060b440262400b035030000e844071050303043c01403140a032102c480c8083e144c145015a0360011500760380080d080040c285c1c2c00e00b03070100d090100d003646450b0b0310380d2186083c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 197633264 1250 197632014 197632027
    0xf0c11010c0822090225080d0606031409030316080a18050d1413030303090f020a03030203070507150503040311010e0106091505030106060c030507050c030a080a0f0f09090b03030f04120506010b 85
    0x8441d000034560440c10881806c4400b205004044003141c0c412012450207001541d00c8010113000707010004040b031011068080014031130701010050780d0003030080c40312400700030001810403521240050300c1740d06c0c070a07030707486c0e03800036883c0043d40107070b240d500c150003910710340d0340e1200081c00e001482c030000d541d51ba00821041c880181c081c8500130076a80e041c2800180e400950601c1c02c14107503541002074200000178404001d041c4c0000240203a24841d404842c40c281d140c100350703280040d0010b01c61010cc0c4081c40442e000a0040c6010b1500300c05582c00058604400c050150030744406510190f04541e582c0741890010b06a49158005000c0a4000788103113880e0183c0100844030340f0601808004010881c2e0781000f1040c0229050040000c00303ca00030354030340c100050568040c0c8410320200341c28044484100b0f00410213101c081166490725443c1d580b601013810b0203410380402040c5d26000c2040744944041620001d08041c10a031041d03500220788030714102e45003603010703004404518000d0108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 197634514 1250 197633264 197633287
    0xf0307050f0103020a030f05130b0703020909041118010b1b030c0304090b06131503060801090b010e0c0903030310080f150a180203060a0e07060f0c11010c08220902 72
    0x907592070010070b10700180e5411010804034020002d080d08200220708007414803400c03500c140f180444a80c090132a10030b5070b807100813040e003c9100340c0c030314103810010f440700090115040e203100e942c240001502035800c442c18006901c05818090304181040a80840d00309c4243c4110342c104140b11803d10000c0d8506221045540d03680c4c041c40c81a81c40c42e90300c40b96900203c2d04d5030001d8809507410440020f80b001e03122107104c0b50041040000000091a25100042032841405003c143c0c9810002c48241a400c0407002011404001d0503001000001c20031500b40b070b14204010b40c414800074002d4540141003003061030500c8004030000007554004078060414251441d48580c20501e4100005100d10100d18030201100d84ca0602075814000c2104226032184607030042d10903454040e003610405920303280251185a031a1b000d0400203490082e0110018005d910385412104c014140310410b0300b09a5a2106660301c8440d240307011502e50b025054000c03018505200c003030000c0301015420440103415 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 197635764 1250 197634514 197634529
    0x20a090909050111030a0c1b0206030a0b03070f0806040b010f05090106120b040903081608070f0305150603190c09060e061e041d010927081201140f030705 68
    0x245001180d40d01e849800b04402548540000580c45000c00d0310f9207068942170740208000c0d500540800c0140303840048021111074248811a4003c054504584130680c0d401c00a010100c01c86400d480f07001000f041001c0341410b000000c00c0c000b0010300140c0b815251541840d001a805071150901c0e0300e01c2807266a07640400d05055030242e2070b2008200a016645402030031214121035007044c0b134244800103040e4400079580c4035040100191010f10207401c42241c05805c00c07276100300011444400e2800d65480303500402c1d04a0380711101241c0d164150400100c556005a40c0d5070055050101d105406911600840c0f11851341d6060840c5440d26210b4068840c85075000303590b1284070000303404a1899a81c518402c80c3c1500480829261504ca00d00003a000748a41d045c400805440c0d0b000080c241070341c2c024100042801c80707104034100c244100f41c1000da02d071151f0880c0e081106100d084c004000704a44c04d4001c03d40102c07403d8031a1400800d106540a641c404d02c0d010b500130010910441d00c9401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 197637014 1250 197635764 197635769
    0x13020c0a1407030b0115020f28050109050123010e040c030222290f300a080d060e1b0313060212070f18030b0601110a050601080d03020a09 61
    0x81100c0e02a46201c1c240c1424007100341c00c020301590944002150822001030b00448241181d002c690b040101e451006907900c6402803c110280060144041d0b6201000c41c9003d00c1c51040d400402c20341c400303680c4c071405c0d1a4000c03c911502444034103001d070460740e40400b240c0100014a01e110903401d09484401400d0b8007400080c1c01000f58031038900e2200f080c1542c4804d40b210700d1000f044a280302007a072559040c8001143c0022141400b884209854003100c480681c0742c0042c0b410b2501031106140c0c7c41ca401e440000f081070111001003440300400c06001c0140320034418101903554240c011004011154075400c00f01d040548041040000c1180c140303401c0008210814a40d00d0303035584070500c8903820091000900340340c004039440c4030004a8585250007403050703403502c5001e01944002141c0c007041c02e401002c40460318840400100d507030714210a80210741803400144002c40564003d103450700c4404115840d50000c401000b020400307002149083e21035240c04d500e008a0014024040b00690 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 197638264 1250 197637014 197637023
    0x180806060405180f0c130b0f041109090705270d020904061518050129090301110309030d05070806060702012d09060306080109081c09050102030c0913020c0a 69
    0x20000f00d030b481d5400c45410701442440758110355040296007922030301c1d003150507201d50188041c48014403031003c4602a40c21240b10140400c04409920010000588100b07190307410300318001c00c4030421035158020790f80c3c40f031010741d142c569130384000c0c1600300c00d41e03482501ca00c50420746d028054011680c03520454280142c04490100d55074486060003001090342a1580d00f1001803884006940b442008192146000c4040100302c0c90ba600c400f01c441404042880d40f103210202c48561614500c0c9002500c4183d8025000240b0300d040c03d4019034003503000341c039560404c0d131004c24900661141341c01119403102c16840d00e18a43e003007040100e01540103288009040c001e801c1d1034000384882441c0c0d00d41c00b6080d01c409002d40c2900c04c00c0b001c0e240707003881d0081000090070032802107580d45050056450040d88001c07a60f24000152030720200c10f000100d652589a51600c40e00720104000340069401404400050b070754030440c610410005803000247d94189600600c11901e042c0030202e00401400e030003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 197639514 1250 197638264 197638271
    0x91401091505120a02030c0a060c080715020403084603090b040804030201180b070803220b060f01030b0a060c050f010c08101d0612070e0a0203071808060604 69
    0x16415100c2100110b41150340c02540b404800407060b680090030121813030080d420396810390307280c009010100c005030051a010802003d940c40001700030100070302603680602e80d5001c9030700704608580140e82c0b00e81d10946a04002146000701c00d12020003007441e089000e140c039070003d503851001e42c590340706410120030700500074603a05403901e0198102074030303440d4800105e61651600c1d140c81e000c65007090205030300064080756244070300c0c038900441c02d0030b0310b05107a8028100704660b50b4840550780014044041c80350f60f500120403c00742c1c1c1c40c180c500e15100d1007105146150140a00500c400407c0b10305040604101130071109460340c811103015a02d991400c0a000384090400c00c0ca410101c1c0012083c40d80f0b01130071041c5031640004103e00070200c0c5071400074429a200001c140320b01e02e600c01710441a040101140d6141342c9008204a0100c4110684407220b540c0c00d101c0040000c102c1d660000541c00004001c42c140d0b01c40440015507013960080612982402480c684c1d40318000c00b064042d954 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 197640764 1250 197639514 197639531
    0x30e040608070f03050d050f180d02120106090b01020c0f060304020a03020d060b040501060f05191107060908010b120703060207080f0415390804031a04030909140109 73
    0x486400200c0a054804200e6410715900e03610a91079008078441566a402100056100304c0d100d00119818076800e07214590030442c100c50442030f640171500403580d0200b400e000c030300016122590902002480e070000010424a0030120106456403002e659045420081e0790020700e50b2140c1e1214a5410103580445e00d0765500c1c8003140034140b40390006540312000c03403000c10400100781c0004d006c500081d03805000590780c0324820b8414022001d80400410410302c20103c0c40c00c15200021080f00c55842e0001411013241e05d4a424603203a50480300000d542490140042c0100340180c91356004161210000f906062030816100c0c1480e000040586400040f2502484803080a43d940c900c0b11038200743c0d58aa42c0c61442050440c0910341c103021410482851203001010803d00c07091226860080742c94141e1541101c00c404480a07044030307a00d9040c0004000320700800303060011a01c1405803070500741014103001c0c00c0c000d410390149540303605080d81a950081110cc0003070440b0140100441c1350720 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 197642014 1250 197640764 197640769
    0xe090108010c05070b15040204032315241e01020f1c110c030102040f08060708010311060c0322030b1308040501050c0f100203100b03010f0e071e020c1201020c0703030e 74
    0x1606c00700c60740e00a0021401206025030b40c4010345152428444100d107038000e07501c40e03a44074100c81e92041c1000c424200000c3c201c000c0018480054004640c21116440303101c40022007070001c01003126020f0600302c2c03d500345543c04010a04081d40303084010310000c44044114042c00c00c489600c00b0420891300e404010207d070810046200b4103004000350344554603050402a154070078072401c0030a00c0342501162505003c2c11403641a07a4200c0c16400c045d0362620180074265000040e05c0a880c8030400448010f912032038103003a44100074010881b055032941c00d1140c0090b0000e0b04040746018001c1d48800059004004c8404444007820300365103c4a800c2000c42c1001003404040b02c160207510fa022190504a60046206003450b480c6206440c1d2654840e14940c0005d00400700c03881c0b0084400e1004021400d100c0d03920140610702000080000d401c1e5a072400c0c40c2e1030030140560f01100b020000b501d4104900c00018410704001c6081686030800d5075a1600180f1000c0c0500c07180c07040b80c0c0303a00d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 197643264 1250 197642014 197642041
    0x40605060d09021215040605070503040c2102040509100c020607171e040b0f0a02040f090f020712020a151a120115080601051003090f06050a0603060c0e090108010c05070b 75
    0x250003240540c0d00300004622110700b43d44041b00c00300d94031841c1c600003411460040c000c0da402a80c0201c032001520303081c1680316000184403201014400b030510885801031340d45000d40c82c440e10080015003984280401680196015500d040c0195085401000b4445602040310840b94103c3c04003000c1a80743c0d01c0112000c070ba01c0900412611303801000b04814000d28850a07409440031842c2040701d6500c94030750208134000c50080004500040c075080050345002e41002e080408060340052a00790666a1021144040701024000d80c00ca002207a0038407083c1000001d0700d61003110280180c51020700c1d1800c1d4060143d1040c1c0c481d2800e0103a420010a013588800c503003110019007105442d8031560000e6880030244078192140b05032800951210348680074070100c00e40c2c0024440941c00c500c0d96000050000103100513001030f50742c032002020404a000d0343c071000d00562240700d071002002003030052006050b0000f0940e80c3c102808004000d62000403188000d0700011501403541710b02c900c4400300c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 197644514 1250 197643264 197643289
    0x3020409030804030f0207051503060a081c03060f18020c15090f060c1e03070e0d060501050909010e0d050a1710060f0810030305071113020408010605040605060d0902 73
    0x1080c40c1031100020140c00c0819540910b009444d480d0300d8180c868403c9a49802130700901c0d4004034083c0c111001512018051074100d140101120704c65621500600d141034071100c000050f050100e84010300c0543c0512400340074161604010346200e09114401d0b51620380303800314407030250780004c101c880340302d05201c2507021542c000c0600501c0e0070001602e0f560b990f0717507a13490f10040c0100e002003048014828121207880c252503c298150125020500c0c025410041c008030511000700342083c071a540708000701545600c12440003c0e00e50618046c01041d0310300401080050303160840083e0194400a440c1d40c000d09207107486962010300b030708200e601c80080d20300034080380042c2c018488501c00603080c01c070503118913a4400f94508680f0340212400b00066900c800402c030906000d101080c8180010f02907e4015008000e6420001d00491840314515a49010140d404142480175031028083c120007080220341c148502810003001652901c81d611014000c02e584454107800c5441f030f180c0c40c43c0c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 197645764 1250 197644514 197644519
    0x4090231060312141209010506010306060305040b070c0c080d03051006020d0206060f040b1801090b0603161202040b0307091e05010509061809011202012a120210020d090b0c0403020904110a0302 85
    0x126410100003987c06028140c50660200b800c0075000701e0000d11a00c0356520640e0410707411841c9450302041501d00400c0200180e40441d44e43d000481d00140420403011003001301d9500207a0b070b142240f05246601882d410001c2103411000c005095940d0015016030040c10440d4240003501c281c0740020010a050f02c94550002f00110740000f403246880b4041d4100c0d809114240241d140107010070600e48409c0300c05e40035034080d1003884119644607501e110340340e0b454440018074240e10b810111046400c02c80e000f200103840f031700b4280000141c211440e0044041c00c0c81c40840542010006810f90255481c414050b0f14003259a1100900c0002e4801c40e040025081440ca946c4a0742c10841415201006a004c161036042c3c0740354500300340c41c0280d80070b011092070f00e0001110f9074600c0c2e80c0c455074101850440c03050311a02c2c9240500c910080a100c0f8400f400040c0f030b01303554a8141100807000b0b0900360310071400d210400140c0c54160010780c1c469448440c030017100200c44001404500b070303900040d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 197647014 1250 197645764 197645797
    0x70f0e0d05030705010f060e01060305040f08040e1501020d0e0d210512060a0302010903082d0a020601090c0f05131509030b06090c16020409023106031214 68
    0x805000022005002d500d01400086c4000d5841c03d0f0170307030103940940c49040000340022004018140c400d074071182e0014481c840400b060000c0c2d403a440e145400c01c2c0c118030001c400c10400e0002e90703107403c00581c400c00828005055407036001003025044c0000c050702140140201c0000703104001c01c5482c0d0500b50558402851601900e2610042550f0410604503e0000100000c60081d140003100c807403c07254169100400942941d5072140c144d004483c0c0204060903081c080301811210520484040d949283c040d9260b1030603110080c944201a0b00030311046181a00300301c9129482080c9100440b82c40c180340385d450300c81203080c0151003c2e43e4007010016070181e43d80f011b200d0b44041e401084074000da15010f560703140c040401a11000030380301960b03124420000103c0400813000702c0c5610340d00040c000a140042034010500301003070203140c0d01280c3c036100d5200300c0700c6041051035003180061f40e6007004480c1c2560350b1010100d08000382c0905010540072841c4007800e000c02240c07411055024141c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 197648264 1250 197647014 197647039
    0xf01020d050702060a0e0d12020c1b01181a07140f100c18030605100803120f010611060417090613360e0c060a020304090c0c0209070f0e 60
    0x20007058140c0d080300c018000c1001040780e028030f6009041c0d206010b48007038040040128800d903825002d400d50a1059602444504d5401d081840326013010700450401110383d150110004252a0790304199206000c203403401808420036004014500d008101c0d038550341c07410301c2d0070030620f03400c190f801d0b0b1081d901c1010070510b0024808100c00164180b8040144482e40f41e030042a10610071184403c20360140104040021506903081075030003c3c90107c520308e5150704c81c2d1a150070b642c00540030150f90091141885000c0c80f107000401d005002a00d40182d0718544c80315103646562000e000035180c0402803c2071070782d0034000c00841d40da50100401865841c061030f031145042d0440341c859490101c0002d41b810800000351003101098007003821100e00580c08140110005000c49101c5408901c80c2e14512010380c0c903404014005015160000d503241c600e4460010f09031035100b0b401c0400c00c1200310070480141c40c4c2184094010180c0d003000560a01c2c91101200d03651840c1c520305a10841d43c0c800f6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 197649514 1250 197648264 197648287
    0xb01052b1b060c050d031413080f041e0915120201120501060c06050106030c020709150b0301030b240f060705160f03060b030604080a0f03090206030a1a010e06090f030f0102 76
    0x1020b144500c111309946042c20066400c2c1c2c1240d00c400750680351000c448000819003d000c5030101200352040d1112428220700101010898100f908080043c0d03ca45c03001c0d491081c8401000d00080413424418080ca00b90041c01c14414000303481104c28800e00c0c00082411a8015403020140443c054800c02c065030351960300508400c201c002c1500c64500c2d101c0041040c912038001e0b0102c814140d00104140b610f0704030340100500040120007e1458810340c04540c403500c00b00194000c5010b28803003031150825400c0022251040b021030244960009540c0300e1076110242c403481642c0c0708668454076903d00741016400e00ca054520504100c500e00e5002ca031206d092900b42d000d0b01d010707540412101e016202071607900c15060307802411a020610244101c1072180e911035840605610380812005000d60105101d5041640d41800e000d4656080f5200303035960088402d245042481c090400515030008240701c1e10aa641c4140a400100c200200e40d4404102c1c5008101203040215524500c01c4030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 197650764 1250 197649514 197649527
    0x608030304080306010824011b0c090509070e07170c1605030c16080717070f06020307030f080402220212040c0509090d0504290a03090b01052b1b06 65
    0x48180c0440d4002000c541d0b19910005070700801087c8646031a420540200159800507900150303406000d085d001030760005040b020804010180c40340049454100039000c07e00f0070146403c41c0001c03c20920412554039840301c00303400002285240042c1c01c1d10b0300951052540302c1c0010321103c9c0e0b0800074009040181c00001030288221031815034000c0201489803a50704500c5118030305803a40142024010b84180b00f0309031a182c030f480340c2220441030f580d03030003a41605043d40c4000c1c0541c0002c6902410300d030300303c1224650345a4500d0905014035140d07000030f00c0a015a5071070480c0e203101007800821801d05a045942c00315000410158610705460468094101402064083c0c110078004c2016014005401551034510b9242d89040500b0102205002400e0f0907001030303000d80380c001c01100b2a0545004018000003550042041c2078281000ca000240603409180100081013880120100100e000c412001162207400c1504a45041c00248003c2d04412890a42e205e0040003601ca5002003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 197652014 1250 197650764 197650771
    0x50408150619030b04060c0e10050316050909041103030c0a0c050f040204120b07020a02060703020d17090d2609060901060905040f03030902130f0e060c0702010504030b070306080303040803 83
    0x165550440002c02c16108203200c0c07140b0004058601210120b00050441d03007201080445610303211312143c0d076100008506658460044020503c00000d010b0651181c9100a040b01c0a0f410300501d41050f420202c3c915840050025007002e442c140c403014943e50920031101254040d5003184c100c6003403424a42c595036064840c2502c80d4440c5c40d0b421340c041c1098000d60b000c40380300c403104440080340c2c1d031034110440074001c04d01e0046001d0b05541400690743c079005071880c607001c4e42c02070500100c0c0b41c9010703101003e0340486030355481e0000100101703050002a0061180c00030b02e001e400403108110701341ca080124604262441060a01f00018440000781580c42008004021311503140e4030010307541121815980907051598921050780400e000c2c2c0c010030501c40c40504000f0359924000140000c680710400c4650398561280d8121720303054030400c007164000c61141100342c40c0806950000c0c144d4405d6100040010000000254110b0300a0740300c400140f060005a07603503441d041c0307416060b40e0703c00c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 197653264 1250 197652014 197652019
    0x60507110c030d05120c0415110c0411040501050a030209030106062a0206030f0402120105190b01050301080a060c1101090602030402130209090f130602070c06200607030b010504081506 81
    0x868035101500e400180400c483c1d900381c48492510800f100b1000710814000d1241107a910100000100d01d0105803055014407500d654407040d0b8a003c00505080202c8820494495400c15600c0e4448110100844d0b084a00900b04540c0e605c1e0061419800b0b8050a603101741d15500c0e0203400104141c201d02121841066003003040c0700ba59140c3c41c00703001501c4c0d41c0300280d00924240f00107403150240e52a19900640014454800b00100c121120f00759181125a141c4202c10340450040101403405164a50320f400d080003400d41d814a00c0c0f2594982c0844005403400391900400116a4011044c000725414045c00910038410142403010180d4800d440c200e0064044550040003428148251030300f45000030310f584041c0d2220f507200c4881400186c2400002f10520311110300090a6200502540e07104a0720480131528098010b0700d9044400c586541ca0080b10001a500120210745258080c003a41030002e510350083c0b0048446000395049030003948190b0340c0c940640c101d1840401c2c40359004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 197654514 1250 197653264 197653273
    0x10207060503070c02010309110402070c050a050307050d022103030a0903021204050f04050402060d091505070c0b0103062406021b0604080d12020904020a050304030e040b0d0305030a060306050711 86
    0x200c58080710341e480202c45400000e00204c5400005620030b0b00b0039241940507540d001a98500c4030001070882c0d0082c0030071100d00791080e40401843c100703104240014101200544040ca291401180a082c0c0030034009104542151400345080006407442c40c9910b000400c40351645048071240c001000341c2d0740190054070818421030480541001143c081e6000602642a902ca94005101c09000d01030000c903808101880800380003080780c03089540b2130b07010380b524503030100b03281c20200100c0300041c044004001d0310a05020100c0c05a40b6064116607100d0320014099136410300c506460b901458500c1000248040000740650380001c40b605c810b10f110901a007404118130802465125500c900d400c20b41150141d9440b15003c0d941898903442000009131804420100082c120b07130040d4800c42c00f14802006200525a00450011041e901542c0400584100703100082014032481e0b001001c20500000140b0100d181c1c0e0882d40c01544d108405100c2d90806160181a100404180103d507115 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 197655764 1250 197654514 197654519
    0x106030c08060708010509041a040510050a0212010806060901172b0305090f071a0408030f1e07020d0b0c07121e09150509030304120501090b090309030c060a11011406010207 76
    0x24403071500360123117038031501500300c800050292544080d8010000d4403a030050008500003c01280078041c03082c2100c000059959080010107a808101a003100c009070707008808000f4151142240141964041c5407100c94841d80c01401919110010303500c411307070385450100d08030042c2c01c1a08901d80c40586031000d1001d95940d034680c0d580c03030034081d0615010341d00016040000003103041c00c4401000a803034169140a407078400107880d50b031000440c0c2c00c601c00002400009100300c4011400c00e02640c480303071032412481d6000111011404103000d000711750198081103880225408445140b54004080100011003102c0900305070720110b5044042c1501054014505200d0301194044d120351802c080c104070105003048549800c5030315040e8151008100c0810b46000301903030000c0c2d0714851000032800f2491440c2c12403482002034541c0071964003d2207403003081d613400b15070034885000c151202900c03041404403c40380005100c01d09146e6501e0302050255428100d08110f10030042a000c43d002c2b6035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 197657014 1250 197655764 197655769
    0x70308090a1a12060618060d06030b04210f0c08090a0302130f060b250302030c160915121511180301050609100e0c0d140702010f0e1005090106030c080607080105 71
    0x3c40c11030715900c0c0d1085580c6c40565071130314102920007198404000200742c0d4481d41c0e81a81e81c4030a8805032001c060030269020030001049000b0031146952402d21054590044050550803240900400214011480e190f064450210b640015134008082d4601010690107400c000e102c090020080e29050210100f043c20000003282c080841c10101c005101c00c01c904d603c4480e8188200450071400f007040200da0800c4104491441d003001301a00b1801245400515412142a0400c4080074500040d080202d41080c4003d01100e07904150000030b4445aa040c00c001410032810b101d00049020a20300160615a001c0c40303044070094008110301c0e19000c0070002010b6048600d50524400784105009000b4083c991940001d0031010141c1455030107000c41c03068900001400b03982403520000c100c0c0c0e1990901551082e1071403500d081120030302c3d420100c0d440d4031454401034070f4036441d100428442d08c001d521010007150003000520310329443e0710689450f10000d84203040024103800010540b803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 197658264 1250 197657014 197657017
    0x7030f08010b030c0d110705030f0c06090c010507060c030f020f180a0806190e0d03240311060a020a0611040302090906010803031303020c180a0c020f070308090a1a120606 75
    0x402100c01e204e0708010714044004c02801d1030283c0c0e40c204003018481c51000030350400c00f400701c40100d50b45c45521059807000b201d20b0100300500d403c08a9203da0204583c0740d0300309045405480d040b00c07003c030f80700b2480c0405601610407403500761400b6200055030504c030540780019014014915812130266890041046040c01450242c0030300d642159001c201e505d00d0032060312000c03455540021944003440b216180c20200a112010003182c4c9803905403d01204d00c0329040010380342001e412111904603150420b61080540c80c25004481c0003c610344002d00810800c0d6100d940104103028242c51807400404940041c44201d00402c0c0680c0420384004001c40c48074107070346c040c0c8010b504658039145d11016109800b035040e030550103612100400b6441c0c0d0501d901d9140c070311185010050914550400440e2007401d05c070021900315092171000741d9404114074003103c2e08940803e4560342400006030001c01a0ba2240d481c1800740c08800100040d85006050600310801510b00d02e6030701c15080c0f2005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 197659514 1250 197658264 197658271
    0x18050303030c161703010b0d050906090c010e13050114090603150a02070204060302040c0f1404060e122a0f013b0a032a0513020708090607030f08010b03 67
    0x160405010340800f00b0125201e000e501401401008021040c0ea64a100a54020b80040103400740005c3d41c8214400036004180e00207002d50001c1000780f0b08407a6490b182e5494845080c101b01d041c4602c5040d03a0fa42498010400715100e070104900d5958180e0300c104944221034081c003482c8003400186080c6404200d4030a502200080c000566443c8240e081c020f6100c5401203a00560343d040200260311a40f203045140c00c010b448040007404008005001d00041240030009903408000501c5810351100d200f50240700251155041e00440900041c10102c45402c03004506201100e02c10140d800c01c402401003030826a400012800e441004484200f0b0920401031460003400001c1e8050071052404e6241001c95984448900460340000301480e4050303000b910188855034402560158140d6410300c2420380c007402840a500e80804526800c484120f140310003540407070101c3c01d010035a0103e800c030a00041c090b65582c2c442d8a4094040e0a100000380006480500013051040740c04003202c0c00b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 197660764 1250 197659514 197659531
    0x10509160b0304060f020708040902070b010b0c0d050903150403080711010c05030105090613020d060515041a0a03020705061006080f100b0d32070c0b0c03070c050a031805030303 78
    0x516525900d07103c02501101080612142d07080007100c000c140c8650251001d42b82c01240035070b451800d410090750252060b0042400e20004000c10814a0300018115002003541c2c103266840300c0307100b40001e0400c204d130078071a491000c5240c100000c0590201c0240c2c4a40b909031079a41e03014a90280d1103007250100b0020501242d420001401145031034100e2990240700200a252000940500341e010b90f00186000241f46071034030000d0015141400c0e01d40e0032030380011705990529103018046080c400e5980301e11400d50748001010950548250100c0340020b4000d03040714894100105501c07140071003482890000340070000400c4511080e00d000034041c0c14850b80060700c00d41003601c840d03c2540203c5061011340d80e200300300d00c180c084c00340340340d240d0300d518036600c00001402d000c401807a654020041d4040001c0444201c00003918200f00540020301c0105081c0c50340e8507040203994580c4d4a00c4040d0092040410350020140c0c0300c42885521750340303602000e0200b44d503a000c0c0359803800103540005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 197661870 1106 197660764 197660767
    0x3151a19200a0203030301031b0f0f0302011205100e060102030c07090501030c050d12030902130905010b03160311121903020c031519051512010509160b 67
    0x1c031103664031405000000e9840d40001d44a00c0305000c01400040107140d802d44a0005014400c06440d200c11b00c03461903134503100c4c0e02103001d400c0d20040b40000c841c00c0c0c10141c4d510142c01418001e8170442c044002c01c0c4c0c200100c01d1165800202a41d045110600500115403020071032100103164818000915506604165005030f07130b0368000d1409584c640a03c000090519140103016010f40c0c58001007017805071000071020207850001407000c5080034860300512a040d8009000201c2c00c408807a42004415039803120080e440c031018004d40c15040e01c500039802c0c45503a041a96607091700340c400203142400b0080740c2c0351404101303a0041c0c0c000c1d04201c0d50703404c2c100201072100c031141e0b00c01c2c051131401ca0002140496045c800c8460191a00080340d07100e100c0790b074038542400c1d00070240b090403100210300c603000308000c840190710f80c4109030303040045558644c080010755140c1d1050a = true := by decide +kernel

theorem cover : BRFrame.Cov 197482014 197661870 := by
  have h0 := BRFrame.cov_init 197482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 197482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 197482014 ≤ n) (h2 : n < 197661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
