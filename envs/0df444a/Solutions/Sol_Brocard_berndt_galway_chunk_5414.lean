-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5414
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:47:43.758167+00:00
-- url     : https://prove2.me/submissions/5ad6a6ec-2a09-4125-b2e3-0e9d3871679a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 973561151 ≤ n < 973741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 973562401 1250 973561151 973561201
    0x1a090903090612071e09080d050301120b071107080a05240109020a020a150c090501090f06030f0f140f130b06010c1b0609080601080106150f1407031707090e 69
    0x10b480000744003500801d0a540711000306c0c1c44000103000c0000c4c148001d40c58a030ba1414a00e146503d80415001e8100070010040d041c25001804180081c1c032400185204104110072552826200e106140d00c41414200840703252042e0a203c5129161440d01029062071a44103009d85a2034000a400a503100d100d80c0000c40c047c189900c030015040c480486105420144d000170740000c001000350480b80503130000350500040040402c55546a0340307070314003618103034034020840d500c49004000107081c5c07521035016542d0403c07451644182101000e248120a00c00003c1b99545409051001d0035802d60f4020340000f40c071034005403295000703940060100d0301c28540780030304100d0740c400459122141d41000700050900701c803c1101d032004104950140007500000c101701880c000c9034140701c000d01031040e414040c50303002141c905402689811492040c0f05081c1c0c0d03039881e1510b4010400c8a081d0410440c1c00b4080c80481e040c103100e00e070b00c801a02d480300c8644401d51200c00c40c030800703070403014040006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 973563651 1250 973562401 973562417
    0x3080a06030b04082106060414060705120307090605210c09030f07061404081504080705011401090606180911040f0b0c281209091a09090309061207 65
    0x140300040007900c294016100d068840c0b04014000f10b40c00c0e545c441c1045418881c0d0140a80c0c1c1d900c1d103003294125415850f100d2850580341c40454494050518050454002d0390303140540000300000840c0304241650f19528210b86070382041c2c0c3c06004100359501000604914080080510295990482c000603052828040310000282c907040300f0f042541483e0f040064108410f076048088011518601c4400034101420558070a035038200016082c0300d02c00051012505010010b0215009250403200a20000e11a170303054002d1680284542948a0b10746980010502d200b0003e00041c840d40500449141c1d2401d4140000b40c0084840000500c000700000103d01300c00f4910b41d002440b9244600d03490b15200b000460a01102101c50104501c02001c6842070394400e400440c00154010350516100340c501c3c00488161003560001e044861611903038040001902e14100d41519007151501c25136503c0e600d65540300e0042c0310070280c018070700303101080a4000300c1003c0f5900000a26180384 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 973564901 1250 973563651 973563653
    0x1a03041203060918050d031a0409030e0a06030501030519121101020405100c260f0d1d0a05100e12090d06021611310e1e160503070303080a0603 63
    0x7040f138010000841d404805074107039800300401800302d09121075950070b041001c014203c015240340e4807078036000e5205039a6404108109405040814450403002e00f40555a41d240c28001d0300510f0280001d440707920840500740a1146410314050b107a60b03000001448408e1000010746440800b075039188240e540911020502d901c0e0300201c40c515244a03514255040441c0c2000d1000e00a0f000284152903268082c011500f51450211100c00c030106101c107076214800b1042d43c0007007100c0b002031b02603407142c4042c00c07100c1c180000f0301c160701501036030980c0c8690000000210407506103000121481e003013440c04013042c000c01000780003448005801d0f501131000c1a40c88030100c1c3e100f0400b018040540528010034080310a03143c0f0740c000c10994102110800c162441041e91000a00322a40d0301503000804c107040c0e4031a00a4050036100e00102c0320590030040c072070700c0002420040360182d481442ca040450300a41410b4000316240500903003461821a102100c2e40d14009098501103611110008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 973566151 1250 973564901 973564919
    0x2010804170f0406030f0b0f010c0c0302030a14240c09061201060c0311010b0906060304110d03211b081b030a09030e01020303061305131a101a0304120306 68
    0x400d96040d80884250f03200e003130020107030480f85e80080c5940d40f01d1818900d801941c83c0d0a1002c0604502420002000200d52424454082844e00000e42501405407844204825400c1020080000c9400d480007500c440328404400f00d0034881084030202d00e40c0201b29219012801007450440c007801141c0b500c181d140340d585d003400003a405038001030100194801415402030004401ca004040241700580390203001034034107100039080c03e1040c1c40000c04681001402e860b1b0980080029252440200e06400e01500070781c80c2c00e02070000343d801d491070114000513501c24000d41d00051607203034400d0382040b032040b90a5400240400307480132411160309070b54034440000d18031a11050760041a0b814603071170018590f810500143c0d055501c00d206000143d034440c10b44009159003000b001415680340c0d20200e400a840d00c0d409040c0182c005060203500e400e070f160440c401c6030b03811031b10b2020a03035503d001c1c1818441b00c9040790b03000b030b424000710740010300075905565200400d2401050701d80d2103002039 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 973567401 1250 973566151 973566157
    0xa020f030301080f070602210a0e040912180807090b0109031a0a060e010b0a030915060b0c0106140d0f020a1a030a0c140a0302130b0c060108060a020f070201080417 72
    0x90030650b0300c280c2c2d64004e0b603c0c0801000010b401640f014019502c2d6076016091fa000d02c0a580c004840300c0070a4a0031954810000440b44200003002448080e449003040306c2481d4071140c44000081c0b01940d01d02c400c207546814442160985401400d0b03003403810410900502d401d41c01c04c1c1c10040c21000000100320f0710081c4001d003081014525526080ca60645001c485880d404cc0301c240c401180100300c0000001c0589108100505001c11405c0080c0b50084ea00355906155001007464503c0c0420001c5500c4054103003145000d00030031601d912601c002e04000051590341c1d40c000042114880021b4070144000407151000e425207030b1598903000341c0e014802c0c01852501c4c600d1400b02c00c01c1680720f25800361120b000800e05103030242c003c05180c80c508501c81c00348150140340d00051402c004003081c103040750060241003a0341d502d40030b01070321080c5c44000030721881400303200307a8001c5800b58030030344221102c1c0b956603950390b89425240c1d401500c7c80c100c01001038900f08410386d85400040868802 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 973568651 1250 973567401 973567409
    0x30d0e04200705030301081009030f210609020c0c060705030f160c030605060f0d050624120a0302060709120b06030a12020309031e07031410020c030904050f0405120a020f030301 78
    0x3131600d0750b0520f4105450404480e940028103400d081d0710f0408683c00040c80383c0b00b8030309440c100307516450081da1807907941d01c02500d12030341c00e24004001541140c02d9001d006194000350569049000b52010020300380101030000d06207800400690388442c0b0a038006000d016404078100c103071b15041391035030802d122aa0340300307640761a1100e040101502d1312041890107000116030301285200c10341c4600b0355400d001400c00b404c1403580368071041030b482d02100014846a0082c40415075011041c4210345981c0112000c4015100d50070200d008140204007140c152080401b04905401240d101e811444401800083d01800f8010b03c41d00815100740070304c44080d485070021982e61020320f00f49841e0082c07041c0301701240103d00c2c440c0c03840c2c203801103028405c0307941150211400f140d2040803c0e0070070070754161011116100040b05002804044081d00144808850400055136600206200f48408480041c140d0700300107503461020400780d001c1e081514842c4100e5410004c001c07005481c5a0081e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 973569901 1250 973568651 973568653
    0xd1e0c12050c0304030c06180506100e0709081f020702030303130506151f0e0a03060c030f0e031e0405060d060906050319030c050c060d0b010e030d0e04200705 70
    0x504003480301480c012550003100c481407141c074500d02a00d0003018800300910082003641c442943c4018218925072203020507070000305580d490f00703120151030980d180324490710140c1302401001810081c0981c0080c01283c1102024142d03000301c070b9038107128032010003200a90740d650900102016881c100091446100044a078031042c1d0b64600700781d407600c8002003816820100c0c0440420040d218054807005060680b4815111340c0c001c2c1100380ca580703c01803642c641058290304004240f00c045e400800c000e1006403010094a20207600080c00d40c3c4800c200010319600c20001c50344100f5021000051401400e00350a08150300d40d00018401c2d8006050403030a2500c4002c1448444428440e103002080200d0042a89103100800464028103000340501480305100d44241400300502a200c3c00c0540103250030390301c003a0b004d50700004088502c4442d0000342074180c41e41c1c1c1e0307040010340600800050b0700d440c3e66984102c030030000136181194000c500c40304e442c41c0038a22040301c030f00a00041c0703200d40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 973571151 1250 973569901 973569917
    0x4110a021b061c0f0b04052806061e02100507050c010e01060f05130b090a0f0b010806061c0e0703031707030b0f01110f0624010201110d1e0c 62
    0x8001e4210615000d210070301c184000c20414000d90702d005861506040044004100b1070010303503900700249480104caa41160030603007013200380c56070000d252001c0b0007000c55001d00074903025184412034089024400225140035840781050820010901d8805928070442c0c039604503054040e07082d504196002c80119a0103d03004020b04001c1c003e100d00094401d00800407586420b0b1071441c001c4051040724014070780101d2090a940b03450700840010390028080c00c6440c2482c54151004012400900300c40c149051601c2010703600c20a070b01d80c050900106000e0600d0100588650a407841c80340309410103030b44d1140030140280a03c07076807000b94003030740307030035959100362440401d0540c8020420010140b8191404c84560359818400710010402c1c6400100c41c001c031800c041c81e195a00880103043d10a2008010341b030066181403403620314292907890b0000c0a60300041e8240c445c803c000355005101485005100c4100740d005a11800314505240c04030001c03000f018084800c60700c50f40000450003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 973572401 1250 973571151 973571173
    0x11030c03070f050a080303090c060a1209200319080a110712050105010e01080304090b0105040e040b07110c0d0b0402030a021504080c010e0d24143c040204110a02 71
    0x704070b80c1300920f0f41d0b034040e52661412541054451124003240352162101046040903544140d810303100031220b00000704003410060800340038440d001c3e41007421403504003441704003600300417070012000e125808a005000040c0d9684d00074540041c0f60200030002d1022008501085c108000001814042c6c8070061441003403c086003920381c141c100c6a147c4c40660010058028000111412102c1001d00061543c2580004840c02d00c2582d005900050507079003800141f0a541c41414055803031a129130121504070501d45444901d05020300d40e000d44000c015401103948074030b43c158080e20040603a52440f04603030024100d40c0d41540e05c8803c13904080b9080c07000400801030488503000034200740c00700300c1c54400008d111030381e000300050159240c0b100c0b00c1c01c0d8800c100c000381c14208064105100e11520010749015200040b03c610754400c50100c1c075200c1c130b40d41d01070294484c1395418280c1444181c07580c80718200c1440c050001c0740c00c256200c000100e2070520f00017900c0640d0305580580101494 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 973573651 1250 973572401 973572409
    0x5160b1c0221061f08130809090c0a17100e1e04120807021c050a03091502070203120c0d050a0e0310140a140718050402220e011211030c03070f05 64
    0x22a0425144d103604041402c1c051900000c40a901006141040046041d2480c0c1040c0c58014030410030380214918003030000110320100035040341c94090707407260301001c05c0000250814100b0f440b98150360514442c1840340071403600c0d51551200c168540440c4400303d502040c0c1c0021000c80e000e58514504a8254207820b0307209180036000a0580700501003a502c40d0406680c0240e0300c81e0ba0014010000f52500c1310f54042d4000010503a005440c00f00200c8181411001a51101e1801c0740700c0d009001c180d10070100803034159140225444011b190f0003030420000d480a51151030f0500c00e0082d80d000205040d030b0104074115040c0d850302c01c0401c48290301090303445002c0c00540320080e5182000c4084114aa042401607409010f9140201142401080c4080d48200541100b6081400043d9052074907030001094041c1989540d4008070441e0740310208040034000380125444a40112240008295100c50f00b01e10240b0050994001d903804100203464503041e58070048481d01814030802aa00e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 973574901 1250 973573651 973573669
    0x50d0e0a0f05061b0a0c0e01090f09380a0204050907020616081504020c0606150708040e04021309060504021c0c15021608060405160b1c022106 63
    0xd140c1203a60a801d010020307000e40074000c001d240501842120000c4c40c5020428000f0769034105e80c01544041e2116942c0340d10450900588840310300b8400a199000c101d07200b04e28605410a400400d003690f641d843d0825040c02c0f20b031f20140040c1d03020040002032881c0030b4450050007264030069076a0701e888240320034194004e00000940d0054420800310910300085d60007411120303c0c20090300d9813600c03041a0b18000c20a2010740141c400b1440ea140780d8000036925000d44802c0310300d041001d01c1c90054410510465000a1400005110421060041d41c030540d402910007021000c801444510a600301c484201085d211a91514140025030030241c02c0e04800340b45000d2580c5000e03110f500e410384800824440d0310f0443e100b01c0303032007400e03036100f030000340f4041d4810600344076080d91f1500c03141d45e100c4080e203042d10240903241943d181c0200700341034607040b5800e0b01c07106410055603030a40080855807403405140140c00b0852011f44c0c07406090803030540b072500c8040302000d0a00e1028004120 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 973576151 1250 973574901 973574909
    0x7080304060f030b0913060f022101090605060a0c0b130f030503103f0203030c0a030e040501030b151306080a03111203041e0f030504060824011407050d0e0a 69
    0x40940d0140050010206c1c1c1c0a0603c580004001c00e20348200300d4410028071503001c0e50200060301031303c4800354480c981ca00342e04980c0d216100b40809a1254104034041c4219140d08012443c40380c541d60002d8000d0306801c2d0b00442c411510310f4291815100e0b91000803c4031001c80c00100300008010b002c1a64030b586070080c20842018010151000803d0440300042081e006070241e90001040a0741d4140b005054886a024090f00d48540010360a00d1f85c444680c00220040786520071b1200081c149071040c24100d0b5002030000c40c180c2c888011500d22500c010020f1600441070140760b4050065500032400201900c200400081505040090540c4884901c0f0850f0760440000c1c214091074040941e5000ba40100903041c3d4002080003030f54101c4a000700040c100c0c0411441c94041c1600080580f00705d43c05038448840664030a04802c1e030041d852040302484030f6040207080c0495110301410340c0500440400389140829a440e25032509901c0c020040000301101d101140c0c031709001e42020020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 973577401 1250 973576151 973576159
    0x303140103030e0d0f0f0c0303080702120403120509032b050f0d0c171303030506010309260f0f07140d02030f0304210c060b0f06041707080304060f030b 67
    0x594115079000f404088246031840c030410020309460103200c591040760b01180d40c0440c00801410039490460070b400700c240310a4001c81e41020000b081d00e0f0020803509468440503110b24a4a4207664420107106080d91700c000030810207100090944c0c9040003a402ca48074201c000000b0702ca20405d05060b605d50721000441045014055040c2c0500d4202c2170310403041c001c40000c501413141d444104d071042e10640000866585c90424464402ca503000b00c0061ba500a560134003d561b1603400540c00e54034085801440404030b0140040000d00b415600100c620a92a0f075034604100d09002007070941092041e0b9420000009221040002d041d0f1403c0600a00c0000380820000c0c90342c01039124082c0000c801e0b50400004001000c000600032007a41540c14411454401d483c0c10400410100b81c0a0b021105141782525203140b038907010780039090103040205418a020f0130501103100501a44828000071310035408003040412080c0064400b600c559540e02614208a0000170f00344c4907405c01c1301d402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 973578651 1250 973577401 973577441
    0x302031605030a1716030804020901090b0f090a2310240c06090c0e24030d05070501090b09030a03050703020a05030c07031707030b0a0905220507080d0c0303 69
    0x3a90b20301243e40b25029402070340d02c540444041007008010704c200c0c135080801c5880c2072040d004142d0443c070402d00071f030b0007a02c1d807206036a260b4410348103c54040c503000744d10003c082d2001c5118a04404031680c8400c03441000324201c0e40004814071a00c440c102c00310400c1c0d140c2d504000010180d0031008009010b1100243e5110122001c0307980142c1c0340d030b04260208250f0221820601180360061134005911a00c2e0000007036480c0e0100001c0030301500c801d94260071101070604403408841d406000c8100041c05089400b1042e030003612030f0303404000c045505540310010100440c400d411494861403058024590301d0700400402000c9032402004082131500c1885100c01c0d1680c4003054075840041c0b0721030169196021706080d11200d01100c0c90390362440300c075020810348560503001010410001d44100400948980d8442c064682c100c411001074102054003031481ca8104c0c110003c1140220180caa50710385400005052007010607a141c003013545101c171181090fa0522804000c02981e0000e0a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 973579901 1250 973578651 973578659
    0xd060c0e0901380415090e15030f0f033a02190504060c081b0d1d03120d0504020a0f0603050f161e0203091f02010c0503010b031b0708031003020316 65
    0x10709001d6030003008440300a004170b54034900d0040442d03c0180003a48071f40010f038074121b440040740f01e4014201b14040d000302000050fa0200018041541c400c48102a50601041031507203040c42c40050a294401c200c240e90401c220b007406c08829070520751031400581d0740e0681d202071402540d01600d5080c01c00904000c1000015440070411080d190310a2100b07a40d62800c07109801070510200f80348546000b00440301d20750540024915210056100c0c005819580301400c1540b02c555a401c03121150f0b00401c401a44900580d210a60051004110003a80c03900d0710960024020142c0000300443d0341c03101800010044200a154004540000c401c1c0801c25050001e09444218000c00c030340249884000881900a000b40c0d48100c101500c54038002c2024a48020310040d2a0901e8016500c1e04d80040116441707102200c0c145e8001080e0709255427034040743d1081038690792483d00b80400b01031101400148003400218042c1c031b518000203242071304500400d4140403105a124a4408070080108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 973581151 1250 973579901 973580009
    0x6090804052107060c17031e0606120a020c031209030702091501020a110102100e100c020d1b030504050d08030a060801060810020c07080d09060f08060d060c0e0901 72
    0x280613101e051501d19060505440d00c004054880c002d83e0700d111078040100060001a4440a112070b401d810300c0031083c1c1c89040c1409100c0c400c40c03192070703103850084000800031400341e0010284004280200ca03c1c1c20380c50100344c8161a01582c44025540001420f10154900310019940208000c2010904161900000f0703640341041e5400402781d080000186a10303078028031aa912800c0422400e018039070a440500707403240c04481c43c036900645001c10b488400c520000380075003409480c1c0c40d201002021074900e90700c2600740c004220304202d010080850140c440e0040960081d2107400b4080c0c690400d24500c409490035900306411a030315110301017001e454001010100540c030074800580e600b003d40c408a0504410b43c00c00c3c186845809800b940d5a03030b010801d5001c0724155134440300d62a5180c84100d0f902102514015484104440014041403581d0710043c4404101d040c09100d20401c4000b1980d028403d078410301220042e1500411281e002800c034940c5100b4400c0d41c80403201b1605006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 973582401 1250 973581151 973581163
    0x37180501120b061620090606160606150f0e0108011e0905250c030f0f0203090a0602240c070b190e011d0f0a150207060908040521 57
    0x24100a000800000110400d51006004240c0034281503513550080151400008104108862040e40440b106840b00301101103040c5c1d54400814502a640b00c1808122003038100d020806002806101c807080080c01d1440340174014000000c55001199000101800314200d0040b40c41c14480c0608601030345aa0018949041d280c03424078602c1621000108c4c2d821180c11078100c0c004081c40c0006000c24421414031b48600800300d0b403240e04101820076404c59018800b04801000300310000c070b03590038081c000c098041e03e18080b88112814110800c0006400b2031503640b02c00003603002030010060b00c005000651081302d4013100b8401e124108070b0004a110720842c400035001200070000700340440018480140000100c0505020745130000714080d00038003030795540e4410150084e01c0362517819000326400355140440c102828107e0984d85aa00a1890704129440300c25402c000c118000740c40c62103040100c60003241400d88641c148020701c51048598000b0425840207144429000c140c00102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 973583651 1250 973582401 973582409
    0x3051c0f090e15060d0b0a0b13050607060912120606050412170c0a0303140709140d1b0605030a0f0501051e2101050712020f0405010c05033718 63
    0x81e65501e070307a07000f00540d141810800c91540f041000821101480154001d201d004800b10703031710b045031a03a8985000e220302c12880f565a0f02e0b1b0a00380108140d2629001500955029440100340400d003640c65540350305204140302d001c030300c0e0304108000001407446180301400752030805a1500307080c488403e000c14070401008007404420150284038204003800d0b5038103010014200c4820561038503024010300a2403940300c815810304400640014030030a00c84007220303c0701c0b200c58503075500d81c02400203031400c02100380c4215400e840092404114290350100610f841d5a4540e00e0381410001c2c48c007035800c80d0100040590400c40180001c0d0f41d5045d04a100280400066101000800c0810210084c0150034003062a003007000904410064028902ca10746995464040e001c45181b01c0c3e00324040d04040940882c0c05000520032075000c1e50751605102e001d201201e0800d645085041c5000d00920000f820700c584120303c1a6020350003448506e44222030341001220f540422a10061034109807003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 973584901 1250 973583651 973583669
    0xa05060402031018060314030403050c0102070b0a05030a1413060b120d050c150c090907020109080f0a02010f0c321e07020d03021b120c01050a02120403051c0f09 71
    0x100307050750703844160310240003980c7c4005601c2d0800c84001c001034407500541300a07112401040c002d400700d584007091002c1600c002405180c24020b1014046490f904010170440040e951903c18488011043c1c4042e13100381e04901201c103d4281030b02d050016200760140391402507449150103010740401040201a1078070303c0ca8600d4958429000403442d2105408400c94030421900a10075030101d544020b2820000c00d460341c0c1d0a64079814012800c848090324098213aa0050000c5605003800b94010710b404852807001085c01e03184543c041084590740c103022008139901181c005403030f90f29080b0701e0305030b9041c8450080e48010550703402882403043c01c08103010001c00b00c503002108036095080d102c942c1d4020b090424820305a20300659103203640d405009108a40c050851040c1c6020031072041d0010744070700509021489880151030340d130801144d90065010b503c1a040f01c603840c4101401c011070181008091043c5011a500b40d403000c00015902080042080b07d8603454200040301c00300d41a9075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 973586151 1250 973584901 973584929
    0x4060e0c1e0417060414150a021c05150406050303070b06010825020f0714130203040606170313140105030402090606090607080d0501170d081302180a050604020310 72
    0x75055141511890300f1201060090042100380340b840080c203244500d10440d2010b0781c0c1403903800c50958030855020110910400c4c0400100c20140707940141605409040040c080e105a140c1d0500507a24102c030031030403841e40a1114130305482c00b802094001c240990242d8a811a82e40705d801c03a14400610080c10302100d4030202d1581c91038809194107458400c08550700e050403500000f511040d100036a90b2586c400c02e10040f03598503a08003d0300110030014801300441d4149410031020b03400c01002a0341c15540c3e0140020009007154159000d44d00312000f96075984d4400d818050f2859841d00312a0034501a44901d065598005046a81140d0101d40030b81945d5546400544140f0075082c50603000400865000c00b0000701070050407988000b03800c240040da17210041c0c81300c1c0420a8256007a0382d030015031040301240c050041550801e041d01d2a400c0030140a8011525050f031380415000180842020808043e2051007070030381064048809502c0d41c10301c000380d213503404031500803904085515 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 973587401 1250 973586151 973586197
    0x301030b040f080f030106020a020406051903152408190213200d09030207080a08190905031e010b0a0320130e0a1412121306091104060e0c 61
    0x41415540701c130868221a42d60f07581c482c24002e488031144441203000d54100f02c00841c1d03a1a0600c184411036000301c1040f601245162210851880400b00705440141d41e42d0034881c110424003d00c0390a0f448841250007105c0c81c24448900d0031100f2002840c808201c0d00344840180c0c0d4410b0410301e020010070001c5402c0c035144040341a60144004d210032241c0000925030203901d041e03041458018082c0c0c003a50142941d81100948558401400030300210341001010411000060b0381802403200c2d2034020701554841c0c0200f450120315030441a0b03078194110303c40390030300424024540165400e84080400310f14642e641c040c00714200c0c48411000e40c142001a1b241c0e1107141101d00030200c0c001007401402c008541650b142c500e980070903503c1d500840c000c107e11a5000502c000280c0b08000681c0c40c120310540c06030f4001d00098210080b1a01101040f00440c4450040420087c0100401d1059801100800c0b0407111305d0750200035881c400b80300b0000640e03d60020b441d165181c903100020041d0034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 973588651 1250 973587401 973587413
    0x3031602040b0907031a04020c033709030606090e0c04020f0d021603020c0607050604060504020d050f060a1802010e06070804180606030b0414060f0102010e030d09020310020301030b040f 82
    0x2418660400c51103c10045141c0d49038115a6809003114440d0340070a005809020076403240c80c0040340ca90f8400c21900c0907910b0340380c008501a10348850011100c070005a46d000302904c015150800148a003031043c81840414400c6030b0092450f070340104a10300c101d031031030f60311203481145007446079070301145004002c042d0b44112998000640800c55130340c0745500c1c14551201008d0b4054005104e031200c08284d0303082c05801c07200c1c41900400200607698565030760340041c2c94010000c070f8210402142c290b001030030802c0040c0d8400250800f41c2840e180620700c83c070803039074840c8110807204042c002050150760010701c180119081916110b41d59802c900f400c4d541841540e000b10380c03a0502001d91031290141f9842041943c1450390180b200414840402060350002540704100d9100e44011078a58034044d0072540c1d500b001800042411060148003500759040100c0c0d0005d07140d03e80355640c2c1149010b000282800768000c50445c00d5504580b54038000e040c00420041202c08403907480c4050200c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 973589901 1250 973588651 973588661
    0xd03020c04060603270f11030a0b0a02090312040f0e0a020f130e0601090b041412030d0b0918030901050708090d030504030218090d030c0512070801051306050303160204 74
    0x20060400c0c840b0540c0c0e158004c0040007180801010307914450050010103040980c80030b42c19401000001c014442511924480004c100d0226414820301c00c5d66000a9040c0c200d5502c03508294100580340c00a06050605000e6030812200e08890104001c4c0700d6440140f009005540d441440440142c3c1c1e4090141e0091041e0300c4a0108080085001030b060880014081c0645001d45901510b80d12404019240d00f83c2a00400b00c02c0013061000303110b91001c400040c0fa0034140102070044522007403550070308540c401720a031004a9210301c0000d4240c10030054081c0c00c41d0041290014800710302a0341601d0740905a0344a0421400203186410b000f41d900a90300403c5000b000e034038054006213005000c0e42d0162004030f000e03c1000900200c0a0441c06042e446084400302500503514004401c500500c0560b2a100a010042c0a40d61350308082d04c03404d030321808680c1c5a20328994144030410030400b02804400300c5d01030078030030180000c0d03c020040c4d40da11084001484105c00482c400034020381 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 973591151 1250 973589901 973589923
    0x30816020f06070b090d0302031b0a2d030c0e06030f0606040b0c01050105041d07030201051c020310030512071e150203090109030f0c0f0206031803210a1a0d0302 71
    0x4400490f2140030302c042c5142d800e0040f802c80c01151000c11440344182c00340e0204581e00a52036503200c0e40e51107488229801480ea086451a00f4040854410195003250140d01c04088030231601141131003445070507104813602c035096800c101c414038002c0300c0019a1440020300c0c166044000f4004281c5a07191101907074050310b194544961103903070392103816000f00804d108080c4564103040f40ca8407208200202c03c1480f00c0c0300070142880c54296001541c03940c8c003081540c0741c001200e03400e010b030162661001d1401800d011614038010b600d1810181d140c042042c003d45010401001031500003100c4101e96010b60f1415072072203003428404e0401c3c0c0d00e00ca08240710310380e081e40000104410004194885000c442c030a0706e82d01c10a00701c440c0c0491305d028240000402c007850381da610501501e0044091076011070759101100c005840d103640c0314155003240e60405030321101c948100c80074820401c1c800e03500420a0000300425242d50301c8003108503a6601c0c00758082c0c10703c02002d000f49403003880714007003c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 973592401 1250 973591151 973591159
    0x5120415090b0f0907060f1e1b050c0f191406190206091608030901051b0a0804180c050d1508010e07030201080c04290d060b07050c0a030816020f 64
    0x2d140c60402d1103c82101259440b0042c00f4040010404034020b0b1402000d2011690300c0203030380b248094002514007940342030031081c803035081600300d10311401e00c2481032294441c00c00703061140141c1c01071000c4140500c2d0702c1d502c41c5000c900601074100108403a40c04031780c4010b4071100f4203204400413440900c00e026280303c00f0896541c001000d143c0004079075004940344d904440000c0c401c0c101110f9900281d008a5040ba0010000300b09a5807144011307040c85402e1042d01c0300b821160000d41f5181c103210f02c2c0121703001000030500f0089102103192071408101e0201382440148014403004242c0c0c49170714508030105988d40070400c0040c48030344202e4042c1c1440c4000708640c210024620303684006e0380c0310407400985c00704000369440e41d9500644040b50000300c020444c2585841c0829030810190035008070b07207007040c0100087d20301103000d680002c0650711030305640d40d04203050060402c080f846e402c078061281c029080000400000450342e5601c400003040c0203490442c40011200004060b00c00e0748 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 973593651 1250 973592401 973592423
    0x106051c15020d11030105090f04080d0e0f010c270807061d03060c04150203120112081215040c050705060a0b03010227010f020a030c060f0b060c01060f060512041509 73
    0x2401c1e404e40154140c4070219005481d503662101010000c034001ca800601c40030341400b00001c0380001c1e230003000c0b429003030b102994580d0780c08403143c41c2120b461008550020b08014080c0160700c00c07445920a00078412040c0c11110381c00c1c100301a030303103c240b8400c100800082c50205680a92381c078540d603104c20401003d43c0c9850a0104c4682040d80060042e140f06000303080c40389a02500000c02c80b8041406064004120b0b031070001c0350280c400380c0341e40559101d00d0800c48803000c4c09511618a12170780d1001200c8600c840788200b44011250b0a40340007041c014104100c001144001606952018041d000814501c00d22408039019010301c45a01c8180c3d40c0c2d0800307030001c8855103400c2508040c02070740e860000207400c0000b265180f16001c0050003150b800f46510003c9001500442000c681404006c07807000c040f40c0200e0103992100458070f81c140d6403103106101e0300500c11b6010303000781202d24085061402852104032104c2003e007004150440411946600d889190400788100f5000040c9041d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 973594901 1250 973593651 973593671
    0x219030e010c1e03080109090f0b06031e0607020c06040b031501020f12120f070c06241409151c05150c120105040204031a15030d0c03020106051c15020d 67
    0xb040300140d090071804652440e001081f03072081403084200c01078109a80c0c5c00301c0704c00368840b91f030405c5000d4005501801010400e41e0501141201e44011003650030003030400b0700d02003400a08140300280d06500c1500d0800003007000702d83c41c1b030943e40c1014194058400c00c40d11007006070b280000e01c0711030301c0300c038021112802d548038404805441c0240140703004980365038402a070384018503c12a10000480c03800c04409000c81c01c0d540c860208803840310f04840c15004254494880c0c05900c0d07014499000d03a070100490181000d244035504401505200c0140d540e00c00d000501881d10b46a407000c84501d03068803d000d01000300914003521140700c4554549041108030700030315030310040817000c070407400000004860425201b114201d82d00f0407044030403403000c50244858045d000c2e110301201c0018200354803150f502800001c1101e0360310703140c0040990f618503020b804d4540f1035002c244030f8811100c21208500f030f00a44000401d50042502424403a58000003009009890107242c2492034199020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 973596151 1250 973594901 973594943
    0x6100501030e0f011e0f1803050a1103040b0301210b06120703230706050a0c02090a09170c010605150406080903121e0a0c120510031a010e01060219030e010c 69
    0x5c10340404102448002030002c080000c2e1048003031001014900903e200c00800d10850241288013a5403030485030481c1d4180314149581c00139044002c81301d9000004008207409600302c041c00f1500505281480032080d114204010b0000f082c40f402414100d0070900c00010070b118000c06103030300c4000c3c100c08014010740311481414041c104059880b82d00d8000c11054016801d4541e03c0d8540e64841c120800da5500b442802c2d172000d0a0380d400f090301c901194000440c2c0d01c04180e00a07040028264841d0085005030b0300352581680b0140c003d82401c011104290058400c80f0280c1e41c41c0c1c1031042040e290759143c0751440c4990035454040315080018846800340d1909030940c1c0095004c00c0b803140352079001d542c00880b11081c0f0058049004030311804005041a088154040091984446500d0307407525078034040501090103210301504240140091002d00d4440782c0981403610003003c0303509030354510322010801c9030006014070091400c42d2800b40c0c803402007409c04a43c05840103251440d10701e511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 973597401 1250 973596151 973596191
    0x2060f090402032715071d060304061a0604030f060207052401050102160b030721060e0105030f010b09180106030c031a060102120a08090102040b04030f0b010806100501030e0f01 78
    0x19440c5220707404102c4804d02c070010320900c000300204d1a0a145803518001076070310360194428000e0243c41c41c40407180550710710010718410343c061580400c0c4c1101c07001c40c5000d00c24490300c0b9030307104150900c030504c04a007298101e1445694007400060b65600b242c02d11620300b1412100b00c02c0d444512001041c160003816407004e048980a03000c079428400e840403048008081d0b4001d0a4405405000080503d0320446c0c6100300c1035070001daa101c0e2880d03a0103895081e1000c640040d010080745c00c004000701e00b01005000303405a094802082030909600005400403c040e0106104070000904084d0050f000c0d8020f0300155800903004105964a07d0310f084041c00f40800c001c9842403940004200e540045600301c0240103001172185443c002d400d0955103508042c0002c01503660038000419081c3c818802407010f0741c080c1c4402c3c1420701c468074100c4a104016007000406410500c02c0c8940006420308540580e0030900700842c0038403000c0c045900e4080e20b00c603101600c1d800c1101c901d85a800307007114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 973598651 1250 973597401 973597441
    0x180a050a03031401060e0d061d07060908032d0c0627060f0105040f020f03010803040e010b1312060b0d031808060c030f0603191101082202060f09040203 67
    0x209004400a40f621000808000d00c2220042008891b07050500e01d000c0d490310542a2144000058007101841c43d0f03696101848074644c00307940468420310140360401d0f051401444104020740c0350540f0308140e861f0086808900c1c0b81d00c1010f52081c0200b107040d20090390440040e007000c580c0180703080d5100e002c407030030006c926040c54138a03080703110316254001c100a80715414202d807404c626480c10b000d2100600400390040490f55003800f5108003004410000c500a046003001136465030b041c034100d8980200103074080c0c90742da101045600351600f01e030004482140c0492001e03440c0340410b81010380c0a491400d0380198440c00d4149400101070300316510312a08000c401c1c0204556848070071140da250400c0d15441803044080c40040c20403400810070b40da2049014094840c10328880e900a80030b01202c14003200c440d42e4001a260540d40e0000841e64410140d00d0b00480c008a4078280e14000070403400040d0085c00300281c0202900c094030b080321480e00010340115520303c0e00c8000300c100d48000d440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 973599901 1250 973598651 973598657
    0x1e010c08090a020a0509060103060305161a0301080604020112090510050919020303190903080a050304030e011407110a0f0e190e10050910021903050a0c17180a050a03 73
    0x80826064100010082c24156014240d211103d00b00f50411441c05002000a0304142e21598040001007060024400070909142880d0b042070a240034104010030f00003040b4200081400100031040001034456001502070804140c1d0160307501c18207000c1d0064540181c154460001c03490781084e45c0f544a684a00c4409041d1480380d4012401c0381203004031048069899441404690f404c400300c0c200c030207000507250400d000ea090352551402e1080d041940070202281001c02001705244d0860340d4842043e101346403210f14000310800310b0201340640300b40030300347c12140b0081d000c098848040340c40203004007484500760169200c0c0c690b110b44030211080c61051160801402041850b030180785d4001c9805400361440550105418000f4907006069101603c01c003118070f10009000c1c40200880b00c01030004000103484000c2c0507095880c050040800c0d01d203800c14614000364011080d85000003007411300102900c07203001c01224001e80c0c007520040707400742c1004041008800520606042d209403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 973601151 1250 973599901 973599917
    0x12052a030d143103051b070308030a2301090509010e0714011e1b0503070213141f0b0a0504031403220f060509061612180312050901021e010c 62
    0x4042504480c203072007092000c1c19010203400000c2c06200903011106c5d62800101440316109529850071540380e0096418501c00814081e8030001806080c200003159150b00351805100000b0001810b41489811010380e980c40109080d1b007800c0d0070900d42214000300302c840f10350b2600000d0410300d20301c4002c5404149088440c209054608642410002840c2c4a40c411108250300e614400402502d003280c1e18001001200010f0340c4001540a0380807140000041e80112481c01607809107015211452410038280c4502c080344903c01c02c4c4080c0c3c0e80300707802e05840c1ea010f500155620700403070f00002c050340d00d903510003540e508000002c1c04001e070b0a00454144105a1074003030340b900319640134001e03070404000300071306c01c907401200100002c1002404c01c0e481d240c22070301602000d0300c1003082100c5103030203001c80300850b59103c149640c020030260324030f07020585995240041d00c0f00b42000d140c103225002c224040980e000703020702c01803804004004005100d552100c507000306681800400031614070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 973602401 1250 973601151 973601191
    0xd0e01090b07021b090a0903090305011a04050c09131d0f0f120403030509010819140624090405040c0b04080c0a0f0e0a0b0f03030a020a12052a030d14 66
    0x1c0c103900c80c0701c40176080104a8070b0300c0b00208082c040480c81074080c0503000c0b00000c0040c009104a00e00306064240c406440c040e024104130a903a406480c41021a1080c048210343c0d684800e0b514410791108440041c2c050004040c8135115180900c003048240200d0f01c940d45a0800450708048600c0340b08151141d007080048282110300032400058000750040c402c401d00355014540c101c2c2c01801c003000e01411041c84070241400d9400b850043c048a140c1c0300c040c484c841c00c05081e800c20403a090f01407081403001007000c4008900070016054811070301c030000b1500f0301c803450805902912002000b1030341c441e02c801c03100ba42e4440e08171201c0d0054a01d003030300081142900c8554000d945400007228000d071900e9222030050300c405500c0742d62284604003148400d0b035080009105105442e00508103a980f2410040e070142440c005c3d00c014044d00700441c0c0d047ca2243c16052030020b42a01400a4410101c0c61580c03440c0284084112000e24008600c0141c10103c03c40324410826008001558a00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 973603651 1250 973602401 973602433
    0xe0604020f150d150b0a020114010906120b0c0f07050304080d090303050d020a200709110c060112150504030309020f04060608011208070b0406151a0f0d0e01090b0702 73
    0x810006102c040c01c0c14012240000308941006560507410f1116000e030a07103400104e034003540001868800b41c4e549842c1c1c4441021442c0006004020180c010082c49280bd010803030a15009000100641440c80001c1c032044108026904044a040007080c4c445d4a00c0c0b5080d90380c0e83c0980100311162181d103007080c040d644201d08010a5039859961345060031420045c003c080c0d001f64903c4814040c50201c100107440012010340c0d000300b000300041842501e030009035021a507919100e103605200400001d082803500161a42c1140c13400b9080142203130507400c004034407500c0d0307107901c040403801c01081c00107165240d004440018005c07511840d10740010010041202d03c00c0c401c54010640b0400100001c1401021003ea5240580b040c545051001d50300c0304501402241c080b2211651100030804603a4641c080001600034070710b00d5039841c203d0440c2c06503540110903c886c01880000303224404004590000c110710840c04009000055241c500b09000d0802207940400602c0b50341240e0b142c04103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 973604901 1250 973603651 973603669
    0x6060f120218040210030c022401320d260702120d08150319061a270709150801090b01020d08010312050c0f010207120c1a0907090e0604020f 62
    0x5802818104045c070104820b5001e405080f07022000c1d0302558103912199811014541050200303054400d08070b6040c0801c403080d0120074840515418074541120180c201120891381d561182100c00d243d08080320301d4480320554004613801d4044414002e00c4828100c0709001c0c140f40c91084400d404c82524050805c2d50726400c800c650b1002a4010002c91901c91002d0184284001302801351a041042c40210741c24001c0a40d1084404581e90b11001200740312094a01100440c201c0c0c0d410030171005074200e40500d00e515040010a0328501d0003052002d0b01540002004002c1c014521800c00042400034055242c2481100601c6e4188110545650b01c0425405005401a1244903151b42952501d642ea80844142da10034440d040018510708c1000700700384055100668005681c4001d10300d00317103031101c900307010716801c2c000c698100400281c0700000f07001c00e040c24980440000d9550466513460500c3c1c9030300c108681d40c0751110440f4071b5000030070030b944103d0081c3d4071403850300b02e03000500088903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 973606151 1250 973604901 973604903
    0xc0f06070c080322270c02010221150d050303070513090608010c0311030c0714030c012c03040e0f040c0510020309010e0f090103030807020a0605130b07020606031906060f12021804 79
    0x245c20040007034140c03a00741d2148040030681d20006082170310462648050420301a07410242c01c003054200110190079070568202c01006a400c10741c1858940d031038603a00d0002820100a0000224015014401d400900c3d0010300015405004207540c81504500a01c6402000000682444d01d20100c1071069800c90340901c115240e05454140251900309000700800c07c41303d5140020031030120140300900901250041c1c42000450203160300041c030403140a050710950068106100800c0505d203800c407041c0e0307c0308100024014590b07031032a2003000441c558003c103512018001d0320b1100142d00001510a80d8000c2e2600d4007a203000e01d00304110b240d560034001745e01c556501c006000007403007618400d030000300701e00480361401460342d9502c0903100201c0f01c1c0f030000c0b81c04025803418011640c098903004035550004e0b003041d0034950003080c0c81c2e161032400d1715800403007045080e0400c50300740d0052000f001c0034422200314540344d108060000130700e60707001d0380700ba0f4409600c0c1511060707030748440d8015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 973607401 1250 973606151 973606199
    0x60a0c0206060405070917150f250c02040c0c050a0b07090f051507020a090204061205060d2105070501060f060201291905040504050d020f0c0f06070c080322 69
    0xb854103c001c5a03c0c1c6e01d1554426242c00780051000c05074100c481c01d607000f203600400b00d080341c1ca04201100c500c818800100000044ac04030507003a103d170050580c1c01aa901510041039281c1d444009803904c00381c1d80b600400381e10907076018905000d039110b0424001d85296403811400d60780e0303520300c2d02c003103255002d903a038442c0c4080c01090008148400526200b407000c0c081141403aa1110310804a820a0348804080f501c0d507509420880500d20409910517804c07078204d61154601e440d46403c0640550059a01d4107004072403c5880d802501502d0041d50302c10001c1c051262184e501046c05006489664050340c20009032200c2503241d0120700701001031244002c076480700e48004114034840461904000100da0002c089296100d5019451080d80220002d01d00350030746050003850108040414019034108880b40099559161a000e0484404070740d000c1e03e510260800a15200255124091501c00003e02001d0207141c004142c10301c0002c8901e40c82d5595841c4042240701c0170307102c408004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 973608651 1250 973607401 973607417
    0x105040519081b0612220609020102010506061602010e04020f070f14030a02120306010311031e09070518062b03021209090109021315050715020a08070c050f060a0c020606040507 78
    0x240c0032440e11940d0307100c0300d150308211840c500d4225060700300343c103004147c50141d102c2c5018000c3d540c09011f083c0e007103101a6405468108041c3e42094000c3c3e8040c070090400c55103c802440e650f44d6a0140c1e07200400030082c20b0740e5414a032901c25000950000100c6210003244640704c1c034050040306880b101010f5030083d207100c010103499040540c0c802090359042c0f50351000c1501421410401452084890b017401025003180348c00c89006440008003410195802003c046c0600d80750b102800030300d140d070302e00031110b90b03150340d8001001c0d40000d50784182000c48412840c4d003101e4240845100d424000c1c2c0076100c1d1920429480c5045106200180741c0040c40e207001089000707115030060441081624095071100e4840030307240003200c2101c04500000d603000c10454240300b0041d00016440d055400d0862501c607881c9800740500b00010015028060510302c90000e004082c0500400e002c00001603501c1c07071500d902c0280040400300c1c910750061094400150250405204440c065001d40c0c035480c02c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 973609901 1250 973608651 973608667
    0xc080a0e031e04030506010b09040f1109011d03010c020304050108160813020409170910030603020a2105010c05071208070c02190b16120219020f0105040519081b06 72
    0x90b00507101100c070369010010000000490414040c55010301943e40c0341666681940080105580c003840314290f05d1860301400540912181d011502642000e00304648050411410040360011171000f003a055400c2542d80c0184a0b400300040c01540c009894601141e100c44c0b032202c8044210131401c40209680d0008110400700011031103020341c0c4024070114084840b6515000402d211009030841c4207408505014a0f1801d40390110680c04c152408004942c51a0005100001c051240036060300155604100c03058103841190701c801e40200085c080e1150003c3c008141c2d078401102914001302070b800e45044188180200790184541d583c803a02c01031034613000c00c00c00201c1254a03014140350714500049000e1140301404110200c501d5848600815051484000100043c22000c54111003038090242961600d40303440c0c2e9805452864031040c403807006803031512854125035882071010543c002c9480c0395004171000c1c4d4040c041612000840d120304004081101000154400024000b0705 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 973611151 1250 973609901 973609927
    0x10e011230020601180e060c0d06030f03050a08010902120a270f02240403140c09040b0402040f110a05070c0519060305010806160503060d020a08010c080a0e03 70
    0xc00101e501c030803614207000003000180c001d000c080a840e0240c1c101c03500400445110310004561400350180c1400840b2201d12016100c41005117510f884010201c0c00c10007004c81039000070083c41c0e104140481030402410060700c02d40000b00f800700061580000400e0460150007941c0c15001d0708218807026403160b81800e006440c5c0c00300c0400d10004180c40322540030b018541e0820001303000d4518881c101c4550300601c4144440c8075100b61541c6c0b04040c280c800b0100b1007044800b1207811210106020342c8441d801804c021030050340710741c400181c1040c84148501199410701840c0b0885007001048202400081a2105800c0c2c04514a000740700d010401401400140909440ba45020780c60741e0f11580001d11040030040705903039220040c0c0d020b00100b80c00d48a020302420b001d1004160358500004508450024518120708208010011501c3d0b525040c80e10040710754010306444115480c2c00c80a4002d02000071108006001c11003c0381054040c0c1c0300b03581d8800c000ca4051841c21074210002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 973612401 1250 973611151 973611173
    0x15130b0105100e06031801050c0405030703031b08030f0a14100603020d060902160302070e0114042f2113060c021e03070c0e130b1314060103020306010e0112 69
    0xb10502401c0352180751165220b100551154581d118102c03488606400c0c0e103400c5440090940b81f495104000c244810f58000502c901260352625101360040076902c03030694440a1403000401002021003032000b010301c10454640300d20f00c500420400300320b880f00098034100c4103842000c0322030205035052088510940061480403d401408070324641e03914143c6003240d2010a01c14100c210382600e5604040d03040c002c0d003000300020322103c000742d41800705241c580051700d001c0d94032683c2e5a81c02d54000c4c0f064401181c14038503542024040c0742e01e01d0300d8078064951145940034070010220f180d2012000c030203000d0754002c1e00d6203401440c03003203c50341e14180113112030304000c019840743c04070103003c0d0495901c1a00440030304401442d100c0c0d0702c0d460000401c0301309401000317030b4403446000c000419a5154103101810341060b841000754440368040c440301000018041d00300c0303080e103110382000d80300058040d040743e00c02e40c112859a039880d808502041c10070b020300d00e1241c08010004020800300410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 973613651 1250 973612401 973612429
    0x140a08071b0f0b04140307051005151e010315060503060d061104060509100c020108270f031206010201020306130f0209060301170c0102121b07031415130b0105 70
    0x1441c03428803164031014000c5901d90401c0360142d604004000401c031500d4001d0351400070381c1c0c00a6003011481d94841c1d85445200024200e801d503160002107044000500341e0103141e5011704120ba240003890a501d0000d101480c0302c901280c1484051400345a403800648116103c40c0e86550560312100c0070130402202d07005041c0d41d0a500c07044800c0b8102c1003800284020a421380380c0c0c0d942d03034016009121103034099958000502154042210160340c00014955006030019002a5000003d80b42500044420307181d0100f1489a801c1d008000c500000041c050714010303a0264805544a100483c242d00c0203d86154200401540a141c1d0040c40e4205020809900354013500f05203240000c01c10300e410991110840e500d200c4200b054943c428480e20b1074140c03080c03000c3c014120010110140c42c0c400c8100d070f002c111a00f05484600c141c02485680e0240d035003d0090750300d0b000040583c5039548801510190030002e448041505642580c4040c00c01a40c44695001d00f030f842d11041001c01c803d00d001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 973614901 1250 973613651 973613687
    0x803270619030c0e1903080c1c08040c0b0f0d0216050d030903110604050d050705010f091a0601020c01091413020f071a0103050604080a020a0c0f0906060302040e0105040903051b0c01140a0807 84
    0x4100310140c3c0002c042c041c811600da0340c502a03a032410341401001c13041c29510440100f8400c201e40d510402a01e012109890500316015030741c0c038a00300c3d500c54090301c403907004b411038000d010070010b03020303403540158111501980c2c600451000d0100da003600c603002550b0091403503006003140e034202406400500460340c002c0c4000101c07402d1400c4142d0070351b8016501140c4014058405100490605040c150060400e01c0140481c01a240002e01031110394010452146414548041a540c450748143d070306100154056440d0f40700c0c1c8044001c80d13000315804480100c402d049284030301036441e0589040700e40100040807203407a07980303840100d030b4080b000050841c06210b0a072008580746400a1005001c0001c0c9040300c607181401c148201d0b22035030008020980100402c20003201e000b1420382c1903940485001a140107289029515840303a000d0401180c401a001c0c01d55a80010415000c088000e80b103401d244518400d01a40a00c619680075011520180100d8241c51007018001c5401d00580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 973616151 1250 973614901 973614913
    0xe06100f020a0b13020103050a0209090402040b06161b24030506041112010f08030c1b0a0e0408040801060512100b01020f0f070801060803270619030c0e1903080c 71
    0x349540a00748411100c113074000908642440465170b040c45801d6000a12460841c101450300c000101540c2c40540045e00c255100c400800300c81e5106404c948101090112454245032203160078818586980c011315400c14200c10700103945130340c1c01007a40d00300413144c00d5540544034a040560082c40e0280c10b454200740d903015500004022100200b048074000301260503150700d40340409058a540e1740010716107800c103024081c0d40345000942001144103582800e50340901d050041680e1224551201d01c141d441c540901061002c220020000c1d107190320004e000c0c1e50344a07400d10003ca1030ba2000d00400360300c807171403440400000d070f0702803540c0d808144107855200c40300e00b010b83e1a02d00d4040300c07107160f0740103003004008000013481038100414215026600f069070701c0c016400d8030096441d04036030500700c050444183d95100c00c21910b40c810290044c04864041d014024000c3c4845210303100401c031120359406492400d220408035400c000300045600c18110f07942d0903503580004040e0756484c441c176 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 973617401 1250 973616151 973616153
    0x3100b150304081b1c1b150b10171b0301090c0c080d0608010b09090616120c05090f180c0c0102070609060b090a090b060f060909010b0d060e06100f020a 67
    0x640110360b240c550386000301200b95104c0642e140c08500b0701c0342d400038040e90680354900031b100149281e403860340100616495820032201030b000340c400300f016240d0040090714643c00d003903080800022600107402041c2c01c20317600c64004d84011840d11205507a4108184010042c4a989420501050324140340c00000f0405070765600102c4d400c44d09035080010345540c41440107440174420340c841404201c45418042c202103449684403900074112605508001f91865507441c02121a08400780c1e171a00100010112820003c0483d0403003490684100506409014035142208984c085220b02203240d0030540c031000364010142d449454250300340e54080c000000440c260707114800c03206000d5000880c140c03141c3e10811500403401031000c0c41c440e103007613900c5020a0b40100040c2d44090f0981d104580c207000c003c0017030f219000ea01d82440d40070b40c02c0310010400102d01006841103140300170303060041e180c950b0300400740070701b04a0b403858001e0f00c036030b00c0750070154881c6842c00700c60346180c010340707001c0300716 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 973618651 1250 973617401 973617427
    0x140a05120709050f0402040315022508130e040c0b180405192009011805040912020d090302010203030f1317070b102409080f0c03100b15030408 63
    0xc07601d040c081045050100140e0510080200300c4010884003103240c01c0c103658403003030fa07c4901c105c00700307000e940400c842c07949074203d030241d040d0588000040a1f20020314900155254070440e048680020407401c00a040307180c42d500540503541c0702080c00c0340f003030620100724201c1d0800b0044140c00c0d095030741516815241d0b0311480303010321850100703124480e150b61610016a105501c17800200c50050aa00241c2025003084d5984807a0904e040c072019103055594040d200b540b0740000b58024549500d43c41009190300364070040100b150281e8800d80042c060035903503110140b001a000d40c0040002a0700514a100079a41c04441e074800840d2062482d100c01d801030850118420304441c0009000f001d00c04540c0d6202e0344462440d20690045040103403490800300302c1010714100c044402d90545030580031704081406045414100c40c0011030120b8140d40d501c00304400c00780a4000c6803201e050f070401a000c1d0420422001e001c040754141206c2013044241d0005200f0b50703e40200340100052405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 973619901 1250 973618651 973618687
    0x303010320040504420905060106020d081603020403080a0816080c0a0509040e0d02030d2708031e1003110909060f04080408070b0409050901050105030d0e01090e04121e140a05 77
    0x2c11700000502c10300315107001340c83c000040e04444155400b03500d03040c110320f0f4001d1540380d00010525003464a0742407400240e0290241c2c1e0030040c074407480406c00070421544203212030f01ca20845402504080010315050321500c0381544e9415440404211b03660740345009100070562031602a000050300d4000414140c104211111404016000001d02c4e01c00c08000d0b00809045244620400c4910b03181c403160401314110040e4010000c98000c07001680b8507070100d803c0b1b44c41e2030000403044154a0203540007903a000c55804104c0301075080140c2e0740030341e04080290511a560b088010160781d12a40d16512040000030303c101d4441604000100307440b881407294100804c0722601c002d45460030080c030501a541d0003002c0d0101c43c1e1401004200c641d40004800f2903805060400b5140d4164050040303800c06400e0700071010201341c0344107020170402d0b1026030900c85101c555401e80b55884800001210300c44d030810361000108144521420300301000d00401c1c185440f424501d207000d240c00f00d1820407113 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 973621151 1250 973619901 973620023
    0x72603060d24090b0703020c030a2a0b06130203060603072f1509150402101214070e01050c120d0608011d07090e1e0a050303010320040504 61
    0x292290700c518200913050100a0f0004031a04095081511080200380d81e4014011960100304000860140b00140e50080c5070700304011203800d120300031050410354100d40040ea0124041c0041400072198407000784260390180c44000c0c1040d1468613140c4048582842080500054032101e61501c500000303980741e696007010014001e8000300302034040c000c905e280d0050100c10150000461061800ca8502026a10a90455400c4c40302041c07c0000c440410a100001131481c2c41c06e6045c01c3c00410031450300d03201d4045a03075000210b0481d1401103d031405460b4591181d0f5001801d43e000944c3c204001c0c2070f103a0410a070004807590355800c40b41c01d4031001e07080003d0300308902d0aa0f810f07000d810301000000c0d24481300140840c0549000d10781d6124180b40840641030410107807d8200340081c040c3c201c20b180c02c00110ba8032543c590400d50005a0010b00c00c01c02da2030611610040d50406005040c03003550041e24680115040582e81d44006103a100801026441c070100e0349607010840007200b04031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 973622401 1250 973621151 973621223
    0x30c0d020106090c0809062809030c0b100510030902040225050c10020c0f0604080d051b0c0604140d14030c10060e27060c072603060d 59
    0xc00e151015030030881d50440311301c13410440c1000801502c0301c1c00161080d0400108840d0540c04009140300b0600080030082c0d11404a08144084080c1680f0281c00da1307a0301d0051404550503215914803003d20302d01c2d4801c0035086048003603c503600c0340c0280e1044110b240003810140c680b803148001109018042411704080b058850100c00034482c1c10481c02c60300c2e40054500c40301c168007100001c3e61b2942085100d81c400c1014110003659600c1e04015200100a000100c907045128030b00050f0454012540e008424480e200ca402c100900020303000c2d1044e00090040b0f4545420258042840820100050340100c00c503032011700050008400c3d8114000080043d540b1850304410f0581042014480001481d0500900384490518035903880c3d00b005141b1400181d400080c0a0011246800384140015024050410030f0001d8108024403005110348540c0500800d0300c441483c4081c4200c103c0c2e494018180002103250419024051526000c2d00d003013141304900402c24090400c0300c10042d000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 973623651 1250 973622401 973622411
    0x30c0d0303090b25080c04090e0703060e012f03011202040212090f0c09010f0506131a1c05070c03051602031c091203020604030c030912060b03070b1c020903030c0d0201 74
    0x1000c00030301c0c8107000c1c000c585411211740c20121071303100003801a8050101d900b03944444050081c0d004020900055034080014464030004418a600030200700252030030344d05012441100c044000842640c0403141e01c00030905590801c85152203d00014804982050742040f05800c1044800601441405108011321100002c80390141c01c014905550502402c0500010700c2110a20510f42040c0e40c8151080e41d29181c035031441c2c00280126078481610780d26075403502d054050200006001190910801d0701c6480ca64150302800c4880444406001405181a445c0024407460041c07500c140d015150100421040d00002e0070300c000b02400c011013000d054050010700e60400c00d140001e002c950030745c1400c0f1806450103929400300500081c02c21282e0980c803030400d40140350352005800c2a52200d0f41030065172510800411055103130600c203210b000c100144894151007101c01c1e50145050800301411501060780281d000703441143d0340b501081c40103c1d00050304008103202040e84d039002040f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 973624901 1250 973623651 973623691
    0x601090b0a050322151a19051c080301080a020a050901141504090c020322120308070c0c060c0605090706020709020f0d0c080a0e03040b0a180506040f03030905060306030c0d0303090b 80
    0x40d0f00d030f01b1000ba800740b02e5030004005c1005900e40304004664003a0707102c0700761401c106602800c403880904001c0c4100d20100c00400c00c030b1000246400c41c00e200b62411601161603004200141809100342d254075000b020901d03880d800c00129950307008502000041c24181c40703144100c00e0720000410607005900108d640800d56101c1da0500c2030b23081002c0e207465075240c1030618685501c00c14000240501032032001017990540301e80420b4540c50b40001030344c84003a072106001000c03034040070000d0342c040c2e050001083c030700750f0041010301c1204c4450b00144a030038508241c1c40007a410502054580d808140302151691500d03000b8450354940f203590300f403a18508006000119000c444007044a540140b20a101d078081e0402262840d0a03075061072113922455007800221048541c10540c5c010401040000d403c800c0107210301d06407403081d03d506160907252410300c0268003080301d10a90603400710765001d009041809440e102c2c58003070328010a5031103268072000458607060f607001d80d1401400d80118 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 973626151 1250 973624901 973624931
    0x18021c020a0b09130204030201050426060f042f010e0303070605070507050f030301030c030b0603010b0307060816170f090312070c030f0206060109051e15030601090b0a05032215 78
    0x2444d815510701c42181894250b40000b400c41c0154040c4400d482c0105100380d007a090442d44201c1900504c0301220340030f00c0d04140d82c5590380c0e01520100c42070741403140e00f12500200811a605088190280080c41c448400d004448002224200300c3c0c06010030815007001c9042401603600c030b0460361303c4071a42c07240c25140a0f881d003400c03e488620f450300103000520016007440700010841c2e400c05502025611100002401000ba0940b140d03410303c42c82e0b0740003651035000702c0454454140e0010340700c80780c610b100c0d007501c0540c0e003440c0b44038240349441d0005400d0310802003a9600a02c10b8411207041c5441e03003006e01c010000c2518540c000c206004000c004060344405c902c0613585562001d42002d043c0180040e113010b13030324050340344924904070340100302e44500300d0101000c1100070056211065850410126a4000d5402034005400c0b800082040a00301c800c503600340c04107036145403441d0b0700e074180300a1142c40616041030064441c89504040740342e081804591514581c000108159802080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 973627401 1250 973626151 973626169
    0x1e040507060912080319020c01090c0306150605030c0706021b060a062112030b030a0b1b07080307030c0c140d08090f121809040b040c0918021c020a0b09 67
    0x1146040c824192840080d0f200020b486d041281c0486c07113030900042c0342010000c1d008082d0399501561a000499007480440d00520003201d0003075404104c0640005407040ca008040d000f52004900c040005ca4440320340280202a640d000d00d200605000c031582a64421b44840608158150700460078820202d54503c15130740104200c041741610400d42c010a940001e07001c2d10081d144035000e61640d040240070750040c9031100e20060030303900e40c100c0c24545034512130001c0d240d0700ba211010407000820f00405904580c0a10307044180c490856560a804030050841480304804209111b0214800651524107104002c038420004d010b1341014140000e0200500400b90540396102e404803441040c0081044c0f4000000600c009581d4107040c2000d10500702c9244050b5004030504041100f8015944447ca00551094080c00b0705241d46079101e4090764a0f20300110f41130503010f829580189031042d09102210111400c1c13070f410f401d142c0c001900042d065801400c1c02400010102210714010141c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 973628651 1250 973627401 973627409
    0x12020409060c02033f0712021b21042304091505072f0c030a060c021005060f06160b040302160f18051b0c100605040519051e0405070609 60
    0x1002ca4a44180c0c0300401c05c0b207002c200000c96020359100400c203510f10a00585903a602c0c0c0203800c1d50f403038614400f1800060400d0072800070500807040708020300ca101c83c4c2c3e0300c0b49001504101d81d05050602c2c4201107101c0744002030075201c0c00c66005a8403aa1202d0042c041074030300500b410304c222517400761000141d420061005081204820a106c07041094407840d48400074064611042900c002a5952510103804c00040d03040c0f050041c02d0007048016007005c00341d01060313030a80d41c2100c032010f82c8009a880c1590030950004804103000142e0500030042c0100131543d01040b08081069103880d80c10b180d081d241540140c00c84040e504610070410a00030083c00c0782d081300b00c8400c0c6040c080031703d040d4485525500050700c90001c62102c282040f154110400f2507203400c1d6480020041071580c40082c14a144051030801c3c100080501c0c0511070b0b90f125040c010030094502400c110002c0040c00c00500d654280f800c000d0b10580c4801104811501c075038480c90040075607c0c1019030160640c0d0050784 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 973629901 1250 973628651 973628707
    0x6060306050f0a060809151321050403110a0b07060e0d0e030a0f02041409010614060f1914071b050d08040306050405190b070305100f12020409060c0203 67
    0x2590082c035840310703070400b41241c04918009085071a62601c1904001c1c584100c0c402501c8100309100501c401088442941031060062103803540e4a481e6600211040805480225805010401c00b00b900c80340c02c2c3c0c1c00d01400418040c541900c844542101f074115840c1569010368480103d82d124404003c90504550384dc140031542d913402c1c01c00660350703140a1030300400c0d8921080d0041c00b1515190000302161035511941807051805032206402044127103c0e0891200741c88509c00300e83d06042003203801000082c404185009490b1501c4003000c03440d480c042042080c0380b00c0b521400c00c1c0d41c9002e888400d1180890403081001d6401005ca000398640060740310300040e6900c00001080c81d02103030304495200d074012800741d4413818207600380030002094441d0211200090010080440c60f91440b030340d801c1e2002c000c1c07516501840040440f580c00f0308c0c100f03441154428010341120402121045100802c041a4003941c1c0d5034040659203040c5030040981d102207960902488203801040803449041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 973631151 1250 973629901 973629919
    0x3315120e0127080c031b0c0405151e040510050a050405070c0f080d050f011d0108030318010209100207030c1403070603180b07180b030115030b03031c0606030605 71
    0x100a01c0301102001c500c0782c80c080080e400c4841080b80c280b0030b46040070b84040543c0d13100d41d00c0c0c4800400d005202e08104003a800b8840505481d407403e481800d009117607040f0380c0710995881005001c420742008111070600b030001c1108100640e20b6000d454400c5a59001d0007440901c1c0c64240094401c40d40c203e41e10a40c200801c110b41e03654404040010103400c012850f80141803400c2084240c45203074680e076030150600b802c01c00c021148080c0345040740c00c00113403070340420341024107840c404900303000d100701e01e801c2040426400040a2030003100d00381c440000501e37000c4420000b44c10145155107410141c2c1101400300240886034040000424004515050800300600046c3c5c0707840d200c2c001e0400340b66444c070407a0001c0c5071000c1c40c07022943c4d00001d034240c14102458098502170145400c3c0c24032003280000440c40c0d8812005881c101d50340c445c03005070303200d00048041c3c2c0581510012103400d448244040224200781940035007007982402c8000a003d801d00100a040c3d03940d6400060103001c1c84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 973632401 1250 973631151 973631171
    0xc070f08190314042d08130501301d06010e06031c030f0906050f09010c0e06040e0405031e04080d110d0c02010e03030c150a3315120e01 60
    0x4100c044d84207901081d88041c0344000d07008014030f00071903000001d100814a0001c42000380341001880c115500600e001074070faa840780111402c1d0100307080880c401250760b0304103503140b004400d20b840701e002c1e040011400034076200700c440000b600000703a031805070b1007400100070070b0002c4041103070021420b0f0007070141d411121601e1460180c209002404140d03a86501c40c5070703400306a00204020b03902c80f405102d01d04120111803081803060383c2c690b080b035103400e042c151103d000703080c03440c41c0407005458503050a00d410500d0103000d00003401603440b80000c100c400045441e0406881e98a00b06c610030b191031324144950703503140010f00701c100018401841503103c0c000d500002c22540845991a001011506610048641c407540e000c205800d4030000c01d40d07583c41c8001040c0c01240014220b00701071556940104070b0151065800c41181380303450f0406003150440301e84000c0c1e0f200140b0140e038003c6a641c4204070074480e410320f141e1400090070042426140500e6024074000c8c450254000c1c4080c20103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 973633651 1250 973632401 973632431
    0x909060a061b030504171c0807091e08010213030302060601090506040e090c1e040506060403020a060503040f05070f06022b0f0c020307090b0909070803120c070f081903 74
    0x10390308500c4a42e2204140c0b04101031051045a0207040c0c03110107002803c0803c0d001c0c1d0341d61a4082d40081c0243c0b541c010355002603100f407118a03c501e43c15074801d0150b91038403e101114219040895006054007000402c41d81400d00081100701c1115164480051a5080090420402821581c1041b503480000c000b10350380d01d01a94142c1d58503a02424036078640341d0349640750810801c026600946c580170301b4070020548800381c13019248255014401540c070081004864461804020f50001e5a01d00511440c0d20030006180c1c880d1042e001c403012483c081e02c0740d915100f40c9074410300213003880401c14802e15606000000001440840e07128a411910079080d84051ba0608440c2c100321000c030700203062620078030042019a03006800d4450b01500c0d8010030001d40514110180902d11400c0881d06040b400200314080351600d20107942400e0440400140040b009403411480100a10102010582040340000d1580c40b84550942d6402d8504070301c00300c400c41d11568000d0610b403524050350320070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 973634901 1250 973633651 973633667
    0x2040c0e120c01120b041506051b0610120f0602030115121811031002040914160c02040f020702040f0f0e010b030a11010c08120a0f0b061b0f010c050909060a06 70
    0x100200c4045000c03100400440c000f007842d20b61038907100d011f490000440d10b0300907005040410034101c800103070354503080e400d503551242510501a20288094100604c1c1ea8503078038a45814400ca06050650003943c0314202680c00a811840f292443c04110380c04954004444031500341e00054240904d10441c61503d131401c081c00006445040c401c1c00742e40c4a80e405001c442e071468960f850031500c4907202d0401c2e200a0050001c00c01c0740c00c1c008000314500d000308400c11034000e5102d43e240120900b02c0d50a00010740940c41c1d40f9114633800384003c0300140e40714051000c10b56041e04000030074020220003a801d031003011002001c56450407800c503c0c40c1d100414010f524503001042d03440c081030140e0040307442d60740780384018020140214581c150b150f2002a51400b0f0424458240495000403009404840c021398a943d4082000c0014070000c4c90030355007043c1c02c50707040c80699480c0400141e0707140c01c0d42c200d50420000036070001a0700d0703030914010a81c2d6800000c155614100ba50070514081c180350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 973636151 1250 973634901 973634927
    0x80705070b0907120b04021c120e030c0d0302060714040b040521010204030c080d030c1d01170a060e0c040b09061c140105030f060f010506130302040c0e120c01 70
    0x184000d00003942181c0400c0f10f400100f100c0d10a50100420500f42443c00031000c0d030301284294050001801100d28880d9141007542d001100078003c4c1c68213003415140f180450001d0358050040b400d54192a81d00c01084003c401e000b034001c1c068503c0c0040d0001c0220b869503a041c0004a0284810b0110b03012400c06d90b03042d583c0c01d80304c60381401c0350720981c4000b440c0000b9991219600000d0040304103d0080482c10486080c0012100f005001c0d0a064082d41c0950884000140301e0a4420400c01007418200d5550201030410080100300540040003810301128402c103005e407070380010403018a804600c04d60000015648034101420b00040000c24402da041d4184100804101910000321a4030102c1112070482d804226468248007007141245003440703158824000d01030400103113100414018462603030b440c600501d903804d200821440d038115083c1401d1161f24040080016281c921070304a0358003058071003071558541403007007060105084461680d590004010381c04141d030000c100c110302c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 973637401 1250 973636151 973636163
    0x50c060d0603020916110303190914060916080c030613080f040f030312020c0a02010f090e010f08010b0d05060601031a210f210d0b060d0b030d08070507 67
    0x242000e015188003400701504060f44c098022414000080c11032181c601c41c40760f040e240e25400005200880d40c4a00044400d944199140c3c80e00651048083c0c0c054505a407141c45120600c240c24108039180403021282d00259070700c0001c00c0c9404900e500c03103000040c4901070042c802c140402c004240c80b50405032804010303003103440c2c0368002c01c03515009544441e030a80300810f40b20761303591142000303103000c621041d0042000c44400c11405105130003115401c111480041074030f4450350780115460018038084c1000c011442001045044404a4081c0244140381d80181d2460800c2a42c5084448120a00703118400b14040b02001034000301d00b160303122009003030000cac0641561008200000208211035030145a54a009416245a60404400d041500100d448000070b4182841d55407100174080c4a00e102007440c0316540c00c480c01c0080865400c04e0382c0200707800d40204045802074000b0042d2028a507140d0311480b481e0f082c00c02c50b00c0010340e03181c6010b140c2810402409421407181403030191017 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 973638651 1250 973637401 973637407
    0xa08120601020c0d0b060a0f14100e0d060b03070902120109090602070b2a0901051611030f060103212007080607030f0e0a02090f040606050303070807110a03050c06 72
    0x8030340c0c02404109043c50028103401001e10b00c03440e1a4200300022035585128007900d4101080d111820400b0909442c589130302641c140c1040400c100e400100c8030f000c2c504002c40c4016080c41515402454050346100b44004540d0038950000c00d41000107030b03000f0500092043c02508060131204510700d045803c1e032140010425003d0500c40c019220352880a4814130f42181800109a00e40c0c0d401c04803500c0f03550000303110005011100109108201c2c0d26400540c003484000e02070b56100c040c0c210078a2160158000400c1e40d080824101134010280d8911a040b0200410501022810482201b403c2a4564488208a402c0a401d40030610400240c1e88403242030500905010051140600310804c02c644031803402d91030050107030000002103042c0509106201000f1080010302100c03082d4000c08034100c80e03a8070706000c503000c040200705031003079a02d40d140045c2d541c600740b004100142c007944000f0b0f600e410b5401c0c0842c02d5018600c0c000c2c0540b070780710420008100701066181c803095080ba5413039a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 973639901 1250 973638651 973638661
    0x51c1b0e0907091a2b0b03070b090f0a030b0403080403020d050915030402220b0f12060c0906070605070c03082d100b0c1005060a030b01030609060e0105041407080a0812 74
    0x1080d8010b10000560900f200c2d1401000040560030170500c00310741d034506000703290280051507151522440348000000040c8100e041380d207001403d4440b07040c1d0190400190650760b03207952800b110140c609802041110080c041455030520101a5209260505602e0801018003142c100585c5480e2909000c101201141c215900c400900c000f94000401482010301c3c07100c00308000300804441188641d0156034841b1040c01c0c15040c24900c200f040c0050843c942d1841d03203007120b130327480b9000d2705510000800c5108001841031003591b0090058ad600c80c5000c0d40c2a00c0c020302841405041c410302c6086604400018580f110210004108910822200d940325500700c400c00203c581c101c4000801c000c600034030800000919138101000001051000c0c2d2030349024041a801107000103402c2288400c01800070401135000140300500c114400550150034000305401c441050f41d04072588840c0c2d0072100c0420608000d1803000e410301c0d1000c5d0801c4451903841e014140b1074590341444241440000030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 973641151 1250 973639901 973639949
    0x1150f030b0607050124030804150908030c031e2502040b0a080616031107030507020616061a100c02090421080f0c070210051c1b0e090709 61
    0x1d034524006402151580c24620f402070203071500c804030210400107443c1881e10103030002c10075001c90f604000e49034641810030030458030800017104d1b1801031202c2c4c0d2030300042ea403604000800300001518041c0d920340300a442d21502421040fa0440c2000c030007031003981003240b01807180820319030f080800300c0c403c1c00c51071000c03070040d2100642080d8801003401c400188118040362951041907210300003920030250540a07011590110344c407800002060243c80002070041c0300400c08940010b14540c1820170000c0140109880d1510854549840385501061280400d0344800c0c0d00804403418005850401c40040544401060280c03158031410045804c4c0200e42c091001400718640c2d0300586419810b102808400080c0c0d048040354508400098101c401c040070340d120986e004004103024030744424201c496070004c0c0d40101c02c038400e1041c1c106074021030b8400c01c01100088008011203c10211000c1c000300c0268200c00e00444c00c810402c02c5007507002d840f040540307002030b00752203a05262001013 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 973642401 1250 973641151 973641161
    0x2160f060801290315010201050c12070f0c05010c260420060706020c010522020a0e070210061e120b0604020a1101020705060114060a090314010207020303042c01150f03 74
    0x242e0000c2c400002d00c1004204150290017902081e0028405070325080076080d1b00344540c4200c03400224100002c200c500d03114203200e20910300546400e04511031562121421034201e0485600890003000200300e2003881045804100c2e51a40c00b003a2035841c10780ca5124004e600700c05556058004251784207441c0d680e02c0c1c1036079182c0d41c103d1411901d962681c00d61030b0003802d05070b0700025844d0b48d005000c2c0c140e00025a01340742c3c00b42d000c2c110300c5a00c5e00d000b1241c0c4119401810701c5066015248950080c203009103e0b660080000801c82035640e0004161403030713a19a0303900190300540600c21040041410003142c5604000b042c1d8006a80d48901d150465265405440c00070b400e500000e001c10502c4400103003035060f01c89020088030300811140070040c0754480c0c0e600440104150940800104083e080c0e4800b054408200151803d082540040d003164801d0708160202084640551500c003d01c10170a1080b1843c02003403d800e5041c00f412820b290b40e4004244c042140101c21213141c00e10a401c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 973643651 1250 973642401 973642469
    0x80717060f2107030303060b031306020310050d0f150606020c0d0c150801090506180a0902030712030305090111040503070311040f06030b06181311030304120302160f060801 76
    0x500e065003550340c44070b03079100d00c958441175000070706111020400c40c640350308403802442c038000e5a94440c44070307a85d8240039400040580c002000405000070b800e40f6050b081480d020721a0910b02c1314104949003c402c0030181c801c9507006646411403d101007900090001040881242c501103404d0701d0740b9009a103003d55802c49612a88065410301d8460341080301e480c182c54141c00c0c180704a9444006000541c80080e1071b20b41001800c20100388a0111a4020011180043c055804aa072114800c2d10341c0820800200d0001c1d503520304000d0007440a10580001d6102c42060701e14191400340000c0e0748207a40e0101601e0a42c5c41800d0790201e0307031160322440c10318414500501940382c0e20300f002d00c0301c03110440f001802560484001c1008158100e5054131070044003007842a0012503031200615816a14602c03500352004100210b144400201c1c0a414a4880c0d0b000313003403000c00f0399441309003203640d1380c08040300c002404014000f594203c004e1034192503260440c8075507203581c200e600003028000c90b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 973644901 1250 973643651 973643689
    0xf060c0307080a0f2304050f120105180609120f2b0c080604050f01140a030f1b0e06011e03150905011a090f0904240903080717060f 58
    0x41242010fa0840324900702d08620780c40b0107031030000355100c0744917a6803080c044201c00030702000240543e2400c841200007100d80908984c0c0a8689145280c3c04c41b202520031081040701210f1000742c0c0300b07007082001e51003507454018140d59012558410228096581d082100c050080b41039620b501c000079050000d41010342c10701c0441e50351100f00100800b401402e540c0003c4014000889504281c020709020300e0140300c060003030740e10308840250001c00c052035883d804140000700102060a40e882a4103c0d801918440d070421313000d107a5200220b00304d0344102c5a501500040044980c0c01a80e1040c040482d86800d403d5154074038001c90060081c2003600c800c15603048000304d110100b07a4401c1e4180d86048a101d8460048031324140034900503c0c5503141e21848850851810f070514914413904544194805840440c1e0444d01c0441c44804581081c1802d03600c901100c00c0c560320249080c0c1000550030500911000b140c0302030344a000040c02c043c001d060b0715220302c01c15110007851510071a861a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 973646151 1250 973644901 973644907
    0x30a0e06070c03082a1b01030902060d021207020a0305030c03041a04050a0c29131d15041a012106230f030604030f0516050c100e0f060c030708 63
    0xb242903c00d40d00880d079141c907880040340340c0035400c0505d58075002c20070b000175000703080c0000c1c00000301d00508000120035040548075800c030001a101c51000d8104442d46a1000d602e484c110150801c14020044c40314046600c221105c0e4082a0028102e907040b400304403100e591b030359950600c5d1201a24011001c0c0c41c00e0080410041030000109104d40303014414002184a035a480d800c03124200383c2ca0461852440d510840d0060310f0801c00020403105062441c0c0b0460b00d9542c00e45195201c10b01080340e60549244410400040c0120714403e0032030718112020840600a41980141c00300a190242e0520a0720900b1310030b00c21000300400141c0c076602005000098607803841c000111142000d8041e42c5034820035040c0245004c041481c901c00d0082e0040403030b0380c1d907a1011140204288500b5050280800c43c01c120f1503018464a0b0116000d0b200508a11611905100d038060031604090104aa12042c07040140c2d502c0d08886540042143c6040e01e60f21a16035040c114810500000d1200f0400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 973647401 1250 973646151 973646153
    0xb0904060b0c101a010e0d060e03070309032d020d0f0210031a372c060405010810091a07020c0a1a0307030c170a05180a05030a0e06070c03 61
    0x40f0695800001481031210034400c0a140c0d0441480518440c0802c0c444d449102031400c203401c0342003415004802c0440e1041c2c0c01c01d4228110352011344140d000a8000400384140700f02800e0030f00103080e01c80d2944014580c4800039000f0f00c4402c84000348910900364041040c02a421482220144c0041000c010700182090150051100702c1d20441070350294180559186400550b001403070b0220b10000b60a034481c10541e48000400748000804101810b4000c100c016596010b20715100440240c04440300b00c0c2c80e1088580380740140f10f103204500341001444a00740100c0c1e810302d221202e030b1010451100380d01d00090a4086154200c940b4000740080058040c0d00181041120000741e40d080800e5480d0480b40a41100c445002500c2400c1000815001c512980c014909070007546030480d4041d03c0010810740488007620007260642d1030350140840c032803401420b201e00d00c0c0c2c584000d10240000d540c03129200d000c2c0160b01001d10200d8100c09405885650448501c1039001010695581d02e03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 973648651 1250 973647401 973647403
    0xf02190f0f050904050a0615030c06090e010506190f0504030605040f06050f1003030810050d1a090706090312111603030311090d0b180d030912180b0904060b0c 70
    0x440c400d0030a54518200c000582d810b048040ca801181c001028000180c107035202d510207455091f032070080a9600c8200040421500700c2060042c2800f603891415251801c8604406131506070001c3d4403c8004000310f1030400c998440311580340c8060704000b02c05c858045010346081c05640c1c405001181440c04200c00c1010300301c6140c181610608040100d51100d0140ca0303c0b0420882d100a44841c04e1036040c030100303004000080c0c1c000c0c0c1190030100050740b0b80d40807600541c0c0040c0d00b100c2040a091000031070b8400e80000035400880040249645890540010445902480b01504a4082034050307000039200302401c8407103480c04c900300c0c0c889104600d1204803c0c045031100b80c001910b05504190311500072000c50310b541030004e11510800d5015140d500362050081c01440e00c2d514070f420320101115007800150004d2041e61400140d0b80d1040c1808200000b111141c00208528410700c41d26900822251406481c00040c010b52120f0842010800402d0180c0110107203035004100c403201d000e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 973649901 1250 973648651 973648679
    0xc03060b0d020c070f0506180d120203090901051f0e130905060708011d0c03090f0601060f110604051f09020301050c0405040b04090c060f0504030c0314060708060303070f0219 77
    0x8880f44955200d00680003001035000d8187d100c1e200300800340d002600d520050080e0a8000c00f0000600059552864410416440070300540c00101e050300152501926060040c041560902c00c107801240221503450650341c1218180000e44206a80b55268100030900100c6699000c211142c801d042c01c50741d440e0708552240003d1140b078008a0b04a00030406202c98101070000503445407074140341500701d500010003034a914490a00f0066881100b04451402801942c443c084214491070008002c040f0940410b1130981c0300400b808000b500005660492202d00720b48000303d501440c030804044d141880e0b000e0751546c2068103021058000800410803690125010882603840c00244015621069000362048100200070082c0e1400f41c00e0321006a440e900d4014641a10b07541e0700c000501302c40e0004e03900312040c4512103011100410880750400001e0404008628201000076a00c1c4201d54004024a80003c181c01c210741b9031040e100040b8501840f038010454030765400c0c1e03121764 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 973651151 1250 973649901 973649917
    0x7030921050607020a03050f0a030f0f2009090f090f010204150905031507140c070902091c260d0e060405010c0302090108060904170307020102070b16120c03060b0d02 73
    0x101400021443c40c0d400000d82c04003142e4103031501400d0451a8250000c190400000300060540350304240c5e2028410f8410161340300c0462000180b43c0111480c4215040c018072500c1c00205800c1220244c04c0e610003101560000140c44070000030f40e40c0714295820804030300a808440e60000c030b40415418107070500b45440f6892661a05950b550301d03810180d0b10114100b0f86070b90480810040f6800c03512403e640c83c072101c0c100e58414a042400c1018901e030a089501c105001d07235021420b00060b14260096228000342a840c0308038002941d181d0782c00b000d0b0350700605e0040124020800c07070304840f0581a1458562000030803c402e12891041a071641c4085900b01c416506e0031200520280c024400c0c7c500104040c0e41e4414540da440092000380c2001400c140d60120000012a00101c40c503030045200c1c02981c0e00141c1c0b1851180340c40c520700000940b40000301d00f00a1310f40800d83c0c0e848070204910211061010401018242c416002040c09401406080720b0014204044040c01d4000300400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 973652401 1250 973651151 973651153
    0xd1d030d0506010c4404031b05030d030e010b121f0e07050f03010b060316171603050718080c130506030303131e06091a16050703092105 60
    0x603a50302d0011541e00c0050a8004c00b103210b002c492041c0c0c81203c44d041c41c8104000b0b610044078068000690b01140100c0c17104640700711000805204101042c504c035a540e01040f086101c00e00d04010011744c4428290a84104160350307a10215910301d42504600c04508014281c5840720f40524040c503103c1101d100c18411241d80710140c8030400e07885205551001034140040c1540381d06090410aa01d50550212581503403581601c6101d41d5401004600803450405040c0c110b4240f62000b1b072030a0000c14a244003120140100a61102c80c4020f080c8517029034a800200c43e40c410105540003404009800202e070502a00840d0305040000c0309501d50408480c4080030f4a640440071040e59421600709405410610104507440e8404641001c000e208105448000c203000c42c0320810343c000030f04182c400c00d40340d440440c180300340d5000b5021000e1000200524030718042c18003c0809005600400c200b001c00201e680c203052080107110060280f01c070f01e661b0342c1e00c004c041400a481140d0016119 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 973653651 1250 973652401 973652411
    0x30f060b0d0804140607080c16090603050c01032f2203050a0f021201020307120c050313030503100e010b0306010206070c0c0e1e07090801060602010c0e060d1d030d 72
    0x50700d0044622590307103038071000d010701e043d080054203040e00105540369600203005008100005501d10003510494400c000203001c405182213072041019683d502c80c00e5018074005003400811400302d05104903c80c28240805d0250101809107690710a040304007400360300b1580100c01025601c402081aa19010f40340342c43c0307101601050400482902c00100694441c000120001e040c0d40030003410180001e10f102c0c800300e860082030342640d1040b102040041c1c01544101c21004042c419100782090358030f00740c1d04510342007501c07412502141c04042c003401008400038140e8101000b82c08040c042035040301c4883c0d65a20580c90719608285e170141d015001384d80010302481d21036824041c0c0d07240c001c0e507200030031460303c48084a88d95014240400041e6803200080501244520283c007a00060780c980786594680280349013120308582050046906141c000314020b5400304020161050403038003e541d440110700404001d004402002000101d020640d180504021000e40003c110641c02400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 973654901 1250 973653651 973653671
    0xb0106020706050c060105040513050a06152c06060912060f09030703081506192102031014040e0703030c0b0901020325210606030f0b0a0e1906030f06 66
    0x83c2d14014400030360030507440980108068030b801d030400c9800042c5040ca40c84440c1c1240c41e401c0c00c000520409641c40e81d00c03840c50001c00015180d80380002d095484880350405a1000a402c400c0401644c1841c0c0ca07044101080b800e9688104580300004028064400f002c074002a01d9181c02048803044840c40c2c5400009020080c044100d801e0300e9455070b50070190359101283c60303040e02e00039200c1b5908170109200310004141100011a048020f5441d096042d110302e06020b40d00c8032055841c0301406005000b448030051a090f0307080c003511440240c5d640003c82140c0405d0080801d10b00ca0403991184940002c02e06412450342107000b4050b143d4501c45c2d9440b206800d003070740b0007903800800114107000d03004c01580004800d07200840303907444d0040d44c3d40041c0100b04016810f950300c1c6524581d403000200702d400e415100c1c1400c0300c140130200740503140b66000051004889d41c450001200c9642c00060138420400c07040003890f0f81f204004000d225181c4c00c01e400302403443c280c110384032498459004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 973656151 1250 973654901 973654907
    0x55a07080c0409030e010f030b1e0405060109050f0f0312030a090c0b070804030647010e030309190e07020703020405013302010603081902010501060f1211040b070b0106020706 77
    0x30564245c0c41d0707a0306501400c00111001491085031008143d034808641c8826500c0250300f0030214242040d18410b8852103040000b10703040030f440141071003d082c10800c01ca88400304180340e200710445d903000b40100b0b6400400d00b400c041d20711180c402d41c000020411340d800399030302003c0d04d40d001c4d00f0401c074078075110f03210f1600d40d100321780f000f0f00204824001000001c4c4650442d41104c554030000e403010010340303440d001c0065881c540c107003004603110982d0100b10141c42002d6550f05024a04070b50340e81c1031100070940764450201ca89006082019454040d030901b1072090005200e2030321807800d00e250840000703440340e40c00e000c1284603504110001400c504150270380444003101d8401800d44a01030348268200e94107005007c0b0075952524400000b040700704014002c5940e4402d003d000c04e0220a00090071118141c00c04c42c180054912004a40d0398024072a4062786e08091000680200510241e01580541d60110607081c0000131100204840031043d00c0c101e58240d001c0326030007a00d4103803d07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 973657401 1250 973656151 973656161
    0x909010615090315020f12161e0503010528150906030606051c06080307030504080106091b030506150a03020a0909060605070b04020d080f0304055a07080c04 69
    0xb03086a51940c0050f11184074681c000c044c4540100c00d40c034505020086a8030347e044041b162140455070145078603032260b0f04405044a0025084003036222800510702c0501719010601446000d0248030851401e4420b5480294600306100b0301c801c00ba031655440b0054400e4901c64441e0300243c0d980100180e140c0c007900811054900503180c07541066142003560041d5502a00080721a9464620002d8090b50904c0203101e118061341d81c2a07551420109a076094034810740c01114414a001802c0c1459080704261100715815840c2c04150350303c450380014031081c2d0305446080903903000104100e0554069000b010f002f4070507241d0005041d6034040a4003200c40d2441084007080040114030700281150106c0703640640300418482100b19a42c48003401504002c4000ca5407000020600040c0801000070f0381204440d100c00c002040c401c031a043c01882402c11100000140b190141820120301e01c1c1c50300c4101e85640d41c8c010380000170361030007a99441c0c2486202039078014640c1000711790a050041c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 973658651 1250 973657401 973657403
    0xb010807090b0c0a1b140303070803040813180203150d0201020d0c080d060305010e0712021311120405030904200f030606071401052d0c0a05070209090106150903 71
    0xc1d194120301e0500882d00540c021840c0c59043d02802e20f002000a41e004a000500803030340c0d030200c03203140c18180080d1690f181c0c09440c2e4030039030042c0900400920740c141140e602a0340030007880c1e1a120400d68500301d000c41500550751003803804d141d58a00040300d50286105103251406c1c4206e4854000a000001c00403c1011b030061b0411000310a02e03d02461f008101c05104030390452912000210940444149400440d05651a10310071a0f0b80c2c0010881040500006444c400f0200500d03400030302d80100d1144248003040c1c59455481c1191243e1003a42d20700d8000440a4401e0303d06441c20a403a9400b02e003241d4810351030080c081404c1e154941500e182d0581d40060140741028444000340c0715000203111030781c084002c01100e80000d00320035007060b040c10074130b0012809082c2100300841121451014101e000c0b80c80e007034400420b15030100e00350080c0641c2c3c00d0703d50b00d030031003e02211035204d010300c040d42202010341440400b020560100040714607600707407404210704d1280211620161440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 973659901 1250 973658651 973658657
    0x19050c03070e191a03090d141909030f110a060906050d0207050a17030a1d0a030e191205070504090b040b2a090f04060f1802070f0c0303030b010807 65
    0x140346400d1405a6524901d1000c02c0c10f4020740d0b480409024000f40364415245500002c0280003510070200b00d6420b04426034200110b081c03401040c41a9180600c884246c0480007840040c42100d00650b4244003441c0c0080d41d44000305082e04000300262001d24126000c1c010b0440000341892240e9856407d440c01c90352020310703047e402e003207000107500320142c240d03050f005880602001074070440c80513845600303100c1e1417901c0345014958a81140c0c0c3d601110000c0102c4113801802a21005c15010540c551604007840390381800d80c08559101c0507001f50608503000e54501141c4441500040b00301d03244540b04440e00c454440c2d05007c00c0d01d4441c2001010500c0d000c010400140d9050803103a40040c8400349504400e65141a5500403146903541c80f0001200260700f03049818550100d14000c107050f602440b07041d01e000f004101206c01807085042802c850440b104121303410340c04840c2070b150001c0b0448240c0304607040284428400d41320450129240a443d50043e501036080313141b00380050f803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 973661151 1250 973659901 973659917
    0x41202120714040902060904090308040618020a03021905090a060305010e070308070210021c050909070c0b0a0c0509060c0c0307060804202d10140421050619050c0307 73
    0x140301c090140200206d90000041c007440c003076511507200b290070841c065518019541410f0411104803403e40110240d204142d452440158460715021411a40d054850703020071000c001075004400300f10740005070705c02a0141030010007101c94005106482c044d4000304244441b8030000b640d00c6c0d200d4400140310322424407070200940303021581082e840300140180c45020900e15210700d00c0c040e031480c003c40031070000311b1503007410b051114016130b05c02c100d410994603018860b2184845860001c10b50002c41d07071101a0104440d02c100140c4014407009040241c0310700589028548039107005624070701030712860b0800a401072158520780d0045800c40403001c00340e01c502c60b26031250851405000c1e0489411444d184500c00036030710121211101400a554911510f03007048035140c0840b8144d010800713007030540360038440c1c014110750481c4c100c0c2c485255001c24603000a05020040c2d140540039010710400c001d00100d498140180c00150700508203d1569a00c0320041a1b00059031000c000540c64 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 973662401 1250 973661151 973661189
    0x309060a020906040905040818010f0c1506030516030b1b1c02120412080105030111040e0402220b0406150815150a0302070b060d020d1b03080412021207 67
    0x394020100b400b0050801403405071140003400564105540450b45000c0c000391041600d00c800c51a00d80c14030742407030007905005902400a000b401c0c5810701604188441d481603e00811030340c42003004603449825204c00707546584515041c0074080c4003d0b0b88540041000902c8902107061269204144043c03050919525911000607004034001200207640e0820441c00d01204d4404424410380c484c01210603a03c0ba03620700102141410303170146d03001ea810322207009401c150800989055032440101c1c11004c0e0f46500000d01c4101c200000760590006000c5140e41c0402300340c000c1c00d41c09400303a9003072141740e55406481401980c5e8a8040002880c04070104006115810900c00f00c1c51008080b1045243e01c400080d203180d010718502008250b001881c00100410511600c1d80200110b0303881405100c19008500d000c1002007006064400082d86022035200740a5480082d40e00501d0341a101d81d201c80d5107060108110105034440c40303040e5009065a0400130f140e81c1920b1140304805030340845 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 973663651 1250 973662401 973662421
    0x90601080c01020303040b091005010803130e1302040513061d1b06040b0d062d0504090206191202040306050708241903060c03140c0c0316020102031e0d0f02030906 72
    0x1f000d814035840f40505c54140d1008001401801d004e440d032500510750b2000c03904101d1008015035489811915451001c00040843c0c4450480c09a5010740300421641ea40b0781c0c0c0c40c228102c40d0140280390610b010f20031540720000701e540da6209803287c0d00300c800010350007001c43c0c555900041c641e94801020001440203c241e03902030020660300072008510680c41d00c1140e081040c503564441381d03002c0070460f8640f4035010000c044009000603202001045890f4010885902c2101e0300705040854403003100f1200c030301c03800640520980150045480b0390710ba2070800c01901c0c0c1600c6560001d003103030780429240d0040844000780b800e000c2c0c141411000405090140601404140c1080300702c04100c0000810b005004e50403015003160382c0001c1204124655402c03440c406040b0b1042040d06010103038034031308000100c03103ca04401715040c0111503c3d200407072851080c0c41600b500c402070116060074100c00c81010b800c401441d000f0034002c2c0c0044501400890000700c400c204180d1040d070206a25101e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 973664901 1250 973663651 973663673
    0x170307020907030207030c0507180b01090305120703020a0b0a1407110604171b010506041107030f20030a1d01020a410c0f0d2006090a0905090601080c0102030304 71
    0x4400d01f003104c511021515428244032040e40161201c10048040c04031408080c410030041d0a0b013403c091009505585885588a02c8189050440000002c0c0c00040c07500030008000382e240c0c00b103503107201440c0035007004015000901e1510b0196403a140800c03e000e00468076200001200c08c0181940e60351911a0801307036104141c034024546c4100420304141e151240c081d80f56020700000030030942001024041254400c000300007607000103019a200280d4814040140c000381860003202025010644510300c101c1101d2803041403000051032900b5503006041001811072840150003200c10304801643c403a41019001400c402400b00c040c4104a078a03a0143d01c08591000700d401600c2d1039021445901d00c03603030307070810240d408a0f041004a00d404881c0c1f01450009480302c454003103165030345000709500c0140039801c0d03101c809005001c0e030301d81106554000b00020040ca0020ba03a48646500500c8181c0e0720002c0da000d41000031401c81d10005210060800c180d00441c5150b45030345070b00700503038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 973666151 1250 973664901 973664903
    0x120e010c0b22060b09070203040302060a0809010209040f0b033c190506090d0c0312020307020a0c090204290715150303050c011d06063106170307020907030207 70
    0x540c2c00303104003840c20140d1099072240c0c0d12a110000340c07203c0703042c200300c1c0148008080008640c0108400c0c40181c4401040d81d0240f043e904241070b03540c403410111030280c000c11764803680052604222003e00700c00b94000744842e040540a417103a0040501c5070300c000040d0300c60000306c00401d2040d002008081400311080c1d88403000c0030303074507901c601441c030014004080b001904c490307001c10b061142e140410f014116071003009062040c11142aa034014002880192954010940c0440010045402440b01003100c90340150300620041c0c6841d065002508a070040b00e6000140039142e0204034517411840c2c04d40b044010085050520968960500007002c0c0c51481a01e42c0b078102090480c0e0000030300c0d00c0514465125280c9801d49481181c1c02c6800321a242041c0d010384859800d0110000704610340c0101003600d1200400211000c1c0a00d09000d900c000580c4440102c882012003005174446010b8603c0020500102484211015980d00a0b01001f079401500000452140e5010b0b41c0100409 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 973667401 1250 973666151 973666171
    0x43050f040906090b0f010b0a1e170405060702120c0304030b0613090803071d0906190f1202100801060212130302060d09020901050312040314070b0a0c120e010c0b 71
    0xa805180e5a02080c1d43c1c01000840303651100409001080b152450300c140034144080b003032414800c620740001d108900718204980d02107001c403c4580200d105c0c01410714801c40114004107a420180303845a62000300701d90390340040c01101001c1d00321801c1a000c07a50030311014001581040d0542d10b42c00114000a021a503020f0880d561440b8a044039016802655004500307042e00d0345020500076040c041490842c2010705508000c41c0015500d2401e11030f082441680c8100000b868044241c582140c6a00030341c01c2c02c511020000f4603035108084142e00d082c401d90700400e0341c64485e001034900c0d003001e0141070096000780f84440c0810442c074001c1c2505040e52146500701d16a2074000c1030b290b034060503031480f001c0e456035005002d50400c0700c0000d004007019401098964407505454546000e2800002c24440c007481e4044446c2c40300300400d60290008816035955418031540241011030000c0c2c04075900c4034010071007006940a01000c035014081170311141c03410540f0341d50706004400d00070680141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 973668651 1250 973667401 973667411
    0x30605130506040605092b080f0606070f0524011404020301063f0b040e1b1203070b090607030c051806130305070f0e130201020d05070c030543050f04 66
    0x607d000c40d02071130029004a101241071441c2003800501040004015003030841e116424000781d51a2101102c40d403513000100805101a1450594100041680f41a000c17211009640d448103048200d158102d5801d041210358100d50b000600087e408248074850111b5590000451044101c0600952000305d0b20303580e00c02d5089450b45680310050490340c0c1605213035143c407940c1c8103050501ca4401e6445107040105042c00d4101c0015903240c0440c0700c0b560103101c0c0100104403501c01042070b03403442a0f0043d503203c040d02c2c141141d9652490129442c0b030020303003071044030814540100103c5035004451040506000845024840c403036000c000c10071103d050012001011510500c180006086e420607004099490000800b96090001e400c0f400c4c200b480742a0030700140c2e00066082c407131070f00508000c3d46480741030505a40030041c0c0d501c040c107540aa60012804016204a0301c503041884010510248410010741c00c039804007500903800030700b1144018010740c41c5c01d4070403590300c0d18000d0011507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 973669901 1250 973668651 973668673
    0x604060e0916170c2202030a0c080601111b010306030f0b06011701030b0127060605041a0f030708060a0305061303030606030c120e0309031204050f01020610030605040305090d030903060513050604060509 89
    0xc1241c0c8211150700003036070794005c9d91080070f90002220380c02500901e44100083c1d0f001507081e85410f540350943c081c0d0112416640540d07400b0740c00c110b00131038110060017040c42a6082500514200315001070000c0c91a1884040c1000032041e1941a243c0019040141d071782807110203060f1450268000800750319540034601e00e007459028020103040313141e540c00d07155498440001d80511941034950020354060107070314004e1503000e007580d60100b000e28060841c0d840e800c020648072010740c3c2000d002801102c0410460410381d0380250041807090f0750400205a441000b201291103039403801002440300c40c0c0140c084111508980c03008620902600c1c503210703003000028905445a0b0202c06101c2c0302082c10801d62400710b00ea00021f03103084c0050f00191804140340507a500c014040140019a02d40104040c10311410a480c0030b1036003c0d00440f8104110f044c041c0c0390b0000c1b03110440e4128148000120740c0036090340110cd54940c018000d00c081e07102da82e280000340c0001401c01d0f44510842c1e44480d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 973671151 1250 973669901 973669969
    0x6010806060c0d09210302061506070c031a131121011a090c0a02030324040507080414030a0f0c050f0601060f0809061504050604060e0916170c 63
    0x1202c41807982c441d10355181c6004d417140f1480b00300620344018541046601408030307801040c940d0380441c044118201c259968400180c4c2070140072005800090034000100420010510511141c10954090041a65408070b0b56840c0f0313071400f40c001c1c541e15046054482500303090804010a510000002a00c0c40005020b103003107070304038071081044070342c40504d411041c01c140103a6600300341d4011000e803a0100401c0b001c1e6507031001500c070602c4a5958a0038044510b010407000540f2400100140000d0038503200003007983e0026a8180c0320020754036004a4500d0740003044130075101c0152100751104240e02019a2004031040c000d071041d01511080d084821014006503001e01000e40b50f601d1801da4520004000308402010050290b00000c02c1c000e420359034105d114004803044a001c42c45599600100300501a0751b03009401141e403800c00d02141200210301d10b144941c9110750500050f0395184d0740c80e02f244200c54904040d42222003000d0b441e06060721004170103020213a9003c001c107400c0f1050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 973672401 1250 973671151 973671163
    0x106051305040c0519030201140415051b150612011518020f04080607120c080c18030109080c1b151e0a03052d070f0306081005090613050606010806060c 67
    0x1617280d413000c0302d014000c540c1c011100c0d842216264682030705140c10102520112002c2044480c00e01202248110344003613400038941800e540030080e00d00d8038100c040340c1600b540e0300340c5481307124a200390746045100310305205031001e40841141c034035505032030012161041c1841d071001c0c0e540e0300c1e020454072a8007190900108024500d000042026241c04400100506030120313408190b03d0030075001c0300f15140e0106001d600040b014040683c0d610071501d51444c02d0080d80081074040d42410039900c01e004142001e82150440102558034140080c0724000b0003400c402106503000c000c1d00354507280c44200d40041d01c181c00031207290b0f002000c40e075068a4055000f82808000103130303d40d402c010722020b0000200d01c40503809035040c500c0c01c01140001c40c00038030003850b013810410500d201d0181503110f0341161009052060584103072080301740040c80030b400c040b114400c2e9807080c10046041d011138010f0721103080e6081000341040e5141d0717400458214101a02a9505ca2018466018012018051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 973673651 1250 973672401 973672429
    0x306010c0506040803060f03161511010c0c0311030c1b0d08161a04080a081f1217040501050d0e0a210215062b0819110106051305040c05 60
    0xea20f417645000030411191070f0380c110410340aa08550120341999404040381410b8903441d98010340c801c02a03c03811503142d080186c4a030115800c1c88180ca60164100d111215220f010313075a82d407200c100d910f00040ea01c1c03184003030081150784140c529440800580d0014a110500103140d49001c0405860f0411180c01906920709046000d00b441010800d555103500030010001c03c2c80d03051407816032038108490040424403000d002940b0001034155044103034114602c88141031043d1030715114210340408880b0042c04860701c6d016500c40000c0030100605807811560142d403a5460800d0f44050301c40a0b0916101d50602445941044c00005030300c6403004402c890106d0074940341c002d6040e03000380361116019541200700c0407281071001d80e4850340c01810355100301f0400d08641c25049980700c84406242c03030b4084c0ca05100415002452914406103e06509503503440c43e440e248405125401c03126607105595000038011006000080e282d002141c0c024003508824260079911800b10f0001e1082c025 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 973674901 1250 973673651 973673663
    0xa090e09102a0f080a0203040c0f0b0903070509101e2403051b040b1c050403031d06100306110c15070306120c0501080c0c0114040c05060c0c04020306010c050604 71
    0x240700000d098142c40700000d181461816000c118012a0090900b40e0040c0040440c40e0300040010288001219000020400d10030042030281e601d40032101240c0200c0680c6200740640e0400156515003120740c40d004024aa0038403080c02c2c580044130b05140c2d1900b07606100c0f0f40c244800040c0c0000308242d080c4043c5154140701d5540e0984a10040807103600074400c0c035068800810301415808504291400c0e1865502040d6030703044a06034140081c9604068180028103007020070003095410307007000c8403002005030b440000c40410780e001511074200b2a84505040701200080000c168a900441701c001d42d0515860700d42035010080a040c245004100913551a4a20078414007070381c54403801c070041c80109443c200d20402e0b5075610703a000c8a03500c02d007410045000045900080702104413244061044002c00170380304400050150700000b00e600707a80d0a10b0315800081c4900b000300481c0e1406840901810034200d43d10700308070094201400d641c0c108081d40b424000000c408200700303405240100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 973676151 1250 973674901 973674941
    0x6010b2503181e090b040f021317060403080c0702010c080d09030e0d020a05060a02010b13090203010b010f0e09180a03080f0a060e040602090d060204290a090e0910 72
    0x180c03003000c0b6041c2d03640700e41d60740b2003000820034851030444900c10a5912000d804248a81d091000901070680036106610300b506c0080c0c000344484050140d030045a0145d84d0000440d04410342d050749602007110040e0104012900190301c0c1410301d0018401c40d80b050526911401c0c140e200d01155401a0180304081036507416070070141500310050040e00c2c4000c49500710350000541c00320300b41c0401031080500400002c0f44d5510054001e400c442c11800010702480140e0840b50711140245c400c6e104164025413802c400065503510074022491031001584a060030960000140b0152600042095034007440702c840061000d5414007040300303414000d5441200d1404c1c07016611018107030107402011020b1610f80d0410807640b244000c160301c00d41101c40140c560b240d50b0003041000c08070400003050300344001808500d1182d600304041800a100004030088129082029098410544550702107070751410704002c00142428104d0703104888030b0944000c83c980c60124016941d1034100341c5a640c040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 973677401 1250 973676151 973676177
    0x2a051309140f0609150d050c031207110a06050318120a051305030a020901030b150d060c020606040510090c051201060903140106180903030209090901061d0906010b2503 74
    0x400076540000f03040319110580c0c00c08210704074841000c00511409214540b03001024801c0c140b2412909920190070b440607403556182d00c00707059000703420441701c90f6440190580c46081141103002a2131451312a0703403940d211500b40140794139146001e415148100d403220402c0c80c2c0f80c0310107403d1080054442a4481c01039011321b0307051040d01d4000c18040e901c00c2c40c018015039202145c1c40d04403030f00002d040c40765451303503a900400003082c00001904201064551002c02c03420303a004200c03c0c49181d00f90b4465031542400c0200351a025510713600340c0b0071010814002981558000c0d0210040c6041c44d03881c040304504240e8499009078414004280c40c01390800c140034001c1d1241c075080d0403076002004600d082a50300e84055440702650760a0507501c500380d0040500035030448034482002020f241030b61a0141d05140a00341070301170451444031400b240c01c11016800d40540c010105023001d408507030f0805c10f40312402e810903000d01103070041400741032040e8613100100b091494080e41e2031080c12815 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 973678651 1250 973677401 973677421
    0x603020405033a1404060206010608013516090902100f05030109090c05060715180506010e07140f0a031503050c0d240f2a05130914 58
    0x15101202421519441c0b10245603075402d40064030034803403c0007014242c6442c1804440e0740c1c0040c1c1a0540c4842c00080200d01240c0006085040b1403146d07880141076a00c0d51010002c9070081c2001c11201c6d00c0c40c0d0008040a158440d180841c4140c107001c85513aa15032480c02a034558031a4402e0800c40e6807504018190300341411504601030680c00d10079031209900c8001025440148241155656a42c011000304007902e51400024180102000e8686506040050440c0a0544420850703450f1001e088801d02e50407884441e00c0c0d030031401a045c1d580c0380650381180184010208000c0104001204940c041004007802003081214601340c2c0710700c400e24001c0d04644412902c486d000f0304050040000540004e00b05440301e10980b400740800000d40303001d101d0101e8a4030f40700904400d048082c41c2d203625030340c411074030001107400a1160110101590400203a071b1485040c0b030490100340c000c002c50003600144162515203400465080e41ca0010b50300303c61940303401818685420090141c9100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 973679901 1250 973678651 973678663
    0x70603090209070c0206030f134b0311010b04090c030c050105040509010b0a0c12170a05010608010501051608040e0a050907060915020f0f1509060601020c0103020c0313060302040503 80
    0x10722810441411340468002820901009166141c50045600010900c940600640c21010381c00105d1010404c906caa140c0f80202100030042107c0044ca4488040b101507400c0850100034214001c10600726142c40440c0c510018030001602d075034032402d90080f2601d0314400c1e032401c5401030240d41b10050440c9004071030591203900150410109220030701181c3e40d49a56207044548284601c0d40ea050424802e94600e00a400080d2010304941604c2400d0760b04801048007410581660340010fa45501980d42101d10a0044500090841c0018043d55020310010181c00207188118040381c2071980e00c44544c0c0e481a000900e1003138019091114034142e501032650041d024602030424a803e050000700060442d12400d0401501001503003032490080c0f00c542186c100c40016a140c5100e0380480701d9031030801082d144040351200b0005200c0d4000860480c0c001d840590152044c0c10480e00110041d4101410f0701019000400000e504003400f003001000900580c2c42c056243c91901c0109800c0030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 973681151 1250 973679901 973679911
    0x30f0c06050703020c01030e0a020405040b061212030a05070207080307050106051e1518060c0607171612020d02030f0105030709180b15030601030f02040515060a080c0c070603090209 80
    0x4841480140b000a4000c2421a440c840c203180005040d404e40c0039140c038101409a02035002450f03c401d01082c04801002180308003816500d80e0001000104465626800384030230307036641e403000d00104801010542181d60880f4080c8100e81c1c802c1d072940016404c41c1e0004404072450b80d5101e00412243c2051590380140150380c0444481c69000c11011650000030752909881c2d82c5000211403001803d02e919940c83c1c0349008c2e01f100d03120843c820300595204001d9624170702148c8038682c0600041032906010b03114240b04012580d462009901c107031441050303903020340e01e0290244440c2400d81040d2028500c00c1000500301c003001c3d45481c0c02c0c103040070300c0d5400000c1a2420308011102203602d48080e4a01264850341d0400c560b0740d05040150840d4900d1002c9906000d00c3c0000801d00c00001c00c800c102074000c4601708519114418030303d99000840da412a0070440c20f0010403201409040003030b5105040340095450254000136060600f24150070030800300ba542d042e00c00560605004582d802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 973682401 1250 973681151 973681157
    0x1c05061503040503070311011d01090c0b09031b04021c0b13061a070c0e0f101d010e0a060503060118060e010605190c080d091401091518020a030f0c06 66
    0x9400c0c503444854680c8102000901405400020b2a800c072000b5844002030410031803442204405540301280a02f0b8020001d8840f00580c00d0b010541540c2002200c04021004008006a403081c161505007002415071195015030f091041503001c5a81c04442d88540c0b1030040001401c035081c8042200450061042000e500d01e400c0b401d0001071003500c45074110810f000d24450b102c410924262601c0f620641146003190001010300512a00c244500c41c080d0455040c03000784c59071500503907008805440c0101d01c180000100400400407002c0c5025044010488003140c620740b1200420700d065006ea010156442c2070000b070347d8244009100b0324000d09020413070400f59500d4150010f1450140c3d035000002d02d031040034980c00c43d43c06000035800742da0780869256200c3e82c02e448030300001d00c04c0d084c0a890803400d41103403000711300040c8100c00364103920850030b062140448101500820380306d43d40c3c07252078441789111401759550782400c0000710f10600c6140e1003e4040c3c0342c55039803800964003600c24 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 973683651 1250 973682401 973682407
    0x10030b070206270309030a0c051f0507020409151a0102100504050c0906030f1204050a050d032003070f110102160e01050105030703060b1b010e071214031c050615 71
    0x2040c40b8410009060b0301c0e8040c0c1e50f9508014040d40741d402e52003010f01e00d66051141c00510300800000c80411402c681c2c0440d015100d0007038030b8040d603c103e006442400009403081180000602d0264041c0480e02d005482c06080280d0702c81c0d044e001c0301c403264003143ca122a0141411404e41c0c0c1003000300c40190164000340702c141401d90700d042c2d5690600c00b00902c10001e01c00000e90708e4900b0042d0310314140445080322459181c2920307100c1340b54840c0c02914082c0000f01004100703820181c00126413661700d5681c0c1443c581148038550b00000509103031048900080100c80003040c40659004a102d005000aa02c0301c44810006841d00c0e2280d2456150784c0940002041804048074900c2d044038403c0c209565a5078030307a2400c80c01000c158001c2000f001c4041003424159600d10080c0080c00c0ba508000c10a014035015615a601d4640c4941400c8031281186003001401c60304d81611010421011682480070031040c14942c05510402a011650344004004040c0f410100803404201c0d8581440c0c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 973684901 1250 973683651 973683661
    0xd1b0b040e041e0b010306050429070809030c014508070305070b040807030305330a08060f0a0b010305011203110a022205090105010f12060609020310030b070206 71
    0xc40c075a8001c0c0040c00c01804044080000d140e0406984102584020f020144d903031a440c020f00100401d1360255450070881c0040d0300110070904110200c0c118140b842e42c0c496a90704400c84400d207000f4a924582d00080c42040d55030b40c4240250303050b06000c0c509d5040ca0b0b82c1455915903801049013a02200b28001505601d101c0c1c3d044014086241d41004e4095515085400c05460b0f43c807030718900411035602c0304200001d20032504060241944641c1e414054c40c0c0b100416618858016510004070030714543c5d00851000503040000345000000d090142041c1e075880e42139041c00400c60b45840c00c01e00b00740401541141c140f094a2a900782424100015410a01c1c0c5907400e00903140c00805000702401c0d802c2a034802000040c0c461540101900756888103540c1070000c4010460100c8a558105004110103a9060184034107864260034a600b14a240010070301d0168401c0005440d4250380e1030011032034441500045104207007000c0e03580082c80c55450100500d24000340480115080700c41485 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 973686151 1250 973684901 973684919
    0x80d030f0e030a08072a03030605040507081005132019051206040b12060403031b0201140c130806010b0414040c120e031b0d020105010f0609230d1b0b04 67
    0x907040a40c83ca031040c1c1d402d58800c0c2c500030710410315070842408280111b0b10401c06038150041d209036038082e00c0510180e00c80000548906c0320a0340e50324002d020f00070050216003401d1000d200d44050000340030455055a0b0300204c1780030324110000d81040c81c0082e03524800d80c141000304010744890f146c102e151a11601444c48658400340000340320b291107080c0d689607036854011111200e41d0000607200341d810036203000360081c4070442541e0415441c14000c40340190042c031a500081e861050301c00d20945d5034a0b500d803030070791000702c402607440d81a910104020300200041401703042016952070ba100d00300644400380c00101c02c0454440c60070a082c0c01102e0340d101c01281c044800801020422075580c07201c6c03d0035406000c0807501908100c0c4140215001e00040d11240d0501e1a0001c200590300c6a40352141c16081d80100c101103204908100081a4520280701c90700395180081000900703008005510b0306688503059034014a660301000b0b102d034020385204010b02500c1d0544d0b02d814a011000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 973687401 1250 973686151 973686167
    0x1090602030f1213060e0723090a0b010c0b070c0c0e070e0d0503160309090e0304080a030c1b09050717070f1103160807210c120207080d030f0e030a 65
    0x111410031a1074040f500148461001001d85a80070303406100c14112003c0060303444003e8810402d8190100b0080300e494007408c2c2c101c0d1241a0b024043c0f07680c0b960368442400c040e08101d100030f410448040311540c0854013880f8824040c3c107a83c0d644a07400010340c18810704405890700103030031071a190024040025000030b0881c000710019259681020040e05045085004807105659044404901c440070954041e00100948040071420000c81040303d4040e40ea90090b40503c0b600f69101c0c110764408a030049000c20320311403280c07110121656800c030345805c51400c95405420300507214001d128580f07800c0350904e2050030141900d00503a1070a100003d000d800c10b290700d1018030a200c3c140000c400307024400c03142014201b078602c41c1400d00c140344c030211550000d40152841e503000000e114120490505002e0118010350b2040c2e0343d28020381b1410080450509810b042d80300d22800018a58405c1c005241c4800d4184ca00003644069600c0c01419200310300a15032407900b04020410489811170780c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 973688651 1250 973687401 973687417
    0x323120f1e04240c02030912060702120726030412020a03051b01020f040f080601140f060c0a06050f01090b030307080307030c11070807210f0201031109040f090201090602030f 77
    0x2858001e40c04099094400191030309407803e0b414240341020a403071790000020900f1042c02c0d103040008280510003552545020794400c0016048030149654062030900600055400350050b05100d45d5108001000c0ca40040c4a180042c0400f00400c01800700c0158984200d90141c0003824450701d1694008086100704c08010203811b0100c168030440003000d6040d115a0310794880c0d4a030742d4a4450b2980441c00b10540b1036000a441164000304841c20000c04e0801400760207416101c101500c0c4003008081e40095402c0c0225100e01f0000320045016409107602030303103020411701c4040d41002ca109003950b4110194a00980c0100200b0000444420440b94003103210300d000150301e01494812540304a0342e41014a05104030000452612804144501181d00481ca1002c1c5082d0754600300c00d22811019000e03049071070100070107000d94020303004440280d0307030030340c17940d2804001100080c1100c01c0d509050008070790710203049085503000003076000941403d000843c103100c040700c1310340c405e03100b8001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 973689901 1250 973688651 973688663
    0x10f0503090c0a030c1707080309010f05090301050a1a01051215041103010902180a081e12040311180606041518240f0c0323120f1e04 59
    0x4100400501540b40c0701d40d40101840140c0e941d0742054004101540550441c00e1210f19040c11707400c00004070f8200721004a40610700340107803900191005007a10008005011041004c400c13940d4081c40b4840c820000250b00140000001e051500703040303489080c09042c4101084520111a620003100e58058030350308001c080480e070403000c40c02074101c000c0e14550403403000c4000700720a006600540708550034443d20b0b1800112400030013610003503d00c03980c400c3e0b4020040034070900007000000f03108404d069044400c0c1082c3c0600300c54069000c0d60041d00e0019001c210b8040304e00e40060304c41c0742d40d080044245c983c2e050020004a452143c0d1003a0300703031861103c03041544140201401c80350b94400071890320149650f84002610705a00386061002d20407002c0d09182190f0107685802c3e58048030b5920115408034540e0280c0d0440c0003d0310309510608d182c2a4014003400300380c01401144010940082d03107003004d0300030100c031300000350180032074020b115070183c9100c0d40203103401c3c0d015400ca1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 973691151 1250 973689901 973689907
    0xc080903121306140405010b031203041211031903051005091f083a08150a050406030809090c0c0d0c061d010b0a170709110d0213091109010f05 63
    0x2c16050840159010043ca02c43c181100d0041245500c049248140d020f40300a000081c0148200360f1502902801c085400704144007041c0850070342ca2911081c0c400c00c1c10b000158804440034523241da08108044140c0f0041c841c8802600c41d031500030b42c0c0d0008800706802200908103000102600300c020010700c0f1984101c2410b0300c0350980f02c00594014841c000903107155203003104040141e008244000c1c4d00c40c030160600032149012400c3c840b0703280940d0341d40c0d00d0702984a01e08501000131004020580c00020407001049554452144800451103160b840b03540d80c5c401000d02010100041c1604052401032281044e19000810903881d21a001d240624058046103071403c0201003d66a140000341201d40c5c0717070b010460561089403100d10864040c4c000d5584e920207810020b0044c610f03242a9086a00104000f0341617400c00101d4140034107000707090256184040c812600020ac080302a0b10300814100032154440c070070b420300c40e02400c018a1520140c040042c4c040d084060398a02080000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 973692401 1250 973691151 973691161
    0x619080604030c020d0f080405120613020118050603090303090d0c150c050f0c0601180b0a1a1902030a031a0d02090606160f200d030c02040f020c010905010c08090312 73
    0x18a151700c542d51b120a44104040d6503007480c2d03190317070000c0c0900c1c0c5c0551119a0000302c0c03000c0005280c1c1c402c105401c01c2d080810030540c01120039004484003000500d00504010a556980c90040c2d4420b54502c0c2c02503031280703072070000b1a01c0d0849190b1440140701c80100b45030049410f440311a08150000000895082003603142140c85229130110600001e00115405204d480042405812208583d102d94803c4060400000803941c4c0001d4440c3d114110281c00c00c01d029901c80301c8070841030700c481c140d400e0101707004070455080f83c0850b03407200680000640341240e94161103240030184802c1501c0381002046000300e941d11081e1880644a450310344005005030340c03050111110204170400c0991006468988940c2001c52114100c0e00505200c10b0714010148410080e90080c0c001007481c420b802ca00d481c2174581002c4000d040e41c015448600700f156200322800200442d50900300001014400d03410001d086035680d40b0280f00f0002a041400090701000040e00d2900d41038a208071015220 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 973693651 1250 973692401 973692409
    0x1406010e1c1b080a060501051e150409180b010f060f031d100e06060d02061e070803040f030f031109191203020a1e020a060c0f06140619080604030c02 66
    0x224055004242c0e0040002140720300010600304c41040c840c030001e00c0140d0300c940802584040e40400390f030350803803401e000c0c44c080d182c480007a40091902c094081d1400c1e0303c461246065034101c0e03510442c0f40c0c1060244000300054000740354018249528150350603810b0040091200240d8aa054105030301c7d1a0007003000b0035164181040d0007101c004442d4000c02c42401d0340c02a0101811041040c00342000107002424011b80c2007030343c0c40d07000748150f00c1d00b080ca243d41c48802505004960814800340003000010381404000c60085000e580c3c070b000d212800e032800403c1c4000c461050401c00d03040406818003449a00e0030707a10a030004a070500d9040000f0110144902c000b03a1008142c001d6500001d0203140e00800d02c060000d0098101812240900881022040103400001d4004941c02410410341c0c2c8604442c283c3c0e00d10a0300000c841c0019500c0783c5050701c0e0352448040c0d0402c601d0041c4141460240500b80042c000c4900e00030303005107020b0a0340e0b00e880008001a00b40081100403500f1595 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 973694901 1250 973693651 973693673
    0x29100609051c03030e0d08091203011d13080f190314010e06032e060f0e0103060c030b0306041505060d02031b0604030b1f0b03130f05031303061406010e1c 68
    0xd044119058906c560300010801c850176103561419005420310b00710781c8800d4008030717410f9035400700034000320040d60204001d41000007032a002d01c0e8400c80c821140003d03130060007072268106c106d2000307403540640c50128220501b140c121106042c980704890340e003101a03c101d1070448501020b850116901d102c007183c00d194040c0040c02d50180d581a522030f404c05580c104003501c41c008241040000c0d00d0345580000341401e4000d0086011040004000058a03038200080c0900c035403030302088410100010078506103007600c2c211034008070b2a814805041e80ba2090f942e0210048131190002101c03900441d40b02c030b18140f04d011803a14219080d84440d16204201e900840d07010040d8a01840d000c00e240c02c081d0b80e6840c02c3c42c8a118104400101541058190780c09144149100302c1500755650ba42c2084510101040f101400b050000035800c2c00b0340b25032180198051040841c00d11002c0c4804100040b004000d103052240040044c005901c5262000414009040c007c9179904082c2c145610841 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 973696151 1250 973694901 973694921
    0xe0a05071d01120f02041508040f08090409020604030b0f0708060a0b0d1b1706060a0815010e0604060504170708060f04060902031f231329100609051c0303 68
    0x6424203651046107004c43d4000c004403030755a0446140d00804646c12110382c0415100030f0484030100c010a00892162001844c0f0b0440080002407100c0d080d501064658000e944280c80541c1242d041105200450842ea680001146851901e91811000203902c1030014003802c802c4050220351240c611903994041e00559400b410701c0411070386d06000080500b040d007807980380d2a07585903012550904182033501c13229401c68841245543d20111024031014900c440a8100808a044902c0588903c0002c2c405007130b4076541c00e03a0355420204890f4005c000c0c1030707028130141d00118040008180c0070801d03d803c100710040701c2800c0c2c2c0700d80c03e14401803d049440a5814010041810f40c00c4510300249411140942c40620210152803400e149404283c0850341e40f80410900246250145914501c032181c400c0c0480d4401180954003a0308020074400050344c2d0250401c1031010b00170615000d07800031310083c0b81201040b13050902254007880708030070380c0c40c00300b401e00031410415002e0f0b003044445c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 973697401 1250 973696151 973696187
    0x170a05060a1e090203100f1403070e060f0d030f090b040302060a140d0c0804111804390611071206050c04030b090105040303050703090b1602160f0e0a05071d01 70
    0x1d00745031a1410b00091b00d8804e0b0f0400b40c403400b10005050041e03005030344001300700802074608607203802c40807400e08000500342540075607001169400740d540c4482c00e00e062402f07503903520018807680034090300180b2203402c83c451000c001d000400040c0d9800003240c4586c1c0c03240c540328144019820710440c1034052070026001c4241041c50207050035a014049600c142c0c023410051020858041c24070139080c00a00c0c1030542c100014000a01069049080798502c035045d1120b054503030342c01012001a64004040c135401034035030f001c080118603880b501c504204161480a069a6460304242c6600305294800041c40c035a191320008a4921400e010394009541060030302c80d0038601601c4e001d00800f0b00700c0b001c9021034900004178a01503c07900c40d80d888980d00c5147c002503030b1240b80030b009070312160311001011131117034000c00d9485040c208005d1001708080e4080603401410720b401d01c0300000d4014401042c45182008200c01545e020080c440d80391b8551504107440a0941d0048880000e168aa2180307 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 973698651 1250 973697401 973697407
    0xc0203161b050a0905070e040525051c051e07090909060b060703080a0f4512090b0f0406110c190e060409050d0f1e170a05060a1e0902 59
    0x160a01358100368469120781d81da40030007600d80e00070441250020b590842100c203d0086c0340f54404592480000750000c0c0707003401030070320000d81e0607200b500c1d25001403142403d4482c1c0070711045480c404034903000032221a01109a038a0b00a80007483c0508600c5031000d0180c80d28041d0082c06280c2e804880c2c083e02c060803181c0d80d42403d04020b024030030103407903030704e04c0918064004120360842d110b2041d990b40110700001e40300814160055030460b40c0c000400c0424240b031141519011450501324919102d03a01641030780741e2b81e641c007400c0d401450b03104800800d000c004440107101d501d401ca81c191925420446038020f07403a40136a28144041d210150801781c0d140040e002c408103a8031100c102c80e118082a15140e8450041c4401e84800c0d2100400c56440040b400280c2ca000c0d46070503240040600c0c2004105491000000000104091300c0c1c012502d6420340303440141e121015a0352214440f030082c452030404101007414003116100d0815180b10454408005552003410700780100b00c03050741951 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 973699901 1250 973698651 973698659
    0x807090f090c0e030a020f0103090201050c031209160806010302060d020c0706030605040f11070206071403030708100504090b0109020d02040b032e1d07140a120c0203161b050a 77
    0x18010400c107a000b00d01c3d0986a45114600010007241c1c42e98090124034031083d10724015005041d590f28101e05220042c440400808410400f500440c2840982040720341008525541403084160301381c141005003100c01e08c00104006052411a0344c107450260b580c4400c51a150f000b400313501d00180080c01206400644035074076400840c00d03100111800c1142013403d01401040f220710342851440c2c0c1c00140705d542c003d807920001070919680a218440c1d64442400026400d66004845120100ea1343c04c1c2800405103840d10608050902594200850200c9445030384507000305204d088051500052101d1000b0703103680654001303059540315192241401c910401e000b60f1140d4890749410300108076505000f10b800407181c11159a03414060040c10740946020540400920200605c00c64071b5440319941488001003c84072596036074545001e15035089801a903c0702c4020b45d0841d4400d1244890140c081e0081c000500d61050a1980d0f00d01c0d03140301c0000e8102c4540c0619440343c160301d4006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 973701151 1250 973699901 973699919
    0xf0c1b0a03030e07090606170411190e01050f1804060b0d0302030903240c0c0102091305100f0605090603063001201c060f0f030b060418030807090f 65
    0x11030f06504003078030005600e5421141c00c558040c8a80e1000400312401d03140261180c045498203e0700403080c13001e2408013035004c00d240c2c081030716007420b41c02d00d540410041861300300e24441c090302c41114a206e240400000040c600000170001004004402d0003241c2002006da121009200c80030300030b141119580e00b001782d03c0e50000d101c2c1a0003400b03048407040d12400400680202608282d645000c59250a0009042030304403c02e1481c0d00d42d800c0000c02c00d940c1e18106180164001c411011030b21b403402d80d00442011299502c1960b0301c10002005004040d004015901105025900710751242d550710000f43d606c041c4002c1b100f40703219689003d00a9000450404603041c0d90110090052400e081c8201d075680025000c1008191070500502c0c240d441c4492040c99034a2400300302160880d25240b5a100c20241c96000c01a000620b103c2042080352440026612503c111001c10007510008940c4512000d5003334011f00704952080090a103074025034241c405088001003001d010f640b100d0000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 973702401 1250 973701151 973701161
    0x70b0f1e10031b05090c0d02130e06040b0405070504090216061b110703030905010c11031e070803040308030109150e1504050f1311041d0d0f080f0c1b0a0303 69
    0x65501008083c802070b0b11036030035045001210805407102c1c40c0ca90340c0183d020f5480d080b60070710700d03201e0b81c081200b43c0700300801038507282c06849030441c081e1041c2005810002103821540c0c10340d000310f007448100501c2d01d4000083e202180d0b13401c0c4000d07a550f08109064002081d41d58801080b20345400394400e400c5410340000785803a2115100c80d560109807d41c0c0b581e6030b402c3d610001300000c20010080c8095486454480042440740010b07507114020000001e040240c5410a06001c600c40c1c040380e0003043c003c000c000c0040022402951400c0d085446000443c801400b9034000c01e900e406600c0c00810a1120510041280c002d0340c0c181400c003920140a20b118080105100c0c0e420310002c62900407000350321034000c100651561032010b40c50350b14008251503080e000c5600580d80c84a04c00c00b190401690818951010094070110341c200801030301c0207490305804001c0050700001c02106050045480b50021400c1e43c03580d84507827034190201d00c00041c203464684203000c0d56210000700b40e050303045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 973703651 1250 973702401 973702403
    0x12090601030b011208091c1e21050f0c0a080a030902040b0f1003090203010608070825060c140a140d09050907090e13020603180d05070b0f1e1003 64
    0xb02404a0341c1e5030700c2d9150904441100540707601000c000c209681d10304840c1c400d221449000030401c000805464072481c0c002e0000540c041042c201200504202c002c0d0482100004e12a28030a4010f240741c2c80100700f07015800d6003140c0300800140c0908200000c0103020103260b40604035550341c480d01c0c00d004000d0100c20b5405c9000e20706094a41500d0701e04425214140c1c080a05030383c90080300d507682180900308104090307070195a80c2e140070888000600c4280041d1110344020b110285440307079485040e2940c6100045000c04000090000d2036110b403070000039580210f00c118000c40c1001e0840d00340103080d5002400d162601480100524010400c0c2e0600c1d5401c0d00c80300c100030f0f903800609c14860821629440090507802d014404c1a511060041d0403014800c0d010900c112954040b420b294415100320941c9046480d610360f88101c10450f4903002e100c6441c01a0030320744960750700c0da04000040d12144d0041d0080b40020040900103040c001c8500200c0710094550070264800e060030007044c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 973704901 1250 973703651 973703663
    0x14010f0603270f0c0e01090207020102150103111306210b280e010b1c020306090d0906050a2102030118020c0c04020c030c0a06051806070806060904021209060103 71
    0x2c1d0048090000c1e500c01c4000800c0305508800e40b8210b5620074080c0003090408035020014a54086070303408410651a0290425860042e40c0c0c602500001e4070384511510042802c6070800700510001e0b07401c043c2c8181540099483d140c203583d014098801070000f541016110700d074040008080030805c900d4608000380178400b280059160052081146c00034000781c05441100c03660520b409451700d5001c5000b461404e40002501021840040c010543d030010383c040100e01a9071042c21352600340195a0003140c9040144030100060601a100306c0c1c0920854041c00004240203240c0d600455280490103903d0300c00412899a000c1644000d400a001c3d6407003440e81c000f00c02c0507981d05403003211903c0408800800301c1a240b40100000395000c9502c0c20300078001031010300d40d81041000007042091190201043c10f00d44110300107034082c103909218456900038400d000b015500305002030341210381900c2195589840d040403a02a03c200b06031035040d06500b8042142c4d040002c68114140c82c03190b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 973706151 1250 973704901 973704911
    0x619020a0c1403120d0b04021b0d1b0609030c02060c161a161a010e090d0806060d0b01021f0e0607052110090f0b1002010203130f050114010f0603 64
    0x1024080307010090500c4140c143c0d010500304084081002c01070300c0080701d11400071405c0320a201c04a07003644c1005000c0001e5849e0040c40311020b030320134000901d903406030b07280850040070034111034000740d845400c5c09001aa40c803030480c02414814010000e0250b00503100d90b54400120005a545102c0c520340c0044026400300081a41c0d1560008082c034580b000c0c40c1c1e20300b04055500e10045031014620b003120351030300c1813a032043c1d983d6005034400e00900c003100c044806031030540e910a013482144446082004400e1040290640e10303c1d0994441c2c0d4000764000800d1100300c00141d00d0b091b6a10071005807491a17120742e20110320320307030000f0302c000d40000143c0f000d90305e891a058855014a582402c05c0b20803c0142100d01c4918240340340d800005c0c080700d0f4144540d1940d91008030b501d8400415840785e21441c02a0603130605548500a0560a10085203545414032155005d07201645005103ca0302038004007052160940001c1100005400e0b103241079650760f03070001d12010044c4a0702020a080c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 973707401 1250 973706151 973706159
    0x103111008010501091e050d050d0f030903051206010c1b0501020c0a05010207031b030f0c0819171b0319140301033809010507031a0604140619020a0c 66
    0x1481014101c41c01a100c8502141c01c0c8040c85262003400c501c1319001b032031400c42c0006c25640311a0111081070160b406015002e1780f10340d000341581554a2800705040c01c02000400103075000e8100c0e08031030040f820101f0325455441c01201c02ea4031003240a00103c81c00c1d4000004040e07682a100c00b1076400360219070a41c0300240600c0f4000c9403600c80e90740540c02a40c010800b040828003500c1e0120103800f00d01070b01c41d441c0d540d14a401d400707050041e540d04502c01c809001002d01041241030700310360302c5c2202d50914415a54030114402c0c07403945142203031000c240042009000b201115410b01c107035042d40d880790000c0d510f410105800c410341c034000403101203422070000c1101c422a4180d03074100402c600c03c200040105401200305801443e000003040c207a206c0c2402c10103a9090040078008000f01e840d05001100a041e03525950122111110b441c500703612503905d09048504840201160a01c40360200000608500400807215400e0261140c0d5030700d52076021400403c0c03144074034a00349185440d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 973708651 1250 973707401 973707407
    0x3120408150105090c0a02070e09070e0a0b031b0a03021e100f09050d0212010c0806030f0d02070e0612061513020414090903130f08010b01170c0304021801031110 71
    0x1c207100b140c1d009200c02d00402d072050002802481844200d00403243c00e55524100b280c181070044a44c841c3c0768110400501103000004902030300302074004000c3c8a110901000a0703110001d180050314103055081207100340b5120048180c008640080032001e080f1040840e1072101c00621034118030a40e03201a4640d000c80c005c0014620905082e920307104054203040034011000346511040ea4007611180f500f4540410034041c0030781003102075990440505100d03040c54540041841d100f0a2034000710070540d0034030f50025001c011144080d60404040d154000450001d01c5503090007001402082c08005950941c186c0007020b484c015030316494500349401d8103000300e02440c000c4260308401a001c440303d42c5406841150425145001e40e45000384403040d003090607449504c025aa201900c801700312044080c071130b28230641028280124804040c42c240307111000014014000c0c6817000c0042415911010084030311504034401031482541c503410314810142d80ca0900754461219100711b1309001c1c0c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 973709901 1250 973708651 973708693
    0x70c061b0c0b0f0f16030605210d0f02150c041a130b07020906040506122a040e030a0507060e0d09140f031b01020f010c080403091a0a140903120408 65
    0x143d96800d28525110017400a56217045c1c010340100b0541c03200c0b07000c80c44c0d43d41c00750001c0b4104d140c03c03108903852000302e0f58182000a000344900c00c2c06290204151401e0b008640308044e80850715030304009a50b00700d00070403540640d4001e1006848000390980711001800002e0850b008608c0e409400c25035100000302843c462198001d4100801c0008a030280c06e0681096410100080280540600d41081340b40b400c41203005a104200d4101c5102c1c01c1292884808985110191400d20641a0b020062580da01c1102401d0b0204140000c20805000041d80001985800001500d194244803000248103402a00404649203103407213248506141403d82d542c44910050044c122180614200c035801403805c100707042c150f004107407541c2c2c8102001e1090135528201c60302c800c0b66906183c207009283c6601c0d9085040c1c102000001501101d110070142c0703400035158505881c6a400900b91412280201d401094142c4038030036004580d001d030307000900160345004085a811200b8034800d401519 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 973711151 1250 973709901 973709911
    0x40602070e10060509061e0409290f0a09060816050d030212030c04030803041211070807120f2324011703130b0d0c1403070c061b0c0b0f 60
    0x482e00040422000c0d00503400b0700303032400c0010701c01030030018070030485182d00da0b80907d10240442e00180502400d601441034410170785155081c91240201c05135030325400b80741d0700301551245010f60a03510032562400c100201408403540c0601c00303d6038401040ba42e9141442c0d040303101448161000c0751700c1c100001800c1c003ca4050307005000185411183c600c55600141240543d01410000840450038010086008600c14641c1180c00d40b80713031400410362441c05400010710780102004120021000400909881d86185000401c281c203150500c0d54500f0b110005003460350b01c811078075852900c4080c1071142c210301800c1c0c40001480740703200c2c00111600c4080c0c500040a2000501c00c110120b4a010003c88641040303c0c5400d80a07504d810491411f5844078002c83e90000b640c0785180b0440c0102c02003030190b8203002c11402601320f0300344202d001c000c0400b01000041c01c00c0005000207500721101c02a074000c941d00c001c80c3c20b0341c6d000349001c1d42d0110607501a20340c0400320f10f040101800c1c240c810 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 973712401 1250 973711151 973711171
    0x7150309050d0c0b181c2106080d08070201020909070804050d081014040906022d0702060a0e032509060b1201060f020307150204090b0a0b0f0d20040602070e 69
    0x1c1d541c0e021100d82c2c981024a00c04400c0d110304c0d00d50150350300003000b4811802035944c5a5a0b0f0500c0340c0c9040300915000b107a0320a00c900e0801d00d08114100000540ad10741250030b040840a40e4bc80841c224024003801c0500380e0700030f4005c004c2c0108150440d11090141c0d000d602990501030501c18241d07030710001603994a4058040000801c51070401e0400b40406000040002c0381c280160703103c40c0300f0390300f1491224011000d409401c1d07281220014a00944603603c060341e5090220940000322680a035005e42e806100f28a483c0780d10b41c5d40e0500807400d00984048081d00300b9814080030782224007103806500b034502d250a1300428515640c0059030040c41492030501d440b41e00344101245da2000b80d401d6103043d484213110300310001d03540b41344442e08900001c10050300d507450b081e1000d00383c811140019001d915505010300580d107104003180d441390850320b02d941e40c8454008844c0010700139411252500d40c0c0c1400c1c8088400b80c44c00c0100204c07001a82254101512551406030039041030340c681d01d0b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 973713651 1250 973712401 973712423
    0x2010f0902100e0d05010e150a1802130213080303010510050414011803051f110307120b0d0510020307030e06070203161103030d15060c020d1407150309050d0c 70
    0x400b40c401c000d01002d00e1405406040940d11a540303180c00e41301c14100900064010100400720840580c0c840c551016049100303108052856100541641c9001030213401a0303220310344000a81310a40440740d0100c0d01200303544c101d81d650000300f0745a07002805240d10800000d8403040505104030107640944444020107107000c403001c1d00645012424002e200d03844107a0032000400300ea005d000d016203551501c041c9241001105490608880c074060744a151000300b8014850f620b42e03c001c0c00f24044485560000c0c420b0703000070000e003141c02801e034004c102d481038118280a6452980146028031882d031000e100c0004004140c2c0e4075100200c1300200182d200340038280c003008208020074003640c0540c40d40b84407460154042401e5070310520b0034400e4641c0f11040501c0a4101250420080c0024507080114014550000b40d118240420140c12034003440e2128040b0f1009006240040120740f40000c5100b80d81c06c00600030b07215082054580d401290065480b4034058000346407076550007428041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 973714901 1250 973713651 973713679
    0x40e0604021605030706060503100603120c031b08120901050c0304032708031e0c1b1c03081005010f08040b0709030b07180909050304050d081c060602010f0902 70
    0x750407441c60241c8582c0c19419010114906100601c04a0f0044e103000c2030490910701850711703082d00c007101603408520305034080000c40d12200d400f01240e212072505200080441c00c0407600316146440c0c195072031511802003420032910b00b0060985411182c020051599070140d120708942c0304a40700400820100002030029104400b60085042c0c210408198040d000307100d0304040c0003a810410481d07000159049003a00641f0f40101a0303c000703007074186840c1d8503810440c2c4910800000440c01360052402520566400d5800f090001c4403900c204060070203030500400311201903c2c904000410fa4202044551242681100c001e03081e858150103030310f40e0341c0c0d0080752040080200c401c0251b2460040001100090b8040c0100c10070340d5803141d44014100824021507069125004091802400710300083c800701c00d0398200d0f442122607a074a002d1504182d00385203e44840186059404170340075104e85a1079002c00d040d0f60840d8001c00030804100c9525085401c0404060340c01956034190351 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 973716151 1250 973714901 973714909
    0x504080c120601030f14060c091c211e0e190b0412231b01021b121005040f0606140d060c0212070f02011b03120506061b0c0108010b040e06 61
    0x9804c1030301c01d846049031610024149401c002003a036901140602c0020312043c5403804ad20b901d208526510965282070103141e8841e4803002c080001885440381981c2c05814a40c00364003000385a81403120a07070f1301c3d216003810040091521780c140311711854420440075101112146404142c400e801002850203040203004c00ca408941e0070300704c400c5191810105c0943e40210b185180150f5800003d0001a82c8801c45120f0940c140a105045600241c292031b12004040884030301d0f91000d603601404141c11510050038000c01c091032002c481d08000c140720400c61504070080420740540300030800c4584824151110034502c224159101032050300c1c0360041a0191701c0b00100c6012801115a61070000d052015142c01813001910341e141c4100c4c144040d5600640440a040700382c000d0107000d036915640141c0140d600c118860001035440300041c1d5030780c031444102e40b030042601c0a00b2841c0f08907100b940790784030540300c0e9090028610390000554418944281e405482c0b110721407504a5641c24144 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 973717401 1250 973716151 973716173
    0x2150403150504020607080a0215090c01140309160612050f060f0f04020d0f0605100206011a0304030c14030304060f020405220b0402040e0a0605031c0e0109030606060504080c12060103 81
    0x141c0e40807001b00104030000e05c0e014001c107198040d070f40203400c00c41c0561441c080587e400800004203508a01c41c8407441784e9000544000c2c0380344010160380c698903410343d064540065042134a074502c00017200800c503e90840c44006142c2c80150051019940d1054058901c1c1d400707a402d55000519550010f01d03900e00343c1044200184003070001814010320103121816940c41550411415075031b52000d0101d412320b190052900e10040c00244815454120b4044640c07980c51401d490625011004c2002c03d84070f6030f030072409250400c81c500c0002040d0341e070045d103990090314110780c45440e0008220316106940203580840310000c040100070300801040040c0440c414810303800440e920b018051150382c81d44043e00140041004c210620b2810f101c0d43c1081b11140d0704068403980c04a0505c0c1054802c0020001e104101e52400d04240356030070700169004034058000500e505e003030071000300c1c00300e5000003e00b040b0b4030210212003400c9424414405803490740d04161403103402150050012596a83c00c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 973718651 1250 973717401 973717403
    0xc021c0f0506190612021813080715050603120306100e0a0306022508090d060f240f0b0403060216200a05040e07060e060c1902150403150504 62
    0x410460344600c0e0740d418203100d4102c3d212025a4140051046201600e100e510080e124014403848038040307a40004240c0c07000c0c00c2400314044612000a05000400707580c201c01140d1041c0d50986070a0281b41040c4030b18000321410544e14a0040000c0003441c001444a8500006a2000f032460321454144101450104420b400f44910b45d02c0c1c5c0c00300c070b4640310500c0000b035000d0100180c48462516181d2024620039807410485078210f0000004124654100c91030760604a5003040013001c58608080580780c1e000341020301600d0075006070400c54490040c07241007280e2004160495441c5da00304004107015000f0008808814801400003816582c01006030441c13480120401c10010740d5007800030b5000c1200840c4560b020a0104100d00300020110040e00040ba02400810b8031081d4590351040280b0031001085011091254182c80b030070308480180c036070b002c00c0d0780e01701100a01140301c1c40100724080740901c0781c0f00c14100070400f00b0300c1543c0980394818100c1d420f0f0000001c0b070001a0502a01c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 973719901 1250 973718651 973718663
    0x16150213050f0a1d0f1006121e0504031112041404180c030309080c010318030309230604050c100c0620030106110111090102120f04082b0c021c 63
    0xf401060b040043c02e00301d48500d200114440d414600020140390040703020300001000c41c1120800d2040540200010181102c6440001841c0c2010040b0100300300b410101e02040713614040c00e100605601c8942c494810b00514115840282200c030b400e4164425803041401a02108400055620381600200400c07640301d0081101c8009541f1101c0c0710302c3d19580100c4c0425030825040040032410300041256a80c2401c00304070307245045100b51005c158a00c00207080540e600c41e07840400c0f005c0c0400d000301c034410103461842607040440d50707599200c055a06071074070710612030604603a1801e85482040000c06940d510801c4009a0780c86c4090008070202c44100003100d0486590380d042c2802550080109a482c0d2413804a00b20f150b6003166601b1143c3c03207050104010a4402e82d0f0001455100c0d0240101c90030707035030070078448003107210b010316008241103000d034905415080100b1000c0c031000400c0903e07500c0d0303180110442600c200c020100002c3d0080f03440f840c1c0615040021a41003040340c002d071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 973721151 1250 973719901 973719919
    0x513050f01050405010e0301020702151305090f010303030c020111130f09050705090d05070509040602071208010e0c0a050906040b0a0f08040b19150303090f0b030f0c0a120216150213050f 82
    0x140c0007030300100d40d0f0800d151202030082052024020f00c4c083c5500109410348030140300b8203014043002400201404050281625900102e804034403d52003181055150036401c1d0301d828a1011403c1e051680344038034100045241c00108002d501c80c03040710702508003602c2c0c1c185091010424090a0101d004095641d8041c01000058035100c1905aa20940c45003c2c016a1031205140482d1609599040c000801101e04018080450321b1b114554021243c0e648040d00d4041022003220140b180b20340e49500030701d0120380050102d010b0400340c0000ca0072a26141c095a54500c02120140001c86000c3d10140b560030204035102c2d4691485443c45492010101c0d615103040c4042a040310168005c0700010104081040803404d007507040005040619082491403c041d80314515048010f880b12881c0d1000080c107031842401400c2c00e00180440342429910b40e514141c1c0d00311020049601a1010308469a40b1012200640b0032111140c1c10204049881420a401d0001c01500c0c1d1000742c1e0804010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 973722401 1250 973721151 973721153
    0x7051315081203041e02090403120e150702070506031501030b0a0306090b01060906031415010504030c0f06120b01050d0f06171f0c210906020a0513050f01050405010e03010207 77
    0x502c02d514a1510364000e95560b81407529101912030101211241181e00300150400140c0e03521222135081901444e143c10603040451501d401400d00d40d20000c6a0b1040000c100b02c840101112684100525002e4400050b030350700a1040920045440b01884002d00e00548102e44c001c0d03101c440d602e0700241051021170b0701e80c0e40d84011135055201c240c600403810001007200540c051940c20182020786420f000c000e403a25441c030368030000a018011040542c0141080c543d20032002d6800440e000308013540001e648001107c0548040e00031180002c0491100b1505070405000d600000701069546914002152544000416181a1000c401500e41000244007a09030020604804a0384040c0c0000e64040580400904924400c14441d42c20840c0d45c01d5203035001141130402c0d5032542c00308000c00c50f00e850350f840102a85c1364018a90b41c404618203844075030002c05041203205212040d058643c0361000c1090079a4101e86190000c0c10800c01401294820302e181581520301600140c10000f075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 973723651 1250 973722401 973722403
    0x1d0a1a01050d02070309090612061505150c010f020f040314150403030507030b1504050306060a12080703050f07121206180e0106080f0607080c07020d030302091c1209080705131508 79
    0x840c0c1c9c405d06c425000000e8002c1071041c18800d42294038040c01541c3c030b0b140e150130040740611030101c01004101c2070114500030405402e400035404540d090303004644e603482411070000290042c2c04140c2c0c1540b01c04181c5400210b00040d210200002c0c9610301001d680c0e50b5078110046e00b4004c0c50b00d410551507039807002030b6840d1210030100b4104458841c80c2c0311401d00c000e00d89071000050440d0b00c540301d0312030108400d0350541036020a20760004851903541c0340c2400d0942e824480d800d001c6a10400003d0f0750f2003070000c100e201008500040d65400e008850180f0380105403052400782d02c04c4c100c1400340c03103200344a8547c001c01c02c5900d0301d800495260750b079052690030000100b03401d203041c1c1c000743c040140035a80b00b0006030303010540c1c0b9001400c10200382c022682d810b00c96030004042c10b07030000b00c42c803490303940d01d00250501103440c99104542c0c001d480d0550540302d1500702007020070900380700824041004542d81007640d0000e40300d030070001103100d000e00c01384c00c180c1d807940741081c904480491500701c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 973724901 1250 973723651 973723661
    0x9010804020906030f2b0311070f03140c07140d02030607210203011e080a120807140a0309050105060301020a210e0d02061f080c0111071d0a1a01050d0207030909 71
    0x91440300320020322071b01e4482c0039031141c8414200c0c10075117443d80045d0072820307000540d25000d4201c010000707000300e207140a485a1500f0001400303060004a0040ca034458002021003da0b14407081c02c0c09202c07554802c0c4200c0320030460009505400400000e0701c0c040c8162000e81881c5040100d20001e20100c18000080768800e0f0444218070f0880c9a8180562110740428001005404d0040c16840100d8460603800a0754100c1c601c01c1001850104036214420740c005641100700d00c0017159920b000e598060010100c500049420307508150014903246810b1080d10403540c0203885081d030000c0b502e0a0000140400c40c100c0d01d09556404100000341400c00a8003c14407142d0001e103918200030070f100c003041b01042c6050444801c00003042c4101c44c0702050a000001080c02d2242d41700e405030484904041c040d8002d800d250520980b003400c0001c412074041e001e00c060802c1080401c2d0145108a005c0015410490206004005d0802410a0350340185160b60103858810400b640f201280070a80f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 973726151 1250 973724901 973724923
    0x9020a0801090e030c0307060b010e06040605070201080117070308090409050f150109150501051b0111090411030f0633030117060912130f061e0509010804020906030f 73
    0x50051001030260803140e00c110f0141c40f9000c0c00440c106602c0d10341059a91080f658010452a2218a0a611079015103862103401c0001480c07251101d455460041c450342003074405900060000780000b416039800d400505050350440e001e0b10400c6e0442c1c1758800154424210750f604142c2c1c0d448041c01082d010301c80c803040109868050310440d000c01c403144420442c1a0405210f080c0380c10780032030700340c034610710110211002820800e46804011031050340d40840d22024464550030305e10f40009072020b18008107211401120100b0054042c011a50124002101c0c24a2080c0d0b010010810784d02c1c10304c0302d2404007560b0820020003410880e00800440400303030401340c140c40000c030052001c5c080c003000c2d02c40800b440c000100907620748240d2203555415948076440b0118000941d0212030200c0d42590409000000d420401c89030b6204401000035030305110040c4424034010304440d00c944284e045a0b455801691440c01648451b02004455003000d400d8a038184074007080445044c20600401e1440 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 973727401 1250 973726151 973726157
    0x4050307050f01140a091406090d2307030c15060b0316081003140f01020c1006080a050a080d0209030a1a0a060e0a0e0f100608010b090402010c02040b01050409020a 72
    0x55034003032600a2504025955416069040074075405a10306861985540300f0546240891446802e0804004025407100b070b8400c00d014000c10405201000240a142d0030782c19a24181040404441107000060600a44080706030401c605400720303218491041c5007038010a220f0800c1c1200f08400412a40a6806030840700408000c000c1305801c5400041d02c0301b46d07181000c421920b818040380d8005102404010864240601082088041080081c01ca0300400b030085565203908010681e82c0c115046441002a04010002c83d818801103800340c86903a004000348a4a9880ea4411a807500415980b0980315401e1201c0d0a0a80c0d04104418909009000c0020220743d203902c41803040000504010f000d81c00c1c84001c018a8424140301a44000203041c0091495170245071179040c140140800310341440790411080005400c1d074000421218108000c1019080a2080c4039101c0022680a030110b42031124080c05801d107500004a90201407510703900e807a4413079407a0b5040342c00001c5404c2c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 973728651 1250 973727401 973727407
    0x21021e040305071503021c0509010e0106080705030c010f020d1112040605130f120803090705121c09060e0f010e100c0506090613080a1b060203090c0d0302031905090603040503 77
    0x134105402540000105146010361800c030282c601821044409010380322101d03610300001b1604182903100743d02c00043c600090010a959188031036440f4040c0c000e580c424090001d80003e958001d10251405000301c1c0c018022082c01d03907000742c82010441a80d042030380103003690760210311a0040284003410f01a282c068940440003060b08800302660010007210700c0018003401414072004202044540c07040c0c0c5030341d8a03074402400c50300340035650784038030f802807002c5440803e03800c0e011904405031070050703010101d1170840c20011203903031000b1b1080b80c01040c188802020b03a801c0c903110000d01c2e14410304100211034801700128105104071400000000e11285603030081000500900d5007003e2540c00800150078607484034407194050000050050b840000ca8400c5280980c46001c5d070941c141601e21101c021a0505c580658800c5521440d00d000f01c038101d140310b290884001c19941d030158025805c151905440c0300c2850168041032091000500c0070000590310480114800c41c4684042c40d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 973729901 1250 973728651 973728659
    0x90602010c020c01080c13330c0c140102150106050c0d081b160b010909021201090c06210207050a020103142401110a05011a0121021e04030507 63
    0x10071281000d09100454101d4044865660b0b031040c030154022060745401c60361212090205000c48a0a90109000302100e1035840020004c0854600b40c110f140c00060840c403840071421100200c2c107510050505800203020301c547c41c1d096080907240541030048a582c1c4d214200f481064030826441400020400030703050a00c80018400043e403410941840d6000307041413190425a10b0010030041800900815241084400d00310b02e45085038100e1000100741d41c41710284809880161001c0e8011024409080e000d0030051090303a4109811070382c98240340b81000d0003201e1142d401441c4012074200c0e08a94480d0410610007442003e01c00c100074003900c0010310001d82510f0010000b21490901c2008200b11021300d42015035282100c1d06e0461031982e8514010703540c40c0b1803440b81d060648110b54485040140541c0004501c074a1038161035641c5401c00011249018900120741041c3c8040f5108010034003141c01070b1040f18000304034242420500040c100f03154206510640b11366020f402e00300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 973731151 1250 973729901 973729903
    0x3071808031c1e1515050301092f0d0b06040e3c010e160212090324040b06031903110a0203160311030331260106050303090a120c08030406090602 64
    0x3000904c18010000744040300e01703101038054001480f40c015400c3c0c071103400003015a00c80702c0f0801d4060b9100d40000d401036000041d0b81c0150024291500e0041c9000d181d400c952605006403401c13113000c2420300280303564498528011440ca00c4001c4000c800c8860341c0d0000f000390181400008280310000706a940c0b601c0c024500c0c3d0700c0003801003d13907419078280c0d481e0300c2a0302050034034081c856444020341d0340e40d803c80460300e03150074640c1c940300300059a4030018030101194245030180b80201c500207810b03140c820806403181d0b00c0b183d200300800250340a0400003401603842001a81024068461285c0e558010a0078070121072194100d46d42d5200051040040d8003540a008000540080d41802160107440d41300503034100c4106490f003a00000e14840ca402c1c220014082c110000d0381c00712750016411030700380818202c1c7d850105942056400f0403a400c000003130702e040d020002c2c1b0151445240000e4440c0401da084021f65600b200401c0100d074020b802c200420050019507a17501c441850300d1002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 973732401 1250 973731151 973731191
    0x312051618080a03080c12010b030a0e0d02071703070606091b020c130203090313061d01050909040803130b070206011a0307080f0a0e1203071808031c1e 67
    0x36003000345400500038840b00140c140071480c1d0509008459444910051a96000c0da8010207040130201d000818410f203c1805036014040402090180c0c3d61102d0445440e000d0405014006a218141c00c03c0119440c03110120901e09400680c1e19003c060b07290141603034a2504a01c101648900c803400040000300c16924645a942c0301808015807640000703040c2103503281c1804a03994022001c00e64040c418401c0326200300c00101c000c608160390304030203000103900755090000c3c8031b00c100c0e0f500400d500039401c546a080f00200030450079a80c035582c002c010303000a4241000c00840324260302c000384009032170501441242d00280a0f0b58035000050301c01008103010440360510a00501800540014040790007214140219210b50382e1008003400621801d18040c0740f500c203488442c4583c1119000850181d03081d5581e01c401c00c48840c481c182c50101c41e2007414460b500c20445240d000ba110941c2082810030300301d0106100031091088080080a00d0052400703d45e51078030717011344217020048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 973733651 1250 973732401 973732427
    0xf050a0207111f1404081b0307060f050403022b111c080706050414120d0c02030c0d0804020402130b120114010504060c0f0507061e03020708030a0903120516 69
    0x481e81c54801500d244651031200c460f110814084c0508121400100040640c0c1c09007036040221448070240c3c001000122403032101d035501074010f00c100441d0f614440d42550840303000940f0b070285041d00e03607402e110220410b894502040616103c0001c060400d000c10159010b00826020641f5080c810802411070301c00c1071114200c5103c0c80d07901001509182c151003207a89c20400016141c0e4481c200103000c640d000d5038078080e038081e0031071f010350100001000e00b800e500d0300c04042100151441081c2d94378814420411165400712102d000050320501101e54814030107000541040942201c0c1d04000c24190041541401c0118001c0c40c0d114503008000e0040004402001d074a1400c00006800b42c862130241e101082686000c1c44203110031841c0c0c00219aa1190407640065a1840d00410040c00040003000401020408041c900e00c28000d8801c00c43d00010703024030f940c950b161810020140c10303008030144190b009116214501300d100c1c1030720400005003901900c0e00c600f940240380710b901c030b00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 973734901 1250 973733651 973733659
    0xf0d0f08100905041719020106091a0d0602040b030c0715050705030c07020a0b0313020108010806060a261507030c03050c1602011713030906050720040f050a020711 72
    0x4204510318038100800e03811101040d20018241d152400c10329080180c0101701c41c02d010001079200784209100d080d140c0002040da000b080250340301e21230407042c0c1d030900000000000c09200701c0105031400700c40024455202c0d44c0e00600d090795440341c2ca44d4a401c112070140e0301c810b022a24200344a026403012444d900b0041c0f0030081850900000707130172400050301c801c807640307404103154045480e5010114080c210400701261a850885506440200d49240403400202130400018a1708000101035009032030040100d6600760821039900e0f85000e00111444e0500f40182581c02d44110038445180840c00c00e035103100e128508403102805941848000c9410075140038204000d11100c0030980d0714000100d03601c08013890450004903640165a01d035501d40c0e04107401444103401500315440c4002d0b01c6600d54035006656514180c6030b6000d003510240c100d80030220359000d850301a8400d04842880140000341c00905e942000d000c8440032030b0001c03a441d074001040e00c24800e26102202d00d1103400c403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 973736151 1250 973734901 973734917
    0x307030608010e07060e0a031a04021507080a08060a1e03030311072402071401052d070c080c01090c05210312130b15211b0d050f0d0f 59
    0x520f1690358820a101d00d808000140f100c0042990b201c1e014000195000540603281001c40c1d5040004003400340c40407440341482c0000c200f06200f0f040103403680c0c241c024440600300f0002040903070b035101000702855400b551150b000700712180410b9010b20051903407401030480310b05610340039003110044500d200420000b8414440001c00515004265503460388008001c16021480c5601038000e2a01c02003040c401c1c1e130380440d1240c0f0150720107403040381004561003041d0300d044120071a40403019072070080d5226100000351414000c10707521814512030500320f4901050803502c2d0303017151303443c07081103880008401c0c08001c640b178000c0c00a01d180a403103030b411581c412039400096a0740329902c07074581380309100c50000d81c029a4010091000d141c000f0100d410318500380300c0100341001c1034003009100c0d21039150b4200280704000c0ca90281490044c00405458082401c03285482203001181c2d41c5c0000c1c06001d150000d10140544465510303802c1c003d14280340d0880b40680200140410441003010722 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 973737401 1250 973736151 973736171
    0x1e0102010e07150302130f0825050a3501060611030901020715020f03040603090b0f0402030d1224060206070c0c120305070b07080a0b0f1f0203041a030703060801 71
    0x81c4115840840f0030f418010390b500074940d20300f010001d140e032080b209201078900000c0c410f100410f1010a50319001c07013888090040c440d001c010022140126900f1580c00c0a06000f00700c01c03442d10002a400d00b00b0494107201750250000600088441c2c5000540d45076641004910b4008015504070040d0301d001c1d5080080c0000000e58401c2c551144003c050b44130003c00030060f00902c10789429890300c4098a9032681c9075039015018081218080b2903c07182c0100003600485641c80d550300a40e402000713030400400610003141e00800d800d00501c0c1d10342d40e03192178800c4480105029a061001c480d4040d801030325009009c1d0610350001d0010091180134a8180d00042d86803000206840040b00902c030420000d04084a690054040060401100c001402031403904240300174440c06000c2003c0c402691682c0900c1560124488103e802802008ec00d05002ca81e002ca4001b1103107072481181d0504d40d0718a40303001100500420002180d10020901c4149a4540540c0d000341c4a468005d201401e04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 973738651 1250 973737401 973737419
    0x1030506070f1404120c120507090b06040e04050705150f0919050910050a06030c020307080a0c0f060c08070504030b131b0e150301060605030a090f021e0102010e07 72
    0x10042001c00c205104082a094020140e2000c070342e21100c1016100c50b2141c4410000c041c0305503046d602c224a1001c0040c400501b4900800155401005000543c5ca0861071034090140c00d46401d0780040180004201d031030014016501c500e0081c0000d2510078904424004020b68810420103424810800310f40580c038a2400c65481032000e607031001c04031540e40c040201005154101c1c0364000d60703000610400ca000d9941150540c1c1e4121303010640c0c80d90750703d000e500300c3c1c0040b03420001581080c00140301044a08000e80482d800c1c0d0300380304d00600c0300d43d07448007510f22400c003044903030395501c506041000b984801c1407a0f1002d001d0900d5803516045449803440304000900707812480c032058a04404118241d41f40080c480c0d0080442c0c48080d07221f8112a84042d41100c070044c807018640d08ad00d10700d25050050350308540766a142c0c24a1a110b61038a00058400800265101c0c0c411400100c0162207030310800b03180e034030382c160b080c1c1b100030464000a09580211020503150782c40740005101d1561 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 973739901 1250 973738651 973738663
    0x402010915090b0703020a02010305070809101109030a050604030e0d021c02130e0c19270920090a0e1906231006031a120a05070f05040c08010305 64
    0x14034007884005074282841c046807003501c02e80140c0018500401c050040540000e03a00b000d00d80700b600c00388902c0d03458680441b64a40202d03000b060b15842429070b801091129400b2280b0701441c00100e5282c140100c01003868884c01244c1281e0a60142003000305050b403000076a030100c03000302d0b01c15038640c125400107003c8072184401403440d5011420f58404640e591000d02040c50f800840c240034410001c10000d440300d4290a40c50700405010450300c03440200c1d240054207803844080082940c40607002c155034007041100c040c038060741d9035510840100300e00b050a601c408100d0510004005640700602c18200d00290040302c10606041c080c4580c14004610b0407201c3d108240003480301d03800c1d42018000380181ca0700800302c0004800c07128003448003824002e03202c1c0003d885c0c0508601d559110450445000203c00b041d84203201c188224a45400c4d0082e10301080360b0310071180351940685401c0d00740390031070f848004030b110400c00401180c01c2c24022001401e8007410000ca05600d0f40e103806407614 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 973741007 1106 973739901 973739909
    0x70e340f020307080322060504060605040b010302130b0d090807060b090705031605280315090915052a09010306051c02010c1509051609020304020109 66
    0xa0000003115880b5604c903030340e2071840e07445e02d80c0802040300004180404840d25a003070000f08940b401614011030080b00c2c0003441078501010841103c80c00740c1058181401807080e000003901e81e08040007101c0644e243c140d56020b01021650040440480003000f25101240040500415070701c604113003103080d0b840c0c880589a40c00c05951500084440c000e6114040c3c0d802c2c2e451910940180c00031072500310450000c02d000b09802180d00c5204145003000994541d900001d8449a20545008021030782d02084003024a40325040c640c1c901400491446031100086008180d401600c0b0104540080e003a41d0129102c91852801c1c0c2e1141d6107007030019040582c04944d503d062000b19403c10305d141400b0084660a50042d100c110306140242d400840301e075680c101c0c1e51035138062440c0b810701c50800780c8400488400742410906481e000303512814410f0040200507608040880156 = true := by decide +kernel

theorem cover : BRFrame.Cov 973561151 973741007 := by
  have h0 := BRFrame.cov_init 973561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 973561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 973561151 ≤ n) (h2 : n < 973741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
