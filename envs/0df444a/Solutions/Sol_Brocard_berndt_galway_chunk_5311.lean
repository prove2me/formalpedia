-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5311
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:26:53.697712+00:00
-- url     : https://prove2.me/submissions/586d3afc-2543-4ef6-b10a-a110e4f5c909

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 955035971 ≤ n < 955215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 955037221 1250 955035971 955035997
    0x603062e06030203100e15010c080c01050702011a09040f0b0414010f0209090a0b0108060909070801090f060506190608150d03270e0a020306180f010f0b07030e0411 72
    0x5408a00d40b58103800a611820042c0107a6132115914420350a001c0011204401400010344529000750300c2603503604c00c002c0c040e0503090308010403240c88508440c0b058035180b016039541c480f050907a88003092305001400c1c040701c50110502e81603c0d28403005a1000c00100621300c901c000038100b00c5030202d00b06901c0f02a100800c00840703c864214020342c084010140f2807992000010249981c601603070882800603074480e01c45884030414031903a47c3c4040c150203598000d0030008510500300744590405103004858500e0041c03d02d080c140122200580540d0082e180f0041301012419004010400c0b134401d840c10480320f41c0d900c000e19030507071600d650003907019400d10303c00000e059000300f51308050910004142d603d500010201c1216034180d00c9003440000c1c2070703c0060081d4210b5409903a004501500d21070141c6030704003901c50884403c650004a00d10040018050b00b400846180c1c0070700315011203a40341c03105a0b10058403c04c9071202c2c1c684210344071144d440003101420161101d20b03035120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 955038471 1250 955037221 955037311
    0x5041e050a03140a1d040b061c060602060603030a230a1d040b030c09090111031008390d0204060f080c041503033b010215060306 57
    0x11405588514000c41e0640c00110040c00d070b80e440100120494081141d03e0701c40181000243caa1408a8650b44102580c0076503070710120545c3c5c0c0c407884010258840040d41c81ca01c00316080c8013880403a800c80d0000350071076100c03d0401c95243c90010499641d21900e0500d8039407101400c0c2c01c144c2072075032907040c1041d051012030550010758224021141d540112700050000200300740170b0000b202d6a80c0c02d8a50b040d0320400046440e03007400180f085d009400000042002500d007a00c28502d54402d49500e0603030400640100032000c820b111000006d6440101c3d461200503000c110740c41132000b201d81007821040b5000074003447c0c1c0c40c514082013550f4050014403150740d03102e0121a0700e041510451099000b80004032032a440c00c1d12400c00030000d4581310414a60454034216034140e610504202051002c0411440d080003140c1410510030003001e02034808072116000a05140728140c2130744500306120140000c603500070031000d500c03803124450810316100d00304440140c82500d01800c441c10000b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 955039721 1250 955038471 955038473
    0x60706020304020f0f0310110c07150909060e0a0c0c1703060a1406190504180b10050c0a03050a0212041e061d060a05040b130501180305060a05041e 65
    0x940c0255101d640211007003054080c0c034005010782d00b103408980740e605030001c0ca103482d00003402d41e1100c8140d0000009141c02c15039103c4a483c42c180080d0408904900d44103000c04115500c40101f4026010030341e27080c045185090040d600000c406016007004545583c0700d0007006120388034010046400075113804040c0c2d1240c0c82c01810f035009680c80f03806005c81c2c07400400e45600001c030b14039841c034000e010646411940c1c0034400000703a454108008200c1d0810001460100200340d00c80c0058075401c00141000c0c17032104014216407507401050610000b8020864004d0700440c60708882c80d0581091a5116103100d030807418051900140b918482000ca00810140e8403d541542c0d40100d8840103462142c4074902038845803072502c0d140004800000203e012428804040d055028150801605194403442c0c2079401b5080f00e001036000203202c01d0708108943c1e229140b805a901d515940c41446420758840316122080103080c000c07900e803502d0200341000200040040d002d2102c2050140000315 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 955040971 1250 955039721 955039733
    0xf0c06040b1006020a030c02040914161d0105010e040b01020705060d050412020307021e01050702090703050718050a060c080d06170d050301060e01110f01050a0c140c07170c0607 78
    0x8152040b4030380210052001c60904d000186000d0480d070141c50b0280c44400560070000580f096110413944480101c04a40704124104580160861105c28074a0901d0420f070690250700c14091707a4a500200d0000100a1030744c00c42004050003000b03031400714550440c40c0c0141c3ca13068041c0d01913a046400010b80d983e01103560f40c05a405188100c0c00b03048202d51701038040745d40b405849000713544151001243c00c240000711140c61980e08040c1491400c00925800081c0c408404032003e10100b0b4442080022719603000c03001d9940a407018001840213810440030481800e454024501403104452000741404004410f440030f46940309010f00c0204c0d2549005040100d200400c1da02e01d11801600000550140055a05880d00b680d50680c18400ca600110f900c031016030200c148a0103503d8040c030006100b8002c00e4801c180c1c6c16804180112060750040c06135141160801003610203008902140002141c00c400301c0300c2462082c480c140d4100d5005042441002e041030703120200150020030860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 955042221 1250 955040971 955040993
    0x3151d01020a2c060a021009110f0a03120e0112060f060807050301080c0409030302091332070e180a05010e010902160b070516080405040e15010b0f0c0604 68
    0x440395070b500c0044407550203294640402c00541c041c0c00d10f00401012080c24642d018140c8101c440c4101c6520b0703032001e409901103070504801500e0b0004000307100c003501e0034403040c070259142d400e441c800055403075900c50070950f20b05080c08d0010480c9074400f04000341c0c416100d42a0042d000c4c4400c012199480b596004001c00d184544d80218036510001007500b03000390203a81c12920b02c400502040c002c40d4003048000d0a65102c100e09056080c0145c0e540c1c0c2c0c5035110304082d403042c1360340c0004100e032a00002585c4014081704100600c001c050381010325503003c5641981025880c2441c0000f080c244002840d0030740c1d506040c40756451130800300b10202d81160001c138100d0301c145030320713540c6a41c0700c207074050907031043c03a194041c0d0030303d040031140008032079800c0640c0c040300a241403401e103403c0054a5180034106402520320080104042c0310a04d0144548442c0c2022400103000601c0840c41800d80c81c00b05104a20b8806008211003040e608444103d540c4082844166040340c641494240c150300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 955043471 1250 955042221 955042237
    0xc0301030303110c12090d060509010504141219021e030901091d040201121d0f1b01170c1b01051b0c0c060921030c010b0f0a03151d0102 60
    0x9062101c1584114034403000ca8502c0c00d0814041c1103a01c1d0017502d89030459200054040e08031107608450320200b8900c0c41620b016001c0b5900200702c1d4200f40c10305000e810404007a141003038000e0b0b80c0c1d040310804954103d41681d44005080c008000718100b06a04000c1c4420082c01d4a0881e80042d4914260202c000c1c48041d9098031039940807a02c5421023000408050069000103081c01e02023005980624000b00e0035078000c080c00300d09103a07030342840189148441201e070556401a0122850910b09000d14000022904942034000c01c1e0032000904096100c18901c00d2030071400c0c08a50a429094111507214032181085042001907845aa00802e411540304106044580214501c001101c08a8500406140003016402440e000700106540700d154040d6100c00c2c2d1103a4412020a101629100601880d01a603158110404c90a00f583e00c071030700040c8180030b640a00d80c401c0e52545214015070f500a2000a072820080800720010250701d005952840c0f0913448806801c1c105400410b244 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 955044721 1250 955043471 955043477
    0x4030512100e0a390201051e010605071e1202060601031b18080f01091b05030a030302091315081b0616080f070b010f0503370203060c03010303 63
    0x59034409480070000c010600891034100680c10100350304038010780014949030400c000414041c0301c442c40f00d03520183ea4070b01d04640e0060f4000300d0f2140e150280301e6035900010b0202820754504102c5d286241c48001401503000f80840400c402051010704851601426148004250a640c03941004c0d03280401c03150003c0010b00c1264009000e6511030700440200844606424944910414090743c103c4080c20740c0d00c000004058000403440030802c04140d180f106100002002d209a041540510020039251100d03c00e094504001c580c400056005540e90075103001611202c4034400220940002c66503424081e003002d16412103900200c1f01b010444200c9011109004da102d0031042c0c01c00b641455881c0d00820600c07e643d1724031044804c0300c5101d8481d403c000d103003a0704c407000c40c82d468004000a440200f24840184a08210f8020200160804130002d11010481c094003000841103003c000200c1c21000718801c002c050706240000407207a006042d1000f62034414002c2841d60000d11050b000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 955045971 1250 955044721 955044757
    0x20406060c0c14010c050303040809030d020a0503091c061a041a09040b060301060305030d020703030b0105030c07060b2103180f0a1502120d0b0a050108130f020f09040305 75
    0x900d008124041d06a80e00c00c101d518168603058841e103502181c520f030725050010301122040010420b20045100b148035040c4540c0f203400310360905181c040302c810113406542c004d40350341c0d005c52000410385080e681d0032242500c0d040103620f4980300c0001c00010091115051022800c880b0a0405418000300300070f480030044401840d0b50103c850b060750000541007510900800c0c089417929504652103e800350020403d81d513659140781c615031000441601c09640412481c04060317260061160350b0100b440d01a0860070420318078106407044660003011143d44901c45011906c80c0356164000071030144c4414441000343e88090740301d40c401c11030301076222a26204090070b440d007240c08c42c8154001070f02400d8514180b071101606460b22800060641c4156440034118420603c028045542c0401c40410311550020030711000301c074030307804c00c0e07043c08140020044030701c80032074400f95450b03003041d1050642c80040c00880c0101c0c2d800b00d842d5402c55448404c11081c140c10070700424450b190074012001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 955047221 1250 955045971 955045979
    0x60515130b042a080c070f050616020303220218130c0906060507140304151709060f060d02040f02040306021e07020f0904051603062306030a030503040510050f04020406 74
    0x1641c05140030f00c20038081900081107490324031400c4219032044500c01d10138504001c42c2c40d01e2038641c07800c17102222598450b4042280e000918890440001c099000031070039828080300405904141000c404603e4490706151f005650300c0909044c00400f000c0b0086075641040300d154401e5031542c2d24140e0700950b60000026901c20b040c41008211000f03540c070681024030b281d031080400080d05034109407501c010301000c203c1030b09041200e51260125180c00001000607030903c451038000601c445e030355800620400000107154013450780d001a044941058590300da100003001044d1b50900480014804100072080041c150b008040d40301004151305469083d04403010b25900c81d45070003d42101c00c1d4941400e440c104544c02e0b54000e8412815200c0d400d282c228201d1805130346500035680181c943c6a03580c041d80c0e5140d01505d03103140d8801062998644000400c0d95001d1601c0c0050800c00300000240c02d00c4000d201c45030f14405030700024030150910580c0354081480c00c1e18164403540c5044000a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 955048471 1250 955047221 955047251
    0x6030902060d15140d05100c090305070b0702280e0705040815061c0f0201080c0712030902010908011107140c0a030501090201030b0d0b0a05181e010e070e04060515130b04 75
    0x4d408251b0100051150300c0261145402602c42443ca020078040e90741c0003c40000e00c03d024200107017000e0011103858403140e004100c40b14840781c12a460b106a104c41e42e031003d4000a11034010742d0002c241e442c0304c5841c1d181c41118980f01d140d0014400e8002c0e824201c80800c5208045801044129041b406121896480204544060745c00a010502c048906030042d4001e08d801984212004100c6d4100100b0340c841b40000b07108524010002035450458030300710340e00325281c1c0c400391005034020003008010400140300d904c2941c80180c4100e101c0d10450f00701e81d000700f00945280744090208000f81fa60303480c0090203800c04030800c80c00309041c00c2c081c40360340c1406031340c0c5165942c00c10002c1885490303c500300b200610000d0407481c4415541f209000b00c00c6001c009031881004544001035001d0101e032292402c5940e02c0310710205a40040c0381c01c11904004805958219800003000103250300c0b0402c15581804403403110070b0300220500b607400316442c4503034820256034070f05640901428403001060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 955049721 1250 955048471 955048489
    0x20f07081615020a020d060b010306170a23010c0c06060b030c030112032a020a0e3c010f2d090906060f0f031203020304050706030902060d1514 63
    0x1191403411414400c0114100c2081800b041440a0054031882240360b0085945a080e000c400c1e81c50584600410459590610034100213100700304c565580982c502071415100c000c0d024000d0955800d21641420075400e08001c80d81c2c50074608e00070000070004e144047d040301005034082c0e4542e45405400a9803c000348100c0e407181d5030310220301e459a800d05450322100c0c40c0045042c1d003040b500020030308070303090b80e4001f4030864412440c5404042c03002b07104000c103a902a8001c0c00716108100d060101d0360002c0403000360310345040c240440200700342d560001807069100c44050280303e0210000124920b400035081e0640b40704004008041140406048032241c4165030800d034052002410070110303505e54030080b030301c1c1d100b12000300700e06135034040811183c182078100905820030b4030410010810001403206c40c0c0c1045050540c11840c0680380d80303480d030419104010600d0f880e490000110342c0c5039000c5440c7d40c44a5001084456041555506000c04078002d80c4c09800c00e45c004407030140b5002d200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 955050971 1250 955049721 955049743
    0x1209150a09230102070c090204140a0b0a03051807181b021e01020909180c011814040f18050f070f0306020c120c0619020c06150310020703020f0708 65
    0x3031458400c240e0950418030502035000d0101c1d65600b40b000351700041d18141590024200074030050b8072541012100b031040c14050f22502e1154500b102d08000c4c2043e00c0d800d0710120083c600740000c2565521000e0b01c08540c2c03509600a16016150700810461310b2074030307540090440010100449100111840e070038805100d0820003581c000c084c4500c081c002e141c4182014040c0318000b500380402180414604442030340c400035003040164041017501e40402c07204103000c0f002d1030a800145085180d00b090041a0f000da28501c5041d240d0742102500e0b40d8011408403001000c0800c000506071503085001110444122030300d00030040c450711140c0d00000c100b81915030b03d04200c0c250500e941c0d1008000e50103040103184174014911440d40340051440034000c50001d00007e0041403074000c406024004014060350380842c410b03c401e170340c401c00008443c0d50090414010207808001c20001070b00c0e002214002082040c000100c036401c056010031201081c80c603e504a030502501c0c1c5441c0382d195410601c2d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 955052221 1250 955050971 955050983
    0x31508162c06040605040c02061f0b0715060b0304150c0e011d031204150f0315090504061116051506100c03230301060e01110d03020904021209150a09 66
    0x8981141000901c10698004000900010b5a241e481300440d00751281c00994001503040b00301046402e98440000410510071088840c0281381007080c5c5150754000c8800c0a40412490450262001d80341ea20003030141129400d01a102e14043c85c1081e00c289200c40c695032498101042505010300420003000702c0101611204111f580d5402c41c5103180a44019059040c8914043c4001ca6400d010007080034080ca200c1d072290015550a0251508401c40801010907240005c0c070029580c02000c00c105a500d07090012950f6200ca041c84006000d9a0701c409500300d600042c0140000d010304c011224a5100d48159504440445510403200700e04450790340e0080030300308414075018840d070f00d10280740b84a030824180c030b00700020108004081801c46d61380801400001881800d0f002481d40e48001024644031340d100c1e6070000025200e520021000301415004100c540c1d00340c1d2150180c400c501170058070462076181400314a0780d10840350301c445074541040c0020074511001c50007681d08080d0080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 955053471 1250 955052221 955052279
    0x51006081902032a060304060c02070f08031b10110c10060506040510090e041217040c060f1b0b041208010806160e0405100303080a140c0a03150816 65
    0xc0451442e1004404079107046903194400c84044d581d07580c040c41c00b52340510b070005400032003204040d20341501038220086200254004012800000045521401d412a0f100c0040740c100309640d4a403640380d00102070f0140c1480f0259545181800240c03008003118030484214148500170881210114014030f07401c0344003044140480c0c200342d42e10165861480c640034503000e40d580050200c41d401581d0840b400700ca801e00040e42e1550185124400040d5042c485c1e490303041c0741e40c5801002c0551711501c0103011120046c0070f6414003030070100948842c42c17110803c5280c4c4034604900130010880d002c40341141b42c4407000c801e040c45541d000781a00c50950060016880d44444641d00c10604108001000b031202100b1041d07443d1400361502030030343c160003c2a03543c203518014050f885e005005031400f0303103002001c50000c00d41c5602c0359049400401d0301c950711801101c0c02ca001d4400001c5280c000c2440ba8000252138000140381c42c4d0b609000000f403401162580b000c245002c01e20700540521041e94 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 955054721 1250 955053471 955053493
    0x109030204020912031c0f0b0f0d050705060c070f0609030c060503060a0f0b0306030c1e0f0a0504050c030a0f020406050304030807030e12280206010b0309010905100608190203 77
    0x70380c010864190000d222071340f54400013080342d18580c0040c0e2003110001015001030070924150003035488002c2d505a040c08140c0c8440086000c49601c01c0ba06441140340306084003d106082c0310010280c00c01800540d0348840c040b01c450341c0d8091510890754401d0211742c000810303506c40d0129005881d40404a41d04052800344111a00d4001420180d404070030464005250b05128804900074142d001046032a45409000c25061002036480c65018a40b50050801c84a50041c407070360141e41c040f9200451240d0740008a5122065600103e070050700d4001030048020803400698483e1074210020700c046160040f04009078090b40c0b04a4003c1070b0144003090000703000c1c00c05e00c0c0e0b12640c140340016005d1f210b1600c0c60f1400c400c421521780c2f04030000800c1c0d4000548400b40c001d9429440102003004501c0394002507480da014070840111070008004542c11410030341241d000f840d00041160094001040c085000701440d21815503103110b513080e100c200000100c02404030a8000340070749010414 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 955055971 1250 955054721 955054729
    0xb130e090d0513080106060f020d0906080105040e01090b04110a081903120207050a1401150b0304110607300c11040b040b060f03010317031510110d020f060106050901090302 76
    0x4842110f080305500214045918502446084014803041d9200c041400300550b010b400c103500103080b0710410465000901034150001d00c00390445e1070940d40000c8051500301001c2c0106800e0400801400c030f05402d020a000c5040c8401c41c056608440b00b46000b6900c0443e180e50b040404407201c0d9a000c2d9a0700f2001103401800007140154450b42c0c05841e24409581c0e076400e210b020300040321080c1d0000e00f4032180303403424414140d6003507000c448421860f05000701110300f4040200000c2c0b00c801084c0e840d465030b48802c000d80700f68513880344480382141c039001202c4201c018544481e643c0281c2c2d241403080711301d2141060090031904040d0314400d5000800600c80900321095072550410740b6600c10303207403a07102e081c01048100d5074419050b41725411464502c041c0d506e07104100403e56030600134492068520006106803140444000022400b580d00545000f80303101800c180c2d50003009604030078550040751b141407001d00141131314150780e00c1e800c007602c841c05481d07400f600050b03083d0014801418 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 955057221 1250 955055971 955055977
    0x1052110090309080a050609100e070302060901230a08130b0f04110a08101d10050604060f08060603120a020d051c050106180807050d1e020a0b130e090d05 68
    0x2009243c00740c880307519410401d01d04101844119503603403007613040180441c0706000c2203260f41c213443c1092000346801c1c40701a582e032940d0b02004e44034810006410030940c1c0201e9117101e40c80300300040703122407801c1e446840c0e01c5078008505101c00318859100148003000504403444050781e206e1031045184c1c480f00f100441e6160014401c07100480302580901d815560b41c22050010400c0200030807481c2c0440000b903059420304078a16202036213525410f00700040c045104564802030340b030002283ea43d807000280141c581c503889148000d00817075020440170000315200b807094000394125105074825102c1080310b0f01c540b002980042c0c00030b0711204219032082005240005002205025454000103100300304d9600fa4881400300301c40803550343e00c50b803080c0c074144006c007481030192100c1841c0a001c9041262808402045030782508100c00340f10850201c0c011010b600641803101c0d180d164900c200003036000010206180c6e03e030301d200040300d1102c07000706c81c0b040080801609011000d440c090365650 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 955058471 1250 955057221 955057223
    0x3080d0903020705031e0106140a0e0c0f0403030305090c150d02072901050132030c070606030309090b0a1802030903040914010512031206010e180406050105211009 72
    0x201454000180581c1c00700094034100c0c105161008217451104141342c21203056a000c11000444981c9c05456903880b000e002c0120b03a50300e11f9000c015a5078498225280c8204007100300b60620202d0003005040e80340d442580719a40110403030702420001d40400482290507400d5503583d03081002812041c03003c9402030540c0602c104003104107110070811694150354180d518500303502182004220540c1c0c0030300600d00076032803081104440a10181c0fa018120741c82c03002c20031500400008100c880300510100c2c0c030f20540180040005035140e280040c415071b118403500f043c0c5828041e850003a440c1000c0300d10103c1d5104044c01c280c0301c038000040340194000800c25001400213110001e20036516003d0700d141c2c40d03e5400300314015070416003001050f2080c2442ca680710f40c41400b000350080180c88236190804800d09210058000c0c030000039800c1d01b02c01105400d03681201061008011960b004103040e0340c41150300d0308004040117034107901c010b01c03c0c1214200c1e40c054003100e542d0081c1640021106 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 955059721 1250 955058471 955058473
    0xc0a060e100e01020a081806061905191a13030f0f08120106080f061c061b030914030309030708091801080606090601020c01020a1712130b090703080d090302 69
    0x10400500721482110000b0040b60003d075000152116000e03480f460284e402843d088504100c4003150181541c0e98000030480c50280c190b141c15514140b0340c81c0c48100042c0b800404102106c03041a00048401d03071240324100411804800d00c80c0414502420354411490b004041c0c028185180c450071096500311006481038482113603408040390420000340364031701540802a1680d4174000d4000c024400c001c10307000641c4101c00520541e9910240d454110200440d1142903000140c1409001004400000407244040e5804000c1b00b9401d80c00076840e69004802100800f10055100f0b501d030b01c412181524550020041e501c00241f400c000f4054081f409070482208610005050510346000e0304400c2d9664000780c100728040c5459500c46074419400c5c4050111001d2000c0041d588a0f04000020441880a0205200b4003c100203171052282c61036881e0502c2e0501c040000664080c07004207a466494140c00a02c0c00b0b01c001800e002181d51100076035107410000c00e00b0301d0003803c07402c00840131 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 955060971 1250 955059721 955059733
    0x2090915150912010c090f0501081009050414010f0915020403030801180f02040311040510080304150e0904081207140d11070213020c0c0406150c1b0305030a090501050c0a060e 77
    0x26003a003d00c21704101c40c029445080342c4a007021036811440c1c800ba4005410070070103d0802803c0c0d016000c41404a030001a07010034182c48501e003404810106001d02c0040d5840e20001c211010034640201c3e0ba828043c03401b0345d240d603102c1c0711000140d1099010242c003103000307080100440f05c0c0683c03003500e030302207907060000760007501c04111410703a03226600583d01c1c21090f00c407003092460706100c0c01d85c0100c400e4250801d80c03441d00728840d40b40c1c069403280c2e12400c4003641c03903074070702e940904040c4203031000c0204414001e00d01803412190340d4001d4600254108055030000c0c0398503015900300021050070070085410001902c0c0325001800c492901d80100101c2480741c80d0050310b9160707050a000e0254203025803155842c0038014542140315400910450403e0310030042d0305d0060000c500f403071415141802c41c51111303081481090b000e828a4110314130702000008184840400170300b6021031265140c00c0260750380d030011111030080321284813541d04400c44030360010383d480d400340e401c40d940302c019141 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 955062221 1250 955060971 955060999
    0x90f04020a0e042402130509061203030c0c281e0605130302010b040606050702060c0a0203031c0506011706040c0e042f0307090e19020706020909151509 67
    0x101000150f904883c0310313002010180a00b1a41320341440a007183d0f20b82181008440f0004c12140b00c1c0d1803186038040d41c0545c0200d000c0c1d071240000400c0c0004d000d0f01b107e9503424400b00310000e40d4440404a40341c0c0c02512403071400c40b02442c89131075107141c0c4020010604107940d201c00e901c0914604240c1c0c280a060b40b039040005055005261280000b0000c0c416620000e0070040d00303441c00f1100d0284030701c0c90030400307000d84e91704003060f0f80c41107030191400c0e80c40b142c40f00030103450803a5006000c0e40c0351001151407040f02110824015400d400d041c01482030352502d030010f44103c800080105030143c80240081e40ca42000c0d0b1207511901c1d1541b410201c0340381c1100c045000c98004d040c091004c5d9020070341c0303010000407880e0124400c0390010303501403071444c00d014014100d410a00035442407492903000b0400b44404021400d9600c002401c0455660843c2c1c5030000007903110300b8100d406652503c0c0000d402104410f0342140d406400307842203020719041401011f080e402002c4a0364031040d50300b07441c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 955063471 1250 955062221 955062239
    0xa0c0201180b06010e040608030f071b08030703120603030804060213031b060305100602030406110307060527011b051b060702070815060109121e0b070e010e090f04020a 74
    0x10360750186200300200d0504400040035000d200d9a807a005604000040100b4400002100c02e48250040415120a02850000e00b040b110842c0d03840100309611000c40c11700400300c003e001252090300c55542c00c004484800b415644240720280c0442c968000050100380031382c00a081c400c4004107480d280640700d58440200007140aa032001504c10703100c0511999801d071040a8000c80b2641c00c60fa410340c5040340c029940e214601a60003000154072110340680c504105842020b54460010f00091611900c41c0741001740d07140118482c0450030300d00e0f02082c00e061151241030121034219070100500b22388165400e43c01140441c44480341c0500c51500d08000380071241c0590060380c05450030030b251031800d80c40c0000d66a9a103695120078018880075a82040040c0e044900011800c400941e4905004808040355480720440c0803c00818508004203400344501c2204113841d03002c2015210401111500341c0d60740d031250481441e401080e10203200c1c0300101c0c0d00070310042c500904d041d15101d6103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 955064721 1250 955063471 955063511
    0xd0b010308091207030f0201140c01020f0a0e1e0f06071e0501240510111b030714090f10030f0602090108070e031c1101020c06060f04140a0c0201 64
    0x41c0c0d80c200c00030559540500d82800385900c01d80c10000100880c50543e140c0c0010981003280080c140612502c10b02255a0404103442103103000e00c0085441c0c40340b02d01050341d0317036022010740c40004a448118040c03600c4c00e619022550350300404010780d0407844070240091001d00e18400c0d540044140420800241000740c00840480b002f01c20780512807042ca08a0b080d40e40740c007280c07500d0105c07890225407000d240d01c04800c1201d07411580c000060b10744800a45901c1c6855122030f40c0340c0a110007250140144101d0340318505002d8007218121580c0350741c0e005814400a4540da406403484020400c040c0241c01c90307980200c5010303400803449680381d98007041c000010800700c800c06e4000c01d04035119a0000025684906181400d40035030300300708002521400600058004c80c0c60880450039064481c140c0709140381c1c3d070940210b5030b0300c406100e1503990760b80441c3d1803031080c41c140c0c031004000d00303050141c0204000700b000f540c0e135151261407100000c0c0004106101c00c40d981d0383d11609a4052190030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 955065971 1250 955064721 955064723
    0xe19031110150909080d020706060906120b07080106022e060609231305041a0118060801091e171602010e0414132a051f080606090d0b0103 61
    0x4001000244803a10b005035040b181e028800061420038808040349041e0202d99040d0600c00006135100c1c071070707c0e2000c020402e64002c0b26160340782440108182c1c6520000264050040041810315500c01d43d0840c0d07524024050031005030404950b41c0e00c010112000300541c0c20840c8200201c0014003404070086070b07500d44c031100c00500c0341d000c20004006000b05002c1030255450484016401d400042640a03410b0300002c415144e94400141c14050b4030030000c0c01000421800c1e03c92541e45510b6040482c2c003445038286d00340d00d800400220781205125000815a02410002c8601d050740c540d4501401d0401c3d080e00c400301e141c2c2820348240c9070308000340300c080500c40c3c8124415485000040c18040d00c4501700340a60700e4406030302484031a0280c0c1690009610b1140d551103c0c03a407820091f00314545a8160032045071402154810700f24581c0e050580d0b505840c003e12000e0b21030035049624441748141004102c010002c1521800c2020017040f01c2d1102600c1d400c004211035980c044a04001d83c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 955067221 1250 955065971 955066003
    0x703111006170a08030f04060b0a0314010e06090c2b15050601050702150c12130e0c03040b01181b08011a0c0c10020a020604091e0e190311 61
    0x1030502c16020b19510040021050000030100210182c2d1205000c1c400904890401001c00000030204039191b0003000c849107000e44042c8a85651340b9014100c0c03004040d5442c80382d4213240302c00c2080751000481e548035910080040c00140e0500381440340c05030500c1c0e020051250351441c103903101485000c04064080c400c41c10321000c404100040000c86002404107810008c00300880360150341c884d12030961140d94a03207070650398605482800c3c90603140340c02c1518481000f050441200d821801c8000c1294030103880d011071642e42c50b010842d288821180101070451200040c00f43e13000d042803480c10314092040015209103a100010315011035090300600040c0c400300144200100c465a00c026281041426814195030850240d200c071000141d40c1d0003281407544049800b407080001c2410150054109030352540c9992009000e03060b0074016454405a01d00a4240040c80d4814130682c3c0020201800c2e44030111b003415080c940040c0015002c0002d080d43c5208170560501040241082500c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 955068471 1250 955067221 955067231
    0x204110412052514011107051c02090606090d0b130f12021005150103020903101107060c1b060b3709113007200601050a050607031110 59
    0xc518159081115103ea0020800d1500100240000d0080c40740b618802400d001081e2110100c1141c90614150f0005a2118020001c018072550590407084401e0081d1848506a0303101e00510010703120b1400c0c91500052421110341c04a40384c5140240c100e003003402903044034030640c1c0300c8200340c000a44080d2949a2081c00c2c100d10507404100c9004481e078000402d1015181c003980201342920386001c0e49041c140c0004003004566018407100d50020100d203410000458014003041440c0c02000c1c00b210194a0321409121441c0124140e070782d414603280f40c043c46450341e47d8aa4024100c0321090682011101810b581c0414603181c481988001d405400b10359448212207886001c40c0c6980b1444216140c028902c10704041c18007120501c1c002d5006003810b100c1b411007080c2c10302d22407200c8160000204030510500d29442688080b029805d4224640103818031130700c0c540c503076400388a1070307a01c0b403110700c0c0400049c2828406408401d000b401c0c880d00d410b8241464909183c16a0024041c0039521 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 955069721 1250 955068471 955068493
    0x10504080901030509060121060b0d05243102030a06020309010c11070605030603250906050906030a0312020c0102040906050a121e080c030c1501170307020411041205 73
    0x50f2180170f600182c400014107144d407500003440840815041a4124030b0321015006040c0809034200040920010700080c002c00d0141c1081516401c2c19103004420901000410000760b450300310031401b922000d40b8003400340011410024601d01005507902049044480305009641c0074810005110300541c4c0250341ca00d09004da003400c44d440101c8070303400d014000c482d0351001880000c2c083d0a540e801d0030201c0d600e0302e0b04000203181034020000701014442130884542a00001036103c011078603407000500000c4d40341c0e8108103081700b0071115160194041e40c3c00e040440d00c1201200014058110b0052601d40806e8800b42aa480758100c000c080380c03105800c0106041c000c0302c0100800c48981000d03105034030341e80d0b0680c54040c1c940c41d003140c0f4000c240301101401901d008840c14201c544040b02d81d00e8043d50221921506000b141104800380f01d0000140c01070707036002d8540c03540c500e034000e10700d445000c0e03003000700520860092502c4580140804501c1c01d4127090040c0c620b500440050542c0528 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 955070971 1250 955069721 955069727
    0x40303090c0f060804084905091f022106030c030607050307030c120603050d080603070b0403030302130b030c0d0c1701150c061e0f02030402031f0e010504080901 71
    0x2984444200b40e60b003001040701c594040462900507074401ca040380d40340d4100101000c0725490041c140e13002e0640040c8642d461804402c0c0400d0f040b506000701443c03400f04c03204c1b4021100c08641001c4590022000e4800b0210091455885041e500000504214884500d996211425241454a4031040040c44210329080201c031911107000c900500b0b4500d0000f0009005001c098030071020b0503100c1c2403604219005401541614108600402101d40d507410b10f02e030b40b452202850703808520008042411420085100002c0d9995007688520340f031324581e4120004d42c41198008401802c100300842c580800c074000b1409209050030413500c480007140700b94101c8144525460501200d80e42d200d034500042c0920030b045400e0030400301c007108941d070302c2912800701200b4000d08035440c1064140701d8902c1e4544050306008000020410014088012800ca200954010b94141d01c080e2219112514149442611480c11480400c800820150860075210b058900b2200c07180d02055100740c40d64 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 955072221 1250 955070971 955070993
    0x816062901030605150f07050a02031c180305074416140108060105070b16090f08030301120f080a03050f1e070807051b03091906020c0112060e04030309 67
    0x12503034205c90300c82d1122282c60910829400c001000008900d160521800b48096620560081c054400d40d203400b07d1002d250440b546a52000f04a1081401d00c080310880020000d0340e90010040044a051142c0c1a4002141e00e40002c0242c02d51032000d8411a4051601c60400f070100f900240c154903108800b074108000f200740800c04803e0b0003420401d10020f0f241e110400c0c582030826600700c1e164080101d500b88103030680039180ba01d1030b10a11208600f242c10f04030380b40256503030b19000c10341c54041d00d0003820818400d041c007c8d4000c1c80140825101080c13440c0c42c80e44119558800360000343c0d91201c81d600400ea560000c20ba031401002403000c100040564404220200043c8000703004112506003400a4000e901300074070030000410b6036001b402181c9800301d40c03c3c030a81c40c8220070380e00300c0c3c0d40e0340c402100c4034000ca0711541000c0401804106071015501d0036000b0381315802ca40d82c011118411700c00d0550410b42e03121400014540305100c60140141d02a5030080b5582c521428071800c414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 955073471 1250 955072221 955072229
    0x15051605070c0504110702041a030f010b0a090c0e1003050108010506060702030d030c0e0402131401050a020a03050a1701120c241407020306091b030a08160629010306 73
    0x40020080600000d06082d018002d8400072100002c841e618a00c40110038010850300a4111f480c003c8880340340407481c400c21040c21800c8007101c0000200001c0c42d0309031001d001c90542c000090400c00d02010090b42c100c00c01011480c506240071214100000f1000b03c00c84a003500800c2d0313914010b0200082c02e0182d1036000c802076913220325280352940030136901c403540c2404c0010980d40303041100c148c81c4141411294000000c00540d1601d0840c0c03150710003038506201e0b844c110540038103004200d50050050750401080340d000350200c07898a45060b180c1c1d60203809103208100a4801140900d060841094041c00c0c080e0700b0b21107020b565260065940c1c0c5280c0001000c00f40f003040724640240c0180958080350064507010f15000407001069944d8019490000e6060054a080100703684000600580100b401e0720441300300110744052540f0f031035074110068101603041081840500c0d0414448011610a000008190b50000f40146003038006d0400640200c1c0b00d0300c4030030700b25a814003d560140c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 955074721 1250 955073471 955073477
    0xe0402153013080903010b03010c120f06080703080a0513030b220b060415050607030f140c060f09190b061318030e0112180b0702010b010c021309150516 67
    0x40d0034541e00508501c184403500800c04031002030405590341702900700d4004543d0250091002c40120b60001c1c011a69500390621014504402c00382841400e0041c0780403988148041c2c83c695040d616640c110b42e200d549a4824483d0030030404418141c0c8100c04401180583e4580720141848200c8886689160780c07550030985224019401288030380740300b2a0445000c860000d80c1c0958201624036141e41680300580c460808184e001c01d26030404c0d140111105950b99000d0b400783c243d04510141c0c065100748440950000c000241080306070411140c01110203006c82e40ca02d40000d00700043c0e18400c0c44220340d1001008240030043c2040c080c0d881200c070407850b041c0306c86115600d4082944083e41130140c02c0010300c01a030300190b40210030010341c040344140c0074003101c228030a47c9203415282da84100c070150b07240400a40c07010301c18401c6801015050350368082d40c10300f0b50200f041500281215aa40603601e9a4100002b44c0343d21241601035050040402e551400301e107210031496010740540b081c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 955075971 1250 955074721 955074817
    0x6020a1205041112071a040602071502070302300a02090921030a0603080a05030106020717060406110f0a0206060f0108010e040b100b0a050c010c05040f0e040215 71
    0x74030090807841050f2003680e01551500b120751605150803059407145010307245001030f0b003210031006030081094410320f800b100e03ca5130b40c8504201150711315035071080c01600548000d10062400d00040a2102160b014441d542c40b10070f54648562947c0b11443d03400c03548000e401004605100003600d81c44000117010b4680c0d000311510091060703404a41070301203c0400000154091026400400523542010015845950360780001d480c81d8828011740300075200e09a800546071038041009000441e1410207007000303403125907840c4058050f13400000c051a01c00d22181807016a00d50103401107900b00d50040045080080611280d0700e4140d2442e410000f2500050080e58048196141c105a20102051551390342010001c4881c00c035404c8181198000502007060650000240c0f81c04d4850000800050b80b0a1034241c9191082d803085000340c0ca14401d08006821880c0105680310340040d114419850400394914144e5001480b01003003603100d0380c80368406002d0303819103079117071859007100000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 955077221 1250 955075971 955075973
    0x20706140907170d1b0f0506100f0b18040f0c03060612110a08040c08061008010c0806240d020d020c0d02030a0210050a1509020309012a0503060607080706020a120504 73
    0x6220044d601001e4140410803030000400c0e541c038480b000e005600400a0160605117103000ba840c2e003025142c250200814110210780583d42100e524200c91a00074000e250028283c1000e007504d078814805980640d4442c042405031003580608800c41c1502d6400143c1c850600304040c0003502c4040220700084d140c016610b60940030704e07040703a2411040303042004c6141c1d26460114000d400d981c005403040d0052400784610001507203030700000e6a4403000207000395004004210340692040300c4061340b007005900700c00c02c12046100203c0d50f2560f400340c42407409007650f4500040e64014400c030303501d8130750024202c0304401088c403002c1c0690b00c880c8051840e200010000070755640303180f10600050f41d524404604922070a0340b004a62600c50301014040b640d59000c114000e4208584102d03065003005403d801c140e644030a40b0442c00c00d40114010070846210041750b00b80c200400d055000b1304104907441c0031980d02c6000c0c0800302c0c410000540d485150000042102c3d041c1460403501c6810079003840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 955078471 1250 955077221 955077223
    0x100b1f0206090d09080604020f27071b02030d0e01021006080d020d08010b0304080d061211030d182c01080307020f0a0b0d0f061205010b1e09070e0402070614090717 72
    0x580c0058040f200d400003102004000388210103211003017260402c4000ae2550311420100d602c61060080ba15101d003208003c00e80910fa44520850003507241c1c01540c0d208070360500407a1040c0c4c12000610484000c40081c01c0c14034204e98840d0041d005d1584095900210203130704100351280c0c9981440e18080d503501d004a1082e89000c0030b44020310050700410650144640380e4403c100074800c00f610342e6907800d12400e04443d003140b01c61002d4001c7c01480041401035000c0c03c00720f00345c0303a00c0340403075106240790110900c0341d49000d81e400414150b81080f441607044070302c0006030280074002d000d1659003655104000404c468014418024020160100001503421065078100100480301084800c070302c60f0568000c001a0300300031828111801700106011301540403010725001910200d207292684d0300d94054080044980d82c0c0d00203020800951581c2c0704400b0315240d8440600701504160700c176034403601507035049808062111310176000c2016a10701003100790020b0410344840021140200842 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 955079721 1250 955078471 955078483
    0x90609051225030216030305070b100f211a07020d0201110702060a11070f08061e06011b0c0306020a0e0a031101052101030f050601140102100b1f0206090d0908 70
    0x440d12a04842c0180052500a0208000d5080e40c02041d018003a140e20340a0400d4001d141e0517101a00071400298044c1260030f160001c2d14003034181003030440c0ca00050a403034540312020031244070381002c00660008a919000c91071804000524110360320340100700034600311198903950704580c10400c040c50100f4007141201c00c0e032a01940c010351340707559240c410b07a040d51110003a1582480344510010f91080707aa509c1d80240c915040590300107845601065a10410b8007501105080040c00460703660760040404407110010112450700b99000d03600c542e0190301c402c0e0b101f910020380028000e6402544031403518104501180c07401811400c5403202c0c8589461901d5003410b00200254510340c0407028801d0345a60354102409030034560b12132914031301c1400d082e84100caa501c541d400206a42c50804904110040181e0080c01203400d041141d030040c10407104074030f0b04a0101003070942281d003914000c48a50605400810981c100030740c40d146051032100300c1808100100c0030610070010040382d9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 955080971 1250 955079721 955079767
    0x20d2013050f03150703020a03060905191805010c080604060e19050c09030102071203051e0f06040219034a1c03150609120212010e010906090512 64
    0x1554204921022910381070300c43c2d480080e0303042813404001100e81e00d40c0003001d9009150381c0901c40940c2c3c4403501d0007034500540304000200380c40b51610b4012903d41e40540c2c0f000c001d840c41c1c000701c8c0850b030720f070107085800307494005000030a8203080001c1350400e40900070040002d415621224a80001b4a12401d0002202e8000e503588800115501c40c41e82001da58035140020001c644d40e024070b20b000346150400c0004500424241000611054460061410120100e441c0c21880d41e44402c600b40801c03c00510b107903441035092050003d841c01010700310b88500c4503070311b0008502556008604500c0c0d226a0b03605222200c0503109800c0103002202801e801390008071041100c1c842c3c00c407803414540341030303030441448031800035800b00b070b95068025640070314900300005102c0e80c03642c00403900009107010381400e40078810000e00060400d100b0b10400e00c02d020780001100e9a024885600755540088240e401c541c5070201c1c40d007480828000700305400c02805d55a07142208a012030034040c0302da400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 955082221 1250 955080971 955080979
    0x5060304030c02060c2b03020901051c090f060b090c03010b070b0618041a06040203130803070e12070501090e0907050904030203210a050702281401020d201305 70
    0x400c0300454032001c05035140a007440c1c0581c1c50f43c018000d1403c501c11a0031b060f200003c02030a96080c1240d000303200310b407008281a580d00e8980000d008041c041e003803060380054040c0344c0c0c509800300801c100000109142c0e210b400d0102c3d0b0002940d00304044800064100030741243c1c03c10040152009507400c54a850742e015290750307116a1a8400910b1030203000e4104900c1d401c0b03100c204010009498020041c1602a003110f40240d122001404101e02045400c42c000c4003c090100020581031805103601842c5403030003550b81e00040000c58001c2e81d110b611000c003136000440c140215030b0040000d9024003410100c1c0100d41c904105441d585070791510481e0300684010003c20189842030040310805004120181c850303020304101c0d001140c500705c8848140b245410301040486102042402105c115003034807011204200000b414116035881c0100e89402080c0c842d1000c5460070f001800d0b00e01d00b242400152030302c54061003425002400e4110b200e0500800c103955001d030180c88444261641a5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 955083471 1250 955082221 955082237
    0xa050a060c0501110706150f120f050c2d04090f080a020709090b10061b080318241f09020d14040609030e060a020c1c080d09110a0506030403 62
    0x10502a00421080c0018000c603540042c5c900e09015541c0c001000c0307008004100300c801951081211022000c1e80140680016000600ca001c10440b1062100c01c50103401560108801d500000d4100f11804070402110140c0c00344100103c2001c6100743e0605000351002e014070051a900da040c001c200c080300815201000c140040f130f680c420400240035028541080004001e641005010140b04494491140b103071040041142403041c0c1c148004040501000c544016940d80c0e030191035080180082035030302148651128003582008440c030a01c1c02c00c11100ca404100110b04040e0700c0d0014516041352441080d8241c441704403116100c2199010a00107031902410b001181c060510034901d02003280c04101400107000340750740004401840394440d42c0c40f0800d00741c14081d9901a041e0800c026070008042d005960401c2160754405c503003654038000d8200c6066480c1d103100c0d0440c0301d0200000d03942e44040d034100026200070520707805003120300d15010342c5401c00003503081c800100014100440c078 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 955084721 1250 955083471 955083473
    0x2010e0f0c10170c09090106110a03030b040b150c06100b04060c0f151514100813050a120e03210d0b060406020109210207030f05100204060306140a050a060c 69
    0x10061129180001c140007421402d0500c00942183c004585e19441201c03118000201c2600071040a01d040082502905000020303803400e0300101215520302d0340081d00e0b252040c00030303a54140c2c0d03100801c69100201d13072680108100281380c1000202070940d4583c0c0e2400a002c00344c0f0b43c40543e0100c44041c640b01004114500c4d0582500e01100401407006514400702c00c0802c425800031404400741341c040085180d62a400303007070179201109401d0b82050506240e41c00840c4180c00060f40030041d400d200000d0f0f242d955640345071900c0e400040d2a4200c1104100f14030310703400302d41020ba01c00110300805014072071207142c800c00c00c100384400d0540000054581c000305883c0e000300c1d1703400100400c40c1c1d4803a5500c100c06806001d80f0302c01120184401817014459180c806026403404040d58020442a8103580d02d0324503203020104281c9040c8620f40520217a1310f0240003d2018060980d0085155840c080c0451002c420007828140b1446000c0b605215648501c800002254040e00d0102c07610801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 955085971 1250 955084721 955084727
    0x30c060a0215070908060601090311041812020f070b03010303050409020307020f07080304080709020403050604020d1505160801050607150b01050d0906090201090b070b0601030f1b0f02010e0f0c10 86
    0x40b032100361140141a10801428607044000f88003100c5000d800c0e80c0c0f1039513031f103001150800590b0100070310700454402150420f0a0940c0030714000651444807803580c0c0600d454410a84610b80c1680c001a40440b4003c131001d00103000f50002425170300c0b002ca0865041d42d138090040c0c0107501801240030b501100090440e44200540800003000360103039000700b03450700700403074a0358424060491030b445101400070713201000d40700716000c1700e400001400003030701c40b98200608031301a54415212200450641c1400c59418400c3c680a02d4030202e4818000c404048050552038050340400d1003003900703002010204088034105030b10a0220340c4002048042c1c0401a5058000c1401b0041040d00e41700742001000050350062621034000d89400e000c071a48ea84401407148200030b0001c1c20a081320f0003080c0554001e030031801e4a001584004140c1c0f070704c40c81245002c5040310100000242031041070000d49074080c440c10000008441c05011450071460513655140ba50844a0b4000e1841084500410b0300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 955087221 1250 955085971 955085983
    0x60c08071b031509121119080405060408010c0f2d021603030203090913200402040302361605071a0108030a03180309030326071d040605030c060a02 65
    0x98031003c0c249441e07400c15104001001da01c10202d032034144400030803500900070845c030304050304824000c250780d802901a10001c0082c5c40380454403282d00344004941c0d40e45000283c4050810342c4000030301c142c3d102c0300c0101480c5400382c2031414050f901030604440390100c81520303620324002c50040510b00143d50124900140360348244a40003403000301008159000c0000e0200d41401ca442c00362039168040d0507201c9010f800f000400b0700c0840d040c405c4154154010581c01c06000400c010300b440e0782c0c1d0700454a204044400d030007241e90142070f0100440320101e040000c14451600c44807180c908414101200009032652606020002c6200c2081060001c0e540c1c16031340d0308030fa001d2855603551381020758907045040b0140204c0e0401c4014100800c010401148181d0103a0724400180d00d10740303040d5091480440c3d02d80c9810319414401811050143c03125015488903942c001560300886035210544c0c80c1000301e54031542c140281008181d5001614103c410011605e1541e0b8645164007a8500b00b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 955088471 1250 955087221 955087223
    0x7120509210703060e1b060406022d0a0809040c03050f0c09120706261e090109060516120b0d0b0c0d050106050d050117120d060f030b040c060c08071b03 67
    0x5e0810f061541010000300303d5070300714101c2c28403080c1c8910200d0100200703402280903041c0180c1c0050350410511881e4491603071602c0303105110160030360002c110f65081044802080d500400d001840d00c042d81810310a16250120601d41080035003000300c444022104082c20031319086402040101c01c40c3d564181d40ca42c4145068110780440399140c0c000f074100002040858020091341c1d40d0081e140005036000f070300c5180b00c0c0c600c001e00c10000f02450490000701825129540d0769501a4100140c40c52180b07500540000c003804506c0b07200c4000041898121051400e0b1280c01c080ca80d02894a46240d0111003660080920515a84007000b040d100e006108000c40c0b200d083c280001601c2d50450000c1c4003030208070205002c1e40e03891751680c001e4000d5a41c900842a40322071b40301a50300e04a100a0080d90203245808227003165500003150000150350025244091078200340801c015080741110001e0500d41442015064035482c1d420807801402400342043d0818030394500c0c014034802c5540061 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 955089721 1250 955088471 955088483
    0x21240916050d2a03060b0f3f010f060906080105040504030e0a0603060329040b10090c030b040f0501050604031b0f08010c030f110f07150203070507120509210703 71
    0x883daa4441c014034034440115403021915081c03000c1011808441107855009001c50010f1400e00742c000a0090070041603006c0010640080e90100d0100039544070780780c41c40903a070081e070448d4107000c1c80c2d00020350305034005418001e06080812005070844031042c1120320072140003a56940d5418182d4042d1040800c3c03d80c40390280300c0201c0c8a54141c0d00100680c0e002d0400405c0b6180c0314182a205140020f0585114030f0180001800040c0c820242c0b55001d6a03200c1c505c1e07100c2d80d5619814091390000301d040000b1a450310b405441900f13261040f08003c03030781c0d03003018446945400003083c0b15100b20300015180101004072042c00c0645910408000c0c0991100e03001301560b160003550082501401c0c8030000380c02c1140f020342d1450300713002c0c1c0040e10515030701c8146858070744e850701140ca5001945c1244d40843d140300f9000e4400d00c62000d0b5100c2c0845e03494842e41c401007440d0a0032451646030404050207400c0c000000b00351609207075649801e0300304004049007554088000c0c9000c5c8598401041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 955090971 1250 955089721 955089761
    0x1512030333030b06010503040b04020f18150f030105010f0501080a1e0b0103290f03160b0a0816080402010309060e011109040b150307030221240916050d 67
    0xa800d08801d5410449010300c214241c142c54040044130648410743d00a05580b000300c021401520b482e4103410b40c480c50050130a01c3c0c112650ba01c100c1ca2041c2200e0071501c00c00010b443d4902400c0640c0861003222044000b007100d50f0411009100081003401440e041000000c00681010a02d9111104072121038110f020b04c524042000b1001c2d00076840c406001904062410f0402800f803059042c0951201070320011485200040c080503c0100140310b515110b64203d51034402815070b01e5802030405054420380d600501c0901510f004000360081c400003010001012115030300c21285a00b180e42440c0108000300d030703420107a02500c000700d500345042d46000c540b004901601c42c0182488442030714103101c0901207004004415015440c41c41c0d400c00c0420000714007502ca68000e1120070a03200003400343d0140354101c89000402124203880003c43c3e22075410104017180b1600d1260755044405800c0c62401280e41480d02e410403c54070240b0030b000c10440c9801e04140c0100c4404940390720100740c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955092221 1250 955090971 955091051
    0x160c06050103050c130b0f060a0c0f0506040311072312030333010914180f07080a051501120209130b0f040203040209010b09061905070615120303 64
    0xd15002e600c003841c3c0c41001049194480d171901d60082c002c0c07070340300209541c5030f0250a00038010075601c0031401808000cac5030106200041e080f0083c000601d8050710007004130386043d180252880c1c10308200000103038841c00701048024081c070450b1000440060500030200001000310301c444410440d0607010740004010085403540b242146582c015800d1646040301440a1109a4155101a0940c0003400a110a0000705048240c4541e0b040014156451155820300c0203018000305444401d00301d0008802d010300300b0391200600350449002d000811141c14412480211204820001410301100003441007102d982c2c0ea065401600c1c001c0c2c14480d4107040001844001d0a4a55826214600c000081c20403401c2c40e10950b4483c6074080e240804613402d12130881700f50b8209030344280d032043ccd0030080f407000c0513400301c41801d14020399251140c8a1616180c408180c0320500e4040942c40718003d401c00000b4681000054030a405013000119010b5034202c0d03445402c190f65440404a0501300c00c42 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 955093471 1250 955092221 955092223
    0xa020f07021003140f07020c04051504090c14040b13050711070b0408211e0408120304020907030905061303090302030f03030108061005012a0c0b03070306060507050303160c0605010305 81
    0x2045481c0c1d13244010f0040d960b00340340000201041e6a504016486145201642d09290f0b2041c0d030006607101c166107003140100005802e443c910241120084050320701040154414030081c494110111814000b000459022480d03042c01d4514010102c2e840d107000c80c03050f502442c02c00300042100030039280c1440d140e04503042d1650042c4a1142c451040d01c0414000c00e8420841e420100d040c1c4600070700d0031812030402111110700000260300d103903040200250050041008031050001400759544078a040c2c010020b01880052990080c503044c00740000000d0004201c55a009862021040e4200000d040849140225800c02901449580c0521106400000113503040352504011038000c0e55a060300340c8001d505a100b481c1c041400c04428551111001300d119000b03c00e801c0b2061881446500c402d803980380b0b26804118814000418051141d5060090341c01618030381c2030107031400000b55241a5648001130550907036041d0704d100756440921504000c1d0b11660001018400355071030b03050803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 955094721 1250 955093471 955093481
    0x5031608190312050a200915030601052106040c0305060d061509050c03150a060c17120a0905010e0304271103090606030118030c1b080a0308150a0e0a020f07021003 72
    0x4c0014038101c006c1d12070a07206160200c17042c840018282225540d802c00d08000150006401075040c0642808003010510140e145003c8020380c5503211140e500304141480100c0381001c3c3c1c20000c050805d030411000e51a01514900c41c20307400b50001628026070300241a40c40b0a43d04800200c900340001e101e0ba1148000155020782c0d101c03c2d41200b07045401040014900c918800d46001c190a00c90040c04501c419240310341c0380154082240c90700700920000041d9086c1201c5070b40c5103650365600d200034003200340300fa66000070101c002980350031304020303c1c01243d01c1ca020541540c0150040d007225501c503103820001016042440941c6c50b800c2441d0695243da0040311801d0003907281000342d07048803a101c12001d00b02505a02d9100300c40c9800c1c1c030381c401c020010341801d56000d0000500003a000004118440314140241d407541028105082203241101410701c03014820109110300380400703150580829042005408010394030744841c0000c4c3c1060080f61400703903000c503c0f1910314444c25055046 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 955095971 1250 955094721 955094741
    0x14010e0708060f1c05150a060f032010021006060305091f090501090321020a0e0d1109160305010806010b0406051c0203011d07020111030612070e090705031608190312050a 75
    0x487e070307151412a021111103100d00b00d0604107e400030004103000940c8190488005c00700c40c0ca24800d100c0214550107007072080c050050b482444480c000d40307030500c1154050a07141c178007030006040c81c40b4500c0e940da4080b94400252103118501e580c4c107204030360109400c070b0342c000001c1c010200b03a0300f405407045d000700052180d116900004181004014030032140f40103403035100c186e81d401d01d00040c031407900380318041180e099900d00f194144e1a603d01e04941d124500e01e8044810385070a20400805550040e48400450f038031800041c000403e0050a80d8280c40142c9061510340085100d8107100404040611441c1da20000000c143c0807522410581d0580d00b800e44110680c80d1500228201e640b082c801c10f0a00b40140003084451400e089a07040440e8a04100c0380762030749179200205001c406681000255000840401842c1020f10086060b4404081c1100e4650b24084025842d00080e001c03d03040002000300590404ac00b1381c5220fa0056440c480c2006940380c4200c41d40300070004042 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 955097221 1250 955095971 955096003
    0x21090102101b0f0212030106030b030a0506042d02030307330f240b0307110f010203010302030721111c0c03020a050607020604090e0f1014010e0708060f1c05 69
    0x43c10720162400011034449441d039a061052071686041821402488a031943e03503854020400c8040c003091041000038040c5008128020a48000a50400d248210f07001c51702d2440c030741035900a0240c0c4c1e010040e42e880d0380d086040e2280c040c0d039a0200f442c500c05000e0305a0700b20325103084c0381010301000e5131055a526400c40e00400c8040d00c1440703940303400042440d140b003c0c121004002e0000c1e5944102850b08044542003400341003018407806070400d107003012180703034503036000c401001545000c0007604c00810840010400c00e0035429801020000d00c200090b0041c48030307000b1550f890322440c5800100d801da400c0c485000c1c1c50203140501c6000007d10059208007200031001c1000d280c8403044841c0158001d000a00d41440e0010403000341ca044440b1040c0b0340100c21412401441c00d03c90511085140100001c14034003008480d0200e20040e045900c2851030141004200c64000702001d8110400b11101c03d0680c0c104000981d180d0034099456003080c0031040803a0401034006104007103029648 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 955098471 1250 955097221 955097237
    0x9060109110301080c040b03030409090311060105010525050a0b040f12080601050d0905121b0d0305073002040b0a1b05212106090921090102101b 64
    0x1803010301c820b000138010003200d0340010368100c0b954907041d409120b103010013a00380c90809642ea8441ca0455501600642c003260a101e141c08003140c05105160140209003082400d04900d01403c0099009400d44006410552004401449003c0043d10403180e482981c3c211f071498540b40035650b0384042d000032140c200840e00c00311101802181494419070069550740e007411121281e010240001d040c05940b0b0340200f510b8101090381102c020309401100c0c50382c0b0410310b600c241d68a13280504000f100805c0628000a015007103a10101d01c544150034a00c1e5044882c07030f042e0015101c9102c000707140c82c0686c8001400500b0341d00a901809259815856013180400020b0384044210b4001034001c020381c00c08110002c2907000c00e0011031031000600b04080c01d0000c4040c0c130121580d2204198007000300d648041268031714110701450760000c500c1015201a803014107140000c041f26011101d910300012800000f20303403081084000645500e01c00b442000c185280f1001c10b104280c60510002d0041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 955099721 1250 955098471 955098491
    0x9150507020c090601200708030a110705090c0706020c0f060709290f07050706020a0b06010c02091b09040207060903260601050f04090e0601090510060207050f010302070b09060109 79
    0xb09007049442006880c01c1030550f11314004442c020007140e0544a60108604190704c0200c1c104208405441e803d8011540c4078803000000d0070b0300940340b000c1403807a4090801030142d51600602c56800003501d16070b95480300e4140c03034060068020b80810390740c1c81c0716504203010a0440028120b02844064850303907032042c1c60701c1900c04411802d44081c0c40c80200b0042240710050b0600c001c01c6131181c244852800c08100fa9110b17814a40207a10610069109800100c14040072103c801e40010003402c05541c201c44560100e80550001024039030300034100e1007811104036130700c0121040844018011552201d030391502200a10040e0001c1d400101c15640302e06103c9106041d403d660780c441410204c0d0340e074907600119165444444003041d941e20a000001342e16015000d1101d2484100d0050b02071903040c210300100301c0303400601d55030b940340e500b41081140381d401103041001d40780280d808084117010500141c01074418920020010709140c400c0007420030002c101103058425103075060040181d6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 955100971 1250 955099721 955099723
    0x5010503030708090f15040b07060b0105190806010e0d1a0a020c1005060a1211040e0d05180a120803071707080c07030201060f090605030c0d0f0305030c04090915050702 74
    0x9642c40081402c0b030304010390382d40da2404d134040e90ba00b10002130181c100345025426010b4070382c105a00c00003642002181181c1040b13910700650001c80000e1808906103c1102000c22001d845074280343c0602c802c000200c1c02d00d07440f0350400c5c0c10500b009002503483d105a8503006603000d0014092000a854007004120100140e000311260090150001d104640c40651004020080503000d254415004400040c80c07024003410600c1c140c2c00350b601032540301540820b0000b52084200c4091803a00600490204181c1010070340b985010813807a800c00412151010400c0f40d142038100d4400d4002050f04c040c1004002401144200c2c03181d5603190300d03030040d0090150b0030034050703600c880440c00d41030014039401c1c8401c0c0900201802440041451036039180302d03d0200b00103400c107501e500c0d1991428070031418100861340003030001341d903800b8164586441e1159100e021040c014108407000010a801c20b0f001e1090340d010f4942d85004024440c0c86240082998050110403c079150800001559283c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 955102221 1250 955100971 955100977
    0xd03140106170a06031505011e0f061d04020c010c120e030706050603010923070503032517120a11090a03030807033209030c0703080a12020a0c060501050303 69
    0x5561140802c00407000c0b030080944a00400158516a4070039000000c41c8000062043d6803e2181c4000f0b041e5040100c1075000b800545250f4020082e0755404101c0c005686090204588440c9840a0090361045450703003e40c1400c40400c4e4003500208174010314042c19403241c082c03141c4a444000504d085c182c2c07030368155501c4183c0944103400138070500d030100342c140e0002030303000310b0003400081c05584541d507080a50b107200d545142c060840c01007100c8030340000c101c0b44025080c218019802c103040545010541519a440f01200c501061342090400500700d15040542c0c201d0202c440d161403021128814442e003ca8600005074101211410040c44c20422240e0b0000d000c0c0041d0070290840e1000c0c1d803c2840540303091308056803130303409285044d03c880c43e00384010710181181211424082400c0c03904480a0088421600304100700b404010300065031301c080341da012400948800c00140e0640310342c2940400800b80c83c0c0002030f000c4400740d0084c12100f41501c5031000300034603600ca000380755880c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 955103471 1250 955102221 955102229
    0x3010f050a03050c0402070f020d060b040c140412050c22051e0604052e080c040501081e0709050f04051b010c0206160203030c0a0b0a050f06300d031401 67
    0xc0c108421418107402c05070010540a4088c03c805032400030240e02281500c2c031003840035940c00d5174075001d02e42d0034900750060340c0035680285002c5509500c1c00032920041c5c45180700e0b1043d41c406400200d410054288039001240e40000c0408041c00320241f422003d070840241c40e140c00a00e05400144d1144403000115201c8120a24800e05590b40c14240701c01044041e01d031506060540551a003548030104908480444860461072080d280c0009549080c4403c0d00c1c00388160b050070010301070384600151950100071285240240ba02956030303000d08000c81600111542801d1001300308030600032140c1035000b00c0c800d108607036105100c4803954200503240d04082e80016505d0b02c3e07910162402c2e202400d1801d14804100302c03d5045540004d203140e102480140b000d4005640d040f06000c1105003466102010300d6007070146282180024004500c011b2031140b16031001c4600d0404ca00c402c051021240c950140c51030f6080304100a2695511024072103c00000d04010b905100701402040c514125 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 955104721 1250 955103471 955103473
    0x60e01051204060c0309060c0207031e0809090c090a090c020c0a150e030f0627060c030a1116050715020c06090418051014010e0601021506040e030c0303010f050a0305 73
    0x50b031180e65400c0013908181030742d00105030310f5148190200d030040c0302d00c125a01c0310790000c0204511310b02d854060744d40b094061110302e58008118a01065142c02100c80d0010220f401a0701a61201401e442d02d000740410f10350420114030703010502d0000b9034000f1135210600c1c0c00b1a182085140d04100d003542d111f0155039551101c80d20b0301f078036490040c802580070540050943c2c010020146542d464420100e940d4074040c80e1000b1000384080b140c802200a038a07000b4082c1146241c4104106990f1001804036000c80369200d20309a020b50310042542d60401c1032500b65103074200b1038200b0f01c2e42c45055000d07141e0003480381408590110b000040c003071100103000e0241411701900008210041194038500000d41611100035070008805110004092030107140005004003002d00d800c1e0f8643c0b050300300481480141041c00410303a00051140014044c0300c0454210382c0d90400803601908501c58410024807010912001502001c07000d541640c0c0031050028269983d4410000204403c2c4005800d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 955105971 1250 955104721 955104757
    0x30601020703060c02250e10060504030f03030227040507020106050a051239010f1205040503041526100b1806071202060c03190905120a050301060e0105 67
    0x940c842c1c0110403202013600690b14500c4254103250707078090090360080a446002c050030700c8014200a07056422071009815160420b050500140c00c0344500c1c0406480408038100503003c00d80304e80c0482d40b0301c0c000300c03c0005c40c800c0703002e05c29512402d06198140c862400c110000e03601d40d10510598040f00e00051051002628142c10b01a10114021110032a401079404004a0b080c1d00c0d480c20041002e84030781e41f0342c0b502011580d10b55104640d01c1b082c0c10001e108942c80001544078801c5480515407120005950300c0b90324040b850b61180e5401f2001d02040003055907000e9411031003064000038160907105560b043c2c60300245031080101d603400c0050141d110244901e080ca44040c1c05a00d041c100c07007138a403d10a07000201580c01c0303034130304861002c1100c4814800790703414044141c020180100440c114200b03031008940c65403801c40f0040503181c0e601c40a209000c4104104030010400c3c40845988a65000e80182603a209000340c10101b10001200d0070954404c004482c150540440c0c078041d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 955107221 1250 955105971 955105973
    0xf0c01140904020d0b12070e010909030503060603060118090c03061e15030603020414061002070b1815070609020316030b060405040f120207060f1d01140f070503030a0e0102030601020703 82
    0x4000d4104001c003c07190b6a0354071703140e889034032440c1c42d428001022070001d10b5454600090b071103544205070006480c1c2070802038508000786d04082900c3e00903804440ea44d8032591394000480f400d034191280f605030f01200171000140e4140f140e120801e00303006a42d00b03106881e107400340003074540c50f03084406824070540c04041102080c200760060f102451841e01080d080e91f81e40029056904d6a21510801406541030001610703201910482040c1240050b101d80c80c5001e001d0304c05801500d050b401644050155000c9c0e55940f0940c0c0c0903120443c05a4a0b260002414440b0050000d45000c034001e00c85c1e08100103142008500b450100d9601c081c0400680d9280750030310001e040b001d0802c45540b480c40b44014000f40324100c01d14040c29441d802000b446160010081600190760079034400d028014840c25842c107140f0282280021007070900000041c000d000c00b5015101c1e0b40e52209502102281000070460088015805458115814040c00d15140760150807440203440d403501503030060700d00b00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 955108471 1250 955107221 955107229
    0x7030503060a08060103051b1905100c0b180f06161b200108010621050c1b0304030210090509060f0f04021c1109033c0f0c011409 57
    0x341c0e0207080500500030965442c90014500102a001101c1c50f820a00103001d568101440130107806108841200000c0d410701004000e601c050b0084a00031030401c00c0116005000d45000000c055018041285a2610b0171a008204c504002c0a41e81303406078624841e000d48002809034000c81c400390150b40b000302e540c0e07403e407403551072000001000740418131b0741c101142c418a45074400d01c01c4807a4400359203025030001000c0c004142c0150080c040c4c445420705510030b2607048640c1d80c06800358005030589030000c1d0518607010710901c2c052070048008600040700c1c804009803040341e100342c0b8040c1034100340c0181500e4807809400b460303030080d03a2000020b041340b411015a4040900280550301801c0080c400700302a64040d503081801c500f9006038807564000b06101d4612030500d034404003402c000b801c4000907110341e0400c80d46552520016010315002c54421080d00c1c00c0040305400304542000c041c001c83d15000076200e000507502401c0301c092425401080c00610600b41d08071080d18181c83c01c8100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 955109721 1250 955108471 955108477
    0xa1a0106080c0a12020c0307060f020307020714060706061511010203161206080102031005091024140d1d0619020c1216210c0209180703210309020303070305 69
    0x8200300454801e48040c130703c04520091582000d440050b40d1741e0807143c01d0907010b50383c803a400c200340c003441001008080c5901203005026a0650341d0140c401000400009210380600000075140c14a8451700140c040c0324444003070742d03145081c0c541b4042d00d010504030300d00301c0c0002c551003c0c440d040c1c1070804690712312401400610b0035074040700180554881c094242241c20450ba185000c1c1140c400900c0145081040503901c0b03640c06011401450920303c101900c00c1154410484400e6007004060041d40101c444900c03400741490703583e490340d400c2511500603080b520f07002c1c1c2101104040308108a500442c203113215144120402c0307820048240ca000007548000d9002903640107948450800b54985002070107614146080d10f05041010b08089140d80a010782161815080440440c407540c0c10100301c030362240c1c04548a810315598110300b001d040d146400425502d0180f003a0103c1000203002c000c11103180c103604541c405110805099013102c524401c080e616600c02e11034040002c0c450f40003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 955110971 1250 955109721 955109737
    0x6060f0309050604110d06052d040503040512071a2701020d050a110f0c04110307080609190203071e0f050301090c11030708030115092114030c0a1a0106080c 69
    0x88001d000e001c0f40c8901e0708232207094032145500c416440101159420840c1c410010b0340c1140a42000d6090590f1899a244541d1054a0003045208040210044103002c010004d09540754994540003046020803041d0303009458104210301c002e15500c00321051690018500c00341a0001c08040b44091815541d98001030100002c00ca110041e510712030702d040c4015003001c800c130402000030202c10070403c81580d1603040c030508603640a03c00c1110450b4080111504110181c40b907015940317070745c646c1210f003100b0519140c0c3e42074000810b10404c00e81c04460042004000c0b40c405904c680410421141d05181c0480075002520502c0144110700441e0301c40903003501c0d41d0501b92044035038401681d045811150307044d40c2c02c882c007000401505110706030085c016009887d0000403103040142580b040382c10700f2014020303058600c54600c100314405100c1982048164116503c51140400407551071003401e0080740c043d54258102c40e10480c2c072181c054142c50080e11031040b9580d950041e80c1950b001150 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 955112221 1250 955110971 955110979
    0x4060b011d06160804050a0b0705010509030313030c050c0a140a050a06020d0509040e0609070e1f170c22060515040614040e070503010509060d020603060105070f120306060f030905060411 82
    0xd1b55a60714185100107001c46c003281a110340c11810302c3d50842e00014100e1507550006c00c1001140c68041c1d0502e0348559141c02c100107245170509219240c601c407000303280d03040905030801003403801004410395000c4600711000111070b83c554060100c4400280b003880c000d42d0281c0580403155020708050315002c40d010b0000103842141c01e050502c1c007082070310087d1494005410a004c4c0c41c00c4105010750250240c4c41011044515846d4007491011603c16820b0b6904803102105031980184601d49a10788001c0c082c1c8000c18030305c41d1501105180151580342c0c01e00e407500018150501070302c1826540180c82440b0308180c903140b002d82d801520303003808004440301040b000c136065100c1c1c1c0c5c0300d078000c001c25039444d034496051000340600f5140160100313129014941d04100145d81c3c1a0481c1d60215084c03800d10384070121440d0216038280d811500510210000908665083d4590311042c02c5612551701d400c00c03c0d8035541d0680484400400c00342054004c0310026012403d1100451050700780030b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 955113471 1250 955112221 955112227
    0x10c0809120a080a05031f080a06110c010f020a1206030f06020a09090509010903111501090b0f1f020c0607050303040f0201052811010e030d0e03070b04060b011d061608 74
    0x19a403070903198481c130320382d1021440c04810f00151950144143c1440e0400386803001401d401d0130074950b0741c0c02c0b1034000200340e40e07101d2107410750461880d42510b201000e110000d0050030f040c1880d0901941100b400e0600143d801c260300000011280030300e1045a0b080348007020b10440945401c406544106d0040e018821250703400586090780d403240324841e0013010000604030510740b40003891034054810015199006074060080c01102c0d072011811559110320000743d01c41140c0c04200388204840c00158802286004400302450320b18070b0b00d40c2400d2540c00c1e248404180d4042000c1c0340a2a000500710342d10900000b000201c0204100c407140d80141881403c010509640b490407aa000c1c04103001e000c880c00b0414010351300a00c5100c00c06140d03030002c1c040c4800f5500d070700e681d038024207090280072034803580c2000c100c01060044400d80350b08640344074a61f1425041840c0a0100074190a000a00717407030350502c050721415010703401908024110382c81c1c403541900601c0302882c4402e00b605c61001c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 955114721 1250 955113471 955113473
    0x2181b12011a090d030c0510093c0501090b060d030c0b060402131206140903071e020d0302070602071e060c0212010c1d101e141c0b010c0809120a 64
    0x7184007840c02e54800c0d6140406e0042074036000f0706103120011840300c1d6908040e09a4005941e5820512034801035a05200203249030345600b1564801c0e01034503840308907042c0710040c2440010341003a45c140d4002c0c04166019111031042c840d0500450f1030180c0011103003c003a6000a03800029541c100e44002c10140c20501c2e2040b07080090386243e80f00403168400c40e2040d60400142e40281d18460b10041134400341d070714294042580f248502c0702d00078803415880c50050380c0401000d41c03c0b4105038010303014403101c0b140b514000c2d6480ea85801400d001d441503440000d42e174031140d1075112081c3d0054011111092400e40140c407580d606c20801c0380d214580003a0351070041001d2042034150603280d51038a40d49501c44111014989030451261b01a02c2d0074850a00c1e413a0700000004400580c604010240b032000d25030450f000c900340d00da00400540700080c1080e44440015400b0b080e410075081c10021003d0740401520440d01c0e107070005007030039400c0c400009140f0f4105030b44070030f07007c80a0a842030300c1c0c01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 955115971 1250 955114721 955114729
    0x3080a020f03011d1f1701060801150305150c0714010209030d020705011b0218071107030302011d03070b0105060d0f0f2408031e0702181b12011a09 65
    0x1007600040103948009a00c4c214060a001040e50090305001e040102580346920008580c41c40740202003095507410321907820407200350701c14801041240e008100140c49400751022603103040c882030380c940c800e100807840501032481201f8080d4803210103007447d005040d0b6484440d01400380c01e0754800d542c280480f01c83c3d9142880621a03e12859010344203242c14400050000b01580c8850206256072600040058581151203500442c07540d40e15407195842d4041124802d10341903050302c1d207000d0484004200b5405411404040121403052003026920710202c9559000d045806403030650803400400a0b401d21030010590850115408210540341040700001c0c1c41102c030b5441c11043c0e65400ca0030003e0840c180e614840c001000500c003885180580241d82c070300642505204000e11584280f48061101040300c954584c00f4226101082c5140d1034034402c038104440e070081030b203a810002e0340314980310400c41303883c60418400c603442642007090004008008502030318001200b085140d24580ea = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 955117221 1250 955115971 955115977
    0x10c0503031807091e020f09120a170304030c0f020f03010908031005030a03021209012f0d03020a021e010207061d0f011a1905090a0b011106010605040303080a020f 72
    0x1c04981c010b454980449114504a01a400100f08034074185907400d41c000002d0003901041e411541c0545c503121082c16084552003020035566002082d4980e4101d800740c04602c0c1105a8080c00e58602540760111503c3c00b20b201c100e80c000c001448160403140004d02d24603100c40d03104e001802d01d0808802c00004a070840300c040006850b4800040b080040c1e80f51100075200143c1000e0b000380014003c1c0b50f030040c0d92000c4403104110020740c0850391642c141d119074400369a5645890711000030b1012902000404080070340007190b03074010b00c068240442d010b40202c84018800380c1c000c1101044609105020070410442c4161a540810000002c0790342c5005000c500303e02c01c480d151412082e0111940b0303001c0700c000104802e9042c040104041e440c24a0f00510000e03051f907040c082c0c90b4802e44200c101007000d802542c0c1c800301e15030034058083c1c1254031141d48403200b82ca911241c4420440469a036480074031510000480800c0b040c00020f200d00c80c655000b012130580541400d05003500c00425030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 955118471 1250 955117221 955117231
    0x9150f14161410150e22060f05040506060d020303041415030a05010810140705031e1f0b030603030d0902270627161209140106060f0c060b010c050303 66
    0x3a005800c45943c5100d00d1141070f01302902402c15419113031501d40b516100000007001204042403045180a8801a00d0821111564003000810402c03072100d00103001003070b0699060340d442c4a013000285260400c5c110364148140c0080c029428985408414450101d100c44000d03000540c05d400030b6508500760b009140a00c0b601d080201c0e0fa90b0402a0780303481c2c0280d08042d041c100d410481d0780020440c0000d803060700320b440d80c544240d076503468401883c10611031054001c240c41003401041a00d4510600314000350b40100305181c001d0380d54100342c6035a03000596000d90726800400541d6074440071540030401d00b80c40a011114007002424070344c1d1074103022124800c9894407001c100020340c076240060541050440365540b43c6105c06e840d001c1c011a8000342840c2c00086050201070800340100c240e103101d000401414090b10301c0714075100d1200300041c0c0700f071462907080c41c0e00883d410740901080c445203000c0e40e44000c20200a6241e49002d4203440c5811414482c11181c42d0740415000d000a520507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 955119721 1250 955118471 955118473
    0xc0b4305070905071430040b060f010e06043b040b0a0203160c030201020f270f010210050a110c03070c050411070f05030f04030309150f141614 63
    0x1d0340303808000e0003920401001e03001040a05070044440b03000c04001c2d200d0181c1e490303041000b2a841d0300440360321018280b0f0400d00c142d41903000c000400120212480c0f003920161803072020b01900300010744e00c078045602e0240d03004805100600c180304444a802d100d00411080c1e088036010703000701d15410030401c0c04c04900410600d404120500401d40001034004440c1803003145940790001000900c0405a070b254810400122006c4003494400d4050751080c0e010541c101c0c3d0340311249208140041040352030000c0b0440b51b840e82000e50715110b00c1840d050201a00642440503500002100610f8002c2049484550301c0701c02c80b00d01c0714410090100724010000071580c0d4119800d2110103e1002c1e4011031149003400300314889900c00501351f80310258012480c00900403980b07461825400346a0f224605103d0106002041c1036100c3d0082007181c0030300c401e0a4520103c0d080c12502d41c0480031401000c208038104604800f4218401400d10b800701100c500706140c071a81e14610060002c01400c492 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 955120971 1250 955119721 955119733
    0x60602210c1002160b010e010f0308071b2303011506081807030b062d100e371a070510060603020d0c09260a05030d0203040c0b4305 58
    0x20400717507a03d828003502850100d14120340c5080448047c0c40313945d00004099403004035840041241c20582c41142c1303544004100e001039226030458100c80481c40900080703010380101c004107402c042c411400e001a2100c5403c807a24204203055030f070b0174009001040d01801e40b0020480c400824060329019600c10410140d180c103141040044103044035014408413141807140002c442031401c070039102600b0039110302d1122103020006654101d0a0a01c3c181c0040303464407200010401024010b090810014446144801c168400c841e01071140c001e481107e400e096203d058114210b01410704a4030800031280c0b1001d902014070155226640440040394011803850911801c5010b400d201c0002868071450307840c940101d06e80c4030194540002e07154107001000c0f8003441da00b485148103141d001401c4035940e00c01c83c604c50000b580704440c103541c8242074038000719048641200b2104144110703551008001070780040c140d020540c041c042c040e814582d80c1d6080040003180002c01d4901d0044000d400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 955122221 1250 955120971 955120973
    0x20a09060801051c02220f062d031b090c02010c0905010f2f1203060a0518041407080f07081c0c080d0605061804060602210c100216 58
    0x1003070318180c20003031288500f841c2003500d03202d240b1810045a0303011100c0c0d88403d036400440003002400301c030f11301031011b05084110508a81d540c0040b03044862244061200c1c0d100840024072020b0f55001e0004501c0c0b0f8824100003251b01800d262246061030341d2000c681d513940b55003900440e00010080c4003d40d4440341d54020903a086628840140030138200103c2d00c43e0400307402041d114030210058444505c00e102c01c0a0700300c041c01c54104030702224003156040c840d40710481a041d0800c40388644104030560300030845045c500301c0e0202007030320000840c1082c1c40b160360f0880da010482501c64894815070301c0c0054568810803d02042085000c0034101e4a820502280c0c104121420340c200d41c800c4070000c40c94010ba1201c1311321005a004052583c60b2811082418003808984e4811a88120b012803100075a01c40542c9018954000300e90810100b51380b50021303600e80d8641031944610109001d0404030a6000f48020407280711844103844100c40d1042c04401203802c000800c202c0003600707400d080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 955123471 1250 955122221 955122227
    0x20313030f140a0507050a050601080304030605011e0e151009091b0c030c03050906030103140105060406260c0d0615080316080c010b040501290909040212070306020a0906 75
    0x4400e1842d2620010150348a940700c032143c4140304044003007120001d1140288a0288281300101e40d00c0420f41d060b5513924000035036607030414001918110f01c2e100c00001c201d11292041050401444803803411603141195400b4003010091483c4a9604100071a20041c0e030340f074810015003501500c0d00501141802ca15004030b480002c4001c0c074003a59a401041c0b203d811564412aa641c5840c101c010244030340350403106030082c032000c0340e008800400044104641c0e042c02040c50724148001700110b0b6103500401054803043c1c403601c09410001060600c6410301540324016016055044503100c800300310100b010119415400d0724401d031f8842c0c401c03000c46040e01c18030004040c03000007181011801c45c44071600302c0c1d404100610b60540020040c520510a411803814140003d1040105680d02c41081500820070328094005110084800b50b07941ca045e425200c1103400902050025641c5509208405034a00c001100c28460200d0000c0040e49500080075868059a01e184120340342507409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 955124721 1250 955123471 955123487
    0x1060312120b030c1909020a2003031306020d06030c03060219020f0304090203180d020a0201020d0c030e0603101206150b0a2f030c0102041e051804080d02031303 71
    0x10030340079040580d1074080f994000b8410b14544422207420f80341e490b40a60b10a203a925590280151a00100d0200d01e0542c1101c075400d102c0c1d50740c0e000b24402c43d00055140b40c07248000c40b0401042c0a540d640d8202180d85580a0b01454506810000e14607860b500d5050076004950302c00c880454001501b140351420080421007071004600040201581e00b030400c50702ca00590007000c081035808000219104020b42001c4100e046007000c0e00c2da05c03260444001d4445440f094140c6c0948661180008207174403d0300034038561909036543d01081c2000b081000200c0d80058080701080c4111140816801031041070030944a01ca070343d001401307400c04140855803075030fa940000c00720081444174141203030308032040e1082000050204250a48605803082c00481c2e090801a80e900c0082990203468a05500400513074001080720001445a0703000d14000706400d001e000d40002d01d4035200043c0808990340c2c281c200f441004190305207101009104103d81044a42102407202c0003400000e0603000104d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 955125971 1250 955124721 955124747
    0x8060708191418010212070e030a140c01081b070f0f0c0e0a0c0c080d15030c0803040915060f0f1b0f02011b0209270115051302040305060a020702060c01060312 70
    0xa41c2010180c2d0b402e2040311b0002490142408407801c00040d0640d001d203d01c0300440d1740824405540c903401c4002d143e491100428040c04a4004004240c5101411010041703d82c03030301014500e407132465038901b0b0200110b50800c560601c5208a43c000140b14000036034080d1010f000b50440703078070788410703002d040d2203032202640248480c0c04000c0002c20315100840d6402021390a011a800320a55540980c0f04d01a074005848080d28840100e41d13800301000810481e0401041440001408940c10040c0d0040b4456200843c00c8000840704441c02032001c450b8407403050801901030310600304182c26940405a04803424948031241004540e00060384c04914070820081d82c01c11036059010904002000d032914401145582c24414102030003031021414031182c100a010605080b881d00503c10614041d8500c02c0f030542c60481c111008510990341100c2c1c01c9002010543c5401c04180000d501100040e03070000420009021549024081e104c001d5120f1034592200c0700d84007800800804c85904 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 955127221 1250 955125971 955125973
    0x10608180d051b030c1c1b0308130203011109030c09150904150c09030212012d090f0b150303070c0e070507060c08060310110d0b0103150801050106090f08060708191418 74
    0xc42903880703c7d107407030700d140116a040c01c0c0515681c40b031000840551504250003940756003040307440812401c1110190500c15800d0b0708440080390341030100410f00000720383d03400360f83c44035100140c903510300307598016042070040810450203c902101c131025600c10341c1c00e1101080f2500820802c5040ca030441d440a520301000030042c02d1107120090120b00c84000c510701d081000700c20741d04901c0d50355030700c442c01642d0f00540c5e1803c124590f1615102046e01200c100111a00690b284c0500d8100401118402e42d0300c2901400301604000850803881030107801501081810b01007440000e00520a01101481030303207500155190981c20140381002980e69201c40c03c1c10888807802c0703103400a0a544121800c0c0310301040000070709004900070440c0d20f5003841741c020244030001d902c1e0f00c10b50005058505c541c0d034a840c0702c0d840300020121540144549401944005c0000e290107100d0108150001c00e51341c2c50b0309103415031184d0301d01620307038a5840c420024081401e0002c00c100c01c00a58a00140c400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 955128471 1250 955127221 955127237
    0x1031511030604091b54150b190306060504030206090402120c0406120507050a081305030a050c0606121917030a05010608180d051b030c1c 61
    0xd2800322041c007000c0c2c00c1500a1391100140b01c04c020021560700c4961003400d200114141da500048118400b03020750f81d088002100750840b51458402101c82e0036503d024001b2104116a1103041101410855030f0072080f95560440e40002100058000024040a08856280c680c0030b11030107440b081801030b41092614140c3c003041515006002d0b54200d940441d14152900c800340c0c0860082e104240d03451206421003820410b000640790054010303528959503c0c0d02c0c0f4020f040300e0400b200c41c20307a4038002107203003405200030492140e1034039648120f50403079500055080d40d8134a03140d07400c0342c0c5542000c104081041441c0342400c2000d1f40c3e0040c030440300070440340d000d1400242c486000c1c000310001c0c203907081d1880090210a150490103460b94201c09541d915080803400c0080000b8011040003481c81404113001076084491800c0241c41d020181c4940046800151119400680c0003080c400315141c9801d40400d05002030304068080b54041d04004142401c03941008818251080a010101e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 955129721 1250 955128471 955128491
    0x405120c060f36131104061119020d0210031d010e0d05040e040803072703030305060409020328020d0b180a11040c17090c01120903230702090708010315 67
    0xd400701c3d180c2d403410b50f074603500b802000e8000d1300500312494090021070300000740000c6480c0d02890048000d010034003036030800500c1040310340355070030202c10281d48132540030070030320151402d5032903052010007c0c00c3c00181c020740310000c0130103c2c0c14a104040c00ea592100101800070040c46520b88102d21442c01c0c524007030818088420022015001601c000e00c0440000c103083e0140ba00007a00700060284502040c4000036014001d10540c04104e00090a04002c100d060506018002c405540103020b84084e0100c040f00748920801034000c80c0700c400c400c004940143c2c40d050b0341104803038040e0b50202d60f140360040c5980a60708581089000c0795000044650100d100c00106003003042c4202c8007c513030300c800b5a0341118541c510750451914860b43c00240810018006850303511031000ba02d41492030204440000120b65450034094085290242054840b00e056036004844840b1080028148005900840c002102c202c0b0f8800100c0c0c00c54005000f0701102500c10035081413111000e0108000c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 955130971 1250 955129721 955129807
    0x90206030a0b010225090c1b14100e01021e190e0102160602010e06070f05071e050601170c0d0c140a0b0307050706200405120c060f 58
    0x1060941c2166441c0640300d0160f101340070004418080f00c1d0724111110603502c040807820007911408001e01d103801c480c403407018051186802c042c10100c08140c4c0b500c40c55191103a403070240100103c401d018000c800c0341001c0c83e5225030060620706100042c5c4030270b034071400c81c035651a0300500070b02c0500b414041c411504070720400c00011841e0901d0709106040b008030041c0c1c50b060b07240c40100200900e0380f2002c20050390540c4800018010481102e040742ca90040a07648215050f1040c03001420421042c0003143d8140e21303100d0001848100c907001e000403910b465042000a8120300411a04081c50320361a05080040420714401180d04a022940c1950b80d46a920300a1050303041340442da0143e030b45c080d503c1c01321002c0140251411240c0c3c91a220b0001812540400c00440b401031408101d0703507110900303101c3c1c00c844811200304949414100030401c08105440703c40f01e090f51142a0200d00942c40e00405407141040980149407208001e04400c41c48403104203030b10b1400d44100341d0030102541 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 955132221 1250 955130971 955130977
    0xd060f09140603012d020c010c0302030603011401030b0c130f08060f0705090603180c0a080f0706020601033507050303070e030d020d080a0b1509030601081203060114090429010201090206 82
    0x10342204105c1070600310a0240740a4010f00364881c0da203501c5c0c4201603c0180d01a00110700c00c1001701d00821401d4140b40307488000080030301024164406250006001d47c200354001c085900209107100c00c0a580e17003450080c2c01c0c0d0380d90002100d0340c01410a210005041c050305c240c006400d800d10609140d5a13201150480c00700a05001d10706692502d00c0000d500203000220f601140075004606658940c1d0460356240f180c05107581052103107400c00110280701040d4181a0ba5000581c034100400700c108404003515420010351503c6400041c540c60380144200030010103104034051030b1245803021000c2c0c51440700000d182d020760071003215a5207060717000c1101c0e1b00302421800c18600c0c607150581c1c100c00814003c10707425080f0201059035a0350b14907900203442d84810440031100180c0e00c030000f664450700d904c2c5418041c1a0140b010554541c003400d0003d54000c2042c1e501030070030394000009025241140304585407c4000040306c0000c1d84c101d41c003071618550030300003032010818a60201c0d581388 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 955133471 1250 955132221 955132271
    0x6130b010b072114120f01080f07031103030903030a0801081912200307050109061b0219021f03020304062d050a060e1e13020a06050d060f0914060301 66
    0x8180300c0c40d000940b80035101600c00000b5a00185446081c0005440085e68060b030300c039401c0c8650b980000403d55030025031a04103842800c0034098052440d0b03248040071100e00000e43e81030100340b000502a40b001c0001c0c0c07480100650341e8180311751400c1420340c1041c10000c04800261a00c01142d000b01d03002c00264103500049140900d11034200c0000e02d00084c1410ba00d501407030000003001028402c054016003007050103440304003c540c0400e01101d0501651401d18405a0000034000c042ca0801002c00032405002400f00c0c500d0400407052000c0e0010803104200100c1e50200500003400060320031100f440d03c0501c18844a50815001c158601001c092007401058503039000840c0d81506030800e200414400512180c5820050703002400c0481311005444500322950015124145412036206095000b030726000740641406002c0341c0642c0301d128413142c040e407a88000070344101c4441c80706000b17000140002644145020b5800409070001d09041e101e40e0414040f8110148020008920a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 955134721 1250 955133471 955133513
    0xf0504150e030a0c080102040e0112022209060203160f0201140a09050309040203040501021b0c09010e180703080a02010f110f0901021903031e02120402190806130b010b07 75
    0x90301c04180040e2620308200c200400704c2450610000d212801500948244c07415050150100d13030320361445407404005044042e502c100404d902e60708001104406c455502e03c076140128a110b8a52645000d030f91059480c2040320f140e0b02c140d401030a503c41c140842e0400584028000c02101c0e00d0034042c62200074011401d0140e03120704071010413070100200c0c2c1a90760050025134403413510342002e0f4000c0d003001c0030142440d0003207120030303c84403008a480d03040c1c08802803d06040364240300d081101514010103a03003c44e04c0b010790b94440740100f08600300065100f0300100f5075610052200a0a5610380f1800113000c41c01d1000000103601c1180660740c18549003800551165030200040349014916a4140d1000c40155a05018554960400b0545012550303050f442d041c44110300b4007c0307120f9032000c1d80701610144c001c14014546100f00034089880d013010303a080e83c1e4881c42e5140c14940140c6990f0514a4010340e1002001040b0b04141c1c0103005c5424100c0c00c15055885584110820441030604 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 955135971 1250 955134721 955134737
    0x20a11120f220b37140c010504050102040806060a0807090504020f0910050319020306013804050a0e0103110d060605150304051009020a090f02040b0a031e05010501120f021b0703030f050415 83
    0x488885400f0b031b03140051900024441c0b03081505042e4001d5110b8014001d850098074005162400c29402c04801c0381ca0003801823000c1c5240c10750b402300070b04c8040d02c102d030f00c820540f1032030940ba03aa02360142e00568296a803100500d28000030149441c420701400720009002c252a000941d5003c550070341110310454140011a40d64050899005440007103038050058120841029810610140091f180255525001980c8811724004a2902480010403e100c01001d030f40c000d04001104e00e201c00d1046001103005900c0f100059031100004886000c0544040104010300404004420724101c650504000c04060342e000310341040124000d41240769200c3c4004200102c19a048400820b40c1043c0d141e00c41030640802005848200031007088400d03942e807040310b00e003114840e0310304070740050310b81c560b010b20581c0800e00503180138811034004030380c20f01c100c010340c59142e400809030b545408050301d010740c1103190182c404103402e10003408000c4180000d01009140e10805110040c1c02d081c5102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 955137221 1250 955135971 955135997
    0x1101020618070501271509050a210c080304150315030507050607051005070c05150f01090f020c03041410050a0509041815020a11120f220b37 62
    0x4100400e072100082620b4424001298807240070400c41e00c02d80e55071100391490341c480c01c21104071074070f000303070444007000c2c6500d5210080c04000e042c540794491080702f20200d641d00b0100e0b08540269102440c030000c0d611800f240c0036414403683c1300700c4400d943c2442545042d51542c903030b80d100300d00070140120b0000070084140501007081b44a03051000381c05004034540316000a003641c03d8400219400e1041c000e809821101c05001603114551071802d010b1075070300c5d0000d0300026012109401010f15403c20074544104000c0c0020030280c0340342d1404004039803600b0144840e000e030b414005010800c082c000c1d8110282d2010484041c0741007150701046100d00c01a100715112042440288225110b40c1070071030244154001d00014400c17900c030503030204821b401c1d46498129901e51130448800410404400c44060005000d602e4003143e084851114140030001c2c1c2d0704c900f600550100c4901045028904040202007401d4168603074403440160301e11994014003482d0170241506102400c40c0081c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 955138471 1250 955137221 955137257
    0x1005220c09030b010f060311070b06130603080f03041703040f030c080f1603120605061c06170102070606060302040b2b090c080c37121101020618070501 67
    0x1e4095a04401180040d5a4540343d8180c0c00c5101d10503480400c5c280740c131001c030f00a0940e01340c88809420101c40e0215903605820400001100c1c02c140651030364400f130120200f000c54000d0a0700c8001d4900080c0c3d282054102280e0104516009160b43c00040041000007a400d1420308070165048c206100101400d02d04201c0e140104483c51400c010080303009861003140840c0b0b580c0381c60007174030303500380d81c89002c48100d00307031741287c090303030703400c80e104110540d03140412010100a03a81c0a120014400782c07504d015203101344040140da02e050707401003600400d12015101d128004c0c41c09007001c500c0c00d80740440f14004c41c000c4114403d41d00c802540300e03e81643c582006444203001c82d142c1000b030070340c807450043c180b0b000e0783c010a06580b09008650010b400e220b01080078040080e09040031a10503441c2d060f45034003c01140c0c0400e854a000006116180c400d14104d40c24030480300300c0700c20250352000a103044030080ca140e21013000c140c43d0500a44000c84c00303009564003842c000b0201c89012030b40c1d0b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 955139721 1250 955138471 955138487
    0x2f0c0f0717120f070203100e03070606050f2115041a100f050402070f1203021e1e0a02010b0316230f0d0203071a07050f011401050904021807081005220c 67
    0x41d1000606004607000d1040d402700003002014459441048926154028011100c113100c00345600100c91480c06401e110000650142007804103088407620a0300e584441c2c0c4180d0150b604881c2e5000c503507080890f035412080c40550204103240e400f449146440f9242141c0007462080f640919070018484003400500303070003001d6240e00301c520707030003561800072004000394010340d5541010b10350354419000803500c142c21540320841035880400034100e40001c0603c564004801c03202550758501107180140c80510802000c80141400903a915140000b119608200031400c404100342c0007400c840b00307903510b40b0030b00082d142c180d0350840f0f807258610100703260003050740111a01004ac40c5446407030246401c01000828455800e40c2e2205600d110201e0a071000302500c40c074050003650061080307062034140c1a0748140000c040403a60000540c0383d114061040da25400000c0406080004001c4848408030041c03100b076070898205a0b01d40c8106e40d0700442c15500c0c880641e120160707209503610030545 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 955140971 1250 955139721 955139743
    0x307050c0706020d02070801051b090612150901080604022805060d0c180e041502070b0415060b0702090f060109150809060601032f0c0f0717120f070203 67
    0x40314003207902d0300d0001c0c1d600c00c44214901c006110769400415040010700826000326445003d0881d035050900b01d5210a400000519801030800c1c0f01c20305582d44400c4c4071038001c804922032460000306503428040c82541c160018282c40d4088414440107031218230518051003031f01400401d4603e18024002041e8509500c403550040c03002c68234040e80d402a0b44104031014113600e58204858803200c1c54103203040144207a00200c0c0700400000c01080241c00c2c07040300c0380013238440185045095556000006020b40e400d44880d801031183e00700100840c072580000c0c020325200396041c4101a4001561090300609001d6403110003404140c050b4090071005003d003c0c7c1704208500c0201c502c0c0000e044c1c40080341c0344040d5120750000f068040d400b9100e00c0c1d07084400c82d03200452182241e9881d0700c50a81441050604a1040101200d030503424408201c48142e92400b9141240c60021404d410203c1c0114a1a103904100181508001104101c03003011441080c02603c0c0d608030b0000900b06a00f00507 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 955142221 1250 955140971 955140973
    0x11040e0a03090f0f050604170309090106051306020705060a05071109091b090c0a0509130e070305011a030606090414030f0405010f1707050d090203010c0f021c02120307050c 76
    0x245400c0607001060a415900d4209141800d84e94541448001d03111074460141c2100007000b01b808080306415000702c0e803a58413011a0700d001502c1c0b0120361160400d91200000980c08600401c42c1c0d0050b03112400285168802850006e04003000504d140c41a00340e0203091140001c0c084081004954849480b41001404a181c0349891401b9a4a40c042c3c0303041c90200e8030411460098034501890424012103e2940131400d10201c60300c1a2140d62099103035540c4607030030a070300c3c00b10b038881c80c0100c821411040003d0415946185421401c1d20703140901c072a051201c1880442c1503440000380c1c20740c1300008417081c0c407042e04c45023021b164555650300040c0c0c1901001038842043c0300304000420403158203984501120b070040c1001c66602d0480082004c010301b0540201e4803103803041010340040d115501c00041c07800700d1940024211400c030904000440c80d0405809100390301071294024041d10072078110300840360828001d4484070455090690b0050110104040502c11000d0b101e210010708 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 955143471 1250 955142221 955142233
    0x6060f0316030f2112091b0b09011407211103030a0b120a02010c060b0102070b0403050f0d14040e1302040504061b0c1112010e070303081e060d11040e 66
    0x20912404648283c101035441c034220b9001d00c0107003040e021034000344624580d00d080411009442c0c2401a00040c0f0060310405107a185414569054074060344c0200030844200c2d81c3c82208030005010301c040d40c000105480710a0201a01040003ea40729180b666602101c2c1140700c0f01c22001d40e00d0041c040d1090080d880040104480e1582079440400c504104480800985c005040303803669030000d0000c024000b4500303011500006032250080f40c01110b05006581c01241c590b4221003513a0016031094601d0303405042d88420202051090000c001240d14120f0721820f4000354400c5d4a110302e103d5030054900342c00014420701c0c0d40c02d50f4061810350007407003071200e8100f41c1061406442c0b808082d0515403441001d00055501170030b5100c03181d03940441d109041072407003020803594031038881c0e80000e95520f504840075426800e210b460701a6109858294050030300074802c0781c0305903040c16502406c8401e603051200070780d142038200684960050840d0311a01c03815000c10058408481094400e00c981 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 955144721 1250 955143471 955143473
    0x201031e0204050301110903101505030f06010e13030507030e010302070605040602090102120c10110d0603050f010e150c0a030902040c050405010215041205030a0204081c12060806060f031603 84
    0x36070028411180c0c00c800078480c41d0118246410316110783c106155260f0300070344030609480125003100400340145010002c041d50340e40302090816842182c110110f410040060103410318030200305801c0703110204620380c0d41441e540e003d00184546100074080c00029002c0c1001c1d688650101c42c0069400b100c03c0c031050402d4075054000e5003007002503d026006201c0b000460712400c0707040e00d02c04e03d0343c0e03c0100100004064070800a00c801c070f4607080c0c40c0380c00700215035114205015001c010340c4214001c3c8000c66403020164210744101501c00601e812401e0b11880f160005a0300b103070012400001c2a6613080e449505500070074a6100c000e4005052820f003c20190300301015000301ca10a0302a20300d1120041c80741c1481c204221402040e04000c021400d000910031005035a00c5a03072108018603013504c4902d06480c00c010b83e50303441d0b050403500240a000540c030505aa01c0c0800520062240328184403050740c03a00c000030007d6008070284940d0100c5036030200b20f000c03040c0103002074120300c140e20b07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 955145971 1250 955144721 955144781
    0x30f180307060209040c08060619030b03010903080423060f090a0c030b06041815020723060105130c08060f04110d14090303090d0804080d150e0c090607020409020103 73
    0x4044d0303510344924544036407503d580e4003410043d807098000420880c58000509510030040601003005010955074104071160364030309102d10820703d8002e4480e19031900d0b003441e160946000070255142403589407000c1800b4128001880e6401501e040105061036440c3c41c0b480d0720f00340400d44050180c64034000d00100740b020811203103020314000c1d54148001c5050340280f840300400b0392002003078200d5030604005104d8036030b409000d8440c4240501882e00340c00441c140030492000b801000143c000e03500400c00d91411200040d52046068024040b407000b407103028006000003008680950000c075000700095695174000c180712010074071031a4461082c001d5807002050416000b0651804001c04501103050000989114888041c0104410a0021000c8403d114060700884001d8410b2064490480c11400380d1102403c1200507246041e01c0c0c5028100f00c504050003003055100100490001625401c0840310b023241c06460200d2520081d1004030001d04400b0080c2080c0c400714419801c0d6410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 955147221 1250 955145971 955145977
    0xe030a030c0308060102120405121e0d0f080f0f0c040b13080706020307201c050c0f040b0d0212070914162604050f030d020c01150506030f1803070602 66
    0xc0243d444003510b41e40c103070059a1303640c1481c0c092480700405200c10000c501d010482e9884e811304607015900706100d200411030302c1c280340c8202c1c0203564001c042e007583da26034084801c5162071801d2625140768140b01c005000300705400f8001001c0c2c2142c1200081811401204540c014004d1028540c0d468043c0402c5048003490b500682002d0300601100041840c400416120917035081039040081011801050a810854218546c2c10a0148821402c082602d030042c1004901503400b5207110351030881004144101106007a118a00d000c0c1190100d45550318410280e41d4180c5003c01c0c818074101080b441e000280c1d000480c0d140c14500c58a094406031106503001d0000d480d0b00450040b1041e0003941c21984000f0013a21241c5682c446400303001c0c166004603041070155098171200741139a1185404c0d68090a1240c211a40004660b54101d50034401c038001d21485481c410111390900001401070310015026800e09410300021031204100e007003090043d501824200c0341d032203d00c0c1c076144010750 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 955148471 1250 955147221 955147223
    0x31b210201020a081e07080709180902040b04060e010b0d09050a030f11011b050901211e05040f080f2709221205120103081201050a12120e030a030c 65
    0x14413401c04103401140f101e010407880500d01c01c5045055403241011561040700921100410803103000002d10151202c1e00902c017902003000205002d00240140000d9030b20100c00280a80e2400700c04000b80512040900d040d0398034501219039542d001c58002000e032094801c060f01d54000c4a9803602010740011400000301d490391160003100640e40643d900701c6015103142284118182d80740b840442c440c400500b1111414100444014200c8107422824a485013003030344090740d510f031443c4010b80d9441180081c00000101072100b45030543c0c3d0b541803107540c00c600508491010894680c80c1d280c52090b40c0003034401180036030582c0e60103100c0210900f9030b80c0e081c0b03001c0c1340810003045021110360910714154415030707990103046440c1d5488003a0494003041050800c030040c4240d011001d2030213602c5000354080c40046450300381c1ca24440070340b26810790016216050700c0c1820047c82c13140008058810780c0012131140c1c0450000d0341514032000300b42003954540280c480d14000c05411400c084595 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 955149721 1250 955148471 955148477
    0x13120e040e1c0c0b0106080601092c010504060506040915051807030c0305010501170705210a0e1f0209030a0b010e070e0a1214010b040513030813031b210201020a 71
    0x881002043d10007040c00740b00548070510100050048a00400005801c00e4061515103001981c40c40345074440540d50ba0500c1610230342c00c1c04506d0020041748034034050101101d04015641c604000545107108501c984008503480d80009002c0c2d1103100b1400009040142040310040c2c1c01c2d00035440007040840741d140c0480d18000007030b590644a4030070300d030580740f06861b40411a1030b6240881f4245100615078410014104a4038620140c48003541c12451818548400981070190032001500d88003550840c00d80d20003926040c40b95140c04a403024a810030350016a01d040b0400403c0c1011620344000c0c000038101c0000141440c0c0318107400784940c85e03039a6585050f10042c01001901c9010b44541e0707140c0c465281d00d03140401c0c0d40c8000b54100d0554400001081100200458241c0710f0480d40c2d90080070156200c10141070b00800410360001d607595280304002d2103070707030090200510001e81c061248030401103e03041020303182ca00c403141c0650101c0300d2190805800028042d500044101e000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 955150971 1250 955149721 955149763
    0x19210c020601180b06070204200d060e0117070b03070203040807030c170c0a051201064202030f090315010f170f061503070e04060203040c05010813120e040e 69
    0xf188414851000107050003000d00340f8002c01c640800c000fa01d00f4140c001101c00c10f4071340c0300c40b14480b440010554040040c1001c1842031501c150b158151005030302c82d4940e404400354804440c24046100c60940c1d40402800f502c9031120300c42207207180100e40003102c080c4200b00c4044280128840c48400f1a81c0d02d00154901744010200d282d01c4e848079801760f54011180d040c040c03040f40b410303460349035004d03550360000207030746654065008041c0d41c031058444411854110a500340a074850b0b411540e0f007480c4142c806445442d0400035a01e1042c42c8204842d4000410044c10310390b42400804d410a08560104806507100c8a00051080c2c4920403501418008001c5501105c0c000c9280760320b80000750040c1105990741e150817002a064400c400350705018140003c61807450003040c480c00b03540a09001038a91600780740a0a1014050700024144200351042001d40d10a0420102c1c0842c1d111045134401499501c0c2613407980c4038040b6595000e070905a00841e00a000141a4100e0140c0744180c20 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 955152221 1250 955150971 955151009
    0x50f0105190e030901020601230d140d020312061309061a01110c0d0b090a02091f0e25110709140112080d0c140c100e0319210c020601 59
    0x582c130b2180c241010b015030480307401000351802181404226891003500400c508849c440000d00b071030928a411a1801005000450340c0c10040001c0c41d40c44000340004c600d401c0301c1814850013402c008150610400c0ea40b00180015000c503041081510750101c0103110750705400000302c66451801000600245400b02404980e04001034034410743d05000e040d500c0ca12046449889030854014500007451140882c050300585814120610512038000c1d1713250075515290f000455501d0940c8500b1224041c14140546400ca049d0344e501418648808001d20342d1030f0038800d882034404404400d209010b400c50018006ca481d40104100141103095903c0c40c0c1c0c1c890a42c8030b42c8242d2090050000c03081480000d508a015038000b940007107003401c051000c101603084503662a4010b818801036a046103070703c0c00700001c0600441c190440e40801a6090000264149141c5014420500100681d80d103048192500c0320680f28000c1154030410310403007980d480c0c080d595203400c0c030910305800c40d450b01c928 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 955153471 1250 955152221 955152223
    0x609060402040b0f0708041e1a04050a051c021c0b0c0421080c0703060207140714010309031b0302060106080a0209060a0e041d16060203090616050f0105190e 69
    0x1d040d14400c0c0c55060610b02e48030181013135500840c0d002c6980700340070000860300d030011402c8400035860f0354900090300380c2412021a0700310301051001060900900041c00159100c0081030700340d90b400e0b82c12002001c0e004100d0703402084c600c58003a410a0340c0c81403544900020103620300700240241d8004015407140c59100320075114030300c611011405020803043c1c030b0944807138000b80c01501502c5028207124420348500c0c2001c0003035004070340c00c1d580029420708100c0440100001c0d100b400c000361074060b152600d541c0843d045540c03118109030713480382c80c0300415029074890380410108289450700c0050303a01d00655511000c1c06080d0204410000080c4a03081c680200c3e41c200202821090910000d0130054440803000c851091f401a1180125000e0740300c0031008080c052041e0380180b5816642d990081111541c0d60024401c54204200050070740c2c81c0d43c070441e03c0b0700401080134404501c25040c45810240c607000c406a00b5401e203c14000d4100d261859207444008454040104401c0100c1d11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 955154721 1250 955153471 955153477
    0x2010b010215040c260d050301170a0312022a0c01174c0608071d0603040503120f06100e030d0f120207081c09051b060f030702060609060402 62
    0x200f030304d2501d00e0706000d0200540102540c0314150200a5140c841610b0f40e2810888000b800500142010004100011400e901c1014070440d42015000c140c1c16501c0082400740e41c0f07800d4512140e0002403800c4d9640f103504c000a2a04000491f440c208800c0e070007626100c0c1d074a010420700041011301444000440d110074203001e0030aa10110307112008076a039002c5d1b907100850100304900c0e5008052492a000c28015861a001803d40a500e0505140c0081d05c80d81d80a40002c0c03c000140009172062401c1c40c20182c6004000c440709500ca0f0341d1882c002d40355105140e00100b42c040707800180b1605a044ea4891303401004211565001c50b040d036a8210340f91444111400e5040c1c0c041c0c3c1e03140c205607002e003c5d0911540c200703107481e03803420f010052800c0690380001d800300d4100318006148002d020140850103a15124004103000114842d112565070fa4028204c42140c501c8000342c1882959800003107a410b0345041304090786902c0d1070880652a0b030421543c00c1c0c0110207410021700c01d454141300b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 955155971 1250 955154721 955154723
    0x6100801060513180606080607020d0206060102070501031802030109081305010c08070204050402030109021009030c0503010b280f09050921031303020a172d07021e1002010b01021504 80
    0x181c0c0042000140f003601624101c4030341040484055540300106101d03000d2074003d00710000044c201e074108420003e1a0255640d522021900130f40103001803070303902092036001c4640918010503001c450b103000600388440d1030802540340d807800c2d0940c4200a6010043c00a42000c98004624142d4234001035a8400402a00a116a40402000380140341590103950840c0c006000040d00035010360108175401c4603103c18502180c6608820000c12008200d69400703031505800a000e094041804035607004d0070a4548916220b0403a031a5000030480307420340004081d50000e504545940d0206000207010540c0c404226008004c5850b07458120680b03240c0c0354030025400d847c46e45d0b5801e5203d0341da16148590450460040307904220108544160409040b070030320300c1e415500d030001c07910b074408001c1840e1840c044001c4800150031901d002c0056420b0940c05960004a001424a42c40600700d01e0070314065001ea40c9519140e5416415400a44a12800e800702c0d0600816900034040300541250 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 955157221 1250 955155971 955155979
    0xd09061209020315130b0103140706030b090708041704180e03131404181104050106081306050c0405061903110403080f0d02070530210720061008010605 67
    0x18030801491350b43d04a03558007050300d0f02d801611441e16a507441c02544c0aa0003030f5060022401c1c0062180000e018400060940f07050800000c0c11070008198030400c014148824001c170500010f051240340c25844004444030402c190340c85403100031307911035810100d46c180c5200c2d160a01030001068000115121b0b4846140d0045803035180c5082e07208106400100d0507000f644070000740c0c044061100d0191043c502c034103540e02c0340040080500c000c43e00140d010310104030450040c04581c210700b0700a042c080760000b2010a00e50b481c410114518896a480990007100000300d04082485250404480007070969041c0914018201918010b0045d408060405241040782402035074010707006004180d40d4400150034184c5503240d00d410401c240d01e01e9118105442c035030860075008003449045400f000e0705101c2c2004000780b4aa081a4003000d10300b03820604000205174400d0140b2600c207058181051700700390341002d40c200710303484a1058516075548105804049003241040c0543e400742c50000e4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 955158471 1250 955157221 955157233
    0xf0405060a0203190c120f0506090601050307080a0203060103150312170c0d05130204021306030c050a05070f020f03060702030c19170726040608150114090102010e0d090612090203 79
    0x20300c1d0000348100c0c0c072417405201d91a00c0d844502c4060740115003420401c0080000c171031401e9401d00c01108002080c0a0400204104004030240c12190b01504489403010040c0c5942d00c82006a00a022075442c1c14a0580e082400008104000801c083c0e1400b50355a000e0160b590200c145100c2078042c0c4401c0b2007000d00b4844152103940340d6100c2a8003e02c541042042e0815a4010800302e0b0300400d410149000074640502486405006e01c170394500e403d00d032491a2540341440107101c0d00030004010003040481e03429030150b584091380b140c1d80c204020280d40300d900703284201070b40c0d0b540041556001e44c0141c21040001248030480824215040302c0c0d80b10520860303030514241c980c8003140c100c030075803540a1a04c0d83d41c07070340f88d00041140100000880d9203508019001d00b511000500c1c404c0c3c8203102001d1002c050768040300d845101502c44c1001c40e12451902c0c01070340500080d5802c0252072161110303806109e0b52000000b01256980c0d110b50383c40d01e1031081c40340144d0f42c0a80c0040d4141c2c1c021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 955159721 1250 955158471 955158511
    0x30b01030f1203091e110a080a0209010e0f06040e0c130f18122a0807020108060405150405060315100e40080703200d0c14070302090f0405060a0203 65
    0x400d4441c1c074100d2150b0f4411b1800005580000c90200c0103401c601c980768000c111817400c5051449000d4094800c01c1c110307903c07600e49401010b9186c4002491a4001d50300c03205401c50003601003000755907004000f8120a11541001207213402007405095801109043c50b0310741198540c01080d4500140c0c000b01c1101c3c18101c00f0030306544114a041c87d6107640c0300c0001004041e450000d21110744a03100c2c082e8941c2d661101e00005200c018060042882a07140805010030304183e02005041c500c000e8038045400d80c0c5040020b4103048030110759a0b05005110100040c503c03049011130f041d160201088525525103902014002c80c03500305e01c0310000c82004204042c2000ca03071f0205029000d214154800c2c1c800e0b603540e80182d4000705012804510b004071a988418078030080302f142c1480110051036040c40c103820083c24490030315006481d500e81907170600440c800610039200956005480048075043c001c500006a020840b0300350307528040c170008284966021700840740640354041d0460302020107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 955160971 1250 955159721 955159763
    0x3061a0a06091a1b0a0b0415050112060f060b2b0b03060103030e061605010b0103060602030c0d12060803040b071101030c090b160501050a0209030c191e030b01030f120309 75
    0x400003440342107464201d2211040b900401112a05c00e12440200c04107040c18a04504c50202c0401c17040c001c181041c00501140001d0607c130560640c01c140080761746c48100c1d1440000704419006440c9031480055140c0c11000303c4602d101030502040000c000c0b0307800c03100102d0112010740e80669410340003c001080071038418906121030b80c00c02040076207010039030041500061404803003110340b0394554022a0481d070300b41c03251900500090014602d450b000c0b082c019100c001150350001885030305c00c120021900d00741c4c48640074025001c00c990340c60303131107059100309030704440421a10303610b5040c0c000c009035110740104154407445859400c070071404c01d9480c021507000007224400c6040e0024120b00440e10902440340502240c6000503540c0e418138060504250810107000d00940c54240d00c100442c010985480844404a01114284942c2c103012061140141d03c040c100c0e03030380c000011042c00414602c100410f80310714080c08460810440640c00d0312a030b040040d0071000410741a22001071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 955162221 1250 955160971 955160977
    0x60e030a020120030d092001020609031c06050406090203040507060e09040204020702040b091f0b070c17030706020a0e010806100c1407030c0f0510051204081303061a0a06091a 77
    0x11070481901d040c007650b11075440031646c41c1c03030301a20f40c98003404400c403401801c156840c1135004203102401c01031074105082c03a681d104480e482280415040000c0d02c808489500240c042c040040c0148002903540700c005000e50070035601030710207010b125800030b44d042c096242a481c0010290080740541d4aa03002c000094004101c140c1e0847e03201c9010800c00c0d61406145445200304280703611104240400000021080e0303000710384500d41c10040000410058095070048609015a0401d4001c1c0180b5090a601803410000d20060012455086140c1c10040e000d54402c0203a881508650b120010882e4441320701c00a440030030300804a1030003080302a03004034505401c401c00c070b404a80d0759a42d40b01c96041150703c520360080000c20244404c0c5003110094a02600501d8100e00340600b5000345801c3c014058801031501c140040ca60381304502c040705030300c000d6030400300c00c0041600e290b02940c0e400e50b074600482c1c410096034038040364840c05000c0410580300b0002d80c4d0182d424a85840305010382c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 955163471 1250 955162221 955162277
    0xc09050703181208090c1c14062806051f050f0c0a060e010b091302031f020903010605041b080a0204030611190f050a2016060e030a0201 60
    0x1521010842c88800c00c5040078071034148100b8040e4280d2001e890300800301c030806015801c40303801110300e100080d9220294881e41052400c101c025500d21490b0181820f051a040701c0701a002e000c0c1003103105010308003680c1c2a1744000e0400d041c40c04018130030b0002c9030b800c0d01400e580000e00640c4c011081c2099401e0903a400034908106140a005030744074180754000d40030310140343d8041090701e070400c402030040002d01e081c280300a000d903c1040d00040d100d080010000d0921101d001e4884c400c0d5901003105441742600040000045944520008080d60054a140780690b0a14000180364203061141200c102031000440345c0120030a04104d400c0f1070003400c0140301640078000440800c41c1c5218028110502a03007943ea0b4408051b802c1101522480416050000040680c005103800804136201802d0314948080545440c0c40001c1c40800c0d0b01040c606d6030701c16003903004440d400c0c03140350400352810f070f450b40c0115a500501b05543c071a00700c0c3e0002d000441c0118810a400b440101c181c00c89 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 955164721 1250 955163471 955163477
    0x141c0b030c040608030a030f090f0b1e041101171015051e040302090c0c100504031101050114030f0c1c020114030a05040c0608090c09060a1a0a1b0c090507 68
    0x1c640280014060310003a80198a29420010310307200020b4051089007883c2141035014040705445e0307100c1400c02d040104014000c401c0c441d0001d681a0300c01a4510791007541d0b030001d58014106030804c1d500103c8224a4240412501ca68080f0390420380700290388a510300d21b2680d42030a08011000a1100105408800344402406248840c4000100c000009820b4240440e00c4624600401a1102019080c50507004c000c2080c0c90b0803490100710340603003031940c0740081031a4075280f030700b1136400084840080041d4a4000041142c1c04206042501018100c040710550000301910701d444003c02030500d80d00546030f0b4094150400d0925050100a005040c2110000e032010f80f0000c0e6603104481a0000c20341c0c0714208030800800c42003d03070180031246132000262a004240784d64506034036084a1040a1260015040d980c03020304140c040d01a1084007041d0710700c0504110600d401c02d08500c000302e4111940c00c0c1d0710800701102c1202e5660841440182d01e032403c0f07010802031001030404010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 955165971 1250 955164721 955164733
    0x30c02030702060409201603230a090e10050d0b0a1401060206070f08010303200c0d03050306040e0d0c0b04171c0c090612050613090c0303141c0b03 65
    0x1da41c0707041c0036000600c0e0303031400410920781c00c41001c6d0900c4039080e0b20030002d4405000d4030210000c54590703030800640c10b060680764030b540340031514000c1217000c010300b50803280010740c2c594803a0311018000403a901000041865160303c941181031100500410341c100e40302002a5001c80d00004100380c00c0004001c0001e0500d0719480041da050070241c00610150740701c0428800542d6100c040a10b40420600d04280d6a5040d036034001c060f08101000103410800140c40b8403a480414044062a414000c1c880c2400c5140341c0f401030155002250f10030b204034504052010310000c0400d900078000b07004d54a41401081907a01e070880840040c100f030710040048144c0c0b840d01c060460060000038030350408620640341c8141440240c91b900b14000c0100071001c80c2c00c01040b50007841e1a0304940c91403c02007220f55910001c98014074244440300482800c0103c004244071030101c043e0192406a5981c00c460081e6030703040d4446104d40c0441149501007a803180c51003510a52103404e50013001003d07214 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 955167221 1250 955165971 955165973
    0xa14060304060908121006180501050309070503010509070315060501021e3d11030c0705030c030406081032030123090d03090206090d080d0227010509090106030c020307 74
    0x69560085c58414500c28090020b0041c8400310f19280801040700f40313080741d070701c0c0d210a1031300300d0050346485041e0501c400807000c81c244050922100000c6c200242c000c01161900410f116a80c00b642d110986a203065220180742200040c06042c080c3c440680040070801c8940303150b0030710500344814590791402603c004d10721802d0002c40030b5103505403c00e840415880385c400700301d4440704035085422940d858281300d000d01d181a102544c0d07022070072001894640ca11810981e095211b140c039455064007001070042840c90f040702a4500a1402e04000c04000341c50309520030300d1010300004a4060707400d001c040a034a01058401d51000c3d02c024001107100d080b5804c4204207007003002282d840829041d020030103100e2003001b1410b04006580380030701102540c0d0300880c4103031140e81c2d0050b0103130051101141c20b02c0707155012203c418503e11411541c444886c45c0c0141064250fa19124684c03c80e0700811400e50301c180191602940002c00e80e0b40a80d10b404000c0c1c4c014029400e910382580018001d00f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 955168471 1250 955167221 955167233
    0x1533050d0903021e0d0e060904060f0b03090c0d050c04050c16060c12060501120e010e0a05010209090a11030a0915020f21011d2a0901030501050a140603040609 70
    0x9000240b00381c0082c540a0f0164420201e0706861110403070b0b003980540c603001c429039802540062945004d458860703507401044003040140280350000340c02160214800210002020011489610303680255480b049035501088035041e10400054401d0b031241d020140c407407401d58480380c3c0000090749041d24222898455190a0001c940255100c569900540d034031140c00c09441d400c218442c0404100b05420100064125100d0000018001e0760f510402120703041c09502c040d21200d46036007100c02c0d0394142e24015020798442070865006005040110342d00c00b03603e0040b20384564110705200e055940304440c41004065004050302c4000d907500e0280c00141091000700b121403050440c10741d461400c5408244907500e4001d82040815602004200040c0c0148a100c1800c003031440745000d60f29151503480c44075003101680c450082c010794030b001c99810244010000c0724404c1c0c030140040c0e070b601c80c10410300103103030b01c221901d0181d0f0716041441450600f0080d540144a20b10015000c1300a480d61 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 955169721 1250 955168471 955168481
    0x1603020a031b02010c120b030709020c030c19060608011a310605150703140706060b031602010b0a0f06050918010e01050901080c010c140f0a03031533050d 68
    0x42c2c000f5075034803564180700f5503008408251030f0a0a40040c44191041e20100c2d50f40c000c10700c100000b41c0c0c0d000c125000031400c14006ca40302c200d0008210741980c40d007100461040000d01c8811202e0510b0400700082c040410300444142c0100c0e01900400300c03920700c0500840c036004002d501d422201c550810103150030000031004143c40c2000f030006900c0d007442c0900c41c21044ea02d89903035881d107042c4001400240c5c00200c1158503096407865a8643c0914940354014041c1038205d16410a404000c1100703484400718210949a00c0343d009103c01710100c3e00703001520310a4090206400d5485009201c5640190700401c1c0041c0b000d000040c10214680b0329a1100e84207820894040f19084010040762419208044c050049440500602c0c02007200180c1004840940108900c00d40070340c46240350000c2c005804c000b02c80d4400c2d510b50240514000f4014a1800722810301001c0c140804074007108030fa400850004180241da400414909200381d0908540e64401400c00a0412055495043c58054 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 955170971 1250 955169721 955169771
    0xd030c0b0a0209030c0a0b16080708030406230714030c1b07091b0c1203180c050913051209030f070e0403020705120319140703261603020a03 62
    0x1c0180c84208200826050085c4099000d1017085440070502100c601c840c00c540306084858140005825203140c881c5160044036406040d00b030700030080000b07002c020707040490034035810307070072210141446802c0180380a42512514002817800d100c10100700b40510065410800e0381d9a428205038010b00300ca80e003084c41c00403000098104800801414940340100081400d8101c00c61100b1024250300401a40c003c0a005d05145448400480540d009900090107031603d00da541c4a11200b509040f0309201c01da2050500a03c1c1200c00211141c1d4942c561112907a442009006015100101c102442c2c02c46d01141d940750040d00500400000c040101c4070040450f4010030a0a00c1c6c141000380c101400342e0300550080684120100d8426400702c101c80015601e00d13a000303601c00e030b081070444040c6011580705c0e0380200c0004403c0300b03054004c1c88191500c00c54501d518180c50280f10350b0343c1c003400262421359166014100302031a16020760041c226480562400041039840206813809445903403071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 955172221 1250 955170971 955170991
    0x904171318050411092a0702460e07080405150105150903070506031006090f06051c06031e05190201090e07020c03010204060e10170606071b0e090d080105030703020d030c0b 76
    0x600351f82142400f560240f004a0082c040385d0a1829403401c143d80801c00c00d481c081d1013951149400707690150901450041c0036000b083c2d410915000501400b404010340702a00c4070320038606c240c1c64155003115410305a800160070410320040c031406001440c2c0003001502e915005d050b101092686415001c2d6100c1c4001c807808160041c41d0041c040c0554815410480d50308407070007001d102e15500182150070020040038022035007040c040307415005103220f410040904800c00408540c1c050302010700300485005106030f0f46441540000ea08042110380c40084c0419000340b002c10031039028918403580003246005950b40b80200c2c00029003241d010703400500106180310301180c0706007404902c042a10640d070511400070481601c0049030020001c210f14401d01002808104001d0b0f104541060040844c00c8030000907141c050702d01901401712014142e510034010403805082c030400c00b85048603805005000c100d820754007032045501071042e0030340502c00b100340550002549842441c2c0b1580c0040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 955173471 1250 955172221 955172227
    0x312071101180308071202030d0c0f030c1b06090c15200d0210020a02070906030606050f0901031113020c15071b0b060904171318050411092a 62
    0x4005060200c05102c0c20103071820b20300003400043c03601421a907815810101e15419081000003ca1845c800d20300e1440d42642482ca20341a691341203c411030b04406691001d10269400c0242200d901c10400c03403840c0c2c01c1a0b101c0981c40410301c0c0b03034003100901e4003c4105c440e43c03c1c3c9401019100c0f110007a07811001400385111200d440383c0310822165401a0b000240c4030805018000a664001821810184a600040300840e41e0b000b0400388005007900042032002565038240b903c02054203204081c00b5041c000300014a40c0340c50318110781030345d0784410030b0f402c0014000144030090391b120020f8002c0300d40c03c01c562201c0200400c21113080c102070082001c01841e028400900d041c12400c1740c04184d040f20001c020000700c510b01041e900101c1a1180c08080d5940e0031300720003003814221208a0114002511040100040e0701c0c107050b25484016040114420003440c0c00710b0b241244c02400e000b00401d410002482e110252580005040c00e50b00b80281c00380580d083c00240030750150304511400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 955174721 1250 955173471 955173503
    0x380d0b070e1309080714011b08160903050312190e0c240a180302090412080702031602090414012903010614120f120301060215040309060e031207 64
    0x74070ba1101c01c1d000c1d101ea05001002841e0b03901d1410b80103c078001003183c41c0e44800c2811610095000199904c140b16403111041d94403000030300700090039510b03e110301105086031040507000e003010b801103a034003500442c40c2c51b00d00c441d18040100060144010484414030342209110b81d80a202d41c0300310761602510608144d481007003001d0500e0031070080d1044100588410f83e007071150980c2d032100c24070700b03012a103500e03e1000411140400d8000940c049407860500040c40f0520040c0b22000e1042c1c0c503010825201c07104140d130b49014a1035101000162000c1080050502d13900442d007191091120280c81d6030340124890039541301508001da840c50404414802e1240003000d03007143c0e0300c150001c000719414002d81e0554411138180c1c4900615512411121410741000141c9240890009803031100311603034503e4103103030b1081c4105c50062040384000b2400d6458000c1c514007460303164640100315031400c401503882140402c201980750090f15406906501e9040040c03104503c6201040e0b540403c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 955175971 1250 955174721 955174729
    0xb0304110a0b0c15040c18091401020a0f02150a180203010f0f140c04090908070c14010e1905210f010203011e03080f03131a0a380d0b070e 61
    0xc2d50074034004c20820403051101289051010205a4004842c006444447c0100707040140001290041440301c2030b200450340e020040d805421014047c0d41d0303546002c0d10a400480c0d90f98400030407400301f0030f4400c000c03d2000b441a8002c0ca0281c00128140d0042d01d06500043d08440e10009040c010640b41c20680280c80128418007004010b503a440b02d80605101034031000c2400307503024007a0b41a6691420030207000f80c4500380e84c420382d030003d00b06030f01740d0b02c0d45810354100440c1d050007400301d001003000d0302041c0b0744610b85002d0304032140c18403a4600e160004000921a400c0180490780051501c10841d030078051100c4550004c440c0005652945001c50110008414100c021a81501d0020520000304058100d50070001090700050b16504e0b2924100071070490103030010300e1b83d00034080403020040100c41e02489884507110400c0824004440e450300707556100c218000c00c2e0000ca550f94038070501000e0260f8100c10107484040045010b580b0451894801d41e4030001140c0111240105450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 955177221 1250 955175971 955175983
    0x60603080a0f02010b04231b0304060b011b0f170408071403063d0b0d14182503120810121703062d1207060206010b0304110a0b0c 57
    0x2081d6000c0000e80100017040d21f8100b120103c8031120b24440e00071a07120f401c20116455502c010703040d140d940e81018a010002054440046030224071001c1ea4649590359034030400720300ea5000300394101020302c241d540485c0f82141e215a49141c2200344030100b00c9003000c00c03641c0b019007081c1800e24900c4200700c0400d0f10784440103002500d081d2a041c00d900510b0141030721900020600303010461b4414500c1c02c01841d642803a04402402013010070512403072005a045001103100003001c101d615143e0400018542280508905c1da591100c0c00307080303004180303414002c02c0100a20000502c03684a58a28503c200d0000c9001d00041c6500148802d51401003030b0203008000041882040c04020746e40d40c0107441425224441d02e20012000954a0b00c6080038030950340814144410101c240080100540110741c0350755008044000c24003023840030000d41481a201c41760002c101607840c020700d40c8071a074002442181c15003414555035180b03803660100d140c044c00c05041f40c07646581d00007010924000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 955178471 1250 955177221 955177241
    0x60e0a061d0103230a062a030e19020f09010806040b090a1104020d020c0106030c14041406040e21040614120402060a02030708070c15020d1407060603080a0f0201 71
    0x80780c401000003441d40085107a0303094002200850b40100040c089041080d4000007030226420100035100383c10308007002000030180c883d5440704036041e4070030450131a80e2841460b00136a204a0031030603c85101c0c850252918030085c24440c074080110045804008207a03c41801540180305010402c00c00702451030707000c070b03812000301070342c809545400d1800d41d4900c442754000d580c00a034080602c1e0158048a080f594120028400b043e902d18040c00f03028014031800d2424000490006698036040c0520700303032020032100404c019141c03503007000010034a0b0182107149108030f40b180c484052940700450f0725103100752051902e40c0e25001000e840d20700c0f40e50840005070001c1000540002440c40b000b40c1058060380c0c0c0035150b441c01c040036891440745400207402040c01080340c408000074114802c0a840d108044800f000c096100c0590780c40c6144220400400d84001c0c1000f1130351904e20181c07860500418010618680e6038650070301540c08101594006100c0a0204056540901901c00c0702 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 955179721 1250 955178471 955178519
    0x15070602040f050108400c050f19030209060103021c061805010e07080408130803030105030d0302040b0d11070206030109050a1a030c0103020d14100e1e010302090a060e0a06 76
    0x54070388140191019440400442c40c42400c0c03468100c1c10b80d81d4070590000600d420f2540b90850055030034107c100355158800d551180c10541c801100c41d042c404884900102c4040c4001c60081c10369082100d42540208500d04040d4240b0071a120703000b40e00b030a000c41000c58203001400505051250324145511244c8841890520004100e41e01451146d07543c800ca41d454130450079110391401111a01c42c10851414a41182c500492000804801075040310030480844d940d03954074071019401ea0140780710b440640343d81400110848082a005222150344400340c1e18a010b0140d0300064150b0800c5e040500c8069548040000803402071180c400340034494162180c0d10415100041ea41d0104440d20604040d0003056103140340c1242c0d081603100000703108561303000c2d1131721080c40802c504547c4204014440c1980c0400c4c9420b4812214800403460760820300340b10ba0031038080c000780507005031940c00c103155641000146901c145091134051000084040354030b505e030010840c07200c4000030005200b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 955180971 1250 955179721 955179737
    0xb07090b040b030a021b010c09170105041e080906031006030e01050f0105060a120c020d02070b0f072d150b2d03150a1d03190302030615070602040f0501 67
    0x80b20300d20205803030340002e41e0b1401594401116021a4603442210718030b120719820442044c40305900003405009485440300010050b4400400041c240c42090320040c0c0000846140b5a074030880d80c03d00d50883c1070003500d409e40703000c800d400854810352040b44d2035210003c6001041c0310056041c007070480c120980314000d110b141402044d8100249041c4100c5210301360000341501034074040c4200c451142540031080041e15086d43c1d010b51611103075000000140182e11011408440140035200c81c0050702c0340107403c1c000c80c1d6440e01503040100c00c40442008003c5503080c0b5894102080d24845449030410012107070203840c2e0380c1c060703480400e080c901c10800100044568014003003c0b141035001000c10400d0b03404a040401d04006e0707050070220480b02500f04200c5030f104181c105049108000522000c00700d80a040341d6203038085c01c6d0001d4031035043c0c01c07000724400e0722a80103150480d00c0188038006040e00e440746010941d0044904641403600424204204241c043c0a44000d080078280011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 955182221 1250 955180971 955180979
    0x2010207060509010c060f02041a0a08010e180319020706090501020604020603062d0f15031b041203020f010b090c04120f02060f281d0d0804030b07090b04 68
    0x24680303146001c0d00c0700b08480415040304580c8901c41748440150051820000908070fa141320004c0d51090003100b004d158600451261304452400315014a40582c1d20b40d1203907401c0210156042c0d9010313101c812040159141100b0031f0805100a0a00329488680503540864111b0041e0402545910240901000480420140e40c0205101e50310a80c100e8038955030740e85040015040c0744086216801003e41c806a200c41e0100426808070a0b0104407100d500d0f00000b58108200d4130071088102200c20810700215040010411101c4000d41700108640d0501e901c2d8680b69009a0142100754010b034002042e8a035203903401c1c0701d066000ca50540e4285554580b00d4040800f83c400d520908244404002c828828060885160303a0181d07801461b603940c42d00321240741601070304800501900000c41c910703600606003a0321520004915551550140162145013a200c141c40c4221801d42200500c019400029265002000990312480070480c542c2402c0700014460300712a003000003026801c000600c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 955183471 1250 955182221 955182223
    0xc080c04180906021902060f0606070210120b1f080f06061b0f010f050108010e063c0103030302030702150709030f0501021308031b1b010e03120309011d0a020102 71
    0x7540304002540c08909a0300c6031070054000c0c4030352100b042c490341249400d4182a41d011a55501036070014103000001c0d218001045064468228001c1d071001121040785142c90181c0c2c418050015580300c0020b084480c9004940c1c200c0b142c40080c5100350f500b400301601c803500080d40c0741c0c00c24084448000075260081c0802c0103032007440c3c1c40c8a2403603303e600224880000f005490f4400540030003e01c1424504020040604001e00800342c840d400c00440d030415040c00161107110b440303040845001c84185106841c2c0070012550484001440032110030060740c40d610030741d40294031950340141c4c1ca1400701c1000b81082d6029032040100c2035100b0a0103070659001da4604281c84d0001d0741583d00101501d402c42c0203120305c081c40c8a001c0302101c00058800c002201815140e00b04240b81c41ca08245000055161240e800c0c0301c034643c1c0070180b106216548182c1d01c1e40b2080c0805000c80e9200d02d044560b82640d90070403607480e02c5584d15808600609007001d003403a291010200c00414070010540d00107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 955184721 1250 955183471 955183499
    0x6040e0708121c020c010618020a23091f0f020a0b1f0810142809030201022a0c010806010c032312010e0601050702150d09080406030c080c04 62
    0x100d1841e03030001c9054400c500100000a0340c101000f10708640e1079541504032406448035201300101101d10345024a10316507940200d4080103042c1d5140016509001d000307000800e154423403181c901e0428002c6081c55100c40c4e0740c1d00c100110049038501c24900c80d04000b00b00e20102d0800a086410005000001501182105402140c40103400e40036450071314100b542d8114982c06000b0a204411000820b40341d0303a844440500158400301c0e456548913125100480e5540e2541000341c01680032f42d02640d0039607440348a10511910002d0b01d01304000e021303030007a9610640700e000c1b42e60000b07403a01414075003044842c610040a0a1005242c07400e403001803e03142d0070404c00740030f2003450b0f4403030310742d01c100c00210054010f00c4800d4140c5480081c01c0c40300603200c09005074240300401c07001103001d0b513004a05840340b0546c000c0445411681d20299092560401860020066124045000060000b00140014001d140d03800500b07504190700061000070040d05445814204000a0001504400c60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 955185971 1250 955184721 955184743
    0x1c0515030c060a11030d09030c0c0e06010c0f170307090806010905060105070605040f1403041701060b0f0a0318080a0e040504020a140d080a0509031605010203030f0408070209010e06040e0708 84
    0x4000104c400c081106810351041d140904009481c114208080680100718540007900540000c45019200d0403541d940350000d88000c1e02040031808078070f0000b103004c01c140101e98070904910026420f1800f01000a40094500102080000c10103015884c03003000510b00500c1c02100600c51402c2440000c4e100e84112100901704035119000681030019005440315029400041d41c0b540d40545454140c99030068081c5199100008000211840e0140544425603090018482c5461520041801103510102e840003d043c0c50b2009451626040ca680301ca826000e041c451b9a10380840000401214121551a2246140805010158135004070b40d038140d07280c0c42d5008448070030365030000c0c10075003100c0c10040c07040000050780c12015901c60f014080f00403060303089540c10300c041c100c2040c9414803402102c1c0181d0051001130510742d00e02c03000c650441d0043d5502468001c6503004181c607080309030022202ca50802041c0541818103101e5404407c010b117000d424080e080c2605a034036282d076000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 955187221 1250 955185971 955185977
    0x5120303060d17091807090911090121051003140d080604051302041a18070c08030a0b040e1612080405210a05070302010e0103050c0313081c0515030c060a 68
    0x110605191190300d007150301d400fa0003445c80540c041c140f488146424012110a000107082c60000600d800c003500881c0602048046e07140e082c086d080c0d00464501400c1c151800c88042c8010080c190020903104060003020020b0032110a079003182800a4801c000080780c0d54035600100710b48056590000304540c000c0c0c801c94000c649515410b40403604d0700c0900358082e42c0310b8a0720b1440e4107544041040b001505070184c03040d04900c4c010110081ca400404c40d40704012400e403920400000d81c801004503030080140100090503581c0d100420210f07a5141001d901d161310080a0720681040300c4160b00c01890a000c4a00d0038280690f112102c5010b81d2083c10300580002003030042e41c2e00601a00b50301888507a007100c2428000b8100a6980c481d01e101c103038041080b00071540e029500c680281485540405056840c41e00d0781740b450903400750140c505607503682050140c40504541001407412020720000d0208141c140110410003024100008078032981c41030b49049070640b0345805031030020000e41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 955188471 1250 955187221 955187243
    0x30f0e010e101101180501060807030b0403051e2a030c0d05090315190b0613061b1202070501020f0f07030b0408090406030606180509071815060905120303060d 70
    0x500954003c00b10a03000c40702542010003038a15440c500d840324648a0081c03009210080d42c81801b0f684075201030002a00d030103000070004021a000e076000302447c407800d402014440e4030380d503c0084660003040c1c0e100440c403443c80103205c0c03c82c0c1424201c0c1500d42080302a6162007400705141d9501c42d5460802c10500c4004500180070780c2e400e00070300c8600d04141e094240300d07152400c0110b0b000740106911600d11868115a060a828018161030704021010307010095682032850503540e21a000b00c1ca4103800840c4000140000d0b10308040020761544d54000b05901810400068108120b143c034088a641c8042200308282100058110489401900c203480c0c50300e690402502901c91040403d802a0404a0020811240d03502c001c040f0307070f00b01d250180c15042c1809c4c140b041ea20140c50390030302c50b0301c40079090021400c0340d0720f081c01e1110700b00e4000902c002001404031712082e59070310040c08962100c50421450812000030f000c40f0189001031451860003c0c000b0f00c058062031400780928000d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 955189721 1250 955188471 955188499
    0x150f0f0e0303071107050d06020a0807090e0606092e0f11100e030403060e1b04051504020a030216060c1403450a060b06070203120d02040f0b030103030f0e010e 70
    0x5008007405408082e21f1024400640e0525201075446000a800000c0c5000001001a4802c90007030302034a054040049c05921248204400c40d082040c20661080c45001c90280070590340c1c0760091300d00e01041000c0c901400140e000703482c3c01040c5040741b080c001d455035400b015240c0880c4d0004032414410001074404010400d03e403460003181c000400305440d000e580302c80c071031000600c00d000c40c200401d031084405240d000d21098450548100d14802c001a141c06858902500603210080380c618006040208011460240040d24070003520003999400c0d00c1c03909594081c00d92503000307000d820300e6460341c00c00e50140c0c0e035189004061b8070f01d01e0a418105e58a0340150401c2d00310341c013010408941a040030300f92a580c0300d281080c070803240c00c0c2c500300444c4960b0070710200f952200c5400074081c0c03840c6086038500d201554400004c00b000d00b9401c000104031034115103402d40c044d1010b061419281c1d0306616018120b1001092a00103002c4850724041c83c980c2c3c410921560f1510555600000c4c0001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 955190971 1250 955189721 955189723
    0x3010b0301181b080f1b040903120e030f0d050901050a0507021507140c1e0c0d060b0409080c060403080603030412021002161548150f0f0e03030711 65
    0x50f0b40c02402035409405030540207041c0c00111541181e00e0148420794541001e010001142ca46100c0140410100303001041d28000a034443c800110b800c0013964034044005a04555a601401d4111354641d650300500a9800c004d1040607401000007800700b099007001c00c0040c3d5928012180407a08800b002c000800c3c0e20f2007440c24020588540655a03150280d0000c290380781c0b00036007840c05810002401c2c00c5040e500c001080b480202003d4925000340d107981d21504050501200d01300c3e0801d03101c1240900246800009110b9a949007005e44031030300709442c0041a182014100074802c8e4405d000030703c0100343c04000302001c031390304441000c003d1000703102c140d00342a002c2c200d10f2600300306e000c0d00048030080d13210000604120341d135030700d811029041003910940705008234010b4801148c00082c8200c2005e905580c220b6a8150914011703603000ea9a032101c10006500d04021203030b1904000c43e26180c1c03074040d40c07100c001c050b4030034000406c031a0b80c0d45030707240001005c405c00c118492034242c00d1804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 955192221 1250 955190971 955191023
    0x6060e04020d02090403052719180f0b0a06020a0203070e0411060a0215040605060f01020a1121030c0d121406130917030615030124111b03010b030118 66
    0x383e0b0051020070701c8d00102800b1011155809424043d03902c1c04c1d101450082d0340766018055480312119802d682d14030b400c03400028203042c4440e80c0032640d206100c454170750301d00441034000e10b100d60013001141354910606082c5401ea50024184450a1041c03100142c007407496460781c4903040d55102d445401d8040101d02d80500444610300700d46d801401d1205000b00c84d08454850f0400740c1d000b00c2825881c50049980d1501040081e005101c071585c03520480c546080f850b0114840110810300601c402106a41541d05c8035100803503543c4002c0340360303132885e0704403004500381000c2000400c4038940c02c0c0e0601019a40c0141401c4c0710380540d02031244c03078146c554446490745801000020104140d003d1000969106686003807244424142882c1f0080034030044074160f415014400d0607140c10924103410f51991b0401070014080c007006c10000081042002580c00d1268207048011201c14005050031030340405d60490090b41007410342d04a14401d0f806103826117a00c1a554540d800c039a42501204003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 955193471 1250 955192221 955192237
    0xc0d0e060d1a010e0d0b041b030c090b0f0109030506150105041a03040515060319021f02011a040c020706052a030307020601090b09072f030706060e04020d0209040305 73
    0x10380b03031410070b100540000c401800718000c2a03e4038000070100c5810421181c0365101e0041404203100000b50015403031041610190a604c01101020307a103940d9440c4400100340c112100c226501e44c481c22a5182510302030102d45001c0c2800c14606080d82c6a4035202c1c0e2006000044423130207181d00c0c1c40564072580c226001080c01c44103102c0d200c00b6030201300400360310954041e549441b5110428891b08900c3c4615801900b0040040c1400401c0342c014072401015032200380e80c0f10f600c10405000031895110040040034080c0c1c00001e44120b041d607404034451016040700d0007103240c8503896101135000607581c000e503019030600d6600d54140542039103140343d00e01e8100641e04e840c003072051070072080003000e18000c2034a602614460382e240d080010884481001140d0300081d4100801c10050080780404a04007808800b002602490440700c034690100d01c800036415400080d010061000701d00c11040a441c03100032449003800c054001500c1c414000c2d002030b01c20101c0402150402d405481115020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 955194721 1250 955193471 955193497
    0x503060a1707030c0504020c03070f0f0203060f180609030904150305150609091c030c05131712030118020a0c1205070213140403111f02040602010c050c0d0e06 70
    0x70074210111941c4a10380b610040f00d00314842140403c440c9800d0003030700ca00208079801581000c21540314034040c0040080c041c0d810000242405000da20148401c1e0310400c0c40d04040165800d003803c0e554100400131408101a0304000c00784002c4c80390200c102c0b5504039040701e000c52400c1c207110b01c6501e01c5481d075200900d00c1c45034006003d0f4103807046082a102d0041240c0340d03c040c0d80c5002c8000e45950702800010000c050100e40c02c0c102600036031018000b092589041400c040000b900b20000c0b001c1e6410511140142d129807800f141340401600d000994068140340c01c0d945408407405182c0104c030000d0750419000f140030102684a03141200000b40c0001b4071100c0c2da100480c1c007511583c0000c01c1603000b00014406000400100c4c00340c10043c3d1403642c0c07c003019035941d07202140c01021000c03002d44030740101048503945094507040c0c1c54102c903010400690310362600202900311019001c41c0c005102060006003403c0401144c844406501070034100340804800000900900c0b0389804180c131 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 955195971 1250 955194721 955194749
    0x151f05100905040504060e0c030a080409020a11060709080c040218092a0c0721170c01020d150e0c0a0c03021501080f0f0303010b09040b0f1507030207050a050607030503060a 76
    0x1341b10164118218118801085d030f41c0c0200b5410506840310000c4c14050a1054100010046002c03e58024400005640b402c001c0c0102c400c0300c800e04000080e2440000180318003024848613005020b110801e0501f120114507242207581400d1003c0c131514001445940761100155001d16040300ca1580710100d282ca101c08028091300d0014140c100799030300d0f0128800c158012802e070b08421810191400c6611554024486a42d110000003800604d403030280401404a440b2b010000d0000e428515510040420312400606402c8050850b0741e0000900200690500c07052500001c211340a003140f0745081c4401030600c4c01c084c1d10300704020a4008000e80746000014400b44045014011000003005540e40690383c44c10151742c0b8002805410f000f420100b00c40005031510f03501c49907040101510003104c003d017010001e060149154070085100000103402420145d06100311006020201e8410103558103040101e040d40c000c5400060a20100202142081d620f5102c0040241009840c4004c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 955197221 1250 955195971 955195973
    0x15040b040b032a010315120f0b010b0405040b03060606070b091606080708161d0118030c03021c051b0f0a061824030b0d080309151f05100905040504 65
    0x5150001040b00c143d061003842403000341c0350b110340101d407900052000100d1300503007056034580c0001c04004003104c00080c0b0400c44000168504031185c02400c0031103600f5101da103800c05002c1595103042c0c105120790004010040c4607501c100540750080e800c2401c07001c1030f07558000403c1c0b070007240c0031820308558400c803000540c0940c0302e040c4a200e001503075203524040c2c45a825080300321382c0f510309503c0840c0c1014042c084844c40032808610b29070051400c22480f50b0034601030400304c0c406400665a99100792820b02c15414800a034141418031440d290030f440c1d060751030f00d540300d820600391a9034400740c2591402ca1075440744503004840a008190f9503c199480101900d0555440740300d000400701c0c440001902c1501e9603000300082c070300c000e48403100c0703115140403401411a4800c0651100744074074010080344481d00a584240c0c01c0b00700501801480c1c004a0801d00b500070078800d10000d0310b224505c64030034442c021200321041030703e51200d88c805019007610000d4203604840d400501e001c0c2040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 955198471 1250 955197221 955197253
    0x70b07050c0a2906030a1101020a06050108100c140d1a09130b01060c02130207030203041809060f1a09060109090c0e09010f05030d12110f0306040506060315040b040b03 74
    0x41c09040a8480e8440e00c1046800100b8102d84c45607068000310355681c00700d5003414030242d8180741481501c01c103410301d541e0b1800300c81c02a000985980d0010042800c401c600e440346c0c0225400c14284900d40300503500390000f9a1080c00d02281500b0748032000c0001000e203a0400300440c0800400135500b91421214000040b081e4000982d0141c1d2045c00000b2258040c403c65001607402414252140384551802006580079510880440c4410000081c0c1d03d001820301c030800300007001000c035031025681015029121480103810405181c408903250000003652002c6038010103640700481d9a40f81401030361142c555a21103c50300e428860a170100c10341c00200200800d90480300b0103070607603e50010705510003041c048e0079095071100e28032030000d40c000c1030740340c08403001d1000201d003201405001d451550805d4800790ba02d510003205200040c41c203405001d52200c410754a0904614040c4108400640706881c078502440d5200b000c01c1994989411211b90300300c01808072200707040022604 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 955199721 1250 955198471 955198493
    0xa09090b1803040302130b13020a0c020d020a05030d0507141f09060b060f040f0e0f0c0d0612080706290d02060d020c070f08011a010e061b07080d0311070b07050c0a 72
    0x503c10401c12640d2903c8c890300d4403d548540c1070300c1e500c8050082e280d900b4029015010082641d105042d0000040d0702d130703420003400001e0b00e041d641345500c0d031016240100442d007142111000c150010102d80050b000001c0322002403210094020401c02020305040004080305103038150403500008231580800d0103032008000f1112600c56644005564200c0b88a401c101601e509501403048404174a10070840700107007001e4116054002150b071356412045010b0140940100d6165001040340d0b000d009403480b4110890b14659a100c0c500100136407080070782078581c190240b046820341810020354903081c055900304204920115605e86d8144800b41e43c6808520503500300703501c00c0380042a45101800f4a11050003c104201060440c54005480c804410300000c1e81041090000f03642c4000041e230744005443c0c0c0300c00904481c50801c1000f078100403418101c041030505221001d500000c007201161203c0d5004560768049442d800022602841880b56a02d403030312403400d0300750600060030f1b44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 955200971 1250 955199721 955199741
    0x130b0a02120106200102030618180d0c030306091506180e040503070b07020d05040b030a1b030504050f0f1b010309051c0801091b030903020c0307080c0a09090b180304030213 76
    0xd11449054113045500380d1004850194000070207541c204a602408005c0b03640000d40304400c401c3c0094529101403400440c0503002002441c4203960f0b00502da0140310305d601401040005100200203010b00d1010707001c003440344208000c0c0c40d1007886184a140850300000d4455042884d00c90b00741402c0060ba41d800c4036105984501c42400880c48107400000d04e00da18020b59296030b410503107001c1c0f0740806030304004c0001d1141c0d030302c2d80c3c00c01070300a14182c0c0303102c0300ca0303015100000c00707080500306a460250448107a0846a000e4100d00301203000020700141c0741c418154030090030b0125200100c02334003400d640289244201c1c4001c0d04806083c5440101c0c801c065038950b20705030f076554820340075181e0ac500040c2c1001200c000150a0610075002001c680e0700900484124011500101c0d20300251584546026044111808414541416200c0003400c0c001e006009202464803200caa240000e80040705c1681d4500072005080d00500540d0000c5400801640852102d18000b101a1844da13138 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 955202221 1250 955200971 955201007
    0x1b0f0e1e0702100902031011070614090a140109120207090b0121020706090b0a06050901050f01080112030c200118031e02040e072903130b0a02120106 66
    0x250410324103414419105507078660040c0641005007590200070410008281d0700342c010301c1d424803826100d5029201b0b0220f900d0403c196590914203011007160644950002c0d40100701051112a180019505604070341001100080c0048840341900405142e540140200c2c0300003140c442940d000b242d070000326a004d45040c001c0f1342e22140111040311820001000c6552010301010545006c1e07406045101e11641307000035200c0c070f02d446100145404660703071054251203e00900c014100a41c8180c0100001c0c1c49105c0b0b5075141382c00282c0260014016036440710144d90301442414840c1610405564015402c0c1399000042ca0a4140040752554560f02281d2141c108052442680034404122508070410041c0c0c1c005042007041c41c41c0d6141001d036130042d103500c1c60000403542801840020b04200030064590040e04290f901d40480444071000502b10501c204403c0d00300100700e900c1020b91150140c039041e030f40d41d90044001c1c0220354203140b00c0d100312000850015045105407201e503003040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 955203471 1250 955202221 955202251
    0x90602120a09030f030c02010b031c1205040f080307210917070c030602030c040306020c06040c060903082506051e181f0204080a1104180f1b0f0e 64
    0x901107206950000744000c0008100c0a00410f15a1107940300c5c140b02030161002003042680d540009140c5803050714913845c0d8540540410380300c55046086040c0c00d14a081042c4190b01e025161407518807070988020304130040010000c0c200314072402d4106080568401210041072585540700000c0900d0355048820b24445030000905400040c1543c080c60350048660005509541c7c901c0d01a42020f005c0102c440400c1c8404800200c09001601c4a00304e07160041c01c0381d203410308011035140340070f6002c1e9040c031121410501c041b036966000c440060b00a000e1194001e00c8602d094840611102c0020300018949400c4c0703c4144000c0c0d0355440c3e4410b00103511a015201c451065604640354041b00f21198441c6221f031f90000c10001c014014004100001802d003680c84d0a10b5040108160007103e0408404440c4c2403145010b03c03510824407150f030403d0b419405a6500c0903014601a1406403030002d0310607070030307188000c9001154040d041000c440813240742e0341c098055800d80e094a40f012214200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 955204721 1250 955203471 955203481
    0x1603050d050c03060f280b130e0c160804050d0503032a040302040b0a050d0c060206100501090902090a2327010e0c040e0f01060e040b01050901111009060212 69
    0x200043d64042c0100401d22401d4000041c00c120a0080150610100c12402d040d600b44039411284840020322003136681a950b0740ca8048101000b048a130402e0240304095010702c81d06c102d40d4020340b80310110010640092b2205801c0c140903a002d1540310690014140c031903032003002004809103002c0c01020781070003a8090f1845d5541081030040341088656407060100b040503103425003005800311400340002078a103483e20f01007180c1c0140303840242c071845010381c0c04008080d41041072542c400c401044041c81c060034200000c265088512494007519008140710358159140300e000d034000c00c9d41901100c01072102800002c601c16182e20114070441c91100c1c200e90024401d04c1140e000300c048805000568200341510412030409442500048005e2101082000c140c544580c0140c194942e1b0220540c507084000700035442030788440340100c1c02d100300c800107a40c100040d00c5004100342011105200784000003880c00600c0c13200001241c1c00c2007003c60034000594024096406c1d582034009444d81c030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 955205971 1250 955204721 955204741
    0x30e060402090a0b06040315200f030403080727061803020a0b0f0708041413020a02071a071a01090b0607030804030e040906150521031605031603050d05 67
    0x3210080c0d0460300c84400507030b002d0469809000650070050181d4146926500d41c2d4080e24000360802e91625980d448103d22000e00030140395100208032200782c901204500ca080081c0000740c402800c1c840443e01203424180614020482c500840d000e0403011110310301c2400e04075044e485210040b0302900345101e8541b03014559101501d4000c2c100d40c49035890b050300e8103019400100800360b0010240039100c0040c0340c010040c07004150204d020900c40c0407000400001c20f842018070747c0024410403400d802a600840c20358125402040c500c5004500080c4089081c800d600c001051990040300303a034600ca03215180d45051b500071513020026041c0d05400d01070b83c0d12a14001034041044d49000500092041c582046040006040800c03440031f01d540e4801030b14000d0b20700d150404681d4500348031a04140351020000c0305d6203810b90443c0301000114903182d10948820f440c3d000070a514000a010081040381c00940000841c10306002040c2001043c5410401c04026914100b401003450880 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 955207221 1250 955205971 955205983
    0x222d090b1005180901060509040f0b010509060d0308070905030706021005010f0608130c090509010c0e030d0c08090a0b0c0703110d03050a03050907230f040515060a020c1f030e 77
    0x2421605040e14440d20390f500461000345408480d64907107001050760f846440300c050040c2c1c03190f1046c8020601d41e1a00030310009050700302c00d020b011910b0800c840e641d00c0e880406961030709410201020741391401c1c00c40c0c1d05142d5401444c3c05110b60f40e000103405900041b20010101340c0704c0b04000d280d0b00c402d0781d8010003400f8840d00001807008400716080c0c0c402d1618039074809100d90402541c059440b071000d4245c440841e14010144d5403a44082c550320742098100b41480c00440242401101c1c000c406042042c182901404042d000b040d011081d88440c0c0c003441c0074100c100c80080c0c0300c000e0101903d43c0e83d007090008803040990b110760000e00b814030104251440e41e040d154103080400c0408220000d04000b00a49924070480c40d0020b1140d0301c81203481c98088144100451101e100c01c1402004052040c0f903070701482c502010001c80c90082c1a0100e200c840c1111801d030340380e02c0d0000c100e141140910343c103544405108101e410010700c030451802d400c00961024070507070300819a03040c2c903a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 955208471 1250 955207221 955207229
    0xe0102160506090a032c031605010f09080706030b0312030a0903020708011b05281d180402061c0c051b0d08150415140f222d090b10 58
    0x2a030120502e0b031441c2010621542030341b003010480c002c01c4496200003031410010541d021003044c1d015000703005550348440a58000d41203030030948561450180405d65906042c13051504041c3d42d443c1804440e6020b1140500b20f007122506252642450419030005180341c4408401522900000080cc0701c3c060081201c1c10100c100c01c2c4031000701c1e202090b200760343300070415140840b0500ca80e121031003080341c026040490b69580c0e50004001e01c0b10701e8004019582056100b080300591703008a12030f1b2a0940d07913100e941074131039540f40e051003568001030046908131484851300700b22022072000d60140290140c2510000075a4051408401c42511582e0b21050b42001541c40b1000a9541104d6840a0001d80340a000000c6060541e5800307d01c07084c01d03806c05662a1119904d0141c0b40c0342002140a07680300442c2d034a140820a10003196030305001042c81d0440580b070381420500520311208030b803103129584103c210451200402c601c01412051421100d029049002c42c13000340388a000c0f00156 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 955209721 1250 955208471 955208477
    0x180f0f050117072303091b060f160825030201052d06011e0201061401081303030b0406030c0311030d080c0d1d1e06010905060d0206070203010e0102160506090a03 71
    0x5486a00e8115480d00c3c8000400c4655100130f10150340d203d4024008510510f101000382c148011105800107503401c00e141c10900c1001c0c140320300c4034510440011106a50f800070b404200701c0e0210701e4101c90700d000d01070003c6252810115020380f01d0103410615098603110f039000308050348c2e0b01456041e2119030429104084c91840030056990000c0da007403503802800504000b202c80554101f02051148000720340c01c0140d4407038a0400c080b0312084400c84094000f42070007400c0c0c2c078004209000199605102400f0142c07191102c90300b5813a00e0380110f0141d90001c440511803a1203081c407510031413548500a0091140d90b051980d21031081016900031201c040100d80f4003a00700a92801900c0c10881e0064217440018000d01140000c001040c1552000840c1108028807507a2141c20140705038000e1007402c2c2445c0c00c02c2100d0756080d4603550703141ea0488415454000a0001c80d004100084445e0003035032000480d088043e10070340e91004074501c517a04440c1c49680d1440200d480711030019000b008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 955210971 1250 955209721 955209767
    0x28090f1b021f061d091c180801140708070c061a13060f12053309010204060c020111010906050103031d040e06060420040b030a0c020303040312020a180f0f0501 70
    0x265824868009400c90417520480708101d142d403910140713218612a0300c6001c074110084c0c2c0030b07441002e0f103000340041200c0b000030040810a14402e040c2542d0041100003082510f50000d80c1003801040700b0b41460b07400400410401c0507192007414011041e2103800c0c40b0f400c0075004564001c0042c014031054400700d03880130a049180c0016000b000401000c21101805550001003a148484888003100e04220344050411000c21031810007246010301801c101c0c0e401004240006038000a103100d1250382840d040000101e600c8429006020302040100700c24140000001070650204264034918200d1060301084082c8004000449000b0f0440800a40000c000500d1a00d0640d10400c00000c0e0341503181000790701c58244000d00e84c80b68000d10074041010003403044070600c611403051405550700046185003842d85000c0d12a04200c411100c5058002801416041c40b60038001d0071308040c00010080e064484c0004502691580540c03000c079042070200107031541c07041b451810400300014103480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 955212221 1250 955210971 955211009
    0x50a0503121e27040e010c23070f0602040611210a05040e0703050412020c1509040e060f0907050a05060715020418060801140c0d0b0f091528090f1b021f06 68
    0x30310003005552006423201c0a20048010038100c0d404100710900c141c4005a496043c1080078020100303aa01c0c203131440e401007006202002c01d40101210082c4600c04158650368241c0040f00d49101d107401542d42c2140500510850b580c250304400c1c0110301c29403038144104079482007260340366140e40140d60303c441d03145d0101c40700b02418001402d0301c500280012500300d803110742480c6030000a654105404440304100040c00c1014084480586003c171428450b4502c1c110000b0814080c03560050181440399800071040162075046a004011800d611000b5408140e00b820090031940714050300c035420400200f1012210790381d014402c81520207042c1c1003615140380100182141a45d10b600700700710405500c1c15a1f80c100c49540314141948c04d0310311440e0303690140650700a00c1d4401c00f6001d4800d90320a50410356a2400e00e041c2c45100f00300245089061341414050190b1040d44907522400c03000610701315901040410b9500d915007a08010040654048c5080399060301c6550285185044800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 955213471 1250 955212221 955212257
    0x2f0406080916080709140112150f15050117070804030c0501020408070b0408190b1503070308030a050106090e01050a03170919050a0503121e27040e010c 67
    0x640248001040369000031414260401034201038110a00f150700251040110072624028010350381039035031190100d945040f0700c1e1000007030701b81d00040000c03000e12205580c001890303010700c1100c0320b4601c0c144400d0b5401011030414117070038011a8001070355120170004104059003c1e41c00b0301c1081d910200c156440307440840703150000001c1110365540810000807020001c00c600e601400c2c3d82607205503214603100c002403a0081041e1014005d1a5000a80d000710b419107111603030103142d1100701400194003000080c10320301c4a0700002d2107a00b01000340021f800444c0e0145058410f03646903c217003662504c6680000d440300340b10302588042074240920000341070312a10348482c102440745606020600d400201030140301c00089002c00b569820800c22883c2964114004041c1034002e40034006240c1c0d403103000ca22030015034040307420564040c461404944400c55800704070702007411981843c0100c02e41000710300d000000341b25a082c01c418101c401c0d8107205000c11411503444007445100d19480c05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 955214721 1250 955213471 955213487
    0x21315150201181e0c0602060601030e1606080912160c0f080c01120e0613050c040903080c0a0c0203120301090515010512180304060201020c1e0a0f0f080a02012f0406 73
    0x1325141420030207018000070482c4800401404198018004502d001e01c001011036200743c00d6011980d109100c0322081507000c80d0340100792840351800c2081a0740d98004985040c0300d45408082c54180041c1e449002e841c611108208140310701c20a01100d5500e5040300c2d41d0b1100b5002d074183c0303901303c100340c2401580180140a0141900c040210704000303025506d504010b000c58108424250f01103c00003040014000009404003c0320700700001c904544002700849030082c4042c0c0460740c001901201c8601407104900b0040e80101207500c010060781a158a681007071084114280c00e102c046054105211a10015020182d440c1c4e800c100c000c480a1148103000350a1000e016004445524581010720041000e4411070b000503940e10b0002401c14904004001e0103060803103e0700c541c0d0000175011030545100c503040160b08140041c01d01340202d07810085031005080407000200710b0611031b01074206101603901d0207911900091444101345816541925070712140d10104001d00c0b10500035444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 955215827 1106 955214721 955214753
    0x806041403131e05211204050d230304060c1407081f140a0b0f030109030f0c0807080c0102030609130512030402131515020118 56
    0x82121201c02c40d0050900f6400c0520b20701c1801004030161034054a802004039050404121503e400d6042c248500b02c1c80d409039070500c1c2c81c62000304090390112540500041c840449558482c0c2c01c04000029840386010741060780f4007811002c20281001d0039981e01c0b01087c20000d03041c0240000e03a40c02c0c0c00301d01540540800e004007100418030713450012000e52000449040c0c0c20450003e0400c04c041c40c0c1d02c0c2d141410401c891442103420043d82c18005031006030241c4411b070140740c241c40c4943d9001e0040340c03103506240314041c0308001100c2c1c014010b0108900304882a41c54240c903922001c01d01040742e4020003401624a440b585050300708a8180201c1040895682c1e207944522001c1c00e62100140c003c0005010343d21900f5240b54003043c3c41608110603c606000c06c40040c0c55401101d0b001c00c5001c1d600f0251500500c5801410000054450904000c664407204407082e59a0307 = true := by decide +kernel

theorem cover : BRFrame.Cov 955035971 955215827 := by
  have h0 := BRFrame.cov_init 955035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 955035971 ≤ n) (h2 : n < 955215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
