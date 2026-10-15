-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4747
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:24.647019+00:00
-- url     : https://prove2.me/submissions/8d3b713d-1fa8-4070-b576-98424a03dfbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 853597122 ≤ n < 853776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 853598372 1250 853597122 853597139
    0x21e040f1406040603031209150e0708060c1305091305060a051602120a03180510150509060a090e1204260a03140306040603080307031a030a0305030f060406050a 71
    0x1451220704070518024800034245007402d02c60003003220342543d00c2e00e05801101c00a40010a207488d02545d8030380d8031003a890a64090350069120311421100140301c8185080b090303c2c00d00070040d02072070341401c0421030f00c06415060726041c0142c407811200101c1581790620901d28031110f0010050807405208200801c626550340041d209468484640700303100c0000c00d04989555642c035260740c102d101840206683e610a500450f000303594110b4400d040e48068880c24900300c1c00746543c40307a0341e484100c60829240748420000c02000c0c141c03003c41213030500fa4009660305440d0301a64102643d01d03031080c0b111032800c1008915030000148240c0d607868441c2070035404801030400c07540b108201003032496440440001da000c4a160180c1c0e07130660701c807182c40c030302d561701ea00144c005507100b43c50740c40200c0400c0b0240f00035400b07081c01d524002800220340b10404440741500007514441c1d0080d81c00c030380101343c110781100d5201c8150380c84a440307955880d0001e401013400790001c54100e00348c03140204480c0c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 853599622 1250 853598372 853598381
    0x2061309090c091b0512060f0901030b09100c020d140906040905062806080c0d02030a1d070501091202180f0a0e011a0f01031d010b1503070c021e040f 66
    0x610f003d900307102540b02030810440c11050b255000000440400c014168400301c03010450f00030320010b122181c1043e0301c10000e214000281c000b0b541c459480002d11030944002c0090010080c0385074030034800171201400284d103c00c0c04035021800d0050240c0b2410300303244440e088481a410040880e030f15651a11040c100801007143d003a03004000302071701e501004080e46000312034442c2c1c0d007402d01d49440c10194116010140a414020400c00c1409921400c1a203400510310940d00c4441c002400c03000c41112007914802d8000c014100d0300701303501c14440d5990156109081d00c400d07428810000c01c040c800b10f4003907604000d49950300e44904040c44070034642c580300c840c05a4031180003488020a8175078000d00300c4a4000004154522541c0b140e0046c2c241210b10340c0d5200c005050006100c3c403000d40c5031464405403000400e5596603400e035081030340790401e04120030202d5141060305619184901801308164130038080e2040c504580101075a600700508500c000c0f01c0034000340f01d0060396008000280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 853600872 1250 853599622 853599629
    0x110c030304140429060f0702180403020c01080c0a0f020307120e03100b0f0f04091406070f090b030a110403080a09090e0a0b1501020c0409080a02070602061302061309090c 75
    0x4506101000f04444c110341c40e89003015854040420b504862a001c021080d4002401403200003024000c1e8400350395140740001c0728000280c0c00e22000d18240c07500904046030700f004541409490400e100d4444141429645080078900301000c810356040801d91541c040c007640145011007590b40b070411540e020850000d08a815002c884010b941c94580c0c2042d40c0149011070307002400c3c81c020548524021822141e51000640005000b40c00c0341c440b030b0b40061050160000700d134414002c0c03000c440e90102c0310706402e210354034007000d82d01d040c01070010251001610b800303451a1075003290001b104400044034005c1d07521283e80d9550f50340381400039211202c240714415190f07151555080d00000041036460001d03a00075807403c140d540349109010f0503840000040d045115601204455449074420f16803900d02500c21113888004d1000000e10384031454000104540201c07061010503981c004041020715070489000e9200c0000c1c0803d40a12304203644560005410701d10b00109000f10410f540c0c05a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 853602122 1250 853600872 853600879
    0x503030d0f1415100c0b09070302100f05161e05010c0f03060302100f0915031b091d0903190503090c01050c030a0e030709050108060f07180303110c03030414 69
    0x41a280b0000d440c0540c00443e000c0074a1500300f8005010b0b46403901d030a20522031241030003801c0c10140e40714190380920450700491140c1c000b00c014810751500291044103418607280440b003614030311000420f01d00800b170b000342d201001c1800d000d08207c507903600401360040c0103940ca204084141400d034041e104040f00c2c2c1c404601d4003400165124468054075041c8c3e41c02618a050707045068108403540850b10b07048000b0400d2803903010440701041c2d1406401c4a0b81643e000c980b0030103407030314420b4065010a04105000302e001c0100f000c580d11542c2403000c544980c452605643c0c626044604502c2402c000c810300c0d002c00e940005d034090b0001d01840c0a020740b0001c58652085600064400e449608420b075a5a0301c14401140070303074444d0b03070b1a15003468090180c50160303503154511020f907882a003040e10140c01c06810000c15501c1284e1566000a4918007058502824012080341c40078030300014041050340c0c1c1600c01c000c1000c0241c4108018007130300301e070f54441e940c0c0c1e0341c484248015400f8910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 853603372 1250 853602122 853602131
    0x20304050a06060e012610060906031112060403200303160f08070e040b040e0a080301051e0f10020313030b090d170c09010c120e0f030613060b0a0503030d0f 69
    0x1103130010290350505940340f14116a0b412016100c1054040031034802c0b5902d50310400b0010720901c81c00c0c1c0144401080134200c0880d200e401e62074000715081c0d6100e0910b024115901c000441d00200040036508150141420498180e8190b000c0d4040101206902160310000042c0035031020305e12003040560603103645d030049070420318030202c8224000741c8003100040c1402c560000d152070903a00200315108000e10014410b400a2922401c100e415002601c42c2403020004000d1401e05a0b081c20b42c06161710101e80b0f2002688000484101c000300c90280521060803006038800d000b04200d401d8802246040c9041c0f599034a8102000d1504646d0702e0f0841c0110f4040350604c90080756504d1a924000030481050360340c03011115156000100818100184044807201045900b03c800d01801c46030303a6072001a207050f5041c000f81c40b5085800b14001d1340044c1c2003000105084000488aa0340158007007002000400020f9007040d00d900019410b00001030522880c1302c16034003031a0008000c3c1c10900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 853604622 1250 853603372 853603379
    0x16020609062209050c2712060a0e0d0207080615010c200102010c051809040503040e0f0402101b020d0203070b0c01020316080601020604060c092403051b040905040510020304050a0606 80
    0x882d0013003290b4030a000502c1003507402607903804107011090304405000000d104130100380301403812340c00340c4548481d607985200c442c7d03031010280320003003030044640000d188003480d000c0b2040d62800e00502055207945a0101c000841c5c1c03003810f141c41c8083d000021440000207908076406204450072202c1e0140d0318065500384410702800030b42d440c484c9484950a440d40a80e800e00009a000a0044680d400304101c0071034131300681c00c0e50074016a5025940040c03840c291040c03041260a0f0800e12050100c86c181d03050b403101411003840542941030700c02200c40061480400d01c3c01c0d40b59003203441c5034500440c84c034441003030550113148181a841482c100990b0410005c3d1515101070f28030034016000000002c1c08640c603a040030420541c14946500c1903a030307848040400740481000100109078242620180b260f15004454000c00300d5205142d549040b240024860711807403050500311511a000141401000c0c0980c603019180a5425583c914191400d980c032030485000441f2018501003010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 853605872 1250 853604622 853604641
    0xe0a03060f290d06020910020601141801060e130614130c020d0c1e08070b07022d0a0609210305090309210f01050910021602060906220905 61
    0x14101200030040304030400c48202c00d2040b250001c07902a503440750200151802a03c0b0054550743c4808907901409455040c480f101030507100465909102c1c6041000540201f481c46051078112541d908280101d42c503a5004105207690320058000c0d11468440c000500c4001010500c02412046a4960081d901c94440400700c5425072440801640621079000000e03008000d0040300c0342c02400500c00c1c046032032014100c0c8002c8070307404451381a4003085000800c41b440781e0f0580c001000f40045c0c40003c1d0582105a00b01d0314180c085540e0180b5544d46481c0d032102444400001c54200100703000c2c0042d242071002084101090035410600c844080d0900107110b4072801d0301800c22003000c0e41ca400041d000704541c83c00c0c6030b280708c1c0c5102c081c1155074110703280820030320340b280c0c0081002007501d2406c441681e04010050b442c14000030300400c6124503a41da01e40b600d0021960448000b070702c0d041c00320041f48541c0100c10000d10300c1a81c0da500d10056207080c0940c603040b02d040391030500c02c40d582c0b160390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 853607122 1250 853605872 853605911
    0x1801140d050a02150706050a0f0e0a0b04150207150e0c1008070309110919060515040312230c0c33190e0a1d04120e0a03060f 55
    0x2904a030480b046401c0145000500102c40d0010110700c503081c910203848100803900d094540c041000c3d0748000001114040c2d0007441041e07800000640301050140e2900304100e0002040108540c07901100c0d01802821941940ca1183c0c00c10310301c40d4015159a110f00040c010018036032079902c5180d8600300589002009150600d2042e0b40d0150192280401680544101c200c2207441460458060a060b11546c506a1080241040e4860540e00c0700c40040f0031110103420482c0100c0c054092084121512403c0341c04403680003007661040c40c1001021174407402c142d501d000701900c00d03182c840c040d0030f05503010300420010101a18505c80800c0d00300301300d000110011006440380e4102c1c4100c00c0300038881c40000b03030340030344101ca103824041010400c00c03084414150300401e0340d40320b8501c250304110011902510f81c1c40c607021600c200c0c103112040780160041c801021018a0380003814407901c14482821102400f601c1d4900c41622032030108040c160b802c800c4040c407498100c0800100c90304c00032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 853608372 1250 853607122 853607149
    0x30d06080c10050a08042102030a09090e07030308060409140a0510020a0c110103092a0f030b0f09070f0b030403020c01141605120d050103021804020a06030c020c180114 74
    0x80c1c40d0f00c1d0011001054404210082003030322a00481510200116481512101d211f05242e014695600081c5009402054a0b0b04040e010307611340403c5003c029000550320040d2505400c0c0521550f451000007030103080501c4e00182007074503031401e42405080008840600074414800e1b01c006030f229215140407402140c3d48036000a03540c034404000706101d0030103454441010702d0040381d4400c258441e014100e1008070b03080c01c481104026100081d84149965004d007104c1510340e03516500d1a2101e461031880a800d04801819840c080350180304204441d2000380003040000303402c20f54902c90440150022282079000d4001e480b1481c030a984180b807643c6040c088505241d04140b0140c22220590b048070104907a80c1c85071b01d201f000b210fa40ca401a00030703082c1c0580c0119866041d8414040750064000360414540b2600050000690b15190741009545203441d002070480c071110412850310207151442134002e03040c200c2411014050600f8075050760903503003145201d640c3c41000e1000a031141c50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 853609622 1250 853608372 853608377
    0x2603090a05010509060c0714030115180216060e010f230106051308010504060f320a0902040c020c01081602030d0e030403050d08010f060e0907030507050c030d06080c10 74
    0x4001e02035980180301070b100310100035012504100700c08030800e03c0d01d641c5422a018a21200741e40d0040c0341340900030f030b08035880758071901c101036450514210400e014500349034000700c0d00407450100d01c5e680c0c071307020107956504407a06110740b003800321000e802000f002d00001101400c04011091010300b13101c4a48010350002c40d04c07440f982c6451801c46554201d16040f00240303070b41601c00200840240038090140d8055040041d2240c80c080d007284c00c0301c5184915046007512003145140c80c02869911841c101c43c42440d04450756100307a4205c00500390018002d610031319280f00e01d4091980024902c011500c00c0e26039614988030184000c2c0d400103030203103031801a070040010259110346a0400484007001500b182c5c10203440b41d03a640e00301441d9400510008644a00420000000361030100c01400282030180e030141881c404100007000c014141c400b81920740d4041031402d032080e81260300c41a4072200703482d1541407c041c01c2d009000b107849115403a104e9440141c00d07a1a00298610907050140c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 853610872 1250 853609622 853609639
    0x61302071104091121070618090c021c0509030106050609060702040b04180807050d08060112050417030108100f0209010c0f05030c030f0301060f030b030c0607080c0304260309 77
    0x2101008080d10110310202d43c050040c2c3c104400507207a00c190b401305c45109514401c410180050000e2800241b54010410088410184001c1031401c00c0c8035011759680001c00b00d41948035101c10f82c517100080001c1c5408041907030f1094550361b4000702030003600404400900000d9918070401c0000e00a02948581c06541080002d0042c50194040350329070102900118103000a00749448007104100000d4a584a00240c14410408144150b0943c01340d5400c01c1d13034960400303c000074040d10f901d01c0740203001d540c1c0b54041000c0c424003685030f06499141e05c20381030b600d40e15050000d46800c1e1940700501d1141c18401c01c194500014002e541007888103941703081b00802ea5460300f0844194803034060380c081c041003000b511154000d0006151001c41c0f01510b917543d51402d04000c0030a54510701180405282c84031415190b40d002c00c0101c03040f00210fa04d162580a00c2c10b00700024402c0d5012a00ca5201c0060000748084841c00090420502c0c8048601c80e076030b4803c20541c591003099049680300442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 853612122 1250 853610872 853610903
    0x10262b0309020a260601090504030e060c010b2e030501030f02210105070315050609280b070c06090f080303011211031605090105010c17180603010b0306130207 70
    0x940c400003030103000420f03040b11281c3e224a0070740e844100c254103800c040030380361a00c055000104641801403100c460200200d16003510000c1c68003d12500c8941f00b24400614260194025000024100d800902203e04001d60381c00c0f100308041c41d180400301d48560b600012007140d01a00c6a03504803074014520781d400c03500b0b650811811510b03141c400070010710780c40041e0403005024442e01f03200340032603100040c0c500e901607802102c11440350b2001d0310681c030411104115071202071700c03000450002040781c44ce001001c050411901c1c190780044407030007000300b001011701c01043c032441c08582c581d0302d60300b003da17032a00d0440c1000c06a80c061007042c6d13407040004108103c0f031030221010045c0684201071180707900c00f00190070007006411900500070041020704c15468403060180c0101000d080045a012480d81c0b1002444526000285414404209a205041c01c0c0b862a42c0019008100f0356a035a1a4070711021a9041036440b075000300e428980c0380c04d04860714400c07a07e03041e8010b80d031049031148 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 853613372 1250 853612122 853612127
    0x6101206090203011415041104081c030b300111040b300a050f07020705010c0f020307030302030d1b080c070204060302130c021605010903080310262b 66
    0x24500708a801d90750302d9100301d9000218541e030358003411001c5081c115006400c010801565a20170101c1c0483c0300400c0100300340d020000d007540d0b031014050b203070720900340820b2010780c000c09600d004a500810240401c54508041003446001d100d0706000c1503980d420300c101403d00b08d40001d41091a1004100010300800003144081c00c620500441007030b2400500d40080320000c861480540c160801c4c9400380308903000d1500a83ea0f12854040820010346807030076000b0754400052181d1410b00c07480e015004148030741090703c101104c0d006000c45110950700e1500a541c0d5016520610002c1e142502440e108038605100100442e00c96440e10355540394014039074030310742c40801e0481c1d000b6960340c800001070710b50145125030040b028000251002d140c810190030481031012461710441d440e9003d000c03680c0c00c071800e40c0540e50030801194a03641e801b110f1100c00212a04400182514103245110717258100c0140c1d1380b1100c0c620103035100641901000c0b030084030100910061240c102d200405200e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 853614622 1250 853613372 853613381
    0xc0807031a09030903010615030c03092003012705070b03010305060117010902031606090608010b0409050c0d09060626060115051219060b16061508011d06101206 71
    0x660810690349013141400000742180e04940c0400c80c81d10305180c43d00f4050782c06110301a40c998003810140102d03c019640d00c03200d00000c1c40c090808283c805850700c02901c0950001624520100350b400701a2101107100d48642c48182040f01d00d071040e00000b0400444030020303039048940c008010311080c0d00308408035250400c804071082c0f01d99600c8014101503503081010700d140c1184452800381e42400c02100800d6207900da0041018000c0ea000100000f80c16502120100c80260304000361641750111454054400c1c40d5800301d00c1410300e41170405000583c2d02040c111400725907080c42040300ba881542c1c0880d400c4812070b2841d000343d001000140010402446006a00c3c6480c0c0e1070215032041d008104241594210150201144c0c2d541700320406100381c001600581c810141810314105007456044004c0b02d008110780e45940005266000c5110b451001c0c10203000244031000c0036001b12078500042c0b000100c844d128410124002d00a16200902604c950f01d040340c211071155220769010700f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 853615872 1250 853614622 853614631
    0xe0402090a1112012402100e150a0e0606010c05060f09120c010b0405090316030c02010314070806010806101719020f0409150b0319090b010b070c0807031a 68
    0x40d48450b960000000404002c084001440c040741d0f00300d50410143c8020380311040820145210001d00c1d000b221500006c1a5442c0100aa4045642c0d89802803850030300341c031500c1c440d041e10320360000e00094041c1c80e04944240c00e20042141e1040d51814011125040e144401a00a07049075012071288402c01c4810395000d950501200c40304140e0040c9040c065005c10120100b60b55946d888001910701809020f8012041c000118205001040b8400d40c46880117002000e01c40000c10306411a4060b070000740c140f00e08207181c60301d10712305071001500005049070054002000f2a001900c10300d4200d2990217088510f1355188843c4d43c0d002c01407603803c0d80190030304014821800620361022468001055035000201b030031600e55150800c6241595500d00d0b69a0034400d2008090143d4207403941076a50000b41a0383c4e80414908180c258001042403010250030040c1e804000304090507000e0007418101d108024a1841c00e603500280e51300c0320064040145400e00003898081003100c0006402e411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 853617122 1250 853615872 853615891
    0x10b030a0902100c02090907081c090906030b010e0601081015050904091a010806041e0206070c081b0a0807030212190b0a1413021c08030c040314070e040209 69
    0x3038180701d80028075101d402e42d0030400018000d001900850a010307040c640c114100c5c000030031283d0b052070002c40c0c0316502ea128001f110032222550b540813a1086079070400a24103c181005102d88074140360000050074000c4082018040020030b2040d407080da0320034804c2d801c4000b1200550304091031205804502c500c403004020713060280583d159214032582c105244514101400d000219072055280b06050b070011409070800c10401020a100c80d0214441e601c41070130760300c3c074541ca6100181407405188000380c58130110200c085075044000590004600c0801a040b03ca1780039603040183d0021030f800b0712401d640040c0410001414800d1140c140041480240c4020740c1050180c441343c03105c040010ba0701c002a9400340f260b0016684100700b0107051090111000d80381001d07500b160251000030090003410501181c0b243c00520000380452564004101562804e201100340350310303007150205865101408000c814824000201101203450001c442c0503907030f41d25000c2024054004050701e48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 853618372 1250 853617122 853617131
    0x15010302031902190e06070f11060d050a0c08090106051e0103110d1e090f0b09070b18041103040c181103070216080c280e07170a0c08010b030a 63
    0x20b080c91580041d02c40d070101c980c104016000d140d0300041210701c040350a01e010741030070000c0102140003005000d01054000c01a04000000301d00030901a01c01ca03800bc001e6a03203084244040c0300d11903000300710310301c406a6031503c3c55228801e1550880b1000d1052541c802007080030050100010b100780100003905040009650b85a8112141c140c0e1260309070900140d44c07056040c208500d2210100321141d82c401c0200104c1800342c0d2940c004040000d0080c048500f10000070308413000030400100a4a68600400d8403818000409444124202d0085100300c0c104105074401c00d212a096921803034009400300b0071640340c203211640b5032580c0c810728002591544000058207042c4402140501026402046a805207401c4212500b0071a081001660004140c01400e039480046191804042540e00381004004025140358000c080e807050101201c120100501150002c50760045d07c4803039000750040b65684d840907002c641a1a44d1303540031071406401071040e840e040001d141e1040c0124800075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 853619622 1250 853618372 853618411
    0x9180b0a030f0308130b0403110a0503040611070815060d0510110301031e081e09090106021c090f150e04062d03110409021f0201051e1501030203 64
    0x198840020741040d0303090502c201040080650040065903c1121860200c0c0000059a548001003801a00140400c8000d241c000002c0030300f440f414444981c488100c0b652590345040140c00640da90001507082e014a0500060001e40072620203640b09170f041c00f00c030042d070765601040084400b0401c00c2c1c60520402c502c05480001c10b1280b806203110300820f580d103962440c90046031200c0d81c86240d0406078a039135082000200301400b982c2c1e4401513071400d1070401424081110803030148008550b0320002003000000d6540c2c02040641700c43c80e0707030000080411081402610300004900c142c00e0110310b9500200510380c018030009901c00c100d4608114507025500005003540c46030380201c0c1810201c0041c0446000b0812200741c0c0808104d42070a40040c91601c1e181049142d0013121380c00f070b60f100d0f41944115501d404000b03005040c824051281e030000146d00a0080104546400340d80ca4640015260702e036040c00d0b030700d00c40d03242e0440e113441814030f000044019400c041d0144031414803030359141 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 853620872 1250 853619622 853619629
    0xc05030406021515010f0e01030b0d0f060c322701021e19020d05060708060108010905040f060c03181a0a0c05031303230a030c020d09180b 61
    0x4000805032680101004044403c12200c01c0314050300304007404083c1002048a66003020181c02e00c4803c41c1006040a1480b40040e406420441e28166211605000110130080c51601501c00540903c2040100030300e8410154ac5290788000d800703800b603c0001c05800000402a44038600c911414a0300c1c2c20060031810f03420345440c1001e4000c1c80403050301450700c2c1c156410010f005002d401e1103510700d0101c54540c842e80d02e0348881414503c04400c408024820b64a804140700d515543c48030443e601440d00c8640102030150940340c1030f00082001000140a40c2c20340107041c001ca070007a0813072a002c00c243e615200141105000f40062548076104401c4048114a0420980d401125209100c0c500c0c000e091801070300c001c2214406515000b60040915070000c150303170b80101c483c04460715000e2541002c0d40c0103091011300380e0f0841c0c05804140c041000b030b040500102805500c0c00d1081b0b030400780050762141400c0c0d0172040041c0f5691130400801c0b0b501200c140380c3c0050808001001c1c00e459000c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 853622122 1250 853620872 853620877
    0x304150b0f040903110c010206070e0108040615060f0314060120010b12070f171c03020705060a09060518030a0c06060302060c0706080f100b0711041a150c15070c0503 73
    0x2034002c6085019136040d010300506c0300c1d8070340703100900c09030419107094000940101d24004203c2e04004083c0000b4040000c25400b42482011104a90006a40d1400010401220001e0541c0000c2c104500d0b1004245800783c0e035030040405031034420380c804010140c44600f10080c81f602021f5034941d4580442500c80078503492000840c48045c00540c0d00300701c0305c850491007a9100740245280da10440d84070241c04224408441ca40103c54010340010003c220042c2c059604040e03d00c1c003980b414004c00d4403103070303001c2c10b030583c03145001340f0480d0343d00141c840f1207100103610000a40c000300201c0b00c0961150258103207280c8101c000180c502e4680c1c003c542c040d0440c0161083c580e000b4a81400069040944154403801401240d0041d140804d10200b0030400ad200d04002160049000c00420009200c4d40103000380162041002c0041c414003d03801c81c0603521001d0040701c0e5842041e6401c0890800c50b0a02c61581d4020300000c1456540054600750061401040200c0c2041241c0000ea06000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 853623372 1250 853622122 853622141
    0x120109020a051b0f0f0303061c080d05011511010b030601052b1407120804050618220f0c050f090604030f0b0603120a08041101020c040212040b0604020304150b0f04 72
    0x6001c0d480c01c2d0504d280c601642a501070600b54030034000c2104135a51341c184441e40d1550707844200301e0758000d0300c0c0101c1130380075842040c2c2005041800125030498290100d420000265442540144003149003500f214414030300147c240d0091030041c003803070800d50105110b81414902032507004000000c45008400030b84400c542c10010b400c200c7e220010300b0040304003e4403d421241e051341d9500d035221a00345c407582c801e0340c1c001c81002c151404196040032013500b0900c8007034124030403800c046401c030005595900003144080d180441c0c400d2a40706501c2400c403181c095450306407800040c1425916290005800306034005420403021002a90b4414500f0641340700d000c40c11400e040810030182003811100e42510744078002c0c02010401030348051591341203034000c3c00c941c9141540300e004030300344514055040e812a000144500340c4041d1188814441d901500740710180b07844101c1000142c1c48290740140000b00c00341990000b041c100e900c02c00b044039004101500c0b0b002c2c401c0108098818024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 853624622 1250 853623372 853623427
    0x906072010020409050633130e09010e060705041205010b210d050a0c02060901140f0c0c030609070b0a021f06080114390417070803120109020a05 64
    0x20308100ca40111700455810003401c8030400384044d0241c000c0e145000c419001d048030542c0c03140074000d0400144003203a4500446182c280505c58844205000001d81500c15060540ca482907101c523065021811501510055aa0601c0c0501d410740200803180038110944003035517200d1440440da0703200b0752000b42100c000000c4911180880c81507900703040d840400c48084c005c1c01c00c2491103031a44024610080c682c11100d050700c82a06000413910802900722080d1383c0c4400207001224400200090302409650f0340480d206440003200340750311384800355071600d001e510640050042d00360340c401912070711440388100c40071a504903421300304484008078035000742603076600180310405d000c1c0142891400c11400d0382409080610848010100c0341c0743d0400d0f40068090007441004100d101c581403800d400503403503201d0b600c0321410402c1001034200700b003d905c00c070140080d00d04808825030301e0281140525407a0341e80791011690103035001020101c204141040b28000341010010201000c99000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 853625872 1250 853624622 853624627
    0x1020f07120c08010501120f32011802030309040c14040f05090f1902031b0c061e01060c20040c031a04020403150b0315070e1305090607201002 63
    0x9040c0030b11180d0050f04000140d0341440010300034002d5110b41154841c0d80902d46482c007541c40d042c448006c00100707a041d51068540001e11040003d540200c020a040b00c0d402004800c4040000d00410248200000d40641091203407010368139269102080180c0d003410140c01c400ca440150403400c1c0e03c581c20403911520342003804d01103401c1a0680a5016803030081e64819410311440d42c8581d07880201500e01200d4002001600000000b1401d001204080c159180c84821003012292030310400c64034030034001c4030004a0701040043c1030400d4120341080c0c4440c0006180346e1194560070384800300072984803003030307001c880340685039886088602400366400007940070140c003100703218580c1a40740c244030744e005000c01e20218a52002894502d08501c07800180b2100843c00f013414090f00c4c00410526040740020807410542110340c1103049501104d0350704954040c0031805003210340a58a814440d406034000943c802d014a07982c1c07004c11102840b0309a05640248041e15002c0035040d207001c0070790007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 853627122 1250 853625872 853625909
    0xa09060b150319020f030402040c05040f06050309060c091e040603020d05010e100c0f05210c030411010c110405090a02040609020c0c06120441060a2901020f07 70
    0x5190f2114082c10800065213000c80c1994043c0b0a400054030107840303103540c1c0403034080680c00b80d001c80d001040c400c0a1011650390b9420301904a42041310303030600500842c0005495191704c00211394030503100402184031500c03040f544c16020400d5000c0990001e07620308001c00580d130740ca01e0702c6c5440c5202d00004101c4400c12284203003000c80d1440c10581044c106941c40030016000b1038404000301440c606152150441840c1541c104069250960151800d41c1030000c22148000113510841c00f601180c1e9401022000445405003503241c09000306142000350500d52a040d08071680042c100021034903804034a40014046800b2644102c1c4030a60005e03420020039003d110340410307081e00f16800c60410f141540500784000004000034503a03111004044880141030409072013442c0060020480c4054201c01c42c038800542101d030202c1407103030a0009e400c60110340070768402182c124542400310202c1014403079140c2c01c802c0d81039065024205803002c24440030440800201000c1461719040f106 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 853628372 1250 853627122 853627141
    0x22080d09030e0415050409060b120309011d010903060c1709070609050102060c071103070b04090606090e15040b040b03061302091305120702150703090f080a02090a09060b1503 77
    0x840300b190500450030055001800161001c000c000c03a031040e900403940000700e00d8210000c05500300d0f616408090901d400380c0764036001014082030740080c2c0f5408820b00c404c070044840075170b240e48494001840400180000b4101d03400c05c01902045061890300b00c2d1300e0501501029608441e00c2030f40c0c0d889980104034013a4030035141030080c0310a0024000038201540b0342034540c0300710030010742562034501d250312054404100c000c00901b8021030007915075441d900000080e0100703221701c82c00250307031400118140c0b44500705a4051401c1e0810020120070520502000e0210010825840303907882031640260780f02032140c0d070322500c40c0d5050b01103c410f1030303c10000c251502a01c01d0401e009e86000e01800034600040e905e420540001095407110030510008429150800f0a668403640c04a403950030150003c08c100240c0e2001c860000025840721046a960105260040d40c040d401d0004500d5214844e844818018042e0001107042e0001001240303080c120b1442c07e1500311000401c0042849 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 853629622 1250 853628372 853628387
    0x120f1703151e06091e06030c03090c040c1b020114040b1b01090c06080c040504020c0309040501090b01052a1c1b02090402130912030903180e22080d0903 67
    0x1e8029070508121070000103d00603000300f0300c0c040d019040030346a14811810b14610350302140340041c2440d0b680d10340100d0104154006403550401c40c481d41c000c51400f45004c2c0140ca003e0036203075480500714a500b96121046500807082031381070050490000c0001e00c650030040018001050100f41c0e2021032000041048000303403040a05030340742000d001d00040c500117a9200b01c40f00d61a120880751070314503c24406219945c03007030342e0081c8000341034400400e000c00641921103080300c0401c09030307aa900d811400d0319204031724507000510800081c0c07114003d025000c80500c0c0441d100060038170303107250f00d54031303001e011282110107460506420105950000d5801c0c0c03212071591075400301c6805640410314944018100903c02e007186140d402d21020203a00c030702c1585401ca10084128025050003500502040b4030550000d4a9140003c4062400500c00c6c4115201e0703e030407480940c0c034010f041c07110241404803c1d0b01080041a0a4085031216004d08030b0714003a680d001030007103060b01c0c01400d842c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 853630872 1250 853629622 853629649
    0xd0e10020c12041d04060608011521030807140d060602030304051209180c12160e040207050709110408060703020406110d02060402091e0103260301120f170315 70
    0x100d030108414455001654070b0a03401403030016102d0581d171900d1800c540500000e4010a101d0f610348124003100c4104081c51a0480e20346980c4000d03c8540c0f5100746008211801c1c0150220300c1c00e2001c6840c0d140f01c0c50710101d0780c01c08075003810304244801e1244420f4808950016005070f01c0807051206100080c03105105040e00b00510a107424031000c04601201c14201000644803444130000d105c030340c20042203030302807a0822050901c1d4540070310240d185141280b0090001150f0040c0b0320b2147c00d0038822150025002002007001c0c0f4038144640003c2c0a03240b1460343c80100c2031100191800082005d01d0140a041d10701503100d506042c0d004102c6881306207118250791201c3c0030f80c00f2842d0042085c0b5005501600d21440c1ca42d640a02180e400c1000030781d50180032503d034000000c2c0320030400e5143c4868540b0408044078044080b00c600540008e0080ca003003604540a5040001c07420207401e18410301ca10b080c131806026940300c0c00c03095042250b000920030002d40407000c0524003a900070081c3d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 853632122 1250 853630872 853630903
    0xa0b180106121e030302160b04141207020f060c030403060b0432070905060a03091208041a1306050a0207050705060c031c060824010e0412050d0e10020c 67
    0x280786598035688056040c024000441c6402075403c0001c0c940310380c044520740700000c480d181c05a0100d1415483c4440d0403581070b541e18152180c810309183c80030807d03442025050906e03504043e029001c025008203c0c03112161b20180410501c030003240184040e000441c021a000035120601d10180300a803001c1c140d1200104521051090f1038001540c0c030f04002e402c41d4030b08091695111982555451059000b07558400008204001d4050381500b0905c80c2d6072040016200c01c40c3d20341c0c0269880c800555004001c18041c45448240045181c1001d0344640a170910346041c040e80d407198400c44005440c0c50a601c0d03000a40e030707002e000040040c84000c01081d9140761400004403500d0740c4a0080c51500074a4108041001c04501d100d0303000100030b441c00c507058404c204900b0110482c2107032141500600341d480301c1c000080c0010f1910728144601e4000100c1c42d40034103c42802c075010351002d0418603041e0b541c0c04074103441060400c041c0401e040703909801613130f4071000e2220510b44200a600d2101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 853633372 1250 853632122 853632149
    0x28140c04150903020d060e160f0501140c07060f021009140607080c0f0a0e030f010902120c150f0705070605032410031d060a05041109060d080c0a0b180106 68
    0x1030b220800170001c51500028001016546042e040c3d080003500c0485c04200364424901103200c400203007402040302e07001d0300d6003000903401403590710190007906000d10885e00071401c100841c1c0c0c060341c0e018166048074410344800404404102c01240c01c849000c3d9070351359900513500d08080b41041f060f13070011407a0400707208130304c2d04203101c1015104ae82d50030281d082010440c000082c0c051055403581032402415140c62440307030305455000300b10244099108059040c0041c1e22070034086003801c42c04002800050600d1a11800303e2036640c00305e560090b50380b40030083c1402090f0b040c0483c901030406980c134150b40e410801c400140d417000358a00c03040740f20300c46428102d0030369404004040c5003615050116541d0540f05080c0101c0b56100300840301760107064100b20380d0074016440039100307510070410300c42002300a02c280645203604844c442e400a0074103400c5004a9030881c0a406c031502081c0c1100e01c5280c182e540d82c14541003d03100c8034180160742030508440d580a002d003d010380b007001003120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 853634622 1250 853633372 853633379
    0x50903030a06080f0c1c0b01330504050103050714070b010303121505150408060108010c180303050702090405010f0c1706030a0c06050f0f1b0706030528140c041509 72
    0x151a400300c201d440d4801d804503c1020b070306c001c81e0b9441c1c00c9100d07004200c0010350342c0c2d2550b007403101c007116007141c00c1003519440790307a0720444e9408a01d02c1c03170011070707503445040504020054008000103040790040c01241003880304028032103001410994401c004030340b1554914503001e080300d9000c854920308241440094041e510540c00540110394080f9107a004079682c44c501103200340708540002d00ba5001c0d9400104002e0415000040000c2440d5240303504d8642c03003000d808031b0340310300d01008001820400c84035002d45400c0b5031254000f40118000a885620080703882d00320340c03002c1e40307680100e10b046a40301100d007414441c50394002001d80207883d00f12520b90b01c0703003150001c03805030500b8020082107640303010340700d81c094415030040e48040c0c9030b480d4480c1e40a01900c02070020003140610ad24100070a100d032081c000c090050780c15450002074200d80c2a8203203000c005848058464560b1004100352041913401c0381d600030801c00120350781c0c0d5414100b5050315102d06d42182c5003840103141042 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 853635872 1250 853634622 853634653
    0x9050603010522020d06080f0606042d0f020d0b04050903030907030b040804030b011202041d100207061407030504140c0d021011070608010635060112050903030a0608 73
    0x122840c43c924009981c24075a20000200280101405441180d2900d407000c42c0400001610300c0c06900034200f11841039441e8010407040d03508484090342d00c000e60060b10481a01081d0003082080640ea4011429401c48002c1100b00d81102d40c60b4005151504920040c0d82420302c00c035500441d40c08061455403801003003e40e51038440b4800201550071000014040c000c8070400d0301c004d0f41d0301882000d440e581d115040311800c0048131060f88203600d030038407402c061301c0c080480320354038a41d000c054a44518180d091034000d40148a065507115281c50100c40d00050380c00210b032081c0040e460005613400d007800c160020030740b100042c00b4140c1c000c44042c42d440d51015a079561032541200d40d44101085001d08030b420711074840d4882664031800202082a6030801080f174142c0d540b0b590340c0c0449260241807140444482180764003030340c0c00e24a02503800004201f05540c1b0000c1814060801040e21100d08121181110f40081c560004024000c0c0c102440c003c0000511080000300f00c500c00300040c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 853637122 1250 853635872 853635889
    0x503011514071119080709052a0d090c090f230f130204021902010b0a0b070b0711030301081b040203010b0d15170708010c050c060f09031303050d090506030105 70
    0x151000041603010400b41d60f41011004890380c58002c140444c2da03030f580210f07960b80218007803c81074500b0080010b03104107a0b004040d205043d085a03d45001e01c8549541107036034130440c4040e15564032001c2c0d0002241d400e510030030007494480c0c000900d12481c40d1311001210801c3d0720100300350564011110241c060f03000c9968000c05002800c007103d850780e00503c006c066040300029009400411030301d402000c101044200080c09800030700002450000300404060507000305c03042c00c242448150081100081160780c04070b920b080210040803503841a600d0340d0000d81c8001d140da400000b4a01c4400d603008060810b00905540660031941400c01022007400f4802120300300c40d65441c0f200207241c409503030100080460080300520107490580d03081c0c0322001406416250740c20102002c50047c441c0044598484804001d071465488d14124100c0a18004d0f140d2001813106108100311511070000b4100190310410061101c3c6000000291160350940c0c000362085000344010002900e91014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 853638372 1250 853637122 853637137
    0xd180c050415061805130203040b010b0a0906050c0c090405030c0f010203070806011b06020f180603071e021c090306180203100b0402120c03092a010e06190503011514 73
    0x107200c40744c0d01000c103441d08908129417085d5488a200c2d503003011124100e5009600542c003406408500c0d0b83c030f941e259011841000d00b0708001a002c202d00304180c41c440c00c090140b440359803042c4c81200c80c0c1100080e41d00c800680c2c041d94141c0000400c0d01610108102c1070180f0001d18000707606514003403c024101c00c60050449040c040e01e8118804c1391100790131148005c0780e10260454650780b5911180140d60003620081d0544842c03005d04401c2890711209072803003513545036500440d4041d0584a03064841030702c0880c2c0103512490b818140440b441400c81540722a1603690703910301529606050060725690131010f484e040308180c4040141e01c02103511880d160b44c0040c00300d003024020000c10020320601200002c500f9030f42d400e1001d001d0344200114018040001240c0c141c601c0102a038070148042c80c007814804904568507502c550149010641070013006000c06e04041c003c4087e0510103152003400400a6400401400000c0301c41040b10803c2a191030040301d9420003d00000300d038481c150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 853639622 1250 853638372 853638377
    0x20a080703030207050601091512151805030a170105040e060a1d06090304030309050613030b060109080a0507240203030f0a091e020109060302090319030201020d180c05041506 77
    0x500d0350107060007a01142e141681c0b05040b07a6031581d454a21500902e000100501140417041c000075140030030300030854000d6003002c40c1000b01107502c1d510500030b0540450728810b82c48404002c002140301800503007e14440d40e12468103113001c5010010302044140c00440c401c5140000c580510400026299030000202d4400644100401c01d2040402d80311205034034140f04203c100080150080080c3c81100c0c8203481d0088020788445c100f111038010900c045000c0040080c0c2000407803501e0003807940011041c140181019200e8881605115200000346c0350391f400000100800c0c442c2d81500d0b17001010303112080105d5045070304001e440c0e01c00900a41801d680c07100c0481c0c21034419921120010b988114410800b07084038001c000d480c20b02d4102a0701040981600190090182c02100d1b04000020050004005444128000092101c0050382190760a1001085500d1684101000b2298141d401450b41d5030501d803082401c001500311602450800c003c684070410410030070300a4030400d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 853640872 1250 853639622 853639627
    0x204091d1c02070807140907080106080a020a09030204060e04211b050114040b16030b0f1003060e190f0b0901050d080c1605010e0f0a05040207030513062607020a08 72
    0x4400303e241100f590081c940a000705100005c140040002102806800351000181c40c0d84a44060f204800c0c2440340e400400e604034006092600c3e280c2c01001c1040c070900f40f9050558503134010404940d00f03500a54440102e6200740002d0045140340005403200d0781c00129804105600d000b03144108a44000000f603074a40f10110404c0303429041400c81da03c2440803a502031601d03003010040c00e04140d40d00c026901780344048440452080c001c4c620b40b040040e0800305a144540c05000c904c001d8414000e041555480020a4030801300800d103014011b18101c800d41c0d10040d138207040485214640e04410b0525007400b042440c1c0780c01880d541110012a0050042009810a481188903080400b041405a20600320810a007481d4a10550702c00703a0307507030510000e6401400b0204200d40034040c0d103c10407803001c01c5146000c0e00103000b168801e03c0c10509144400099030f52024146e00f000021400408c403c80b80d00140000303441c20701e50855042013841c2048240030b500c41103e014043d1845400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 853642122 1250 853640872 853640923
    0x180301020705061501081005030304030f033014040c050402031b070302150c03130803070c05120a080615030703050c16030306050f151b0a150204091d 66
    0xa6064810550304001030f0b0300c2d42d18181c105030140d04a8551071074007180030100858800260080c210701a00c50141c015450242152900000c4c5406e83c1c00031010800007440c01d140030b149a40c0d0015a0f40d030701d01e04410808004040600580d900d80c000c4003401480c050800c400700c1ca4411000080320025200180d8a485d11a0700508030300d440403008c1c080240000d03102c8100341e400220f844c9a044494661100b5845011281d4200d00c1300390782ca400c034035010001c0100030441d0b240080d60030040c142800726100016035a4541008104215401e900301c1c0031130307842c0e0115040a01d40768000401c0720302c0c00111032403803290703603042c000904a4004c240c0d4503000039402c0b07084082124400a80c41c4010b014100c0d0910b8004c025004900800d802a00d0b006442d40050410500c100b03906030100941c81c0c1407410720b101980154601c43e000301d14030b00c9410322810102d14408000b08003498004005a655802d061486082c3c4218200009094008400e101016400801d018441c819807944c2c04601d46070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 853643372 1250 853642122 853642129
    0x8031201120804231503070e010e040b0307080304180519090206070614040614071209080904091401060b040b0418090213020a02010e01060f0e0a23010302180c18 71
    0xa540107000c1841007081136a901c0601104d14185403030b0100c1c1c58642c28000c40080181c503000a840ba0404030f920a152035000d90301038040462014400b0708000390702c905e02c10000c1c0c500401540040307695040004c00380800c100c00e102005015510903c184013038185074402e626410758100e007416101340e85220780b03c210342e101401c6880d0f064016105201401d004000c0882c181b074241c0b4101c51207854a00c200304800911a00390344218030688450041161206445c1d02030040390400320b4510324204005400740d510b900c030300313a0264020045642d0103540c07030b00030600b12112900144000f003030a0208009900020741101c058842c40c40d901159070100884000241c0800c800095003c8100343c04100014104d5002d840003224613402030000000014200b800c030740c0d044c050a080903c1c1400c041c4584c41103c800d00340c2044094000095801c900d10b9001195039103071070304140c240c0000d0010015450100503a4000080c0080f13250f0701800d1008000c1c51034030a8000c24410b00d0001000c0809655 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 853644622 1250 853643372 853643377
    0xf0108040c050d1a16050f13090e0304060f1e030209130f020306030c04020304020d0209071209050c130203070e1207090f0b090f01030c330e0406080312011208 70
    0xc0680409001d070b5152070000658060104264044e680001c00200f402c140782c07000c03800f8000b458444524100140c100c0c860310341c0c0040d01c4400c010302510301c00030700c44004e880358845130b80740f0030042d40c0c50754204400181941ca882c11140c040110300401241e0711480070f500000420032a080040c3c1d140d2018000c06c03490761801e00c401400c9440e0840040001101e60000c501c603000403015a1451260760040100300e00044da00603421004010b0742c203005060091141d03401280c9403c0003010420314142e41c20545520207002c58071030f000602d000e00c050414861070442e141d1128010f601b1490540001840b80307000c66403040c4580b03d40d140544120310706018060103041005424040d4851003004100a8400440042d028021600001d030315900c80e111001e060b00d5121061001040c81c02200c411025408450140c070402045059903028031480220600c050140d21181580301107182008103c0d401070748070f0245504104407290312076001484d41810354400000f107075552001410581e071a030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 853645872 1250 853644622 853644629
    0x9043f120e190c080307030203041206090813211511040b18100c1a0a0b0901030b0718120311011d16060201110d0234020405090a020f0108040c 63
    0x340142406086604000c0e101c002c0050300a5465005140c2c0d2010490350303038842c010014005070014041407044035008500030a50078011100441c00740d00c2512008a503902c449080e00303d282004800b0043c1840f19450380c000c2100800241da40103100381c0710042442c078103600740e1031456a51101400c64500c41e41c1a03c000d40301d83c002803500c50003e081602d8204801c2400c0d00d02c034080410382d180c0030900c01e10b003080c4c07075a9202103085c80707040e201210110300c11806407031900025105c010403800c944800060300d000790f0240c4400c405070300304640040d1045007018044880c00106500034040c0d2034801841c0c1c14400e80c546005440030a00490b814010003041c0b8110081c0c10600541c1d10b0442c00019071044400c1c840c0c000382c103c031030b60b5a00c02c2e400c840e900740400d0300f07503803040c070a140c03100c4620f50160032400c170710615132500203a17201c003101444035445210101e017080b1411000190309040c443c2c19071096201000303010400c810340002e024160341001e83e07070401c0f4030f000004082100e0320540b10000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 853647122 1250 853645872 853645901
    0x619300902120d090303030b03030c030f0d0f0c26010b03220b0103230a110f130501182313030207120308060907050922090209043f12 59
    0x60300c0200000904d01c821303911060740000c0c1030207000402480c002c000c650758003410000a500c0c3c0b104a4810105540007044078030317211030740c0300a28400924503000f11901111a1360300e0340f0188035120036100e010301c009001c0020f02c0c040c0c00c0c014444000c01c40216034211a071041205807800c0e6a1200c040440740c0150002d2229502d0000001007042d94210181d0242c5146040015031040ca82881c0c4c2c1c40040060150100032219030036003060800c04030080f41a00c02410f0200c8140700c04040c00c050b0784c8207910500b4060400b880040c01c651482c8a90040d803000c0b4aa6210300c545580d0030590351520191944002c02020141e034010580201710740380003840c41012840c0c0c0f496017410043c0242e54110f41550065600b0b000146230b403481b030707421038210740c1000b803540f1301603807120122000c511721950901c1b40042d951048580940e99180c2320520442c8180c002ca400c0c02c0741c0d10f110b900440c091002c110040104e20100b00380520241c8092404c010007407421480112409030000007074080842034106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 853648372 1250 853647122 853647133
    0xf070f061e0c020f061c0b2b0f020a0518061903020d1b03140304031b120b041506090e01110301050307090509120f090102010c0905010906050711061930090212 70
    0x2924032501f040340c0003401101c1c0484504079000d2070030412482c514104400d050594040f00020b51031600102c80c00780007801c2c160110f07889102055042d00e01140c0d41600f0a02c2c1782c20040301e03103854042c501100364a18044201645940d0208030007070783c3c41c680100081c42e2007175403000103070810b00000003e68000c2c680b00400c4100907030090b00ca0340303d808156007140e1074005803488260003820400890706168114419440551034000d50f0410203081140d14801c640c41d070f455940000d004d000042c01010000203081d8520301c0f0801e00711031401d4031648a000050004006503500422000e0807501a904041081d64030400c5050502015005101c140e50010400c1c960b00b80d1418080c0c41804000c1e0003c01400d0181d090989208901e0700c103c50010321003040c280075540c880d001034071f4601c0c4500e1240070f40360100000103145821802d4080301241d040251440e20030740c09510710003085164080c0120b0517140420480c006c0002485011185485400c0e150031034559082c0403401840090507102e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 853649622 1250 853648372 853648417
    0xc0e06310609080c06040e04061805030a1107090504030e0907051e0703030b03061012050f061807170d201b180f16020f070f061e0c020f06 61
    0x808014041c0203103c11480342500206042c1003080484054421114078200240c1d51039440001074601c104101d60f07100041c3c3c0500d0001501040078110f991099120b040d403c018502a403844d0180e158000317106107003081b081c4000301e81c22020031180280143c03041d072282e945000c8161014890000203500300071b034807038618014042c040041d1004610036034003486a103002e1010540e41341410317070701d07e90304440415080200c1c00340c1116030301c0c00c14821030994007944a012225810b14030304880c0c44d02030001c010300d076150f404000e001200c0500f540800702d000c10840d159107290b46402900380c01c400c1c05002c0d010a1404541e00c0e520501c00c90080c42200d01720304400129547da842c050611724010f400054003c5d03130a03180015041d102e101e480340060b0040c0e0307420002040050490480c08290300515040d80358001e014402113000e850ba4004545a0364640314000f084d240900c4500540916102c445140d1281c1c000e0300c0101d026012203e00d00d0005c5103d001842a1140381c5161030702100103200607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 853650872 1250 853649622 853649627
    0x29010308031803090306161b060203011406070b0601050310081c0306080d050f0d0b28090605010f0c08040503030a0306030c0801111902010b0607050a060c0e063106 72
    0x1e52250b0005030000b03038501d00c82d42c886a82e0380a413268040c0d041d0410f8001860858000f440a55540000e00e0810410b100b11841d40400b03064126003130f1a40f680000050003080c0141384410b241c1c84054440c2c5241550300d48850340b080f200a081c0604108001012805050402902c24040c200704015507000120841c0d50040f07813452100510f000c40d050001c0025404000300c2e10420303900b40c645030b4034a8a404115054030701d03802100004d12071643c809042c1c900d40c40c1c0004100c000120400e08940381c8980641c104c01c8034540d50b1240030041d0402c0c106204c4d60342c4c000c440102e040d01c0e600b80002c0703d5590f45001080d9005030342103543c25100c0850074845a6906030401d0f01120300a942558000d900e60400500b80c03412081044c01103441004881e2450902c00301c04c03604041c03144000120f8521389400240313a41c0c03003075070144c9160740116610414021144546082c4061904000280c0c0f650400030448500906031640e020001d221403840d030351105581502c07681c00c036103002456200e0b181c0401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 853652122 1250 853650872 853650877
    0xa020609120307051b031e07030e10090b07020307171e0106081f060819051005010503100c020c09010b040f120203071a0909040b01051e090429010308 66
    0x2a14200c0c4a900d0014106030030001c101c0340116110350b10f8510b002901241c25180900c009060740c04d40c40104038400034201b444450304010f00c19148800d0b0740718500e0500404017800d440680e40304414540c4d883c41d0460308004518112840384040c55150040350000030705068140e4070440b4400803944480104200229554260391000800d0103141521120082d00320b0700a03004441d026800300c89850840000f1400c107040c45d1113031040200c1c0c419207802c4150704202d1031404011507405ea8400d240100441440944103802012104000ea903141c080020398803081c006014030751954496020100703a200b408501091038010380007401b1961f5420f030703500c01e0303520501c2041031a034a203c2c404a00c0348030f0b6410350380e60f103500240104441e83c00e1841046032a140c040c1585203926042100c0c084030b880b07056a061159024440e403409a40c50141070141d91500c640005030f01d020036844100b0f150303403001d004542154000300c4085104c00c0004484040800b120090b2011801b210700000801142c01c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 853653372 1250 853652122 853652131
    0x5042102011d150601210204060c060c02031e0c0102040b180906090712020a030204090f0c1101060f0308071e050a0c05010e03100e031e090414010b040308030910020a0206 75
    0x541004052250050394583c000c04921002608006000c180b0561261029111025035895221101c050781c00207281203a00c1070b40420003060840c4141c4007132100900c40e41e00042450300255180c8258030711840c1d4040d4035010ba4409074040444c0c484900700c0300b5415280548034990070642c1c0e401c0c40c01542070702da40b0001c16440c45001303108009102e03400c000d40128021102a101ca0f80c03500884402c00300650403080c40542090340c03d21002840d9801c0340111880c07540c01500c0064045120b03c4010644074200a0f040b100340c0c1001d8007081646420360f9281c00300d07500311f000292519a549854070070340310064038030803103001101101001e00c400031841c08051482aa48282e0060341c1e207005450203202c40140c1c2e54035400001601d80c41c60115005400058040025203241c00090f45807000340034080b0100d2101640042604202424640b040c54856003c0c120300340c5040d0701d0201400914480d60000a041200120110341c10180030850301c50010304c2540103540390700302400000d5403a01c00301d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 853654622 1250 853653372 853653401
    0x1050a0f090201170402041b0804030f020105060f060f07050312160e06090622180b040203040807030c17030103060c0305160e1e0307091509021204060504210201 71
    0x950030650300d04038850820315950603100e0746240d01050003a025030b6078000f0001d83c0c1054490100711080078118124145150b020313114074070641480e0400900c40c03000b01094400350b80c0342c10b042c0705c0165034071039170700d10000c00c115403140d07079080c1d0795017032100c40e004500c03004020f4400444c0c032242000c0c07449942e1f403003900b20100a540c039102c590f80032a28a044072120b04c2d000706081048101608091005111400c0000100610340d001600b1403c40691a0b510494201f41507150346003c2103428040e902c00028112019415405d0603107610402d4810028001c081c0308030b900140e41040f04115046c4a210748241485032290380d6420a07202400c444500000028640740014441c010460918a01c40a840d40c1e6103a2024241040c865003810752102d488201900a80102060b94204184805841003210200b641226925030309490312040c2c00245d65680180070201081115a0078107030310517000389001c120b903204d41c1416501d841c40c842550500064070040810901d030150040c000b00035100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 853655872 1250 853654622 853654631
    0x51e211e0705063919020904020616050a080d1d0601051012050c0406080a0c090b030603030904020c0a0506090a050307030327030e0913050c090a110d0b19210507090e01050a 76
    0x4400c0700030032170201c4000b540004903401250241c10600090003d100d9464024900a00c0940342c1520f042c1031130b0f104480303a020000e9008114007941c00fa400807804101400d080440c1550000c3c3c0d200d0300c0500409005050740707940c45040034030441402c40c24540c030740f008102c1814500380340c140d954460301586001c07400000110748000520300c00c141c03075081d0903610200301c0f0b820100c003030036254006090b00e541403206020354400703960781c0d01c028402c3c02884801800d00d4a9545082814000001c1c41144160425910080030443c040100d60300d20350300d07150000c1c0d81030551039031000001c10030601c0020810035920640030183c100e100d0110744882224919070b00c1d981d2000804502c80c08080042442c0c001010100c01410a540b40c250001100301021601e00384c0c00c12840101e40025103124040c0340c5030420368416040c0803424041a80301c00c0d40780c019090074584e40441c0501001c00080f15100e0320340c81207003804000e00c1107030081c1c4a24401481400469070f20349001e054107840d503806035841c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 853657122 1250 853655872 853655893
    0x6090d0b100321050a0f020c18010f0503060c070b06030703121116060f0e06042112020307030813022e27051e211e07050639 55
    0x350f003001440f031081d40c0c5551500d170594030103c0e03813020800029400d5100e0301d0b0a04405a49811070248184103111140751070350324121046010002c10391219010740c1210090055855003a01115030050b000b00c81c440340da0719900c01003440c03c5500c2e48003504581704190100000c030307880311401028941d854112040362945880720085112140b0403107000c144d106601030382560058415802001009000600b0700b41d072600c0f1010850076103506a2004010241d620b001c000d104281851600124802107052800030b9501414800c8058a00f20425069000705801c650340c845500014024800d060300070412448a00030401410280034000302d4035004000d50a808513007050340c0c6c0740d062071040903121450203003130054003151854040c1c8080141c004a85180d00e40310b1b07900e0740b80b0888581501a000080003800d0030240c0d012200b100450720051003004050b80000c400041d01c1d0101c5403c2c1d542d41848200b00180407000818480047c400795210703043e001886151300300b525820058038204500d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 853658372 1250 853657122 853657163
    0xb060f0a060e130b0604080705011b1e140d0e18060a03170d020a3f020d02131e0b0304080d0209150d09030e0a0302090606090d0b1003 59
    0x316030155400103400e00002803400e00c0c04658603030307a06001400016000f01c8140c0480d42580c8117030400040307588611401c01c07943d41c0c05900d040342c0d144001c104098440f00703030390780f085440138401c820070450100030500c2c000c0c45410803c16100d40a05001c41c2c1c150203160320003900c002c2d0200d1000c0d104044800c56040324025402c0405c2c405c9800403c200c01890842d0380c0d4810034902c1514624a904007800039100680c11480245000740158a4140c202d50804801e41c41c60000d24042100c12403640a0340c200382003603481c00d00702c900803c45d00036071a204840c030303030030003e0080c0349800c8491a0062030005d04001060000c42d800d40340e04100e10503840d201c60700c00740984410b50b4001c00a01c420800c0351a8241154003415202c4001010003441002d195913200d9176420080c010310034260f8480100d402c05030001c1604040c0101641e40e450300d603156800281c40142c005003014020400011299034030b944803414880519886825003003981445986200d030f0b144a40000c5035020a0704c40027940b01e44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 853659622 1250 853658372 853658389
    0x10050307030f06020c190305030103050c0604061e050d140a111312020a1d07020c031209130902060a080103031107050a0b160501051305070f0311090903160b060f 71
    0xa420581d100e0b99004140d456030300943c04400c50b540c55000b4080390045165245042d410307510302a0707031501d880307504604010b0700309030074542640d101c1e0000b0807081042e15003004040d99444a060304890201204070000d171075074841d50f40c030b8050080c540410000056181002540102000c034000c012039011414810742902c10a80700941035000220100702c80700d400c3c3c690020452016100084440d99a1001d13010301d1b02713100200080d01d90003402c21400542c100080c0484207011802020f421009896803034943c410880c47d1070099079080303640050424150040106185d01902042c2e54091055004188180071b000840c0010400031601e010303048009240c1040d82c0c00200400700c0d40d85041c1070001c040c5c1c028494800c0440081c0b49004c04280c0a20030b0304e100f25203001c424140700241385812814081035400103000b00c0641071090000c07034902926801840001d8540c1c4103140c46030001c0900c0d501401701c82d0b00b2040c10b488010030402c64201a4a0301802060301c10b02900c2944500300007011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 853660872 1250 853659622 853659629
    0x1021c05060925021f0509010509060103020918031b01061e030830041110050c1e19030c02010806041a040f0e070b030106180602190809061210050307 66
    0xc5545a02c1d80c601c600d0500030380105848180105d9035440d44000e906000319085102144880d076a40c02005044034003801043c1c0e110b142c4c90003030700c401e40c1547e000540c80c0c00054485018140c498881004061007003048441d003d0321400b01c08035a45203139810a01802942c00380d0f10003c05030404210458003400b1a050690b54422820b071309050b05413911441c0800303504103100d05d00140fa84807000c9041803480b8980154000e0b03420000d958094024001e40e51005035502041040c104070401d46e00501041c06140c90900452540861649031030041c03500940104811600b86204c0007041019009140c040c0c15030b100380c855a01580e6404200801c0b42e950000c4100209090450076030701e46090f600c91820341d035422600040252500031000e1038141c05c2e4225243e201030000c010300000f5000900d8945140c0c0786001001c1c084d08154009440f20a010b2548901c03540f03140c2480100120785055403a8010090728040d156a0204030007014a501070302e50042c802d0304010045001d050218044058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 853662122 1250 853660872 853660891
    0x7050d0305090f0d0b040f020405060114121b0408060f01170604030f091701020913060503120306041b0309031106070e090408070c060804050601060215190e01021c050609 75
    0x500305000305000f00c8003a09082c0c5a40304828415071400260319914180c0207500481c5680f851120901c1400206c80e4041c05107810f015141241d88107901101e012501d0110456810b10015102c0303401c0517181d10b00028642c4070181000c6404100048005001807003414072082145a03640d884400103405c00307440d03202c03103101d03000030001401080c0540602c8002e42520300e0416140342d80c1e901030030700c0310b1080302d00721085940000303e03240145482c0c444c84600144886d8100901d610b0800002e984040000e40190703011000301c0014007554680d44a8000b4400c0001c51545501c18094000d00034449094200c020800303100b40010158070008480c4d109280355100c00310b400340d101040109a00009008950311b120801400300001c0140c02d42030002c082e81c5d150310314542464900981042d005810007002c5510081c1100701c07515101181580150501141c20f80105401c00418081c005140c521006503000183d9604862825216002c2d40c4080e0b210401464642d0b00400c4007400043d1101c090 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 853663372 1250 853662122 853662127
    0x709050105070c1403070f060507030917060610050f0a200a0309120c03020301020a05040f15050f07020111010608070812040b0406030b0a0f03060504060605030c181317030907050d0305 81
    0xa000d09071404d44441040040440d9100e80d80e0b00342c20200e01c4480c1d008400050341c0030980d45c007019006001c04015040403288074410303119007080036030b0720007006060b00e106207050f0751140e24290003031044500f489502003005903156240354014020a00c1d03c1c141200840d03960041d1003110801041d141c900c1c60b0f2603910064524544103040d1b0140000b108107172402160300b24000f0050340c09100402e5003c0b4262502901c0c0d51400c0d148c80076260302a48850280c8a10b03206d80141c541d400011074044039450098291a09400c0c00101c44811500e50dc0c85625031a088002c901203900040d49021903901c002100c524501c1180c94581c075000302e20819154032400e000c207008490107070b00400441000a040d41c01034641d264500c0c201d043c0c2e5903005540445c0e544061200b442680c3c0207000160000350010451684d07480c02240f086400b4400c1013040d8030031203011076810040203001e096640e0300150620484007020124000c540d07c20381e0070911511640a0000c5c0c10308083e903442c01c0385a05602c8050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 853664622 1250 853663372 853663379
    0x2003060423060108010c080601050a050913061710112503140328090807061d01060810060509060310020a140a1d040209240415080709050105070c 64
    0x148840032901d481c5100342040c4400301039120003040401c0c02403090740004140b20021090240c9840c001800c241c0c10008208891640203400c1411604070250640d8400007001c4641900d40c0100706a411050510000c039a00800244000681c8940410b0243c1c04008036102400030b40300300e01c180c410800d0700c050741004007407400c04a4031001c1c1da518001d052146512510b07460710700d081d5104403120681101401402544900c03011a611000d451964040100d5021912072000718004c0b100000d040548890400c1d41104040b030144148007841c1d0021b11016889a20881c2c035004803000c1c104000745030030f800040c0707850315100c400c0c003547d8042d010f03041280c0c0740c010801c0654411543da2003409084046030b01c07207000310f500400c001150f03a0b07203103840002000c0c24142c440481200322449036006000b83d0284e942c0302c09000c054208003980110070b03040741c4a40300c0181c0c0500d900c440110400d4501400c06c0540240419200e200182e540220140d203c43c0103403801d01600c00c000c0e180b900d00c00c2061 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 853665872 1250 853664622 853664633
    0x9050a05032112091c30060e01080a15051e0c0903060f010602010f0506011d130207060914032106010e030a03021b0114090114040e100320030604 64
    0x1045800340c00902c0d24509101d2901d20480701d00300381e038071082c1076100d01c00480f108030f101c0340c0b030f4038440c69545403000a603c1440c405101e1060201030000309206e01001071000b002c00d40d40400010413800f000c0440c84d40c3c1d60600b003611070750004420380341c01c494034451580c40c0c0c8403446118815840c2d94620182e06c480c80c00c0c0e103c807690307006080d8000d1010030058191150740400c040d03440b90100e0f03850307680f1642c14054020700350340200c0c4841074141d040505101803070780c10401e0030300d000e240e809a94400c0c0270004e00180b41c25043c0d0140314940361000851505100d101d8209255840c018a40483d10385c65501c00c041d524850601e0412580c10725048118901140f01c402c0c2d40c101c00c0514040d0f80405800000a040144c1c6940c00c90240c0d0081700c032080d29503800c2074070681c2003800b402d20060100c042c100e0140c00d80301d40010703281002410301081c44100090001d450151074805184050fa11b4001288042c11495020907109a2010f20386d1500151201c0401104184060060700107621142d42d403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 853667122 1250 853665872 853665913
    0xb0f09010303031e021c0e060412080606040f08010b0a06021501090f0e0316110f0a0504020c0313060f02070905011d060a0518011409010b0f0c010615030c09050a0503 73
    0x1050141e080524840c111141a002070b04414446c0101c1c082d00c4400440c00c10101c8400c059107195580200d820000440c400400c0342c406207485061604071030740d4000005e4032030302c1142c0252054202e940d0380440c40c0c210541c80144200d0060358920f0070985c4440041e81d54045c24480d8101a618140050011030103540299032405690320300400d83c94103080f18103055400c410850300c04034809081d0320b0240003040c800ca019480c01038401c102c04103400c4021482d00c420074000e96015540000700445009010021160000c0c107001c107c08980c0e07142d0b50010030000c1c1040907034005100c0c50034041409070a80c0700b52412a40d000740c1100a400210034030b80d5004070001d2160b940210f00441c001a940c88030035804000903501107220341190304100d155946900060103c0303014000810042c0055840702040301c496020000300e898650040d0803840d0701400c1241c01c043c1a60b10030101840605c0c0d05900304940509045d2a8454a1038482003480340c800c50034403442d945540300120441529407140807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 853668372 1250 853667122 853667141
    0x907060809120d090f240b0607020f030f0109050706030c090b04150309050111120a0204032a030503360a060c1104110a08070516060c0c0c06120b0f0901030303 70
    0x1020642900305e0300c40881800d525802911590404529810356a80b081011a19a0441d10302002003904640100d0914020b04400a0103070f17188040d100c4060360100302c60180102c484c0020300401c0d4a91510340c3d07c2c4c2c40948030f02e1002c00d00300488894828003c200d21000c1d5820100043e007860700e0041e800d035421010184810615654003601c0003c039200f030003801103110650700031a503a800080c10920fa8010024001168144144001d1002680d44603815800c4400c2c00d400041c0c424408100c40942002940000d1003031000080100c3c0794407a1030640e844040001d41c040903065484a081061000e81528041c0d00c90340481042c000b184c060602c50803418064420744041882c09000b003000c4490140302020300c89000300b0180009030340302686541c088804c2c5003080c1828001100d004060805902c01041c10f601e8150307421200744680403412601d41c0241c80f400103559134500c0545004480c4000903101400e0444a1030340341495009203000c240058810303481c40c0e01e55101240202074540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 853669622 1250 853668372 853668397
    0x30207032a0c0b03090712050706030b1201020a022a010e01050c0c0d0609020301180b0f130515061005070c0e06010905061c05240405060f0607030206090706080912 72
    0x400000b1648000b10074010304151400c071503590405c0d0110b03034903024540c0d0114410400680d031010009201240090480d5410705000c20521020350001c5e6840c0051580b00c4030940c80400c50800c50303a4001010025a4200a44620310440b28901409800011501c45000c150300e01007601c26540301c2e000601c842c14408056407641e80c8600000717190802d18180944815489201c0030081d45002c1c41040004181050120303498512692a10703040c000c01000040401003003000640403202c001e8040100d2544481030701c40459501071a12540c44050791001e025a0b8050801d0300458052400c44070170542203074406500ca0b261010708040c00b50000c100e541085400c040c0007866888240c068042c0380802ea041c200f1324040d030840c0d00c08031f44000348408405150660070324000914004c5100b0156800d236000b00341640d0344070104141d4861030309081d80048001400070f0500d9070106120b40518038200c10348201503510801113480c50320581d024000394002158000f01124a01d000702800343c2d840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 853670872 1250 853669622 853669697
    0xa030c020103150e04020901080d0206150d020603041a060103020c03121f0308070b13021c020d0212010911041b180b041401020c040c23090d08120703020703 69
    0x50003c4403800c40c05078000034208101100b40011460156000c03405403800c84004d0084990440c0700030b43d40e0902915015400c901d859401c0b03580e03110426119052500070f0842c1c0d5407400c0500c0d00e170002c22209510100202c5036000890720350761080c002ca540d00d882d140d0055040c49180400800e564801070b00310b01c00400d508485001414008200030021070040d030360b1a40b01d00c41401d040303180d240d00034000c0d00a03400302d0f0b00d150016943e010230480ba5104111400341001c07000d202046d10ba06062002039441004d01104100307074407054201c000c5462143d11490820200703070050109580e01700921030341412203180c00c00202c034480e0000395800e42d425503036040300740c2c0d40341500c81540d0300c00c2d0442d0342c110042502c140713001d580400051803001001c0c3c504002806140710024019261109600644030340501e0f001e43e601080d80649005070801001050449180c0c0303000c05190b0712258212508421401c001400c8600910a840344940c05465010f00442000c0c010304103012243c1c40300300c510301c02c5c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 853672122 1250 853670872 853670891
    0x106081f0b030d03050702070603050408040b03270c030c0616060203040c170102030f010e0f07050a09050a0906030b1e04060b1507060605030f0f1b03030903060c07150c020a030c020103 81
    0x100310f24044011551000203a9040021000f81094840c3d0420411705007040705000000b0002d0b4216400c540d625151070351a900c80c1c00c0102050002240000c040050b0006038441464000c01c9840e00382104030100c540d0040000240314190082200c03003a5040000d803503100c040b49807030300216030091148500c140c9460702d1f040a80ba0845014268004503907011040040c1010042041809011205420b5100e40340c110bc440410400090480c001c000020900d084402d00411109010340401042814051f031141003c00060089110a58903104c0f840003041e008442180300c000c0029054001071800c0d41e4584031600903010881e230141e04040d103c3e003071a02d05140d2201801245210b18000310301d5a103040100362501341440c0c0d0720010383d0080740d0003032079525000803009a40501c401481d070710528041c0000e401c5009204000e50140111000c000740b00c4032410080030510300c5518458440b04100c220601281d8051940c400568008a00720340868041c003050742480cad20514000c03940e10070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 853673372 1250 853672122 853672129
    0x203070b01060336030e210109060f060b0403030e0303130305031809190b0d0813080d0e1507022e02010e030a020a0b19060e090f0106081f0b 62
    0x30036801000025503035080d5007054940d4000350303c5480c403041499080004024224401d2419114000702072103000416081c10342c9682440d10070b60306412102d1070400f402034003064040c05201004890440c50f10b101554401401e1040710240c1b00d0b00b4862500f05401c581d4166080d40e00c81e10200d51621046c0407003011442207101040285201c0c501658403400d105502c6000d203200e072000e8a218150160401c01c6851242c983c1c0004601162000700d0440c6c004004221100115131010303140140c00034409542c01c0c0c051150a04031401801144c40c07210f0302e4582243d0780d00810380b0740d035840900c0300f00c0007261500da04090420140000e00d0b407030703c9034404801d10044684070390913007000b50407445201160503020b100e0103000181e40c00c080d5140400b808402501d0341e40700c6100500208059000c1404c41aa204604411055103602000f40b00c2e00c407003404c0e9400d80111303100825442480c2e800c04911006000740822a040b02c03008082203850300b000700c18a0503a00d90101170701c1c1c1d95007041b02060707078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 853674622 1250 853673372 853673393
    0x1051b01020d0b04150605031311130507090e160530060120070924030317130b0a050601050c1002030106170705070605040807050f1518070510020307 66
    0x751011800524580f041d001d04c81a01d0311190041d03200c038120b190030041c003504041101c1d030104880001e120803a1aa140030820b40c03150003110741c0c02c88140c2e03030703040c40240302a4882d6000d8075158545185460750b401040300950030480e803019500050b10850a03d060240000d865018652464a15a280c42e001d038264042680c10f50401d107510100e09208140d6007011b20007a0044d40000404480e02081000a960390828400c030b64100d80c0e1460070755081071068482050724070300e0016950f100d0303660381001043d0880c540000300c403000f14113001ca50703070041da1906644c00380d134010300741d0015680e0345440e0002440f00400d60f6060010401030740041100c24480303800d2600b0300000061300c0f035041480060101c0984031041045001078030074002203641081c00d503041c2503800701303000c102036540d40b074070110328098184020654032602c503581d001020085418030b9682840c0240302081c1d0380d0480400c0841042c82c02203d196003020200f480141071903172042c81c41e020503004507880c2040035a1a103242d403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 853675872 1250 853674622 853674637
    0x14130806090d09150207050904060917041a0304020108070809190c0801060f0803161502070b040b090309010c14160f03031101020f18040915090b0a1401030201051b0102 74
    0x7900042c4141c4100d941001050028000d0b000c44c0f9400007012800195440c00f103401524803e44649000804020003500000301107940461280e01c03250703619104100c240c0060042800600344d28a541c0201d11810f0250391042d82c050791110041d4903500401e440540e40074008015a001d80810100960500000091624401d40c00a403916180c41e0009003158001d802000c2702e0309003403104006c0304200109840c2c1c51080409490300020744c40c50312040e1074155030704c244195400403035400c0510440442042c13046010702c0c02d01002daa503201c0415140e100b03c400031400301e04041941004194200d401800340c0c41600700b1a41c00a446001c0e103048105160301104140d03e41c042c0500805512446298110038090700035800c1c00c040c03380010b00e6025407d882c680c0c0826600b00c240241c0d0b038035008803e9103908279030040c080186049228010304440c1c6800c0e9100c5000502080c060302861103603845510030440200100c1c0d003964011121a03010300e4001c40500b401c020301ca14141028070042401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 853677122 1250 853675872 853675891
    0x105270603071e060e030f030703180f12060b090108100f09080d0605120307050c040209130c260f0f06120601181b090b0a020a05061008120a14130806 66
    0xf11460301c000140000c201455440c040d4000c0000c1c4203c2100c000b090b103003041c0e41414020b1054041c0c0c24100c2c40d116140c0d2043c03031082c411101c00a413002400c0280d40c4214003484003403050210300400c0c41a03494003031244222690000350300c9245541d866201080720015140c01090400c0b150301c48001603004218001c00c22550351508000302e1174811080c00c0c4005098029508181d0592100790301e4000703100a040c007850700040c1c2e0382e441e80c0e100070342c1d030744068805101080034020460009040c001c0040d251051110311710310081381c41500059040c0304410f841c4980c2a582e461002c0c44211715405064036803c4005184601c51040d0244041c0c0e001c0c01d2200754941d62194400d41d400103032001b09030712403058418200e800200c02d5201c0c0d002816110034800d00c540c0d5490072034040f89400c14004d000380950140b01d051084050070801c0d03000072218008101c40c09a106203800c00c040b44074034584400400c0f44007282d8040801204007909904000d07400054100d503440f0300050601d0310407159400c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 853678372 1250 853677122 853677179
    0xf0302041d090606090421090306150e1b0f091906120b040b031903050d020f07110a05012c06030f0604141005210d05040608010527060307 61
    0x40800b0200100c41c0d102500b02d900b201281416107503032119950004101c3d02084d100071180d201140900b065034010365020302c04100e100b0885a0002080da250f014031420581d000f00811502c03002d42401060312210891090319084048036054003aa0084082c65080091413580c2e1403140300c1c48941400824017134940c011030b040b604c0d42c064201d450452074140300e603140402c54403054500145003094580c000311421007031481c4e418240d0310380c02079580b10f040250000911540601c625005400c6681c496803240c1c280c50818400c002d074104083c099940095581e128560700c80c00c1c11102d51a1504100e592a007050f9580004604a0380c011194001e1901400302400424200ba2050300d000c10059140f590b202e082420340c030079000303089100d0144240b00c056689024075402c51410300c100c180c084111a0030882c8070102400303d8006102d0140411202c00001a0604248452151940c81c8640002c6c010b07983e0078080b5580c81000d40007a03018460100040303039150310007183c0210351804955020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 853679622 1250 853678372 853678381
    0x18020f0318060c43051c05040e01030807111c02010206100617070507060207061d0f030d0c1803031107080c06160f060504061e020c0a0305210a090c05030c030d0f0302041d 75
    0xa0300030700046d4840301008410002040090340608405041d41d81c03140030217581e1849400c00c2d5542c1d08585400c2e503840356416207148100a44d5072280840745200381c0a0b903100707940b007000c0304c2800002d034419800480c1d0070302c40c041204403030000d52a500c100507003005820b000241c0c483d03104980015404403545a40c41d070640b0b22a07400b10f01101024041e00d0010b2000550034043e03a0340740c2c041c03280f01c142c0c02600d409400ea80580900c5409882429856024007419500d0900501145c642d164208950051308004580c8100c081107a07140f80c44007501c0c03107103050b208441040c403541d2803940c01da901fa1007044841c0c0004205002c1c0900490040390041401d045001206004440a981c3c25409510403c402188c4010100c1d034104500d40500b04203450300c801c045250000c001c50032441c80c9480d034000030058240c5c0c041d0b20040005004001041a1580301e400b415a40c140e000c0806a0641c0300c2e17848c10800f01d104182d146003c6215141c0981481e80d152102401500001e00e0320303180400100810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 853680872 1250 853679622 853679653
    0xc08061b0703090608061c050c041103011d0c07060f1a060c10200304030216150203031603110f0403110405070918020f0318060c4305 59
    0xa25242115911074a4614542d81c00f4196405521803402407010749400501c43d5070b6905140520344181c855011050760540ca4072603180c20074940024443c600d07003000781d0290554202601d0507154010703001d285005030302285002c281c3d801081001e00c0c490400c440c000141080c041c50204a901d03940102d2100d0303114110b02d809201042800d40526000c0c08048007054000583c01249540c904d00001e8007018012007400e41c08444c0360701c40040800200340420583d0000b0803c09049a09000580d615120340e4400501e8886001a50041e40288040f820080003445030305128181c508000034014018040c2c1a00794114400401c20200003040c1003041c4505498140750070803085901300654500840f001d010850300380030720405414800030194070b4206c280e04854004c03814462850322840c1000c0f2807a600c400e05203010300580107600214401310303010303029200180700c10320904644211481c0340c07426402d800d4810708d401e43d03640b1280510780c900ca2404992140e0003140a00b10480d11404903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 853682122 1250 853680872 853680901
    0x1202011e05070f0e04020c03030915060a03080a21110403061b050319020405180114031f0b150d0203090d02060103030c0201030c03020904060e01050102070e042d0c0806 74
    0x10340e5490303003840c0401280541c04410030000c1c0015007050500c9001c410301040080c000e010548003984000000c4c1302c0c0d00c40c40042c0d1040c0400850f2080e00c040d0750b5086c10f01000281c01e10005104000510014000d40c0c0124803640c1103501012001c18030802c402095400c0d2074882980c11154070001a041c401d000050095417521036042d5143c2c2c0b030303010458400604600c0002c2000041e800d1144030440001c01c0740e01190010302009105410605c10740754180390700c4200788150a070240c1500b0242545050100c1c450320b0f2201034898122409001600040160041108030703940f00d1403a07035501c1c10325034600300a049210314001c001a100c2ca001085945000d00040c20a019540400d004000180d840540394042d09d1342840c020030342103007941040d00139014070240303103030300a080c84400b080003165100300d036040740c1b002da08a40546684120050a4020540b4043e25071100312a119445440328440c61100155004c5000c540c00c5031074807400d40945040e0849130079904002c0078400d0b0321041d14403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 853683372 1250 853682122 853682171
    0x6011818110310060f12032003091201050411010e03120403110a0509040f0611090d210c1e051e030d060f06020d0305070e0a09020702090a11030c16120201 68
    0x400c14142005d000b070320128403500c9800009440b85420700109841624650a2950b44c42070505a48845040d015125002401c2d021b010700c2c29403d050110003814007a060103940c105d4034980e201c280e0311004603043d10f2521031103170b050300c680e5600080507504080100019800785014a20101803402000900c82d401e0b80800d1103681900207100101d0034041c40a031320203600060028251048114418003402035020459100072804d0f860001c1c010901d07039004151800302e90f01840601d0124080c0c80300c000d56640a0300c030068000245c54840060006014454091000c0f9002c101d88211904450400072240c00309503000032602a129202ca07000d1000a08204896180a207040c20390007591071001a604004058980000c81e400b50300528085440010180a560403103442d04540c2000c1e501a80f4101e028040c03100005200b80030510820f19007107030041340107103180c031065031075817680c3c120802074140716426011000015801c0c036640840a4120340010a134111803210190643e00c4911 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 853684622 1250 853683372 853683403
    0x19030e0f0d0909181205090d021f032702010c080906070309031202061509180f03070b0c0405010c031214150405160806040c020703060f050115030608060118181103 72
    0xb513850020311100350019101e03c030b034504240c54200100002d03085694414010b9006070650703804c540500f213202e0807450014896281409280c0d480160003c0041c40302c1c0080d0414200110000d00641c4142c1c0401c120f10b009007007080c108a4030a000425650040e0011800328001401c20070801120804c42001030201d400580901d14150701c1c104508a0480c411038410003620000420000d036280314009010480e000b101c43c41d54049041580d00d0344102000e5030130b400c21000141a600030441254140c85042c0d40d00c11444070113a50650b040c8001404006966417144000c1400b031805601961050b1840d618003522049041d040c4000c0720005003854500c1c4140c1c0d0f540e400a56005090960404410b0b80c000071145c80901c422802c142e000e03040100510f00b403961010100e041c603003140c8c0c10f80c4e18202d20610064031014040c1d00b180c840c1d01c518083c0d40c0101004202d00307002111114400c81411310082655107501c14050007851015400701c2c0c541c3d070200300c1000c883c201080059040001103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 853685872 1250 853684622 853684661
    0x1903060302060301090f1409030a0905150d0e190303151e35030403350313081902010b04090c0b07020409120c02100519030e0f0d0909 59
    0x60700030440318801401018040c5407501c0a03000c031210350b5409250044030341380c0c40850b1800c1440301c162700c0c6c1d40a0014140001c01122000ca2640350555100518881d040c80562401040307802000c00b074000c5401c0c00c034160280c0c4d41d01e01c903030044e4101c80c5258a4800d17500010108504880e0001620290f040540106501903500c0c2086003a50380100603039080041c1d40080007600e541140c00c41125070110348011400c4440c1174540007000000e001aa8402e0754014811569000d200d08a02c0c0c00340fa0003502c842d103445035440c29040640c001d41d0000b084450890000540340c40c1c4005aa2050700740c3c030704400380300000d15460340e0f0a2003041c1a000d0112014414800152140c2842801d140540d81200d000000d80e01e0456a99034494071041d039000c0158041d04696410150030024400010390056502e400104440e42c4290102d80441c80a281080951240c8110440007400d00400c081a18450780040b5102d40c01c040042c0108000f065540410090030301484400740c400e480544030514004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 853687122 1250 853685872 853685879
    0x1031101020601091b030e120d02070b070e06031501180b03100e09070506030a062c09240709170c15040e010b030a020403020402070305182d0301020c03030a02190306 73
    0x50380f05a4210410900e000709840302200107a50418a0f481418180c0f540001200c085c3e4000c0c50700032f4119030313005012111803a515440280c42003010803041d140d02410410028080c01d010a1440145400603d003c141307440504150b007201c4540303034002c4800158048100413043c0385c40f201311030150110310b146035003a0809101171685e548150181500c240c0c40400000c2c0c0340801544600e0042c103020303500c480c41c03c824a03520000d03c81e07002c100204007840080061070803c0f00240d592106502250509402c1840c409000c03200308015060b1780801000d104000781c411190380500c0c052410800180c6501c1000600300400c11240d14580ca00098042c40100a481861032040341100c41a40101c0d94960f01e80c03000c0e100900c04c6400c000d50251002c2891414140c0c031102a041c00903a25140f120460b10420800210000c1580c0003c030b00030307504140b1420100c120110020b4100c018002604001c00180001d0031350300201c074502600c03075000c01e4110b0100c003615070340c090303155550a041051904 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 853688372 1250 853687122 853687151
    0x9060f0b0d120c080c0a080403140c010c020d2604050a12170c0f01020c0a060b0d260d0e0105070f05071a040c0e190f060b0304060b010908060103110102060109 70
    0x11666000c9040c094483c4220007071122210458940401c03400a03107001d4107052408030343e41d03001400299940424801b120058402c0050301c02403501c0e05071180b10b5600056400c1051070784c0c54020860300400622801002c0c0320031200c1000c400c901d03040c1450b840d07500342414020707414500d5011750341801c903000e03a0101198107140342c0618030b00500e110540e1040c0090800e0314010030ba40c410f408945c80060a800400b0780814072143c40c074400c6500740b000945503801c010f91078202c5e0070003401d044c0c0842018074503e00310484603250427070100e40203424a25404426811180318454101059443d0300411041d658007045142201070542006030404400ea191500d241e020908100214400748021400780b182d440005030003450250700c2c43c0980d00e004030503030090050415941c5c55560038011212111344071405814180c4411141c0e00b4107680e81e0351a044050200300031641c0c14881c0081000c030f00c4480601129000c1c1d80655108840420020b00080c071700f25050340000201403510303030481c1a510 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 853689622 1250 853688372 853688393
    0x21009090f0908030609220b010906050405160e0406270c0c0812041112030a03050912120406060509090a0b09060709141906030b030c0d03090506160609060f0b0d 71
    0x4015902909176587e41d011032038695501c000c0141c0168407101e070501c10402c0710001c0d00e06072501c0c8402072280c0b40d50f034000e210944106031340068690502403400940c183c030508501c1f504190003000842c0050741d0f00f80c054005060150707071918050038500596542c40803401100740340c04030f81c0342c04494011187c0f11a0b49078092140350186201130341020509121960002d42e00c0180014100d007103203035101c00304e40d6880e8801d10031140400e040c0b500042080401183c805075103c08409183e00d4801100c141032031441703005208071100c96a5110100f40c1d0703100c01079a5803155140400400307140c1103034103101103400c03801480c1c540141d0109081055690340150b14008652003e0030503a80d02ca038041c0015040070315180300c0c54007192000f00c0021040c1e41a008408600400c2d000d88000d111160140101c40189020140c08200d06440420080c104040204810701560130042000320656440c20b0546860a10580c2c1c0e00c0d442e0003100052010510401c168500c08a80300100060030307684004030030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 853690872 1250 853689622 853689631
    0x9020310080106290f1207030903021605031c200c2e050a02010209040e01050717040b070503091207030518060a121503021903050d0f0921021009090f090803 69
    0x4c04100f82e0031501a1100b40c8080c01d035503617030301500713445c0c4070300000d004200c0d40b1000d4006120f10108411541e8008004e081a02c0c0064050f009191f180c14000b04000c81201ca440100505035045e400c1c100550520ba260190951000e0305c101d018a1041201040002000350050340500d03403c4202010042e840b82c2d4849510b080564603482c00d1041a40280180d58500c0d403ca81000c500030780d41d20044d0300c01442030025031a0310480030000c44030704d00c910300d0072240244036070421310205100b01c0c0031741302450b0310440301d400300c0304bc10255a51840164210340d50440100e040460000f50f5007a440000005900c42a1440b0781000c0b07051000410200c602400381c01d0f619511414204060b1014481a02840e0003400712400780c6500c2060104034100d500c0b06070750350300400c0c41401c061031140704403030040c8031140d5410041c42d08000c40071540805003030030b60365585000310030400162200c1c0d000c0e1000c8881c0d80c813040c0055282407046801d03550800314a450551030604058005000c041c1982e401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 853692122 1250 853690872 853690949
    0xc1805062d032d0705012604110414060312070203030d0b1906020d030b1806090a020c150910020310060e06071e0c05030d091a0403020a08060702160b0403081309020310080106 77
    0x90301d8034201a81c0000d50700020541247c1004942900da404000c2e00f28001c00b020b80840f3b42d40c81d080840c042c00b6020f0002e00075850340040000c3c0340d003001c0ba9000044501c8000302001007031015031030036401e82001a07010b0700140e0044060781211540500c56203e0a41080c0d07803650b0480d1141b62a00d40035400189644d2142420b9004142c10f00e00b01c0c1c0c196000302c503500048860b03000203003c00c0c07480e00c502202d41c042d441c8100300200e51200c0c1b0f94001d07a40190f5000d446100c2e52070600c1c0d030540d4440d8040d00100e401030803d00041000c200c400600c4284ca40c100140103c40b1403142c1030003140022030f40c002600a90091680940c040d51010303601c81141d5910b100c6402000d14081000c419210b0755202035800384e00c4890100d0790705404500d050241110341c08a40407806e2400c02e0808003081c51144a1100742c00744010408164104001e050340412140142c00003602c5207003407022a0000d590000300000141024400ca0320700b4410780c0c018210924508421042e448542d00500084190042c50f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 853693372 1250 853692122 853692197
    0x70b0403030c020a2d080a1706040902150a020a0812070809070b03130201090b0301062c03070317070204150501021b1003090f0c1805062d032d070501 66
    0x1440c60448145c035a5a80c0888400d035030b401e8003000200015003c44102d141c807400c910200b8080d2900c2d2080e4110140d002d80104064144458800d07031540041c0745960960048004010000e28404014200b118025800d00c4450804110007454034500425030761040e0312040041c0010075400c0d050781d40c8001c8038104034080c1c4500e44012607110174594081141e41c02d0101c00400c034160040d100a1010300d4602e41c51000702000400c3c64008d40345400c2d00754050300218414808074046004030045050000c0c070f080e01c0e040301540400c040351741110383d1001702d00d0007030400d0240390703030521940301c000d00484141c21204a03104009205071140084480c03c0c10307901c60501701003003454110380710f1190700007001081540d502c14801442080606000b000d080c60407000441e5440c02004405030048407036015043d0080600c4d882a1490304220065807602c242595050609031000c00542d45943d800f003883c2090407482c00c03c925000440e04243d0500071062607100103291840c03101d010b210107030040d800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 853694622 1250 853693372 853693433
    0x90b0a0506151b010b010f050406120e0a0b070e03161707031403070c0b0304031215121a010914070822200105030105180c090303070b0403030c020a 65
    0x404454541004401429000c40c26010383d06030581d00802440201d4000d0004c1010400116100c441ca1a05400481c005000500c01e42c0d10480c8040f09011480d4400160740c901422258135211010030100d03101030040040250b03985d400308030f4120380d2800350003c124041484152490520450154203800b0f90b040c820340c0c041100c200310501c0195004220b458001c80c01c40070283d12544400d806841d0490f4a07440024400d28030400c99104540582e102034142d04500140130140c4080121402041d8103c0c1c800724070301024240300030310039110300d90580c21076a070601c4202c0d004405920800c0000c2c9000b42c8055103504822150303a01480a10b030400140ea03c845c044c1a61049824000545900001601003004035a600700103103680b612030b03800b80c90203240c0700442da0b0348400d005031604141a8150095403800c80320740c0c10f410031402c20303e01c0e042002c000086403942e001202e0907075100048205020625806104028408816101904214a00d61500c040b035001c480313540d03004d507200003a480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 853695872 1250 853694622 853694629
    0x31002030c0d05130b040f0308070f091205070f0605090406050f0307060f02070f060e03010e060928080708032409071218150c030203190207020a0e0f010306050a090b0a0506 76
    0x880c44503603c41304d09909820541460047e038110900b049000c43e1034500401c00e9280070f0a4100c010a903103030707101c411942c20006061014a000141200c8520030b1500c0840d0440178280d0600c050300145d551f003522540c140c0d08001c00c1d110b40e507000c2401118105121103054030b0200b1004140e07912401d0100c44003040c031008910340503040d800a00424542e50000c1501a40714030403400b403410490007448a03212120045031900000d48605000fa0f000c00380c5010a140425121040705030702141301480c080c1140c54500641c3d000780c9088a20b51400000c00220642e480c800501100000d0030000f4000810404580c0d58036010f042c0006214031002c1c4011648820741040441d09800c40c48841c6907129854802c404042011030115500d0801c00101c0001d80302e40700f0703203100d03001c0140c50080d8000b1000c1414000c0d030040000f42c0c2c104000190215004018101d16405804c0300c030002c0810f0b41c0b45003064011210040c100180700ca00b80384510000c503034140f414980102080c00000b6036a01c40e035002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 853697122 1250 853695872 853695901
    0x60308030f060d080a0f030c03050f0105240c07051f1409131a010809011503080d0b030f0f011a010c11030f0109030309060c05040b0f2d0702031002030c0d05 69
    0x526130341001424071400c0d0b030b02000d0090002c00945050004100d0704500350190383c0c0c00c1f156001004005001003282e85050403548001c04a0050601a40700c92000809181e078042d01400846510074441000541800651044802401440e1001020f251000101420b40d00c150460080c0b01c040f0b48046036540b20003880b103115245840802c01c2002c00002c0104268402e56028040391840000500f00081801081828120401001c500505541c0c401d000c9401000102040c0f41e03440e800004140c400300305049030b007100c000041c24042d40a250003400c2d101410410700140d0090307090490542d80000e00e00c01081d030710090a0662004e03080100740f60801080c0000710544c01c0031210001d00d605a402010300304e00640080c090a0620001501c03070788140e1280c0c1c0c40000c0d041200b142c3d000c00d5000a030001450301c13050564240e82a40924210751405a0300c500c00d04800920b113401c42c50108010411000804025400e41c0f070003082401040c0203004544189a4030b41d80004c5e074802d00c1240 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 853698372 1250 853697122 853697149
    0x20304061115070215091204060c11040e03070b0108011b03020c011b110c0f01020d11160f1d0105011e14030c0406120504021f0e03071e0504060308030f06 68
    0x71600c405161510f0000c0d9201c0c40c4618011281c603450340494074403140455800c00709801a003005140038504801295008240001944c039010b840000550035900d50041c6442d9178000c800440d201d41c10360811010110060b40001c9150b854500b20441200d00c0c0e8801820840d1702c3d050060f01d54120f440d035140544161000400694854034074004165006008000c01380d840104031080116680280052451903006407405680a6500140719030302c15213103050f09202d114280e61800a41c402c0e130031403030a00c680245400340c00100c0140711500c00342d9031090409600c202a001c840d407610002a001400948102d0001d00020009842160154014500c0e028045c11025030f24640320794031400342e4006016100010300310f58080e17010045c103406070502854000b00110341d000301c0c5c94415051082098800800e104400d1a02c0c41c440ea400d0000c400108401c148003441c04902c540107422110b5203400540c070a5281540610100b92903c013540d50128104200c20040c0d251440000c52520b4502e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 853699622 1250 853698372 853698403
    0xf0102040e270f01150503030408061b04030f0609030f080f01060311040807090209091018021b01020a020c0f030d09090b0f06041712070b0a05150607060b0907020307030203040611 79
    0x1004030498055015050002c621000d017510181c0ba6020035480340310381e00c40c000706039200102082e0f116512a515074503102a0005880c42c0c0759495482408907048079009403281d540d50003203401490f030003a039214125040d515101711207281228542d0840081805441d080560303c16811480700080703c1210b0150001c0400c480010b0342d0b0301e03006000781d40600032103402a1044030100d0342c45200312a0500a0fa922814691301212140d007904000303411000310412003010895413052550390030305c000d00314060158082c0501d41102005c1c003070031462000c41503000b64050004d0700d11071035100d600107040d05c40c610b4020640d130500c007001494040c00c410701c407540940002400200d102a040b40c22804943c501c098501e02411048510168000c4000280c4401c0e1414005200300d02d03903501099010407075800c4002d20704d54a001003842500316010803500c41c0d68030080c0800500d030900c0c4859018010f840294030b00328403607800039224082c0b07210310010303c81d46140100343c0071401d10189017003c14030b2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 853700872 1250 853699622 853699633
    0x90e0403020d1218150e030307050f09010309060c031b0e0f130b030303010806150d0f15090803100501090b030903042711040e15030601060e0103140f07020f0102040e27 74
    0x5d080c6407112074400e0920081c11490700c0d40590600102005880c4211010780b103441c10600c0c0e05d02903400f50b50144800070704140c2d4400710203001a045100b254083d004a94000850300705220959018110280c0035205010358203050802d19500d20040c40d01081058801280031030301400c2d14009042020b640940c503000100021031061400078401e8451440c1d0810401d800940d002406020008510083e1001e184141d41a01244880707201000004a046c070014404507140c5a21442c0d80003626040c49030545030204200a6a100442c0c030050122001c80a00c0c41c01c103214101c0e960300c190700ca43c078502000320103141d401e05000803a512031203002e00020300094a0003030f0621500c0e4001c0c0620103118030641c000c501c1c20b1800c6d11485012160207802840c51b0b9003040001d5844a4004164030304040c0c903410340541000c00c1500c118014031590401440310b04090b040070341403030a00c00c05013819038810b20040004500714101c85030804003840a98105501c410012203050080c1b454154803403040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 853702122 1250 853700872 853700921
    0x40b0a09020a09060c030509060f0910030e010e0312040b0613020a0c0201030c021c050d060b0d0209032b03050a1b090e0601260a1b03020307090e0403020d12 69
    0x41d001000401d200d0750301d400500c1c3e101d00045c3d4200402c1c0300003400051042c8199405402c04000034084031030210043d50800c0c455a002503804240d1a04c0d51303001a80b21030303000c600c0e24804d01480461000c4d501c0170354100f210b9401d05554440000700060300a07404140482c4054403900b400090041200030295a0340c56002c1e030260140001e0503040340024582940303440018400300d44248000801c400c0000c41c2c040a0704c0488080e0000700843c845640c0d02d100008609d03c8000080c80c0710110b18601680307900004080504001030001c00c506440d07081c114494849203000d444140c00040c07410f001807152180d4216000400000030010314070404940c205810760f401c2580d0b80c0c04c030f51101d4409607555039190011140c41c0540c0c42d0318081c005c5000c400c9041240c0700c0c800e241c0c0c0040355900016454540138200340c600074801901c1c2002c6580042031050a0758000203040240070b42c0c0c4103128290800e658000c0d6198142c4406100f0803e02056803c2040d110f43c1040800d6500d00c682210000304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 853703372 1250 853702122 853702139
    0x6110c0307110a050d0503030a360507051c06020c12041d0903251106220902040b09091801050a1d0708120d0e06070e01032018040b0a 59
    0x40740c1c4451050388020000503407172030311044041c88545c1c403001450540d120311118602518402c0c44e40a9080e1052100040c0c0d041031400191072006540a07055202c07215090003070134500290002d80c00f400d00030031041d8111140070280e04510340e01050050b640e8103c803040318100310300500e000140f03c2000500003031001d110752400407100c0348000303207044945a01030955920b02c82c1046010700c00491440d410503807094000d00300c440034000c00303000180c03160132800501d03250b201ca21110100c90200c20032060012180318504050301620f00300710b00c0c0908014010032540901302c0244e220b011140c0018001034107488480c158007024100174086030800801500191841c1440c1c081c070b0410140e10148404000102601102c44440180c04010118800040302e03a00141400071030075103e01c2807034144902001200d20840b1903594240c0095402d00004007900c031078803500300841d281c5104c40440c14907841d007290400210368400426110100012401414480c00403a81c890800d80300051042c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 853704622 1250 853703372 853703393
    0x9120304030e042f0715050717070801030308040b18011506030f0605060a0f2c0f0d1a060117010f1d0108030f0702010507050d0207060201061d0406110c0307 69
    0x10b40803641880081a40080d5401c20004c910181481c841d10041c007040681c4440001c119242c0140144205800394404031000c4e14410303104200001c6503032031000c62300c0d0740c4c68100f00c1d0400003a00e4060703c254510344000744000000f800280c040c050100200d085840040036181404c3c00000080c080756a2910401038420141d00c250b80129040584d10600c5840c14030481d41a12401003109040c17041c40e903030440394081841c011800f4400c0414600c05035054100051860101c0100507620110044061001108000540c103009055090201c03000403c8103c10491a1307038003c3c0b0f120b5907940c40c1d0340100c802582490302c91003420b100c1400803500a008908842c184d4000d41b964543c1d441c089803400c1101c0700c0900c905201074009000512540d0900e000404200c2e00516000d814401181c903002d051081030039060f005a0b104001c1000030170340a008040040980301040e80e02c40c031a001c000300c0421401007008040710354500d990386480b40c029040d15160441d243c103e03916102039241400800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 853705872 1250 853704622 853704647
    0xf06070305181903090801180f0809060c0307021017040303050c091008011a091309020604180c0f0e0d02130204090203070f0e090106050a0509130e1614030c090912030403 75
    0x2170b500100104481c841400b95004203c106a0b41c84003a0550703840d040c9455124200844031100c081000c3c807a144c1d95036000d005405c50000103142e44900301c1c8108a40019900c1c0c040c814402d4416106618015104003a0b40c0603415040110b150f0344d40001c1c00d002403040c140c9082c0d0000e28054020042030348400054180e80140751141000e03110310a44120764001c15001681c05444032004100450303454022966007840a0300381c50425880c0c95000400c507242e981d032010385613a601140010b265001c51446103200c128100345030580001c00100319200d8011001901400f600c00100300c1c1c2006903412a4010408103e0854681c100080300800032107182101c6400960000d024650918040d54a00c1c12541240c0344d841c580a1030980684441c1c10045469602c410124401e1100f0503260050b004404125400b0b04003195070b1171a82d4a52084070f4019094185031522000103544001800d02000c41c021034080003582e0310039061a14188540c1c103d090100c030040280030805400091a0800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 853707122 1250 853705872 853705877
    0x3071707090608070b031b0c011109040c0c05300409090203060f0702031b0c12010605040e030c0606090402030a0c152a0201050c15040b04050d020f06070305181903 72
    0x2daa94400d026039a80da13130f500880400038400c2010030490285190100341c040b01c0074441e2420b04884048076400c6605a81030b000c9d00702c4002400d601c41e0301e800d108900c590061820007000410302e9440d020759810350300d5809405520045000100b1401200540c1501241d1420282d600c5440e65407410140c10a104100d00910a10012031400541d1540c4144120060b900440c01c290f000c01540e00400000902d040b400c0c081c8120404154603620802c0302402c030b502c400030030715900e03150a0004641081d00d0700360103030b0803d21400107144000305030315800400072121075001e0303100d40c000241402000d40340100100c800c4038001840d610160b803d030034608111740322411221200700c0e4120f04807003401146d50504084004401c015801400517040c202446401c03500d640000310b81d40305c0710a00660302503902441705001c2004000040000d82d40341111880540355204089029a42d00c00300a0010014980c40f440020380c00c180b0b01000c1c4000c080c0d00e8045801944034070a00320144900c4035003c8c3e00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 853708372 1250 853707122 853707131
    0x4151107080702040c0c12031e0c1d1206040f051501030f0219091104240207120615030b09010507020c030a02060705010209280e070c110307170709 65
    0x25154024000d4034522504122030514100281e03082100a00c5102c00c82e00501401d20000c40105000f100311510f103000c075860004200401c2000050100e8502c8041e400540c20800303d1480c40d54029110321204c0c01030100720354640081000030740c0078000008121624800c1c84100010b00c650704085090300e6010f807081d101002068110544c041009010252414030640c1046c001403d10301c20001032901400c03100544540c5419003e000d541505502e202691404942806162050302e019040082800803600004d5100c0b0f1002e91076804030300c03480c810f09140c1d491240500ca80c070b8001000d0340d04407a072101e82c03094076407901c0302c2001020740348a1746943c60000040c88003800001c0e100c100410050041250410035400c2290a034058007007120155001e2040d4507494850a504e0540121248000b480781402c508910404901c0c55100101941c00742c024001440e820020448125400071440000c1940450110745805941c0d4000440f0003a5810400040c0d0300100fa1700c0c0076221226021300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 853709622 1250 853708372 853708391
    0x50a02090423150913030e0a0609060219110d0303020702131a0301060b0d0213050d0c380c03071b090f020408031b070f03050106031505042112050415 66
    0x12003c1e996020b50f500b006824000c9080d40c1c00444021a1807882407030049655144407010410b0725015602c031502141084e8424030070316130180a00b490052203001e10300e540407081e8a81c1801d440000c51181d02440403050a0014075101c0d40480d042260050b01500f006422040000000c10340d0300c46110540480e441880414507045c0115002c80d075427891440e052481280280f40217501c80300350781e00c43c400703c2c10300000e060f2503105403040c0043c01078016001451030411080c4440d59050924aa48603640b5100b02600004089590b82151044102900c0702e4454104528520800d04090146120388111520f189581c008a1081d00c40c0020107000102c2d80a0040c41a4081c0d40142900d035003050001c800184403414070050041501c0d07088801c159030b1445480f01100c882c2d0002e03200d6075155a018010300c0300004010706c12140321b4404000c0e624268903168020301c15212101c00800c456040210914071401810b001500c5421003009942403610b4025046440d00d054025820b0034400c1700e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 853710872 1250 853709622 853709641
    0x90109090c0801060f030b0301050c03010801112118010203090604022d040510050a1e05100c2307170c09130605040807120e090f0105030d03050a02090423 68
    0x264801c0c54648440910364204203017900c0c2414500029420596160242190307540e0900540e8040c0c82030b05440c0741c1c0e03541000e404500352101f000301d1501c2110100408080140d109440126844140c0c440f40741c1522420030543c403600d017488004109600102c240054030201240ba40c0c080c62003151100c2c0030b509036840500c4d42c106540464040d06000f40350b0301005013400c0c0c001560094507080f212540a0b2150000780240406410185105023007104000d021150050100c0160000300c032902d0800c5d0745240c004060002240c0001c1c440348404845a524901d61004105543c420900352400a61525680c030800c0c44100d1400505109442440b00c91b8188807404a00903c0c0103650380f0680b00c130700d403140700143c003000d00200d0328204100038400c081500c4906088041d0041c3c1c0c1c035048808000700410455040140801c0480001100108266a40003494002d210741d076042c0403405036030381c0d00c1e000002e0042d6542240c01a041400d48000c02d06d5504409054411082c07402c08151154141d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 853712122 1250 853710872 853710881
    0xc060f1116060503090109020d03170a0b0f0105070c03231501050616050a06060905090c030601230d1a01031a061003022d03100801020f090d02190b09010909 69
    0x4081e9800180c0003400040d204400540d4824003400000c10090401d5001c91441130035064140d001807420b1641141c3e240d02e0601300341d0000c0c1e50f46410300a584d40003000480107041400000d0501400192000800401511030001590403042031099103a000e1001c0c00742c002c040c0c4032144a400741c0c0b01c0701c00002076500e03820741c140d41014055070305240000c02c040441039a601000d036443c4c8251070315400013425034094403019003000c00010400d03041100e20076190860200a07203219802850050021280910320b5404054101c0c1d5150244200ea60104000d40d403d060040c042c10b03400c02160400c000504c43ca14122480b48100e60246443e03942238105915042c0c9c0e0865100f240780c3d80c802a0300744030760003415801c000d056400d080e004505260301c03030b101e9401b003d108505c40084200316901d042c2c0d0340e140000b0018280290f142c46140207402c100d038031508004920030700e00410f0074010b41d1200705954107d0f1040400b400050350b107401541100d600140c4200740000d23a0743c1c002113030990b018002c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 853713372 1250 853712122 853712143
    0x80a0e010908071203020708070801090c0e15090a091505041a100b1305120705040506150f0c03251704182a12110408061902070c060f11 60
    0x26080260400c822182c0007401251305a007144141381c030105003a1424400d040081402c400005100c4546180c00d10102c1003a6210300202d8542c48104a44100d041c0100100007a04481c0c000c8640d903040d100f503004090511001d00b118000e28001c80c0c81c8030711039111a004138003a51400740740e446050790200780ba00c001c403640b1102580d12903081012451800250036282c4140e0b070400e00c0992240003150701450700042c042a0356022010030095810709202e1035030000710540c5d460000444012115803240f00c3d4042c9014443e00001d05200d01d40810320946405d095a00342500603550151201548184c4101060302d010300c41c0c40c5050313901e506450468044a10102001c40107200c200620710003080c080506001840c004404070410000e580640c2201044030f480300c02c400d0442e00685411500c2d41024041c2c00e020421007400f40110001303980343d1003140008004c2e05190300502d880c002e4003a01c02d000341418039950003c100113422450301030b119205a0341c5c070186103100e9242160f0b00ea20414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 853714622 1250 853713372 853713389
    0x1e170c03270d0803041a0f040209160f26010e09060a0b1315030803101a0306030c120102070618020103050f190b0d050d09051e0312070311060103080a0e0109 69
    0x542c0310000e500324018581c414095409120010400c0142a000510481d8054801054607007040114a000040d190b080031421401a485444280c8007070070302e922140d104400d0140030f80782c0c00b843c00c0900150941603400c0002003d0740e035030b6901c0c0c04031310307100140c4090401d40580e0000904c4480d13184903010121034010412002c0780030304070214000b0a0186290000c81c5040d400c00f2021401800007140171303680c540a802065072a24040102c41c402c041c604e07a11050341003092021b150350010349801c0314101290003a0342c00401141d203d009101d09100104098200b404d006000804110000f2655000380c901780216515509400040882103070b501d100445181c800c000d1502666000284c0300c6006060041f10b0015a11003914105035000a040003800b4104203100c541000031210040003018003d401707168040d58000391f2500016440400040b0b030106a0109140c440c44006800d4064501a6801d6503181d041160580c0c0c03005850102240300500c4044065100f030036250300721780e200c0d07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 853715872 1250 853714622 853714639
    0x10f0c0308010504181a15030105010308031602031c0b09010e1003060209030111030a0b150f030c0a0e180a05150306010b0f1216090608041e170c0327 66
    0x81048010001d1001c0802017042c0440d07400e00007242181d02404001d01c000b584c41052a001c84009607005c0d07181c43d0180070342d041c80010070014460400741c03600147e00c02d902c10349040030a04128070311300030400440e04078006c1c0e183d00118401d1070307480000c42c50020b441c00041c503a01c44899000c042e405407040008005603030320400104082d40c4c0502009403000340040764440c407100200720650400d55065210943d5000c180c20940360000c420071001a0200d200c90408411003500c1c0c1003400020504240582c0c00104000254490070000110a00042c401c903441241e40000c000600e000311a550902e030b142c8004180e4890180f9540b5141c0d00c801001802e080c0e00b00481c42d0401d4100401c0c05c28402000d02120070540340f101060380c0318002e41800340360500304c0310800501c5004a070380281c0903c0281024440401d01302c0c1052480781c2d820303c911550000700c3d40b6040842c3c0305210049203d00702e0110303001039554400300c01041c040884000520b082c81c0180100607903048080d800e01d9006400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 853717122 1250 853715872 853715879
    0x30201080f0601120c05090a03080405030c0321130b030c030405010e0303011a0904180f11042307020c1002030a090512030a0c030e0d0c03050d080f060607060f0c0905010f0c030801 79
    0xa41007417102c01707880d01c2c0190030714580e0408520b14480c50f400440b048003005c1011311450404111007030f481c04003103000f01610031001002c13119403507078080200c4030001d0005080b0b03892942d180b130701d0008214144505540b45094450400540c10559040b2080d508000501d120520000f0a5a040e20704a00c031601003000c0c0780008007526800603040c0b5030010344402e440b0080d0383c100014191100d00864071400c0341c0c1136515090122240c3d500210340304514014012405412502000400c1440c2e98542c0c440303a124071205174503101c00040c1640e0301c0200040740b030f061540c0c0840070f040e1490807078a403001101c2d141c20810094a82002c0181c03103070361042c0032000b840e81c0700704407021200f8000d04001a440e03889201244076240c811070251782100300c0800070003c02c80e081003000c01c4c4c1c418074074120030241401d0584004201011381454450302005c03c45006011203503000c002554440d0400b000500c4003500050200d50f05071040d5400f09002c0e00741415480e000300c0d00e104051b0f5140e50742d194075070308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 853718372 1250 853717122 853717157
    0x6031b010504180f06170708030f030c0c100504060b0a0518150a03060e0106031203020702030601050907020114040b160503100b03040f0503180909070b0318010b1009030201080f0601 80
    0x10f0f00400900154450034035402c56403c1c0d00c5010701402c0303540300340d5140100350020503140229560041c04581e10070019400e5030030704081601c1e042081215039540c0c442c3c050000c40d1400818000400e0003e01d400c0501003000500c5d442690981000d981400001e0350316400c11070030802c02d01078800c100495500180d400c1c180ca00f8410500d0b24024001d9112603181e885010441c3c002e0201d0741060b03035468009209000c040301c0d40309048540da107000d40c03030243c49e40e010940f504010701c61a4001c0b44801c01181a250007034010710151b1b0040780c0c50640c68074290030aa8a601825101c010450709903000300804544908100c0f8450311880c3d0500f01c001e0324141d281266580014003d6480c3d07a201c55000000640c180b000f010745142c103041d042000c0311078104025604001614440e100d41c09a902000781c40301c0d6605172944a8214100c0c0f106a4072501c281c1805422441d40c0c0d280d00203000076102404581040603101924001c1e80e90f0001940c4492625a001c1d5003910194007207803c40c0c03117011b06d140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 853719622 1250 853718372 853718399
    0x20c04021e07060212160c11030123010e06010f02030a0809030d020408010f0516090605090a050a0803040608240d06060b0a02010f150e060603180a0b06031b010504 72
    0x341ca070340700007510102a020744556004407000712011a00059400001441c1199440d00800f0740248819804a04e45000d4100400c1c000c00615920810818042c19135080d801b00c11200d000312849411010702c3e94004030650024021b4000e24000b4001090340e6501c681c4552101202d16001036113440c1c0789074401c4d20020030080619500d44005c0044480a000500107800209408800450307180d240c10038000c2512001044006003000c603403c03a0b00c540e61300140700c000b21000350034087c0c1d96501600c080f4900800580040313030010000700001070181c0e40000140b00311030141da10040c6580304e0b2081d005480f440e07948542c54407039580c1c000e04a80e03d800106103404034498200007a141c2e5443c1e50904d46a088040e4600150359101c40c11403c200c2e5601818900c100c072180d003001003c0c10707c200440c600324040c00c41c600602000c0006035011519030a00049081614112030307101e00d0314035000702018400c0b1003c1d402801003101075404be6030121940d11001d40140c43d028207003418005c81030151f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 853720872 1250 853719622 853719637
    0x102040b12040c030807030806180610030b0604241209020d060209040b0405040302010606020c18180a0b0c130e25020709110706050f07050d1820040b040b01020c0402 73
    0x3c0040d071400000580d200d0000d0030228801c0d15210810f01d404002c21078980300814600c0d600c130001034104030069070b8142100000c991242400034510400d400030400e10f005507040300107103802c100703103039090700129410b2211486071f1565a0140180040000c9050b1440000c00941107025a4410000280c0740e401400e601c0310054000260064240001029034809803001d4000d41d40d01c50f000c1c003260380c0c14007100f011080103459108000102103040140c101d0024401c1e02050320109055003a10f405001c200844d540081d41d07840642840c041c24400c60b4022106124540c1240d580020008001c101051040301920303142201038050041c0d00324010844e03c400c904501500f200411190340912961841070b00109101d6218161898808110f07400074200215070400e02c07003006900707607001084604c4020f614801103040c10210140222510010100070b11203103a103008003500107605080c100301c101c000c0b5024070081c040941404221038a000c035072801030f000440c14140501305a002440308 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 853722122 1250 853720872 853720883
    0x60203160609110916090602030a05121e07050c0c040e0a0f0618051f060f030f0501020f160309140a0512070905070c261b01060f0906090e0102040b1204 67
    0x70f4040c0c0c1c80040d141003001c890000400a09110301c0148660041b24003024004a000031440c05160b00e00143c214050440d0070101e440b2040300103240b65003c50044e40507030184611680060400c080082c110740c2002203800b111384183c40a034030680c90700d40201c10192408001412140d026a1101030041600c84815101c4985804400c4607401c01020155030581c014130140c641e040060030300340346290750704131030100c03c0d81441014019040d050124038200d0b54001d40343c9070b8031881403805601900a0035804008070380003185072016511401d06000901d88a40d40d10b000c1c2c5602d40c0300e06040810302c00381a40d0800d10b5824288000e00b0160140000102c144003140c0080d59035140d50400d5407011202240002c40d8645901d0401801d40c180700c1d0241600020b04100c4200000c00319110f0103031680717440103c1c09842c0300ca0032490080d44000050150780141010858030342c80500043c004521502c0c0780c007031610a0300310443c41c061094600f590300380c1401524044100002c0d0a00401c00b034400d070350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 853723372 1250 853722122 853722143
    0xf12030708090d0c0b2e060216031e110d0c0e060301110318070b030924040f0611090d0b1009060e04060915140f090c09180c13090c060203160609 64
    0x5012000c003003148110499100e452186d503003031020090500f00c400310340700c0030904111000d00015500c05191018410fa40d07070811081d03041828400c80740c02103d4211034100c07156000e21800c0c402c00070071420a81c2c4030401e109210761180c0091508851100d200c000e80c034041400410500b00c5580b0003d01611001001c846004c0d0300c0f03800b04480d9a0040d42d0555240c0d0000440601043c0e40780c00c1d44008402c1c03501c6c2c086840c07a05886581020081d018001c001c00d0341c44060300201181501543c0e965200680200c802145901e40030203c00010760b07001d82c58164500340040c503001b8501a620690700460385140c000d0311140e59540203403841c2442101d05014100d0310914511b403510500000540744040c005403400c00e183c030450700080150540d00e440d0401021114641c40b000201904400940d50041d5800c01c80c92050f81070070f080340000d80e800003100d521000030603d1078210700d403624014860b20848584c1c03094103030fa9038400c45011301e840d1a410040718012031a182c0c01344000074010501c101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 853724622 1250 853723372 853723411
    0x40507030605060d0b16080610090b0702060c0a03022109031c030912050d0f0c0203180307170c0a050a050109122d050c0f0f120f12030708090d0c0b 65
    0x32017100d01119551510282904a05003e0f0740c8080038507005041a078030b4800700618550002c0c41c40d600341c0101718140000040c09011500c82c1811100d0064011068401030074092030b0013034541801c05400b40c41180c010034a1421200c1788011940000e00080050403010581510501c00c0e044103107005042c1a9110420004245060b40d104200703111543e650b0359564801a01208075007205605903016850098600c1002d6000030403110030712a911003900408181c800040c0c605074064002251148002d040314a24410000303000072003841c100c0d21100f6444d190818030002f9811441101e0029145d802c040100a800c41d80ca0b10300305006014001e00008581c00760721001544400d1505080b00c0d04641030240002407040c1541c140342150320041100740c01c0f0001d086a00e251141520510201c030020003008010400c560741d206030320381903418106040404e1009504201ca108000c50185c600085101c00041043c240ca810780740c4864881c40030b00d0f240d231000383c0c5005041c040301400505048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 853725872 1250 853724622 853724633
    0x3070e041b0828151d01020d0209010e0405040521040e0412171519050306130b010f0312052215022104140a03080706090b0c03040507030605060d 64
    0x350240000c0c01c02401141ca0003000c0800112615444461040c000c3d040302c0c001804e00c4045a402c40c42e860301c0461404a80b0035061030580c81c00c00c40b040700d5813001982d08036401c4560043d24150009884401c02101200e0074001960070480f002132541e00848003840e01c5100c4604d80c2041c6e5005100302508003a01c940d1190082002554161084624112400c2c45140e100c240e18620b461300001c2d0315510304000c03110032400b64980c842944503c90042c02c9060f002c0c0300150280082000600b194200e0400c44421118568800016150340c1104800401e00d411002569801c9903444244400000036044085840b50042540c1c4183c86440318207220f0219074505000020301160000c40b20705c404100f4019241444c91103220480181e4140fa08500e1f4151001303441c00c8540ca01d100100584548002400311031494000608050021a83d0414080c5036400091928450440c441c0c1c0b540b01d00e03070706545c036001c2120020441c0d40402d9041c40001c072960851608071202406104180e01c10340d599 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 853727122 1250 853725872 853725923
    0x7021f0c0807080304060b061e210f0711030304030507030e310f060e010e09010e070807060801140f0f010207330503010b1806070f1101140903070e04 66
    0x40c0c98590f0044103100034801030307104050081c0c4003200d54030325002c607800320302c0c1d00314880c0f84040c40141c40c040b800310400c14001c1c50514400340c101010880303502c0c01210380d00012a040d0713007590001c1c1e803013071600010b403200000f2203000d41d4054070b4041c18920240d8045078625000664540c05c0800c1f50746004000401001400d6104408400c52384001c044864800172917a1580b102c0c80f0960402c2c034100700010701402840d06403100c500c1001d4031340ea04e9015035800350888080c004403500c244040000d642c0004901d003000d0369440e40e03640103140d03680e12034090031081080141c1d03481114a41141032500c1e000c40081c98900d418019114000d40d6015103510b800c070800d256001c2d04000103c40d0501c0341c80f03c20043c101c03030b145007030842c21035061070000c034031030300802400321440305902c1c03424081c0340d89420545e04030319804090206280c90902d492910031444a12041c08a05610400c0b501c02001e0b0040d16000785000d401008024584120340002c80e10180c401c0e50480d105d8a1010545e142081a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 853728372 1250 853727122 853727137
    0x40510050406200313080f04030506040813060201110301090b0a030b0a0902090c0c030f0a021203010303110607030e030d0c0306091119020a020307140111060712060b07021f0c08 78
    0x4000b4020401e550f41c0d40c0c04485403018815561000c000704051072440c54982c81d461034100b040686c845005c1814884c0c940300e10303000500144110b004000401040e00c0041a00503104003040e22a250f4500041e4261303412012040441d10041c0010302100b62554000c040701007000708200081503a98aa0703440d03901040d03840390003040d2204180030a40c1042803d4a4003c80d412044034500701d81c154006840f40913040140d8203158001403111300c15031082000a61340c0004d01c000170f9803035039a1320303000e002c030a03082d0000481800b070319000500b890302078802c2c05c08001018001c2e5240c14010800703075008020159403207080c56034841020a42c00050300c40c90320b480d00c1e11040710355a840000c0440c01045540f40c0e0704000c42d80700451210058030003181d07401c21030310300c0d41d10b03028142203010043e602c7c11414998002c96120780410081a41c0c0e00039080f103840c6004c010108801c2d42c41e0f6040103c20312882c00c0c080d4018440c102010000e0401d00e000c1c1c819000203242c6481042260780c0c822280e0741c803004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 853729622 1250 853728372 853728383
    0xc151509090109170a0914030606060c120a0e09060f0307051018090903230d1e020309070e0115051e040308070b0610030516230c06040b0603061e0405100504 69
    0x40ca05c0304490300486500042c0121040040c02802d05200180c3d6491004008501600002c681c4001b1443c0030024684101c1c1059240c0d91560a140c10003440003c1504925110b0f21000010074801d042c807002d041003106002d00942140760500090002d40101d0700c481d4410000c0e00550102078030b4408500a0240092180218540c00c02d401e00514000f0003034216101c010344807e050b49500d07603800c1100c42c0700600920125038005808514804030b032040c0300e50f00310180000308001d00b411010035050151203c16039683e1040e41c0341e03111105800340389607210020580402141d500090302580e40a1000103144501c0d10b0541c90343c4d91012550810402220025640320902020303141c04d0b02280c40b410014074040056103009440c90310440d01c003803090014003400c80c0d0440c003031003455080c40400c002684030715651440d041d050b065903040202d500390303032003460600421f09514000c142140a66030000301f0407000c03c1c02d659400012400a0000c84152084203206001c499042c050240b040d806107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853730872 1250 853729622 853729627
    0x30402011b080c0f0c0315100306090f0c0e041208070509040902030c192102010906050904060f080a03081e0402120307050601032a050907030b0a0e0c0c15150909010917 74
    0x10406d040c602001100c90039081d100307500800907201074110442d001c0b01d0304100049641c0c40141071642e485404104094418040190040340052100a00a0007148111101032203046149030860b801c0000b83c0d100d000040f01001051414946031b040b101c10207000400303640458122800040e41c540000074214142d0310742400c02c00c42c080009501c007150b1402e6805600c0780c2d03240fa900080203110907000d00e106100020803401e101351039aa107d0350140080c40100320b4030b41d40700c01030b4a603a40000d07042140001c500d40d0029007034081c130700e1000c003c2001c80e21082685444039801c100041d10001c0280b2401c0c8002c0c0a40000700e41c08000300350003140a40d1642481c85030041940241c1003021580c2d404921030b00c1d0f010803490311580031050703122080340b400041000c1818002001c03980240e10000c1340701340e10021300031200d803488028100001c03080b003280d50492000d1191090080304890594a0303000c101102003480c00e00d413101c0d40d0300c0820300b40000342d00340c0c00e41e46050f4200082013a511034031402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 853732122 1250 853730872 853730893
    0x110d05130516050105040504050411220f06030c0b09030307050613210c080a030207050f07062d08060f1017010b0c070b0906040f0308130b030402011b080c0f 69
    0xd11022444088000b840c0d05007a0400340060410702c134a20070709025568420016040c401d0342c0008264542004001800408420f540340d400185900c1c1801082031600c1c10309400082588211400c40342d2007002c81c2c2840f89080c00801c05900b20649080d018002000a0000100e090142c42c1c800d040511a5000701103a909007018030301c4801c4600d0b0600008038010628881c0c00100d00c030104e90b0300c005034503940e14200c403040340640100800242584140801c080d80e103030b030102d01d28050790703840e54807518900d0f480d114000719003200d6211800560480d95030001200d20401c0626072120300031b0900043d0568a001146051480b142800300003a06941501071380b902242e441801030020759801c600b003140201d0345a484031902c0c4030b041c900010003d0004488d031102d400741d0300108031110803000700554a05242581c0d80c1301c0104206032a041e5070020800881c208144d9000d550107a50341d0300c10000881c50460280c8a0340c0c415100408107215040707c030341041240c024100d07400f00152000568 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 853733372 1250 853732122 853732133
    0xa022403010e0f0604060e0414011b080117010501120b07021e0c090906101e0305030307180812040b03180316050f01050105030c090c07300c0213110d0513 68
    0x4007904d034030310850512604020328100440c1c80751f00250080120319404000301003c9004040e05034400e00301c1743c8900b5240c0042600103016504035402500c0d101e60303004440856030300302e80c000d004014070513401150300303c0860101244158454400d0040b24010ba84da241c81c0351a502000103c0d4a466001080c05109803c01585654022010b100104210b04240d41c0240c2851064000d42c452031001d10440e400b6858040068801180c01505480d036904008100a00314072031803100c1c400300d10104c0c0d40002d9441001819036180c9803c060b0f400d0400b810b229880103940e002030304042c02940c280c1108900b548080c80104a107480008403255070f1b040382e1070410308050304161407040c81c3c2d16000042203140c90200300000030102c110b9244400759110b040705030613030150000c042c12020005401c8803120300d00b2007659903503a502840307040b1142940d16084a240e621b2403002908094464208501c00d00550042100107828600076810040c0702c03999241192001c6071050608c0c0d8815111005200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 853734622 1250 853733372 853733401
    0x12050f030c0d0c020d1e0c08070503040e1608010e0a0902100305100b030c09010302031807030302071403010231030609080d18050a0b07120e0a1506080a022403010e 72
    0x544078000b8080c640038000b0060843ca082c00c51910014054001211a0601c1500c15804441d403148e07a20b40c031084103003401656a007082c0500c00c1c18000d03a0020841418000740120034050f001d5441130400e0713003401c6001030b4204029011074003030350f1104128801a561840d043c21031204641c1c000500d40741c4a00d0406040500b64032840070309a0400c1413020101d50300003101d100c100e003820096a00d448a24030440001c085664040d4240a0840d011040550210303001003120801c9000004211040b0101800c0748203101300c41d449000c00000400e0340d95000030460488641e81d540c2100c00780d6036604d8010594011800c101e030a41c0c400207130201114558840c04070310011603c441e000d0600b01d1303911a1341d076400d043e001400748421040010411449540408210000000309015a011445095580700c20004048504026070380031502e6000d0244a102c003100c80b11802480d4607480e07902401040c2d120b4042e5034a03006c4030280c3d0201c800900c84000c600810300b42d46914518500f150b10001c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 853735872 1250 853734622 853734641
    0xb0304052506090312090308041d1b07061d030c07150c0c03031b060207060b01030b010305160503100b0a020f0106081903120e010606030b03100e030712050f030c0d 72
    0xd00e40d203000b4030505611045910580f91322514807503418818110688000c03038968001030441a0000e0081b80301101c0c50003d041415081135021002e0b201e004c07a8800d11259840e4200c07800300140306410100e1010340184165601080d10854200c0c110302c1240d04581c480310798088140e00c044001c001402d10b042a40450070b109113028a401c000c0c0c0d90301c00400419a110140c100400b44000049910303000c0c000000035540040210345c0c4000700c3c40c0100150460700980360200e858403429943c194000d009441c03240d01d9007840e08006c50540c000075030b020342028011054241807090041b500040400c02482c190800d07400400006008041e02e40c25105940c000100f590000e41640303c0ca039481c0c40324046840d138035040c001c810303a82c0a4202002403c11184003d20356003059000900d442e0980c4c040000b0100941c2034413070f8030840c48091400d4544a09000c0d8451f4020002c08021850a000b003a03058112440d005281440e0b0a1640542d0341068440c613103480c01c002620754000c4200d01c0340b003501 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 853737122 1250 853735872 853735933
    0x902031c0507080c010209041e0b180c0a050f04061112040f05100c050a031d3a0605010b1b0c030606010f050904051524160c0b030405 59
    0x864a030303000100705000e002401441c620011800d044001000c3d010744580c144040c0080120f103100b010703807500948030061200750a91500c00d548a582c145103500600d2000c2c54103103410107440380d400c5001c1c0e90344100600d03410031500303200109542400100a10041880c2c0d600c502c0340c00002e001c594103100410b6207130800448200002c020b2a5010941c2c28100c0324100c47e0000c0c222000b0809880503031888a00a10341c2c06641110740401d5040301e2914640c81011148501d00c81100301400302c4040c1111503100c85403c0000b0000c201005202003501c2a448207201c404040d9042d5200000c0e11020382002d0703c07040707021692403072801c54280c02407a204401002010240e40c4c02012a45030500503100c181080502000411910b0288044402014015004000381c0c905a01504803528107803170b40c2449220301801061443d80f00700207003070340003560030340880c41d0200171803900e130b60110f210400311141014481c00060869001028602c1a4000c0000c1c1050011000d2803011000207560241e60 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 853738372 1250 853737122 853737163
    0x1305040203010e1b040c090e0406050711030405010804170c06010308070302060f010621060f0b07060e0f07120f0210080f060a120303050a1803021e010b0f060d140a090203 75
    0x3d05141c0c21300142c0d646009a40000d060911854100c0c0e60f00020f4114480d040d00c1710060004000c030f0b0794405403085e0b030a95a000c070b07200c0c000600a500c91050344181d500050a40b80414045070080415001c0c140d0090b00040c0361000f045071180c01c2c04000d070710640307807010301003010000d040d0148082e5901c4842d01072014003642c103200c409080204080012807174819020500305e035440244d030005c000340c04040d122422683e03036030548407810750003140c04860140c03d01240081444001408800f0340008401400006051091128a41580c00000c0e034125490001002c0940c4500c1465440201159911800c500e400d00400c2c02051024002900075103c46400b0450000c0d8105d40c07100c559851300d4007041c162242d0416001800c2c0900c4810000c103840e685100c205900000d400d20f40508491003d4604ca803007402c22800c030345449000c2504003003040004011840c0a800611a44003203020014200c00d40b4040c1e010000000c481007603500f65104810011b504d000c00020000d030244100710403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 853739622 1250 853738372 853738393
    0xf0306120b1306151401094a10060e0a030c061404091a2103040b07020102010f050a0b210d0c14030d0504120206090a080c0c1305040203010e 62
    0x240c11040050002c405094500c60100802016400000845044810f4010060b80343c2c0d40c01c8441140c50810719010643c0d41e5400500f2600f01c1050b01e99900034800d4a921503240700500820640c4903a004084149580304860015904280c00b14001c2082c4001c0300e24850800b000603007120500d45a261140315401402c10001d101640d408041d80c00910b01402181d08100c0c14480c00d0180c0d0b007010901c5070808041803402c022000303450b40050802c0340c1c1d0010b02d0100002200021000301c1d884200c58104000901c42c55000e80000c140040c0f042c400001d0300716814003030404840c070603150078180684502c060f00356803078007010458400c0c40700c0420200ca00144802140c1d203401142c8054144145c400e800340038049902e8500c41124a418140c9076902245854003000b060201c404982d40174494030003031521480055014811110000105140144e503103071032046030810710b10a001c40c410115078007500d0f12183c1d00101d121081820105489c2094810142540c0030403003400095440a134030324 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 853740872 1250 853739622 853739633
    0x90a170c01050f0717120609040f021c05100608010c03020f1c02041a0a090609120219050a06022103190f1103070203090a06050307021002030a02190f030612 69
    0xa49500c04242003007580ca610f00701c0714050700d004510010b416480007141150410364000018440c1031400741c2941c20036543c040030028038140070785010344a000008806001802d241c50700720342580200c15000c88429060387d900345440c0d0a000b0424006850780400c1000312800d0298194421160505504207680c031141c018a030300610110300680c44098504000310741059045030090821f41502043e80400c2c001200d01070362040c0c1000002910b60f60300029480e201e481010180c074900c2c00030388140a03481e000c100803844814252110f402032050001030710f072f80c2ca007001002040c550f009040025041d00403040d0754007000c40e02481c0200c04204102c2082540381042c88000e000c0100020400d10500340c984c010701d0107a0031f4600702d40c0e000051000c4103030004090500c1ca0001c0320750341440c5403034a4007103c1501081d0344400250780b0104a0480d4252103402540d84018141c400500303000030520050f030501449417040780401d841940c00a0590741c0350092a0160828803003465000282c0c0d542c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 853742122 1250 853740872 853740883
    0xa0905070e011b0516060e030703080403030c05010f0e07080610060206070c060b0a090207061b0f05070f150603051905030f0304020d060f06080c0922020a0f03050102090a17 76
    0x21030b0400c030180c005618110b090800c16540e243e045000c4508600b441480854030209500403400402c4913000d0000013441d00080103c107982c0d07ca01d940d4101851641d05598030404c289041300c455481d80050314007030209124240707207040071074024001589000c5206083c0903014140c074140c52035840c1d00b400015000281c8036005001c52404140c440c00504010000300010321f14030340d0004041c0c1000500b5405a00503000250080c00c0802800e1207401d1024a010280c90403600451480c1e5008140e05000d80042e00215000c4e0140000da00c9071580d039424251460428844e00c2681c40c9130038028001c04012258041d1140001a40b0159180e00c0e0b8950700c1c01403205c10b074802180000001c0031522803010311074060341e0000703040c07101c40703044c000b03040182c06107000b107845034881d020940b8074600d81000464080d481961000418014400030142c506841c2c44080c1e801c91511140081c0742c071070310401403006500403400117840c0d42c12602000240d07491940860a000079039406003090358070100c7c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 853743372 1250 853742122 853742147
    0x50405010f02031e0705030c120316030513060b0a0b0c010903110f100207080d0c1110090305070f06020f07080703020615033c010b0906060c030d0221070e0a090507 72
    0x4101e61902c0ea1890031b41e180d4800c2d801075411714003500342d04050106440014600a440f0341507048081d2004c2c3c401202242c0040701e90a0407680d0020091000c2956640503190404005e05459003007a1204079030180c42d40324101010303a41e0741d41e800b424141a407000c015540d1428010180030344070f906038403595aa1458483c0820f00690004241e01049204000c84100540011007844141d00301314014280c0718654640c040640a0f44a00280304903540c410303414960740c5a00c03100d040c19801d40740d4080101980108642169080006006044184d0058091188035442040d9960442d21f4003d0501c0350213064080d442001d00c88030880c030355000c514201e58024990320240f446504d900101204140107000c20400e0b010b00e480d44c43c100b5419017200c41d000c0c0d01540d403c40300c1c0d00d0700810f03c4807910400d24041d610350014401e0200300e9501e6001004103580c1000680109540d104003043d80110980d048008610300c0c0071203104a003003030012400207143c00c43c0100300b0303850581343c040c2a00b0200031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 853744622 1250 853743372 853743427
    0x80402090c0f3f041506050a091806090f050d02060615030a06270b0603060303040e191a040c0e031e0724110109170304060b10050405010f0203 63
    0x1e40b0700c1c000c500c01c940c4110010f54550708014a0381069180d0124070800d890a0703d140d00380c5490080308410074003d810840d03001130b11801d0400c0c81c0605450090445004080b8500d48440502021444501070386400c10b01415140c0c140d6569441c1141ca803050300c00460b02503402907800c0050b203640c0d001d2028000403150b0400b5903a596030004090041040360084020303429403c20b4084c194030810076028054002c0c1070b081100400d084200200c07800200e0340240c1c944c0c4100014000100d80c10754a41c0c02030300c84410111902d9410b0360388400e6420404003440c140114265858452a00f40554404051641401c04102c03800070042a11640c52440c4510300b29115030b54590801030400100005181c80d131001c01c0c070b400703844201c1c4c5880394002e4154070001e0b680d00010b50340c408040c82890b0495500c01c0d00034548502d244501c86140e04024803c0c0e40081d5100b100e0341c0b46072103011603c503810a440c0d8a49a440e030400f0700140455039214800d02c210360042c0150003420450325a464802c07581c80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 853745872 1250 853744622 853744657
    0x30902060702030f10061e090c2a0308060402071703101805180303100315111809010f12080702060702130504020306060105070b0601080c04090606080402090c0f 71
    0x900110303425104040303000390180f0030411180844180812110141100c0f10310a10007a0340c0c951307103059203034a0600315071648000200100700c0d259041e882a0101c005500700669030303640543c00880c448900b00e8080039800c1c904242e2100f05644040c0c0a503004100704c401f1418400e20b61510004211503520f1200007100000110382803603c400282070040c20448071189a44090701c1500014100540391081004c8001100f00f0510358040140c910600c2d40640740e0900d0340c9544c03130380c9022441d40f0b030718004c50541d00c4400390b4142c20850001c1071528002910070000c0e94641043c051500c00590100459484a0906000f66a1900ca985042c5904100c0054451003e4000102d40f4421041d009621107002806901c007491a0f8000f544100d000710140d4245542d00d000540b0b69100395800109282044400500d0540c096540c6541281182442604141e02c80540d002151040d4010701c0100b007031a0104421840c000745040c3d4403015640c5c8440c100f49042140c01490b001d52000c18a0300c4a55 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 853747122 1250 853745872 853745891
    0x82b080c180105220513020408062a0f03040c0503010c0e270412030f02131520100612030504060f030e190b0a09020a1202010306030501420603 63
    0x83c5050f544084203041009a59107005000c88818031424440c4501030010000c203500756010900c01c0d88c0c01c83d036400015000603554000c1100d828069400d01c0140c2e074080c01840da03641c0d1310100c0a040680c404640056403410b01c0c0c104038681450580c4103e100340e06004d81c241d0000c0c0d21241240d940f9100340e031400b100f032031620b00d04089c81000003280e06024034604204424418510100c904910090301d04022011900c1c1400081e4800d24030320314945100c011040001007803980220000425601d002240141c0070450707000702c5450f00303059041c0355000180d00c240c1c2c3c0c41603106d5207005100c86a540b8210403059600500b05014a00c64542031245040c583d5201c40e00a030840c1d0700b01030100080e191494100c0249074840742080d1401e0700ca40e901c4c0f2002407500b41c92807040304072450b00109020503152400c0c0d080c0b9a5140b103040c8c02c030b0405031510400800128240103403c0780019a03030844a1a91241800b80024004c000102c003ca0700300700124060008220640c2c0d00b525007034a400710743c0340304 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 853748372 1250 853747122 853747127
    0xd0503160602071403130e040203031e0a0906020712061d42040b09030c160302030d0f050409090c05031c09080a03021203090106082b080c1801 63
    0x2003050450620030140321603030400819500078180c0b03510070882000c8a078079000980c2d503a409458030304480501e82c80b0b41403110003400300e8902c2e40284001c00f26071604003103002c01040d1010b4000509041c3c080850020480b9401402c1180a859184020214145003019000006059080107083e4a81e0703080d5060200001d00e55540d01c0c1019032003194040030100300381104214101203540489000064020440c140003404100303503090450389051913403110b848035051104040c0001102d84410401c24940340310074070101044ea0224002003210a141d030050500b0b000b01030800c9020011041580c207030705034014068a007554101600011041c01d0703031420001c441c0b43c1d9001554103115044001540c00740910340b20740e040c1c00a680d44000d003035a0340303172090791006039080083c096007141100d0b2213203482c000080d5900441450001c1001e82e40c03200c5003424455142c40503070f80b00103080a514247c40c40829904e64500c41440d00c0e9616207400400c1c260f581c0511501d00460040640ca103500581c0f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 853749622 1250 853748372 853748377
    0x2180913081903150b0d11090a030b040203070905190e030f121008010c020a15110a120b090f0627090714040614120115030f0b0609010b090d0503 64
    0x55004400680e0384071000c0c20141c80182c40c0e10701c0740001c3e003004041c0050720403244140080307034403005c08039051240110b8100050038884103910503c520038001800a565208004001103000e0140d0310b8141c03c0a0052501300700c16900840000c604040a02481d4003215500708006040301d1400600110314454850440c0700700784103408140360110f4240541000b014105000303d40c000c003103081e840d9451811509030b8444196034805a0450040100403800311441c42d9002000306100141880c00c001d0786030340c50b40008808000080b100701c5801140d41c500e11401c1503186c2d0444050125103403002d01c1c0940000002c1c100c60141c0807042e221101c2c1560710003400805a0609011030700c910340b8200d040e60381c030400d01c281081c81c00c0d0b081c2c500506007441c0c4106020394100700d80114141d0b44400a1007245d8102e0300242426650390906d500010310481c14a5026500c11010f982c4800041d0170640100300380130780500e12a141035001040790001c0c0400b10341c0b40140036504404801101e0600e02d0860 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 853750872 1250 853749622 853749661
    0x11401150306260613021f050d020a0c020102150c091c0c03111918020a050d0e031c020a0914031615020f0f0a0f0f29060103021809 58
    0x580c2072002d840c00001d1400c5000040503645011107619941c2d04003401703c08001010041d400441da801d0040120440940703840300d0680300d041440c0b41c001454054400c0344d00c4401307120005100c08804108540c0e060104038100103da1503903010b18201501c03641c40c5403040100c1d4600c9006a844046000030010a40114064028001c5400d0390740c2d9040161081e0702880940d44111000c032820103001150302003150644406e0319022400d085000e0b4144020742c06400d6400501c001442005035010083c0507295840303545a000d5515112108040103034030013042440381c2824010f20100410340d910200381c0d8216024004403000c0084120003186c2440a00142012440c860100100300c48078075045180741e5044a03421241241c5c0510107403621059000d2030301203d038000380600c001140324400380c080014000c080d031754044051a42c62030351004408503208074451800d014420040c180301051544031000703090075132078602c8446040003840c240801440c4156503060110310541d0030210043d00d40f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 853752122 1250 853750872 853750889
    0x1030b0306091e03031603090606050d050d12140406090f0b090102090f04060602031c1104030506060f0301140c09012115090e1002070c080618010507030c0503040303091a160908011401150306 84
    0x1200290704100c1e440fa5100c00e0f40d030ec003140c3e920001030322048462003210000d100281904100da120b03540d90f000079002c070310030030f0360b600c0d00d04a8003030042994003650034003c1440c4000140e03100700a000b0720515003030301c8209920862501908002854004c0f04403104490f5403840d10070680c1403c10b40c8001004408600901c00c000414007100308000090b1041c040c1d2811228840362101002c10076099503600960020f08500d5034000c40c10040703c180c0503150810301410300b1090050743c203101d041410902c40c1403569554980000010094200703005101402600d002400780043d10004595100c08600700214071380d900107101e000744015510484050f041c204151100c50400c4c1c0c404100044d40601401441e5180a0100d0390407800780c460b45201078083d0700d0341405e542d102e8034150300429107040c05598a410400001400c4030003040c00d80c0c81824070038030513a04016034200052421070190405140d40c1e24050707803852203941c102d62442c11582c01100c40c404803090701c01e08901411855021039030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 853753372 1250 853752122 853752139
    0xf0905030c07050a0b0c0307020108070309061517010c0f0c021f03061a0c071505090a0303051e0c100b0102070f090b090c0a0804020f01030b0306091e0303160309060605 74
    0x452807012580310300b107a40c02c070b8045484036120341008000384640388124119078002c1064100650080c1074060b885122828005501c0035140c49900c02d48240c06a00c0b0b00c000e00c00c80040c4410414202480341c050b0448c0d00811a03580c40c164040c0c03495000341d100006012020440c20110341e5000c4041d0f9013044001c1d41c0710100700303800301c0150241c0800e004000e804072000f012141c1c0498004183c40c9400d01482c02007240c940341840402803c17005521500800c1000c010720010341c0c445804180045200745c1e1015502c04405031100c1441202840a180081c01004001c8451030001020002c85801c800b00040080000c0e005034902180d80e440741c900d000f1a51000140750b0615800385400c5101503400f40350a40d60003d4100d00340c840c410800020421607000715005d41400c2e15140340c0c144060400190f060148030000e80f0b0517a044460440580c0414038134015241c0e84044001c070b52411500460850901c054140ea01c41c0d030401071002015614030401c001c0c1704140d00440000d28018001d0300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 853754622 1250 853753372 853753387
    0x1e1a0c0d02070804150507050c010e0a050306040f030e06070b060f1207080604020a0f0302240f0403050a0210030e0d1805040f0f050606270301091a0f0108060c0d0f090503 75
    0x104144c00c14841c07100d07242030f400180e00990340180c084501e110360000140c020000c81030b0064076500c0c401c40d082d541040c1000f40120350750310204240e5014901541c0d108803a41c10328030780289440d8440804c9030049200303002c0c01000509400e50300e60005e5003150503503a04058000451050880d01e020110240700d1403200180703038100800d880307015500035210766a031141c0f28004110420801d22000390040100d990720f45000c2524213091f6403040840745c40c149006003c00249415422640065605800100d1080d0031840d040c030039411110401c0c207050001025003c461031725682400012028420000c0f00208030810700b01c1114060440100104603c003d00c01c1d01000800f501c05010354014034040c007003049031a0060540745105609842c20076404201841c01d842c055008904641641d02e0b01d4107500056070110843e049484c40c000b520300b55181401d0103000000c41a400303080d0035007190003846404c843c040225a45c4030820100403880201849196000304401e5102a100d4003020460300d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 853755872 1250 853754622 853754633
    0xc07171b030c1c110a0312050d06081c09050306010b1207021618052a0903030909040f02031204050d080a1b0803011e0506040303030e03160b041e1a0c0d0207 69
    0x90080d0044000407a907402210178491215410700019110440d401100d500c0c080c400c60003000030038941000400c480f0303600d08006181ca011606404c00c65520313440101d00c0254000b403550000c01e0f0890040030294540300b024007903480b0381126840003440714000510494003c102c103409101c0082c0704907984075070310780c07036609008155656030b0092402c180100c1d00b21340004489207462170360140090426280b5521350710180d84042e0901360103000a00031079801d603540c82d46041c4035901442e1b00340c941c505144100741c02d04041c2c20200680c42c2090006200c2d60b142c0c00f02030841d003548120050b9580c0c2400c0e01c05d40b80b5120024030030349514800a450810030012402035412030f842142c10020501d01c440c80360441148034003520750452000e210400201b40320303800407500d45000c0002c0ea0f103016410500c240211a041d5420745003204030200313200810042002d1106500c03001c0c06141d410403100c0d5600b508079040c00c3c603100c2c0220300840104003010071a004450f10100c80103011503455183c1e2400c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 853757122 1250 853755872 853755919
    0x90b1603030507020c091801060e09010f0b0a03050601030222021c1a010c06050709081009050c041107241d0606090105060a030c02070b0f0c07171b030c 67
    0x100c0001c1c1c180404215000e000044a030030b40703003000f401d440d015500d20100040510300741e80c83e1181d0b036403201d0000400421105505016480d00d400100e28500d941d0102c10a031003904111600a480b5000200082000400e0f0141583c0c0d048441c00c0d0640d40112043c400195440b075041c41e5188001501003140c0070011002c030108440540501034101c86a00e400d1080014288290210354842c0d1883c000030f865138030281d440074032814280d203100c0c0c50301003007441c0ca03160004003070000c0d944034014002e008041240e800351035012a002d00c404420158044a103010720f00f002014203c00134213000d001c038015502c0302a4051841d030104005a0091101811800c04061916140c080e80307004c507410381020b03c401c0c0d040cac5030003030400f030710b0000d5a1804900500c00300503190218011481c0c085a082104401050b180d202851000c2c2c4500c03959480c4d9040c510b181d8440d8003a8080c0e541c0e10404080c01080e1001803049020304804016803400101c0d003030810801520360f1001030403002c00012a840c046 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 853758372 1250 853757122 853757167
    0xa03020a180f150909050a05070e07030f05010f03080915032802030106170a09021c0615151b0b01120308010b0f030a0c110601030818030106050d0f03090b 68
    0x2060151060508401d401c44030403011101c0380b43c2c030600e028014800c458000351030482c81a02101d4404c0026103d850034000d80d0b400442c030000841040c8100207a00d4082c01114004203002007150f545003c249210108641c4001809020040303140745490b915000c0c41d0140101140307070942d991030b1124040b80d0041c0454031030602c590341201c000e43d1250651007030f24180c41460301c2da02003400c4100e240020643c0002c3c4500421503d81c0f41d07100050310741541e07550341040c0756106080d240060b407030b1200c02c1c2e40740810320045401201a08009800d04d03400d120100d4046420503c00d03200a0714030300c8220700381040d400740950650400020700c0c00c89031080d1510441c069601d810130382c2d88500440c9000c2c0b0405442080c00c020600114070311090741e9010150041081c201034903030361500d41c0b409081a0090f44199504000843c541841c02d0880781544c01c500b2044008122080c10b010005100c2070300340e00050107600301e08291304200b5019600000260050704d86080c0c54940c907404010340012a0f10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 853759622 1250 853758372 853758419
    0x10221030105120703050c0609032109011b2111070308040f06080106080a021c0c0801030b0c0a0804110402130f0302030106090902061912140610080c12060a03020a 72
    0x700f420351078080b410109903030740702c0d0142961080c14000c0044540003650101d41c18080c0c1c0200180f041c9606c0b502040c1c0443c3c8031030343c03912101d2240024003441580071003247c90000c001030344000078407100d0981141c41c80c500c1e181000a10012002ca408135845909000036200c0c1103804420301807107201030405c4410b030f8403503248800d844082c00c440b07459082c414070021445c1c420218030280762507005440d2036100441d08110011300002c904060f642c4c881000008a0725241c014000d2062140c0c030702e640241038064292920010311030081c11124000e001526141002c0700004403543c4a1301100ca0701d04081008040d00c03610b80d00c1800750042e05100c12407080d0b280500c00559081c050162007030070744d00281601e080481d801e100200754a91000c0c4d440c2040201e100507120905244101d90921a010664219500e842070511100402816031901881030300400c00c0304141018040358520010000860f81980781c00c03011480000f0160002075002c00c2c961008a035110385010000c18141205 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 853760872 1250 853759622 853759639
    0x3060d15091b0603060b1803010b040f02070507080106120209060a030b27120d0f0609020c0a1109160c171216030c080c070312181505070f0c02010221030105 69
    0x460096048900d58894660341c1c000500091502c03c980c4041c01c007034540054000300300000e50100040490740310754551301d533099020850800f4030004000a0000c2c14613040204101800c2c941c00280481d00960b000b0320a04030b04d00003e8032603c49014060007154001d0056900b41010034088900d15082c50000c0b60b035030007840000c901000c000911851031150240d06d170b4a080a00f0701490003405d01c144c00180d10548642000178100403c0c0700600300031a001000d0002c2131380354034012014040d44422144105030344000e03c14811142d9060320010b94040c285543d41d54120700d02900d0b00d044804221642070800709081e04030b5014200c6580c0f05003050101d160010344003d0083d821a10b800d5551400507a00c3c60008078481801c0c001400d05a00034201401c15908a841c08420740302c259401006404000d4040010480c2c03030300d0b071908d502011003810300031454807980041542c61807400c41000c10001031000810340e4000e022500b6410324000c44c0c455045100d0803146025030080c07050b42e0290280 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 853762122 1250 853760872 853760879
    0xa050403080f0f010302010302030406140a200f040909020a031b0510021501060e030a0212150112051c110f0d020d02070e13030203040e1608180303060d15091b 70
    0x10b1030202072107040d1103001141c0303590940c0c0044000307400c001c00031a1120f42d00c03481d180f42a140003004030310034004810082169006454886035040c0c6001e9031240038681404040808500102650140d031592400001e0b21790441c00080c0014415074000340142006040b0404681d03402040e031000d90b0803d40b2515104d4820384012079644e1440100e03402d81401075070041c05078a02c50118000c0c0d882000302201c0c44a400d80c1c000644c0c1000a0b901c090855201892480340c9900c4c4000756801402c00c101400000c40c41070b141c0c41c0d19501d51500d4800384250000f020b843c60381c060000301a82805100031030300740b00347d0310f2402c6a8500c0800c0844015108030f00c003d98841c3c1c40000d45400b1f4070415080e82c04240c4810701c00c1240d00c0d120040c1202540020b100208a00c80b0140c0400d11034400007842c4151080350440140c510343c800b5100852050328911070110702600042200d410150540d4110030700c4000f42005070f03003080c01c02c0c00469424280b010220610900103207140d0400078000840d0382c00c5a4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 853763372 1250 853762122 853762141
    0x1b0914060102100c02010605062701230a1202030901050405010b0609010504032d120906030207031b1b0902040302120c15031902040e0702100e0c040f020706050a05040308 75
    0x104451207401640894182e841680300c0781c01c581900b08403400086480b5485200040940c2c01c200983c0c0d0110882c907500302c0b5200e00b506d0410000e01c10a003003d5130302a00e500c0c1700b8034ac982013a050300c5202c0d500009040725a04d01c10368074940c000c036900b41c04548034208401110301804007510280c03850342c03e1020048052034030030216284560161151031805145582303004800d9004045685035212450502038401c0c1d052400d102003d12604a025136074080c1e10001c0d05108403900a582014414806480081d40201d560b501e402d030191034a683c0c80080b4503210050206047d03207446203584480c80099440100d0300608240c07407080381c070320783c03a52045407115560380d00c1c0c4401584e20600c00c0e48441104240800295007002e10298044c1182c40c40e0320000303082e42d120b0390000181481c031908220a071581800440440896500248991000704d0030040d901ea0840390a20f102d80d981d03000c00304658819504a84074140e00100a10061504003580e0307004140488040d0007290192000480104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 853764622 1250 853763372 853763411
    0x7080a11030d0f0e15160506040311030c06010308090d020a09020c010b1906110f15010f05190e0a090209190506120601150512150a0611030913091b09 66
    0x3241c2da4480072200c0c001130400580d040140000c2116000800100c808070514100d0644040d0003100105035500f081e2034002d1109000c0c44104a05403c103100041c41800042803560442c0c1c1c10018543d03c0e0348020000a0401481d0702000f5480340b103c030800a1240d8417074000e442039071303a841e00030045c0f2038014050002a81c081480309420200b40b404c2486018010040303103141004c21421180c0050a00e45140d103050b40c5089000b42207075903030004014540c0a002d00d400900350949480e1980039a86600c2c1090201602408060038003e00016169048a5005000490700142603410b071341800d84c400302d030800703007105210308542c00c0c000000d1660400d50043c03103051724a140145502d0786001044090420440c0140301044005c022020b2041900c4500a00901103010004001c490040c00c00c1469840b562210090042c9864680100703040402624540c20050300c07c0400c01d05002840b100818035108020400c009208080c0500c550080c00c40742942c844500802000e0501140c284109 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 853765872 1250 853764622 853764647
    0x606040e0a0213090c08013c2f1801050403030903060c09030b01060806100305010f050906030f01020a05030403020c04060b03040f15050a020904150e06010503070207080a11030d 78
    0x99020400a400606085070f002291000341d8100168400180c0c1e200c012064155200e0111603442e000d0100e100387d204621220103810f40d424102080d0b1214118807004031301041c0c0060010b80c2c524016a800c0000314036000c54031840440b9040060740b054201407980c000140604103548403c1c0c18205550244080750b05480d01602ca800160346542d03680800b030305441d5004003c00082007000000505a030008038060030450319440b160b85011010301c0400288000c01c00c00309410172004100350071201154a0a42e08160b9941e00e032550381c40c01003450704052006081d40342d8400203100c1d4003503505c10f02960096109509030b4084d024000200402d640481c058070740e011000b040401e000890405c00d48954038410a213640722000401132030b1044130021103101c5035903500042d603402189131905c07681e0074208041400210740e5040000c003010090000b00341c0c07030502c54000003280100303008003c000024040c0c03100b200ea107104c081c41c0c54610711035441c00060280c40b40c1e9050040950244030390010b071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 853767122 1250 853765872 853765901
    0x40e0319090e0402210a02030703060c120908041412070f030c0b0703020606010305060414040c09180b040219030f0503040303111515060c01050411031219030218061308060604 77
    0x18076040c84174000842c40d80d20554071034403419a01d0b01c01a1400c1c0030442c003c40c02268000307501e00f000100900600014a4000c90706884e14a0400c0080c031101d06841c00d4032a1540d64420300400000821003c0308540851040c6120320078001030115802c0e815030f4240c3c0c2c41201d000c00d05075541c07144018a402100c0004003d0303042040041c460b0351103540282d50240008102003074054000380c2e41003051005940689242c0a5240c091010100c1e6000710741c00c00380c111074003800070400e540310f0b1007136100041c0009100c1c031001d010016003030325403050541c0595001080105c20750034030700d4101c1e40c0c1d81c8244400c40108641c8031b004003a040b03011507290140440201458a40d50726041c0e086440c540b944030590f4401401d0003000134680d402d1003070380d204c1c621581040d56100798010800d840e00d00e50b0f0405150a01e070400024a803095403140c40c0c81041030505016031160803810b0b110b500008000320741070300024045010b86032129410f00d00000c840c1c9010a4902a442d0201403100392840c445a9006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 853768372 1250 853767122 853767139
    0x1103030405031204110d05070806060d0305030604020a030b03120d0b0907020c1201110c06150405012619150f110412050102130f15090e15040e0319090e0402 69
    0x8420008401c10713039202d481015030030315903007840000501100c1966000c0d5040d0740001b400b44000c0300204211074000404682c005281d440640c0e000301070703101c01003640b4090307500882d4004140c1e00940003682c0c5408005c00360340303e00590092909080d00880c008035000f034140130811b0646c1c144040040d005d0406035010303018055002c0148001410240c482210a668a404142d1825010400780c1401d0403541c02801140c10003900c1c4400c800c0040d92a0780c810b0746001c00400040168a07038020040025028071360f100c0600e164020b082c0000c1e5030340746031405406c1e804101000008003a507850100d050a0802c126054420440215540d6212124035184200000d00890a41c900812452885000054a00450442d40303c40324030455000b40b02c18a030140d003e000142c5000810b0116045614020441920b003041610031070002400300403c3c5c88880d1a100001d44440c1c04c100d50700010b01040b2a0707286801c0403c0552101e90712242000076000e9100464154813100e02940510b03002840c968 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 853769622 1250 853768372 853768387
    0xa0e0904080406111f0b0108010b0f0a080a02160602072a140604080f07082103040f1128060206010b030c0a1803030201020d0b0102061009150315060303110303040503 73
    0x11001c1030250b400144034443c004401000020591740310103000201280031841110070800988072900680209440003800d100c1010041011029544214003620345901c054880d04442802880362403a144081369900000c4018889c2c20b030010090300e0300c60007446001c00d20803243c41418032002c0b011074121040c2d80400f0003580035000b00041804000924451030f00d640c03640300520b089210b092310640341d00270442c1080600d1003800141000c1178030010f00000106401030350f0031a4440100014002e041c0a002d160500640c92001407085030b000c0c0480c40124044219441c44000f0308201c1c00c18000d03161004030700948007040301412110f07640301150640d20b804203c03d4158202c0308008040112601c1e0070801e0506030740c0f210700214080d800050fa1241d1200e19441540c14259089040d036108005000b880c000002c0c6000c1118445180042d410140907501c001c804a9980081c22040d10405081180890b0b5070002c0226446a100e101e0050a03560943c3c0c0c50303010446010f0300c1c9402c2440040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 853770872 1250 853769622 853769627
    0xc091302090321091306080d020a0c0501050304080c0316020a090b03070e0406020c1f0513420b0a300606050d031106090613140c0d05030a0e0904080406 67
    0x4400f400d0000f41c440d061004080c0440c01c41031542c0d220080541d02d41c0d4040025002c14040d011300e11410344054510246a511000c11400540c440c4134104040003000034144400d282c1900d68181ca4201540e030b0714211071620201d04000c1d090141c1c42910840300000c0e80107040d104a445101c4040c004e030050610f001c881840d02240104250381c515002c22501d0081c0c00141710b1495142812503540245c84d00b202810300c112500200b64040420351400148041008881e1a44002046000b881c070103928000b11400c0c15094000d0030364000c0032444480c98800100d400508220030140c030034401c02e55803543c20195402588991100058407240d0321590a6030405000807414002c11010070400d9507080400ca902c0a002019000680b48881040340c100050101070b41240700d0b40c00a11080c14040009a103181094000070100400a80040d202c110103212003200703100c00602035606003a150528988a81c0034481e40c8001900c01440502e56180003008240155001000c0a082500b050400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 853772122 1250 853770872 853770913
    0x21509010c271e0815070e030111030a1a1207051e0609060a020a080f041d150609040e030c01140702010213030b091f0c0e0d0b040b0408120c0913020903 67
    0xb80699400240b1004c580950208190301141142115150052410714002050a49100c060510a0741413110510707400961605907070700184a418005105c0c40440d101c560703e61201e840c0190051084a40c4054814001c0b8600e421a0000d45004a100c01c6001d03884088048410344554041e6042c0824500b034102180070f0040c80600e4011640a10700c1511110459001561206607600000505102d0700c0c1030311072070741a0460f0700328011810b03040410508085894092125000740c8010800d095035a4880d0085a8500304c040296a610703d001003195020300300800c1189050502803021580140c414802c0b40c1480c0e42090091501da811a61a4000c40d400a0300b441c43e1446601c1c142803480035207803554001c6900308840002e84511407003019010001c40668244100c0c02c061640004c036900d00080e5a10a502c44000380c6941d0b9245410a01130051004004c154030541c1c3c10000541050001071001d820211085202c01c110100300100f41d01c90310010a805400c100c0c503040c0100210711700c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 853773372 1250 853772122 853772159
    0xd050c07030b01080c130b0a0905090718020c0705010c050c060f22080c1503061009081b150c0d0f0509040c21111801021509010c27 58
    0x80d21200d96a0340c50b03424041100781c10140c66a040000840d60702d01d801c514106520180000174051901050000354880200b441a0380780c46848100180244a040c8907a0b4080c00b0014043c900c410f54510f2105d00941054608192307502c142c17040415698000c10001c01c469a0100040012983c4041800030907080a01d141050b6034050003040220320606204001c0c0a1110550030a514030b0030340da561509048031203030381c06440c0040311200d441c51003008403940444281c031812103107160a00b080700c850f04540d010003010b02814042c9004029603604800d070812045609181c0030310f204c1c0c20070f42c7e58480c592030b8449a03440300061004981c0070b11203240241220307040c12801c203014400032400f0b8440b011014800207490513100400e007421346c48521103030000b021080090014100c1d082440d84507013102d4002000104001c112168800c00c01c1007050500686811107030b0608030207d60282c0358200030480824001e400310142294a01842d0200ec559000d6590034a8a0000319004070000d101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 853774622 1250 853773372 853773397
    0xf0f021206310207060b04050403120f0b0a1403190b010305071d0f070918020706050c0a09030206031f0e070e010804020a121506060215150d12030e0106180b0607050d05 74
    0x601c06d00c03540e841c840c02c0c0c86280241c41e4650107000c81074aa070216181d401e100d03494985000304013180ba1300c0c1e007079100c802d88054040192415101a001902d80746030b200891080c40740840b564410407807081c900034104c2c0d1041085440c959203440b8800004900180d80d0714090b2461000900d1000c40b540c0140e820070401d0802180c1261101400060a050301ca00c0084081d000034800c410401c0f2417160b01c4d4090484d0f003180b810300e140c403000104038462900c030103445408003002050480403c080c200d00c440018400b42d0198960391b0a118000010407200d040c04104000c88416155006000f072a110b594020100704c40305043c2011842050400071044d110210404aa290300549900c80e074800b0b4800c076001014889605c1314800c16050005207200807500c1e50880564058807101c0042c443c561f403005a400b400c03000380c03101310001c00e8450080905982042d60010349425041207122220000c1c0005106000c401410301c0030500c42e090006105510000c4904004c034842c501601c20200380300c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 853775872 1250 853774622 853774631
    0x110d1b030b01080f062128020a05040507110d0f0906020105040308010504050c160b060f100c030e040e100b01080709180e0a1a0121030509040f0f02120631020706 71
    0x506c86081c0f00440701948124503809684d00b100320582c01c03034500c8140b1341142004450710249901144007000307148034003405a80c40d10b004c1026580101c48094103c1030340c00c11281c440105100050002c140f40c05140041748241a0101d402841070092a03c42c94040d1607440c1964603000c184001440c0c01006591101002d000580114507104000b0705a02d028010518003814400100b040801140c42298842d0b401035150b0300c030b8103400128030700019400d41000b8a41000b44004200580740c0010340d0b80d414014801a541c10040f1680144000d400c2aa1010f0304c2d50b503000d4050b0788885982c0148a25055150022060b01c01c03a500004201e00350b65065581010540d603e4004024590a00b01111801040180000c03070300303d1860141040c64031010111071809440103800c42c421182420b0041d510352140714030700350550b0031403c02e444030201d045545200b0000f0082d0441c2c015161284101202511001c02400a28011819035104075071940f0083c02e01030380a0003548200301c00c0355250340384e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 853776978 1106 853775872 853775899
    0x60503060115050c070512030a02010c0504120213020706051014030c060403231b010e03010b060a180306020a05220e0c0a03110d1b030b01080f06 64
    0xb40c20516034800e180341c0c42c0340c101409074200e503410880b05d9080519072000040140000840c4c1c0d4000c100252103c2812500c40c40399115000001a18424030030261810701e0010080303003481c039070052030302a00e5074071002990411034440d210003154110800c00d10841074103940000b1011070280000b8058500003070418003c50002a1145001c0407588000001103142c210b04606c142c3c1c102c55074498078030501080b1102c0140720b00d0001d60b05100c0b5503001c0c28140100141490020000382c00c1107040e8104480000104802080d03c0078100c2c40000490251b2001303064070241c61b44d4140d80c0d2445410003244c40d010020310301c0c0002c85192400c003d0000c5610f0840d03005040303203440319a5550240c40c1100540000c100c04911010b00103076150b010840f9a200a0b481d000c144e142022100f81110294115000c0c4e00303100740405c51000c0010340f200203042c00b040c0c0c042001030101080042 = true := by decide +kernel

theorem cover : BRFrame.Cov 853597122 853776978 := by
  have h0 := BRFrame.cov_init 853597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 853597122 ≤ n) (h2 : n < 853776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
