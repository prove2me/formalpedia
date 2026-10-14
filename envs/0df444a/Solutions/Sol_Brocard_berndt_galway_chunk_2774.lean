-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2774
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:26.081287+00:00
-- url     : https://prove2.me/submissions/e89c581c-b51a-4f4c-a6a2-f0c2b6bed8f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 498741007 ≤ n < 498920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 498742257 1250 498741007 498741011
    0x1c052401230c0c180114130204090e0f0c030a020303030a0f0e030c0106050310061805060102070b0a03140c040e010b03220b0603011a2103090301020a080702252c0a 72
    0x1e85944c10404c400703103850f0b001c100c0038050313541c54450a25000c2c0105030000b846071404e0511003110103100d40548000d001032000030420003110b146a1a44c0704e8000210000c203010301c004000484c83c010908501d0184c02502851a42e07803544000c20060624580004403142c0d5180d50450200302080540406101c100000503118140401c141c0350031080041c1d50090b6040c19820700c4400f0300c907005011f0f0200540c0d400704082d00d0720320041c1e00340707901d42e003003140b480c0c0010541a84c0264960049410441e051900c50320a407036590000c43c5d01d20950180205100c00e0000401c48005480001c681c40322a800000b00000c00300e2480c0420400030060583c0c42500d070303c051110919082c450401c419848040030350318900740300c020580c140410310403100070010890304403050740c4040c0100d51820400038003c65460200100160035410240c0707400b0700602c1400d12440c1301d071754071422210389e5007000a040d51000d0f04d00041390b660400c420180c0c0101e505c0d40300007003070080742d41e0000324001d4a0754100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 498743507 1250 498742257 498742273
    0xa0b061c021b0d12110a0e030c06030c040f090c020a030c0302010e0d0f18080714010212040e070f0f0804062c011a0303040312051605031c052401230c 66
    0x4002d01d424130020a01002c50f150407000c080c5009040c0403a00c5004060a01102c800c01c03190000c1e090288641c41d490f0404800002c100300d19414200800594401c100c1c0030301a2901d820b415412600d041c02001c0c05644090044808070b8010303041200440d01c03d100102d030104c0000610f0f03041000c144186000300d0305c07680040b40c06c1500402c41441c0f6000740e411400700140341400481c0d80c5c0065118a00c40140c604854a80700c0e4428064954400c040d4040d466545a503519480d181003012078040d800211204907410700300e0300ca48012148400c3d15510f00740b4035111526010b00034182c441e03a950312021490503502d0120314541c4060b9801d2a01400010f0b40411840c03084006000d9548480c86500100014000105440351011030300d410b13444d15940b01c04000104001039100703000c000c1c0541c403011402d00c0391491808017031680c48001d0340f0240280c1e00e842000e5149544d02a034540d144911440d80c003e840d5103e01600c000e02c920810a002d400e08155030400c0300c40d488907110700365540000396 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 498744757 1250 498743507 498743533
    0x905070b040620010507090605180a0b070501062c0a0e0f060103051b13050c040305120c100e060a0507201b03030a05120406020f04090b090a0b061c021b 67
    0x74040c101c00f11500d000340400d1521680042400409000d880140134010400030380d244043d4041c8080340038050501048a030300c0305888040d507044040115815030801d0004601160894219003500c10840d0072800480d5803142d004083c5c190007001280e2a0790f4406140c12400380401411000000d10b00c0501a00d5046060881c2404282860340c0c0440810920800d950349441c00e11102e0080600e4000529848250301c04045108507403002d4454801c18111040f003200100050604602c040c00700e03107080000003010003e4440e1540e034001c4642203400007820041d0ba0f0340205501510341c0c03401c80004140c510450f900340f148a00448155800944016511012001c0a1040800843c000c42c01c09483c0c000c01006031050700ca80c104000001400b181c200201758040d110100244445103440d04c0d21160202c008114a1707400318442c1d075081c40864183c84492049421121001d040e1038600b01c88281d162000340301485940540c25403c100000c0d0048458182d4085c0b440084003802d4031181c500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 498746007 1250 498744757 498744797
    0x301030f14030309030d09020a03080f032401090302041a1302070b0f060303031605070b160e010c02060306220606020304050112020a0816020109120f02070b0705030307030905070b0406 81
    0x207420791180c1d8401c000b40050a5000000c0d290001a070641c013140d2400c01d0300c0410b08021903a88002d00c0c00d44080f80d220100851200514400c01030881c42a01d0203654000403c06011003101c05404225000014005070419401c06101c18041d01901e0400142c103401050082400000e00c900c3d599010401c81c04110310b28494507041196800144811708103c00001d0300ca1201510001140340b00c041d00d4a00c2a006000350742c5c40325000018401c42c1d2400c0700083e0031040c001d606c0c0200182c816482c030740c030710f43c041d22181d803420743c01a01242c150740d5030781c4c1480341c006031501242d0801c032910000e1200d5442c9600803074010f0005607000e1030320f0fa4900400075101800c20500001120300501c00242d8480c4e0000000e544050082d5128000002c0540300381e00400401d00c0261040c040706100e001030503000800300d03040b000baa600b01c0d1410799441503003200c40c1c024560300510a820400c0810501c80c403d412a603203442c09602500d003081c4c1d5400c000c503000d5020385e0004021070940701c01c141d2015420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 498747257 1250 498746007 498746033
    0x50a0b1f0e0f09010b130e0403020601051002210a0201021b0102090f09090a03030902130f0b0a0602030a05160320010f060e04020d06052e080f0106081f020f0301030f 73
    0x945184000d2140c90000440d41081401081903020780811048400c1280346c506030001d02801d11658103c3c00d09040094481909004160090618074100f521051000036a00f02c1200454a1005c0c4044200c20703d92070355100300101402c5640a21944010407951204c42000c403010000040c1e480d59414240700301411080301d05072150b1708580412902101c013043d6035811903450f15001a00c00c5551000807190001c8040b0581d03594076180d615007500040ba0302c9840a5001107401c00c41165607060101e907031707119814540d40001c000388540302c0383d5401119103905281c400c0c00d007a540e003d05a8420b4014411940221120313070f44031241304030b004c0040c1c03103240090106101d0102c45440c0c40d070085a61008125401001550369500042d81d088200403440811446154512082065032541004501840c024802d0720300a5005100010700c0510400e002c49840c00c002e0b1a507000d10918141c0d0b080b58000c85500520740811442c08251801d100660103144980305085080c10542400001c1d0391007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 498748507 1250 498747257 498747259
    0xc0604080f101b0309031701030f05010e01020306030709110405030f21090f010503131202010209040f09020a0315060803040b0318060702030412081e1b070302090109050a0b1f0e 78
    0x14095583c602d0403808030441c1c200c849281404500c001c03c42c07070102d80301403284401c185010216400071080069401c5154402030148002b80007100d5a4000c0500701c0c8030036103142d64035078440c12040003030214680101681000000d00d20381403e60b500042410182000c24151841d04588413072120307000700350815400d01d26011001410020700e100840c05031940c46504034140100403001600790071340d01d02220307500c40c0e00010f242401801644080d000c1d4100004880c812818030603d400311001c5442103030720054000f00418001ca00d10303102d8400b01d00309418407102d403d44800c0c011a16100c00c00080000703001c6e000205a980c81c200e6518041600d040c40103c550b81c10040600078000c0d4000b041d0780c1620710411101c0f50300034051500302c51500c9036000c084001108040d0802e2400300700d80141820200805592a100311000035489c0c4400c06400000c0d40080d40b0b40051042040540c00700740c0c440082e010010b0080c003a000020130006962641100e01d1a616403074010b056408402c104032100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 498749757 1250 498748507 498748511
    0x304120e010f030e0c0d050303060a170c1203210103031b0321020d0e01060608090f0706030c09050418060e2b0203040f090605090c030f180c0604080f10 67
    0x112500002d115866000b0010105900d6825280324034605101d03003070788402d000f000e200c00800a440e0541c2c41e0307002101e4440c0b00303004581000583c5ca0704840c1d030240d2011018050000d680c505001c1110309010f24040651a100601c0401c000c4036a486051009a82644c142074007585945402080302444400c0c014031522410782c8400040d8010f40a0803007141c90454180d04d914281c1140c40c020701901c03c0000000e400c040c1100c1107108190b0240b42034989580d02c03501d9540d100340c02c40d56550310416004101c0c3c0d109100030401c0c907201b5840400c00e4201c40ca400c060b040d640f02c00040545228030003156441ca2010911b0040046a205075182ca2031100d0141030141c880c04000c903450540a00c0c41d015419071280c840c206144240b044030b000d00140005a85099207036040ea10040019001e071500941014020496800206055a1080700e80100b800e007140c0c0c456400d00100400d1a48180c140c2c415002100c0d603a945500282001d454024001c202611100d10300b0b600e02080c1000c5404298 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 498751007 1250 498749757 498749777
    0x40e0a020f07021210020f030603060a0c0f0503070315230907020a020d0c030506280911010318080309011e0501030b06010c03110604150e0c0109120303090b040305030412 75
    0x924802030b5034825404660f140c0130310b03094a036014107014001600c000c885200203036241030210f00a0242d40a51300540c112002556001000740c11904800801c80c04501e00507050342c1440d10030320045d580108107160101d0aa00c86d429075006c01030a83c1c1000c01c030502c0d50000591040740048101c1c1c40c1c83d104403a40e10660a000d02e003e500d8009900000e4020040d14200c1c0f010710100090381e4004560141c22101545001610b20a544040318500d00010201c0b0709404641c6045008181102307400880f804080d0480000640003041600441d0000038009260301010412003400380d0702c241c10314030002c246101c420b0804500c3c3c4296074500504d0074580001031020038400710302075600007003c1c00c2c00354803a946410191083e170150485180b461094904000400071811018813401d00c0c80d000034024a01ca1454071070b100e06681000c9800501c80c802c0401441c05100c40c1c41002d81d01a04002680401d0303900e4a0016107030455058002c510000300b4441001401500c441d05070340c02d0300d8260005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 498752257 1250 498751007 498751027
    0x30307030c0323160f0b090a050f011112060d060606200723190f030b0919110d0803041b0b0a1b170705061008010908040905090a021203040e0a02 64
    0xa004204200c0341d0719041e55400c000300f144c5d420321504443d0b046942010b003894141626580c03600745140407036040c02040018610003405005241c0751402803810b003030a00e0004080f1030001d01c4003c000c01c0d8803e005074194004200340344280f070013604056807100c1c42100c00025031110000359000f00085644020810000040604289060380c98401c0401d407a0303501003400540325032213001e001d1343c1702d00c100707840003800104507603481d42140e02c01c40c80003000e503581c1c032807064884c5401c1448001903049041c80c3c000091482c0c54a006442c0000d02c40c910901c0300d0348a4030001d80080b40c0c2110718114030310b5800c1c00c1e03e4039891044020500412400d02e4000380180080c0051101301e01540141405400f10701000380a810f08070b000035007207040b01c0d00ca00a60074001c0da5584140d03195061280700540200f04a18103004d81854243c00c40c0700742c1d1030303d8508042d040007404020300ca162230b07024100c03100006954000305660b800780c030b0740001c40e140c0d400c03d130303400d8031090000c1d06400030584108461402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 498753507 1250 498752257 498752327
    0x507030b0604051c020406081902150414091009020408031b010912030207060f0f051501090b07080f040806011214070302010804060b0411030c04030309050303120c0a0e030307030c03 80
    0x1650640300305200c01c4c102d50f1000c10050051038102c450a40160020308100d2005600721929542c022901040d032102c081d6920200c0e4802d5000311034100340301d481e048400341421414107070068140c0b80702422007030380c032071105080307807c1900643d03002d80000451803244161602c0c0700c45600d4500d0000c000b0700295594291001103901080028590042081002d0100a50110307201c1031003071030140541e000a18206d0002c000840b80104081c0e580e003507000c51540b0600f0003106851684038642d252140903100e007151604886129a0b214404000100e1030300130134040c0341c2c0245060110305950028600e00b0054018001300700385505c1d8840d80c000c00141c1c2c0e12200440e0441e0308103500040e4a0040f001040c09400c190310454015400001441111203d2000803c226030003580e50044458650703007015228443c80480ba2010610840401c08048400c001005801440e050903041c81d9282e00200c0c0c203607000750a0940105003a00705845c24190403000341c0c0e0581c500c0080120070208401041c00c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 498754757 1250 498753507 498753529
    0x11103071d1009030312060812070203030915091f050d0c03090c03110f01020609030a0e120d05030a050c0c1005070203040506030114041b09150c12030507030b060405 73
    0x8108140007040310070440c104020400c1140070b0039000791000a6400036001200e035100c11000104440c540d03074102c041070b20504069800e080c0141100134581c0d866100c940c2c10009041c4da05000410582ca030680e1b076403c031603691020101180740c440d110107041103010506024044410406035014250556200003241c030400400c071400611404c007404200c0041201100c01442441100c3c40401030013000107248141c0740c0229418400c50203010012600c0d8036082d5070254141e0700521070681d0060158850210600c0041c11903032044035601c14003894428807081c010041038000090100316100c1340106684004c1c0d441c2d40c0d5140a440306030780c60395203c241c02944540307039842002c140294424030464004007002080c04e0f440c1d5868801c003140382c252209400c0c2c0700320710300b46514014001c105600c01c031811080e00d511484501e00700201030040c0b5011094001c0010005c0008001002c11502d1403065070141c1c0c0000b40c9180011000d81105d41800a86100f00c5050000b081982e480c02c0500e5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 498756007 1250 498754757 498754771
    0xf05011703070c06140c0d18080706050d05090c030303150a06080601021e03160606050405090601030201121a060c0102070b0f10061b0c08030a0e090f0403030203130203250503011103 80
    0x468140c03661129591b0181c2d484408950144000d80d00e0965886040d01055405548106100f650788042071076036407010b80302d8200031910034000090f003181c69512956002c12480160740004106100123401c40d84101d81112135008108680c5415042c5507922601602450500701c4040c108100081d43d95204034a014055560f08040584981ca007441035401400c03400301c08000d009110b182040c0582964041c0381d020f98030700000075005440c0040d0041c100ca406844882184000b45d01c20740c003a010030506001c228841c00d120084035140c0d0402013010b28201400140c4650403460a507405110141880c2c060102400070320110010710a25072040712103c1c10f005140d100360004102c86001078941c0030b0140c3c0c48101000400001c00700091180f1592641d81c407003401c10400800c1020007003a1081c02c0d10006840003d800240280d0040d904415440c0e50f900c1100301360342c0041d107060161000031188001e03080c2d80c2154800c051031454042c181c114003d10a0108000d03820941d400010102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 498757257 1250 498756007 498756017
    0x30f08010f06171009111b060f0c130f0e01050316030510020a02160303020304030b0a02181e090103150b030303090606010e010903060c0216080f0d210f05011703070c06 74
    0xc9440a44d000744c070700c0c00615004001340310300b010020010340030350415981584910f003100540c00802c00045807c0b4401c450b5440030f8040b548604190002c0ea4001440c01c402012800c040450414819180b110050191008800d42ca42c1044145410054149c94404040b03040030014000a81c0c0480c03440711003e2012030040c0c6569080d10f04920300364003201d440d0081e00b81e100000c000d140d4044000c2003628051660303c000c64449000910481c07092407070068071884800301110380c0e807034003a000090b8004c03075101001c2e2a11842000400c0e000c001e034002c5918003811200d54540d650280103410100c0b008078061030a500c0c0ca1680280c41e01c1e0010600f504001c10345031280480da00800e5040040c6030000002c004008804001079915980020700c0c14000c020690001064240050824942c490400203001e0f9408920801d85104011450409210300c034020b42040783d180702d12075420380c030149000204880d454410b0040c050304072001c00351403a0b0420030401d404554841d0344c80080301d009140c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 498758507 1250 498757257 498757261
    0x260402150d020d14060a0602031207110d030b010807030c080135100b0d240f020708040f1d070507050a0212250f0608130f030f08010f0617 61
    0x1100035a01c01d62000300c80c0a803001c900b103a400100d65101c0101060005124603da8036081e003085600c10380fa00c03c0b0750050b44200700e00c0e046801c0901042e070300646d0700c0c242101034004085183e4282107260101100080e0384d510300004a69202003130b1904910310b42010840c084402c54000e0040b201409101d074102090888132841d000ba0381e0440d5100c1c03281458450181c80c505090944858942c000d000c1c4131410035041c4400352401000c900f0442c3d070b1040b40618840b5603a080d0742d4007401581815608035940c1d40c0884140304640c0000d100403840303400d10719034580c00c0070040e1903030341819044403403004841d90203202146081c0010319040410b07800c2060322040f1320b240081c80d00c1407140009401911010012200362030000c1ca000c0380d03100068940d9480c90400c4464006e00300184100b10741918507000812400e40195400c2e90060404855102d8007980c94454406d98114414103d000880614660200e0b0354816003007409006121001d0742442d01c3e08800034184480341d840c540f40e0f00140c0300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 498759757 1250 498758507 498758539
    0x1b0609050a06050705042310030504020406051012060f262404120e06030621060103080c0709021e030612060711390105130e0403260402 60
    0x1110540341c03036015500340001d1901e40c00c0203001e600144581014010801035005565040b01c1d0b0201d051032028000c405003000c0300c00308902070003000d04141c0e0484d40d151804105501daa400d0781030310343d840c0d49030b5640046240454030708444007640f00304040400321200f84017020005858070701140ca42d18100e40c5607007048000c035061096021f00024141c1054545000c07007411425098842c5000304007140024207862001d40341000d5071401503600220401c0001d24500c6d0400b903c0e101032060f840c0075040801d0442808d403820000b0b030420b4400d224007040e400446202004031402802e0b00180070340c14602c26104c04501d44e1a12112403c0c007102c040b00164080c1c450903610b01d420fa41000880da4a81000c100181400d00701c10f01c0d0580c140103034441002200c0080c1d4070b04024a510581510104480700e0501031131254964080c0c1c10003000b0440110812104106c16015000007280362501d0b0030145405044a030342e5182e4003000e417003503000e92141c0780b0002584039481034040e40d4015268000c04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 498761007 1250 498759757 498759763
    0x1c0c050105211e070309210e12010f150e0115110307140d0e180a02121f12030203090910050301090c0905010911030a0209010c060501241b060905 64
    0x1403204040c6840e901d0030894807001081c1100e43c0e1010b4409a100c0703580300c100040b400c0d03c5c015880074101c0e000c07407804104030310104482218065101d10700445089401000944c1c1d901c6d82d175040d29900c3e91216100e41040e0524401d00d0550f03a0500601f0030282c1c0380c0528201d06010504c5007441d01e5004110044006003e01860124958000c09483e903801151078644814600c140854006100380444641a1030144d41c151641800c02050385071000100c000d00130400400030132901c8451303000e000b440048425070031014000e1000c00c1401c04010700c4212031000e4070b0071503401211504030b1600e000d800b198021044404500095608a956540da10380d0180f060b16250701141d0558070b03102e02181401000e24109040d141010001d02560742e9903607543c801d81d541101c0000344600f0400c046030b81260a03500420016206042c8080c8041c0e00380c9501d82210026400440080050000c03200050a007107260229541c95052045441c3c00b2216005000d0242c0000140642c3d544c00046062080c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 498762257 1250 498761007 498761047
    0x70c0b091203070f03050f101202060d0e0604050f0d080f091f0209150906030c1806031005010e0406030507150c05250e0402131a030a03020c1c0c050105 67
    0x5841c603540d881c01c02c802c00034858000d04480400080c0350401082c4a90800c00c40c0a0140001c81090b2151501701040442c45021540080707a2100c1c0400180031810010b00862881c00031620150140f0f18160801c94181682c01c01c0d400c6207500400304498402c1d80011980340c01c41a44452400c0b142c1e605480d161034040d4203d612084800c2c9800c204042042c95001021107082c20703140c41c81201c603000d03050394841c010210f00d035512007010f10018440c00a0314018080554490a881040e141540045003041c0d0059841e9240c80070200010720155030000610f2107001070039182000514a15102e164444c6902d0042e56010340c400780002c83c1940c4212200300300a034000c02a1b401900c501a661210303000b45220100c03010821101c0003038400380030741525210341d0300542001082e00309882c4182c020007074111b0300c0000d0165411a107140d614104482e000440c801d40042c0b40303100f0588101b001251035068120f07001d005a24030000000c030140420030490340c00382085078442040d0f80d2a03460022903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 498763507 1250 498762257 498762283
    0x1022d0d020d1e1a090906180307060207060b15070210030c1103041508070207290f0a2a0305090904020105090d120807301806050108070e070c0b09 65
    0x4683c0360319800c0c046640005552114500200b15001c00c0ca41408221041241e4105090f002000011451001d2001404034a0042c1c42a0b034603000c0c5954a0304100e80003580b040d143c0d96560340e0060420708052000303641c0841d0450100e03003007002c41d600003803291503003d038650100758a9424290b01280142015540c0da94202e0980703031a01e441d016081c48400d00800a00001018400031a9444d03001003048030a490440c0107038001e072642d00c0000107680740b14990704030b24600c040040d4484a0705640c05044a1605666544115015080700a006511428450301c00c90300340300150340000c0e00082222450081500d1820706951a40016282d5014074600c840e000001041c10004102107480041107102050f112044280c40d590021510502d4000e4800380c00c803c840184d122040310013111800c101421800400c1d4008600e800140c0c20501400894541c1d44540043c001c108040c0303c480e01400094000104901d00524000d0800c00f2400d00a44035101520104400a501740102c0c018035403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 498764757 1250 498763507 498763541
    0x90b04080a1e08041e180507030f0b01020312040c0e010e07020f03040f0b030a1d0a0201021c0f050d090501060605030919020120071701022d0d020d 65
    0x59140a0151500c0034403038101c1c2c000c1010079103210b0341c031050301142d000c4680040c1d100f41080d0030084c00301220b0541240307981102644080009038034540320f003200b880003400034001c205405c200c2000390903907000e02c20800809003020f42400c81640c0c0001542e0103071800f000701c026962120305010140f900c0e070b500300c2c08c07180d0140e40022030f0208a0f50043e50080000d075080b2450801c548264907240d0003180500c501c891242c06040000b0181c130030103981c00071a2401c0010b4007160203c0440f40341e065030002c10001e5045007a4060540da01400510b5548202c0355800181c1212043d00400c2448402c9206080c01004140746060303400c164003040216038044000c1091544446015145404c02c032250030f02489000060705189150700d10122010b507040c0c664800d1082c41907900200707001e403411070707084603c1403a00018100c40000303a2012549011700005a42c0e5031500c0742e2049401039040c02440e240c1160010200d80d003c64812035605048201d00161608085200c01000d08180f0351307152034141c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 498766007 1250 498764757 498764759
    0x30703060509070b0415050306130f0c110610061b050a05160b070b06010f1b0c0e1e0406020724050f011706062b030c05060703060b0712090b04 63
    0x1800c0c0d481240201c0501040780da0389995403494081c9032145018044400c0040740501185e24081d00285401031030040110408015008454086400c204412200951a12800c44c4c445410944401036141d41e034019000c5031a00781002c00c141e95182c490481041103400c50a400a9404148030b80d4460f402400c0c1c2d840c1e140c0ca8100242e8600b070007c0160300e100c882140005d41c900704c0d0011210260303845482d94a066946600558200900030042c40500c150050000e0050603084422805a44a48640a092403d00300903c5d2229001000c00310801180c0c0c40040c1e4549030107400d1503009500580169031000b8618004400780c0c0300c070340814401e104007201003d2210f030380e03040030b032145162102ea082960fa0703030091010011131088981019800100208800d030138032800e44520000038030040000205083c4860344005008802a030010304050002c40c204541446515004142450700b40000c41c1041c41100d0103106115000f81040b001118481d0114041d071042c4c001841003c07440c54840e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 498767257 1250 498766007 498766013
    0x403050303010509071e0f1e1706040621020d06180203010e2806021225020d090b03040309170f010609090c03121e1106092a0f030703 59
    0x80e410030300a0030321819a06000031402c510074460200340b21101240003949070403481c004c0e14242a152851f0080040c11031074800703120010300d400480300100e41d80d0601c0209105032a45201c60000d07013024429400e01c1c004003e00100000950884018226002c60520309840029080800070764020074650810048155080c2440c6174400c040d8001d90091100c902d0000001c4e464500c0d8968100200740b404d50290804010142c0049d0312920500d0018900a00300050301d8219808944001d1041e12a540341005840315181e6802c1503045400105540c001030240682440d4150194148a074001320000d001e061251400d60b004001100710039590110140710320b525800b00bc81052031940c00c2000c0094011654441c3d141901d8000646408407030843d95810300c0d1010358021038041118003815100b10700441445840000c1003519110741c0d07a00400002e80c1040030081105245030050781c502ca901c1812000d0500d0740030b41c1d50888200c018540d1001500c4882d0b100e48030390705440782041c08820 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 498768507 1250 498767257 498767263
    0x18150d050f04050d020109120f05070c0305030403021e0a0303080a0f1b02210a110a05101509090b061314010e0702070e040c06030f091b0303030612050c09060f06040305 74
    0x80c82c083d00c1a00c100c01d2850380d01740e00381c45400d40014448840440054207040c41502d03c8041e150040c901113103410341d281c4410341d147e192a0425a0107410000f820002c52818031249149001c9441810000e02c901d034000451581052001609005000c00001c686c40001d03803050240c001800300820100340c3c034804c004402450b60700007070054032646014450010303c00240008039540c4007151854100c81840403103403495080e510071050300c1000590400170384203100000340454251400902003000e11040e2100000c9a80603030360013494409a00041040e268542d60301a0b81a40c10660180c03403901c1c001c00504441c8407041480e2000300c008680c450418081501800c0e80364215018140c5410340000c420b00c00351801041c6010310300e01006040e00a8224940c0d203480040002200015038551325002d84084a0703041d251402d10000f4000c0640510940b8054a10750010711000350702c0d5a60281c1d5020407282a9216010540004050351740c2c10421000e49103003c0e0400c0e4803295603160103a5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 498769757 1250 498768507 498768511
    0x204020712120b0a0f1e0b0a050d0b010f021b121e070905060d061a0d0510060e190b030703050a032d05040b03060d0606080d0306090218150d050f 64
    0x1c81c505045070b0039044e1030703c0041ca07015918500f60710105903240189015034203546d03074000700094160381c80014000401001801c0d110840d61906551000f0200141044910200712281032015800059040503400250460b509040007480c500507543c13400094451001c04009985520401180d1542242d0740034144000f10322281c02c54041039100d201020545104980003600f0444540004002c2082e075003066051080c01c866511200381e0324404184244800101070700c00e940710002d1785c4290000c900c94a001061650400041420088411100924065041142c80d500c0701c20f4250035542c2030000390700442d44201220304483e81890080c0006040101c0120361801101d03008034003008a450084100040795900c92030141000320b0300d4619040600742e0b541240300c000070100010010711840c2c3c050400f0b803000701083c1078503450040540c0d1440e0400300c415401404020310140c210514848060801c6940c400584002c0e444408039000b20704e44a42950305000a0125000441e8a068 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 498771007 1250 498769757 498769787
    0xc1e020a031b08220905010b0a0f08010608150312040e040b07030c0e092502060109060b040f0e0601022509050603010b01020d110304031416060c0f03030203040204020712 75
    0x420300b904240321400c1907146040014100725000c0204002c414841358400002103490344c08682d00d2500d0380150000c907902604140c0f161280011901c4449030810701d01f10141c42e49142c000030540c18072000604070880644541c0000d601c50980200e03540c0d040c001c200f241d0325141c40b02922a40e4888054030072010645044e102990324602180c5058400d010fa184401c095403580d82c071410802c02031102440300101000f07901c80c039040f4101c0c0b00b03002c04c1c3c0c8400b44500300d030b0380100381d15418480298120752460780220040c150070001000042c00700301d0b91100f113401c055070301031043ea62600140c1c00c04594070b810a840038056042910380421250080c4252540000100540d540d42030a05080b035181a00003800360b841040d00707114039889800c1d190403841c106015282040d03036907030310503090364041495560981c003c114518900034041506000400503071510721541100c03a00c480a43d108494400307810150000000360564840c0d0301120342c102e501c403c02c40312030380810400030b11114002d0008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 498772257 1250 498771007 498771017
    0x301050103060f290705010203040b060324191d010905010b0103050c1c0b040c020c030f0312180a080a0c020918100515040e06071b080306040c1e020a03 67
    0xc2811400c0caa060421364403001e011a1031403003071020b03410184101160b00b4500388800c000c102c0001d8401e0002d180290302c1104040f055040c60b104260520560b1b01900031b0b41c0c146485c075103285c08444c1d1511a009008040f1115112280148050240c503100043c240a41048480b441e1000c00541c010080c031400390008001010f490b100440683c2c3e802d035120000c0d00418403c042c1c481b2544c034482c11940c465210000340090304140410182c62031040c0c035402603082030124540307a0034207201315500c40400c24007940c41e2426241014100c0031001d4081c0008000da0080c15071700700410800301e03078450741141c0a1a00d4044060300140008501c07c0100d00500580c03010880c14078110b40f0303004448480341e002e040c1e062038a40d00d030002000002c10000d01c2030012641c01801d40c60b140f080006d41e41310040500380c286031500000d424414841119440c0354101e00c40c04002c43c0546043e6038200b00304803004291029103040845a21804440100200b01004140701c402e607000620f0703c0a0500c0382d141c3d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 498773507 1250 498772257 498772259
    0x6170703030909021303081c05010b040f08060601021f180803010819051e0a020a0b030709080a02060703080403050904150807050a12081c06060207060e06070f0b060a03080f030105010306 82
    0x1150280c5c014034041d20140b2490380f100780001030f10200600b60295500382c40702c2e005d070b410807a643c003034031400c0e4080c0844040004041c0200c0180c0c1c8048005040264020074850610500003945c2e19490001c40460003000c4040c00d00f0a00c081d00f02a100103a0081e0807800081c950426034482d0b8401e00c6072040c0d51185000044c585540f03003180c0c240035900030024040144d441440ea856011414004005901510b601d400040c1e503600c001c01c0140507501d01702a120720782401c016243e000030f5040154143c0c000381d113444c010313030340c64046414560b407514201c8002e8440c1c2c5010748143c01980b5281d90b010341086440c1a010084070241c000700e542c800211034075159110705002c1c1c441514041d4084d407556003280c140c04100254020a080c04080300e0b000c00054a921000c8201c0d51075401c00c000580180c10700f0003a9aa2029076220401800c4401c3c528110450344e451052048000d0002c003020100b00020f48640e80d9070300840300454100d080e0790340c2c8030300d042d19440450307200f401805e0100c2d00d4000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 498774757 1250 498773507 498773519
    0xe01020315040b1008100e180610141903020603040f0c0501050a021c0908070909030e041413030302160605040b1018020705070f06050a11120f0904061707030309 71
    0x5002807422004e041c91190700014482194011001440340e1a8068020030005564019101c07491240f03002030351820511407480750382400c20b9405081280c2c0b69130701d040c00b480440c0401a610900ca0b50448201c004d000050050b5032802a8581c4069803120b8080204028045cad21004900f03014441c02d1180045901c520065403180900d450040c01680940100e018600c0900315085003115103040280040d03695a003102d01e01031094022a01a54450418200b0590005d03001c02111600311428000c100c0d08009101d5a104000c100a101d1a8000411402d140c020341c11902d100405c0c100740e4180e008035041207000b400341641c01b2200c4500c4c0c0400202d4101184683d60141c0c1c0310350130051300850300c283e41800690002c020a8403140641c410008403003c0c42002d4000078000e80c1c039515100c0300e074928050403000c03900301c141a194100354074003c2e10054850848188004030408a61289042404600101001d4100102840c10b40400c3c644000703000402d0412684640d84000c3c5040c0c8410f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 498776007 1250 498774757 498774761
    0x2090f09010c0f2a0c180e120904020904201c05060609090910020d0e1c0503061309060603030519050405030c100c0b0f0610080603030f070c08010e0102031504 70
    0x1841950000345a00c22200710208051141880f65401329110f6121807080d445003c816040ca83c00780d40811004140701d0035508850081a01c0a040a0041c000b4541003d545203114800c2c02e0515101e10381c0020550400d6031941c2c000040305804810f807803c41d01c2c4415440405600404000f010030720f48980c2510300d01c0150095900c0354401605541c2411040400c0c410341c6030020b0706c02d4805008850540c00c00699600c09041e0042c1040702c00308519100c1c800301414218103054004d035815400810744056038001c0212a0081010b480340c04085841d80d4140e0010814039200424890500c031f800421326900c00003600803001055140310b0401c011505c01d41d840e02c5540703d8542c2681015840300180d1901c1c003501e180200207400d102004074510756a040601b4411240d40b80010404400d014142c00c21001c031035400d42da035007007503000d5040220000340c0d00e004500480800c5e020001e0010100140d42d280d007030080000c00000e200c1c03440700101042c081d40040b500d41c007120002010300c2c42640780c98 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 498777257 1250 498776007 498776027
    0xb090109081603060506030a05030712030b0f010206040314090406090e0606090919110d32060a0e01021b070e0a14070c0606080d0c1b1505070c0302090f09010c 70
    0xc2d03840600950700d1550f500b0040d00c0c00900342079044c02600ba80380c0100d0005e00c0103003621489542181030801449038054212509110183c2c090044011a00c540e640c00050b1142c0094260030b18074100c0c41c031f88100000a1007507c1000307400c02c0c2080000100010030360031058050f0b540c001910090f5441406202400c402200ca10903d54007804101580c0180c0044082e100c3c1d01901580c00c0e40c44280011526441c0039450880345442e07030400b0081ca0380ea200d50382c0d240310503040c8092039061100f444402d0ba10800039200c405566a82c030440c440c810342c01d50454a0110180d00c0fa2081f00c0d5034181072035150100c61243c9400380c4821400210480214807980c2c200d00301081d007554440c1c0320f100c0200c9500907030700b00441d5510b550303082c0403803000340c01c0029454910955469107100b8407285402030301c0007442012048600b035a500c0034003003000800c40100d03a0000500c1c2040e00c8060038141038082d0070701030740003035080500c00007072108040c180c400d81c6100d8441007000b40310301240e900c000c880040c62 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 498778507 1250 498777257 498777283
    0xf0a1203020307231209040212090c0a090c020706140c0d0225030206070303050403031e270f080a02011416021e25090203090109030f090302060304020108090f070b09010908 76
    0x3101e0000e8145d081050094080c001e800341005080183c0103402d001450401d64041e100f5034450000101360b880d000e05184c02078000d4ae101030010f00040500a0b6480946e80904030610440c11481c003100405002030718880c812010071262120110700001c0c1d226003a40c181008410021081303010341d0038010700d00d07100312640500600d1800d029520214001c00780034208404042c2c40300444040d40d0381078803040b000c103d00210002980401043d072041c001201d003044074080281c500080307020841c40c1100700603864104500c0c0703503142c4082000724014414040350b2807054803682c003400300300200f88450000452070ba07021110200d80900f4003201120f59900306c41e0075580500f51060800001303043d150b083e45000b00c0345505550700c1c2d403d1001130307070000c4402a1581e0354034003a031020b241d480110960f0700c80450030088415411078010035040d01c001480030781404150340124210740300c1000b9518880400c0340a99900075220202c410302a40510740d03041c0001c541c40030118410401140600c42004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 498779757 1250 498778507 498778513
    0xb0702150f07050d0606020601180e0a0b06030a06050702011a2e03090519110a1503230f0105040c030b06180607020622060801050f0f0a120302030723 66
    0x51408841c500c0c808004141400700035040c4503a010f007402d540124009003005401400d003541c140400a0703030080074007204904840c141012801c0c400c0c0c0200b850f510312034010030403900e29511800440d2400c1503011000f46603600e003030100001d0766411740c000c00300c0343d4603641c2c5a4501c1c250764082000048024840010110b02850060148201501400c400c5945424041250402c1d0345030303281080e100180318528080c82d00d41c01c908110060b1040e00908404644501610b8280402c10b03481a030582d00d00070605070344050b2041420741c0c1c0c2003110a8900d500383e0b81260343c40d200d00c145802060030312403140590700300b44c11850f000f0302034000e641c46042c001c0c0c40d583c02c15101e4031410310940034110a40350845410085540507890310030040c1440d4050301e00b1540e14a40c410700c0510f0442080e449030b0b00b0041984014400e940e40c0d52816883c1d40000c4680e9104405080d000038074203030030350f4000031040410708820807c140d00400582241d07400703610700e201c0040128414080420a8220f0300307030190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 498781007 1250 498779757 498779761
    0x70b0604232802040902120901020c0a081602060406030f110a020a030e04022203050c01030903050901030f110a0f020f0c180405030904020403082d0327010c05070b070215 75
    0x18800c4180501c003469a885040c00c0b00d01d180d2210089a200340c00204250f034001540c211982071708000e00307030401d540c01c000318984070440911070380344c40c810000240000b01c0001e2213103000da032039807150340c009400815060355140d40d006d002c0c004280340001c607489142014005601604000c0907500e503038242c0d030061700703000c2450344e000c40300846090040c1d03510503428412002c4208090181001c5100d081c91500305c01c5085080071480c1409030701c0481d041508000c182400a64040140c8401080a01780401c0c2a040f81a550001d00001403410380c0c0d501020440740501903104030301043d034000c55000c1c0d40181d0f0721802000c1d140c0c03d03c1480603810001c1030005a03180d05441184690050188041d281420384402c0020140c2e405a4000d859074980807501e00103010410740c01c88140301001980217801c0f004405185d8240c0401001c0c3d074420b400b00032540030198180303220b80a50800010080159074100c2c40045c103540c025607815910010f00000240342e0f00e0001420704042e101c80c4940b8007241d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 498782257 1250 498781007 498781021
    0x12180c05060d0e0102031518091507051204030203030109062309040c1d06010906170703020904140a0609060e09030d0c09080d170c070309050f0f06070b060423 70
    0x19400740501ca03241e150f441c148444524028405540a11001140740c0c1c8103006001c1000000818070700d211090100e400140854014005001424189004a02d101980d180c5806850790301440411030102c2a08404220406601000940c16074074802c80800c4015169940310800c42001d00d085207044410407200c0b41545458888154010701c124880b2487c1621b40b83e50aa94495202030076421800b8403003030000d20342c1c1068008001c0c0c01d0525140f0404100400200d144c0f61014200c28185540001e241c406d6444a40104851005a200e44011410081e1091008040902c900c4010b6481c0c45404500c1d00b00c042d40d42400b4034000030007507080c07051190241006100f2607481c1c805004019100040400c4140907a82045001c2d848005c2e41840882a026008400800c602072a0034204610400242c10207404c0041e98001d5641089d1950350401283c1c80e03800c00111740758000808034120040100e03003440b0600c20301040d10140080201c003002c03410341d1400314503ca900c0b004500001499 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 498783507 1250 498782257 498782269
    0x90524030606071713030302011404050c12161212050a0207030b0a02040f0b03040204050124200712110a0506070f0303111606051e0711030904060612180c05 69
    0x4200d0160140c4000018540420504d0340d2240440c60030000d1044010024540c082c4103000001100c50148000b500e019910382e6110100c0b00b1046100c0c1c0c0500301000c240043c10040d2102c0e541c1c60344c0b0840c0324141c07a001040c90b40311610b04111484180c0c1c07014070603030520541c1030302c90548954004001a07421541c0342c003803480c0028881414140d087c0000600300951501c0000149116000d076640d0342024014001518016004100f0000ba4402078030607000c0082c181c07405902d60341c82c01d20300d140c043d58001540c051402c03400d40764510440780b01094032039a00e00c032050024491900300024048040510400d000144a0658002010302075400840c5203c0c868903052440792078001140d02600c0c00e015000d82040c1007212080d01e846c5140390802400d442081d80020700b00c82a103a11981501c180780710350340300900300c0080020610501c0e02001c420002e0322100f00c0003c1c002e109054a6210081c070b40380c480d615965080d410407006034859102440e9204032260800c5c94416414288418480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 498784757 1250 498783507 498783517
    0x1e08011b0f0e100509011b02060d020702010e0415080625030b040e1501182a020f1002070c05060c0c0108100f0306050402010809150f04080706020a090524030606 71
    0x107210b00c0c402e4408090750b0310320340d8410110250b01d903652a1341032940010485081c0010141824942040010150343c8d1401603901c400440355015079201e6061004030f82074454014869000740c18103d0b030001d4001440120400d40740090103c0c0d02e190b651201c4002c10150581c0807000c200b031a000c411030024841d8100e11640c0741c000d040411103005001a4500c0c00305e00034140099400e4450060140c0301c0d02d900187c6020a0145041c010044000c52200b450000d20303000c030070f400700150784100903103000f40302a1000c000c0d002c0540e070603100b803070070060081c0d4000001100c04d81511000400c0d5031500350207441c45a04c070800109640040d88005403014000917121511701090101e0028500046144201c0a5841183d010030141040d20001d410f01c0b00282c50001540c00c5252002034402c031100701c60383d00c088003038040382351601c071814803078854401c1b048040d080c9400018007680081e04200c13000c044400680303021403a2003900606100305000009464040b42d41007010441902d040d1020384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 498786007 1250 498784757 498784787
    0x3010303081f0b03090f01180b01050904050a0c0e0601030b01091805180d031b0f120507140705030738060a08032d0301140409110306011e08011b 64
    0x140326603203e00c0051515001143c04000a80c0000e880c0c0d4039140c028099a0750340341c0d10a00c001050641d41d9540100d52005014050141503400300117001c0c0b060400802980d650810141c200d10f1340c48800e1604c0c1c00104843c15070105c0c1c10603100104d19407140402d4001c0342c0544c066040c141c4042c03000320001e8a0701500c0b40d0104007140c800804003000c00d0000751604519528001381c0601240407036039604030920408010702110f694468003150b04860880c4180c5959880012150364078a030036240c0700c14000242c4550300340414504100600080100001401444003d510344a501c00107590180d9000d004000c512041c018038010b0b091810403250030603002010031b4045030710348040340d1031500549002500c10034040400100242c0a2003001c44a5984035042803a641c1450006848012011501c90140e5900c0d0902404c4c0161034886200003d802000d484107540e592041c1d03030044201982d500800300722200c00152440c41482171034004944100d00344551b01050350b003a651a00d90308400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 498787257 1250 498786007 498786061
    0x1050d020906120f1f06050d1e050703032106083a09031a01140909031e03100b12060907050c010603080415020a03120203060a0f0f030b0c0301030308 66
    0x1044061141c03883c004d001d0307002451404c401c0229102e08441030024030060341d1900300240041d4803140c98003070f401038001750240e01d90703c0502d11032503040c606400042c0c91030040720000b004150380507901241443d0344252910003002044400000c42d0041c1c815040142d10010380d00500c407800d16000307103100000252a003408200f221203100f44505940c0000e001442111061081000b0309800c414003030802c003540005036041c500794201284840042910524201e8006031418074104103d0f12440d20124000281d40b0022090005a402c00e840d200382c00d01143c4000328550041406641001e509580a000c042d281c0b40144445000050030400401c24201300e82200e1407424040c400c011841031032055540c901d049041d0b0601d00550320f1610464001c80c20000100ba44800925654540300702c006940b5110000003690841c0280d105c0500030000d41e40000348440000c806404583c09103e0032201a0703540c6000154a11007400000c0104046101107074084101c0d01c0e240070001160065 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 498788507 1250 498787257 498787279
    0xd0e0f030609030a110d0903060f0e0a0c0302090a1104030b0408040b07120f0908030a03050c0c0a05210f0a0c020301020f070615060305090c06070614160806030601050d020906 77
    0x440d00300030040b1282d400c0c41c1e01c005100c1c1c090690003001d01d92180115809440d10420114005000d030310315100140146071030b2020742010409580c042e50a0124560444800c0c0303102c1e00d8441c075500700c5440203074850030100f0001030a40900e0b00614008620f00c109a03031415040d0f55841040c44c101900c15903c0c402c007030001003400f1032030310000c2003901c1c0940d4038590304141c014801040348010107051410000c0d07401c01040f010b48000240c800c144001d05005c00e0540c0c030048105100d015400b015400c6100f01c40420341441300204416868101d16100c07540c2052542d0104092403203002442c0c85041c20030882c1154045c410031040c0c4a4501c001d001520b000100c100e8101950851401940d507542e8131081400c01510b00350300c4000800326810280810b01c0e004039059110340480c802c041c003900b4001407040c10403a1a0780090201c84050500d480303a070619040902d0032400e40b1601501007490403020413160320300096481d0480e10014a98440007540307a007845680381c806006940c200300d407200c13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 498789757 1250 498788507 498788509
    0x90d050c03070f1b061b142d010f06050a0b0c070f03110f010c05060114120d0f09080102040305060112080d0515010f05042603070501050a0b040b0306090d0e0f 70
    0x861040c43c1c60107482c0340300304e40d608015420a0100980d002d00f007481500d07807055207011038030051480310540199040385010260700001d0700701801404038401c032a48030441d8a28050600004c80807041000000b00318025001d0368090031101940034140e44001e5044081103d00c2c00140102010207410058801c8650354500604503181d4580044035000c8600f03245800900341000c404040780e00902e0071803000c08503a00d445444600600900d40d07001c4501d86030300000c2d1550119803042c80c50b00800ca8044036007180c801071015841c400c0050004816440c001002c2c8014003da400342e903041000341c8581d904c0c01900282d0510b43ca001100e54410520060302982207074852140300d40901e000c0c14942c00c901000041c104040e8071001c9080c010107000c00c2c40600b090f0400c8815072902209550200c6000300340c410300d0350141500081c0150309003002c010030b001a0360400882e10205840501c00945044205502d44808844608a6520145108011510925901a4804001c0e0424112101c404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 498791007 1250 498789757 498789773
    0x105090c280f030308091501030b27030315030a170d060b0a080703060b040e010e0c16200a150806040f02070c051c0f03080903041d070206010e090d050c0307 69
    0x58450a010201c2c0901001810b4102548076480300001c00034000003a03c1e00c100c807815240602010380601d80b244001058411104860b4014175189000c0d11034100c000041030356030764821202140009070703c00c60000d180c00c000990100e01580040b5840040c82c0c0400300e031026402180f00303199840e450398400108102c403200103001b214510780e01c100c0c052070a00e6000d0140c80c0c843e402150990303010881046641c0d00d0300b184605643d24480e6401c42504e80c1010003071035006e680d0700c480464580c2280c1100304003a00d000074a040c0c4402c0c015542103540582080010310b514450084038040990f00b03085803510034428a54085402000001d540215441c918200e8000c7c080072030b038800410400744113619080307007907034080d0103500828260901d6079500c0765506003525100030240070b140d8020900b007510603c1a6030140800c00d00240010446a166030245041941c403100503004800010074120081400c0a1140b030103d00109000e641c000400c480e1603000300a03030122030006100c0c0c800000d10007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 498792257 1250 498791007 498791009
    0x1303090518040605070906090b0717030c0c010c0309080a111c0e09010504090c0b0a030905010207030e010e100f0516080a0c022809110c010c031d0105090c28 69
    0x1075108464602490a18200c0d0806400ba2051003105a020022160b000a1a4042d034080300d2050362543e5403441c00140901c49003030a4040c1031008000c10010000b404003801c0d81044180080c070080c00700c524250f0860b803280c10042d02c403401c20080d02d2003450045045c0d661142040b02198003240c01107007a00424859070b0100c10004003822240402480c1448040740500401c9034100019440b0759645c0510440380e114004c0c030b007000070841c05400c90080c0c0c0460102c42e0400029507036070b85903240003007142c08250a100c0c0442c40324480010f4a05050305005e8a0346101d407940c20440c0c130f011001740ca0503081a03420001a040c81100000029110800360034280361075241d10b900002284100510740110104030340700b0000344102484032510a003814000c03181d6925000841c0c0c109100700e0819445000b5903001c40303608000c00d8010345a40355108007a40401d4a4806260411900b410740c00d0320800d40c3c9186c3c15a020202056492130000b03954240308076000030302e844085084210f00b40103441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 498793507 1250 498792257 498792289
    0x20d0f0804230114060f1c061503050304031a1806180a0219080706021c0e04060308031303081506031b04050d03020708150c0a0c060209031e0705010203070b13030905 73
    0x71340b05000560a00c100e13041c003882d5040310b00c103242e804241642110911036100207082d10f030300c64180c14800b00e03105170100040c68111041d250f445482e070030190742606403144c0c00c030713510300448001480b5444509400c0542c00d03c004050621511070075040400003c10744c00c0071569010351860340f401a96802d0030204007584407803039024000c2c9020045820110b26038004010b54028040302d41202c2c1485207841c000800c03074103010812591400102e4000c01060300014502030f000020f1000c4d080c2d04040340d40c2e003a4441e90703550320b140d40d581c5250101182a0000c0917008a0f050011803403940b9100c3d040e1490700c4000c0507a81c00c041d40c03400081d030116a43c41c03041e009078009076028041308005203c0e007a074800125140c001030b1306000711515401e11600060302c08100c14030301c04408118031501182c82e10b0f00f00074202d440450b149200314802e4454050012181d201e40400000d05500100503a024160002d8001016658542c51420220003c0c0781c1141001886d85003c5240e87d2000c0303000c1144c0300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 498794757 1250 498793507 498793541
    0x1030f06090b0f010f0c0303050c0f270604060e150d060f0e0a0605010903030e01111006210822080601090e01051005060904020c16090c020d0f08042301 67
    0x2d286040c40300000480180c07a0405c6403a11049034960f030001c40c0d40280340e0381480c000880d940c8a8100d220a40198003030141150300000d24200341e00710000d1102c08500000381610039020000c1c007003045a1159108000c00300b500910024940e181c00c030303050310031090000161450090420020422a1900e03000b01d5020220301c94240440400c0780321840d84a2622541045414100300000e841c1c6140381c84001c0c10000400341502c0564864030346410400c3e807000859a241c075143da60000130300708034018a49c10f224200000309600e80c0120403016441e0b080584c05150400704c12451500030110201182c0642100c800090000d408000460003009820800551054014249402d4680103012490394104640c000e00c141da0380d0908840e15510101e40060740d03071028881c50781c01c00b02c8100728180303803810400c00041d40b00325a4101d003200e100d50390700303541c10300ca9441425144c07804201c2c03803000090550070000700000ca00070100c40701c0280b03545040c1200042e400c8400c1c2501d00c41c1509170784000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 498796007 1250 498794757 498794771
    0x80403022e021b06100815271b0301060b0f070c03140703110402210a0b1203070c06021903030b010509090703060f0902040b071e0c1509120206090f01030f0609 70
    0x21206010039a0001c1c4000c17114140c60f454031924a546440d03c00da0102000c20580c0402c1d0000803005070440c103c585400b03090020101240c0868440c007841d43c00030f203d00c41c440c4c00805103103010722802c1c0607220f811b1401420880c040045503801d170080b5408440c0b02500820110114a09008035054429080c2c005c01c1c80d40d042d072404a00650304418054065070050003004904000d500300506581e20060380c108103569180e5210020300070700c440c4c0039040b01d849080402108408001024444c1c058540f03684415600c040c202da4a19000000484030f1800a48010000b0311a821408a0303580501d0f050342449001c1000481e094415144a40425545c403030801010101810703c0006014282d0110704252410a00c0c256600c24528001c00444c00c0451000a140c1d00e41205100141c00c4050f4010848e00c030111900d0141d5001151408191699000030b07003484420300607200035a01615041c1083d121009002c2441c0f07205215034141030315414020b070603254a2080c0300c010919104042188 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 498797257 1250 498796007 498796057
    0xe010f0f0b0405130b06160305090319020a0b030403030f05070e040605060309100b0d081b07120c030807060b04230a090f02061c020f0a0f080403022e02 67
    0x1805241d8003290941c002480204032542e20380010042240012201182c5100d210000030110300c200f03504094071041c1c0ca1060700a01d540503012b0100d200c070903001c4a060940f00915035001410a880017907002c6011103040c1314510100d009103070060f00c40e05001c1484250707401918191207086915400148180c440c0c40042d140034012240101401d40d00c603442c500303200b8495621244080d0381208001c0d122818501030703440760b10514a0036a00401c03d079032201450301c0d80c186031030105030803c000c80c4078004010460802256400e0b071429800105ca8807500c1ca1a60f6038461030b041003034182c0d0810b5035088c035450140c03a41e000b6000d0740e034010401c0100702400810340c00c0100001030072a0460394689103080d40012110300482d09010303011140305071114414200c0c6c0042c4070b59180000350407800803483c0021a0441e1002d42040707002c5454880e49585c0e000d50413507440c081142d0107001070348402c84007205d20707515460400b004c000c800308141d40d202e20201142c050b80d028007400c81c00b6180b50040d5100d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 498798507 1250 498797257 498797279
    0x315082a0916170403050f0a09030503360d020112020c0a0b0a11190516080a03020304060b061c020c0a02030a0b040c0807060504090209010c061d3309070e010f 70
    0x40c1c1000030f8001402d09040c0c034028814010348000310815800010f010401d54000c8025100540c0d114040700c0c2c0d07070b0485d00325001c2840f5110550003460700450940c00314640940000d69080d20003d04207680031340181c0c0045640d10307581149451415401c11100401e6a0309102c4d480d0003070301402c03445c8241d0a14101e0f041c01c4910300c03400950f55403002c1c04071030090581d81c1c440c41140c580c0c034a030080c0c848155400c82d444400d240503000b0816580091100e0040b82c15402861040340905020444809948140803441c03140344002c2c110b6010f507082c07108040c502036000e0100d084032201200d02441066010a1501c05510400e8551450680400041016084040c4090a68080609200c0d8680071015101d0b0181d80100c107821074020681803d1030748074000600500b41c100c0403e2004243e11a01e41c4120200c0410364a46400344407288050601c0c1074a5010100ca85450074480c06c04c028400302e0360340400a00008401c0c000c84200143e6089003041d850b0290180b0308c010714a00d440d0448400e6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 498799757 1250 498798507 498798527
    0x501090609050d02210c070e07020607020d2604060e032106120a03120b090723030c040905090106081c26040308060f060d0204060315082a0916 63
    0x2045600c091003419480d0b0355140e5402c031201c45d036400543c6071000d1000160030034945802074040c4d60300c40010403052550019516000302d58540a951600d0030780e10301112881d40300100c0722a03100304068a0b010807000c044030260f0142c095200002c4035002e03650729505580c03002c0d9080c0c14050140c5070109074601040301e03080e040b9508462000b500754000c54559203885030000040c0038080b40d100301052036004d0390072070380c8059002411049607141030500a04030b0715540d600c5020000c0032101e500442c1c00078608581c0543e04200b100c606003840d08240c2c801520000b41410655500d484000618200c03c00c541030404076103241c540390440180b90b000300f44814881c0549071042c8a980000003800307114206a81158162501950640d500f0001c070b810310203100d08060300309400003004111840b03a035000e0000d461907554107010112010741803100c5021680615002d41d009001c008245400c11081c4140458110340c110041600100010343d4942d01150705002e08101080040b040c00e0380716410b40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 498801007 1250 498799757 498799783
    0x160201113003070207120c0f031505071715030708010c05040806090705130c3b0405040c05040504020a030b0a0209010801081903110708030304083606070f050109060905 74
    0x24214070f0a41002951030b20284100859113140ca2110300501000e1000030020703040c1210f2188560340c1d0303403400035801c0c000b4603124500d0034504808502003600c82d090207210b980d41c0114000c0725440e175042c05e03889600c05014032640341c4500600060f20040078083c56142d40800e0310341c1c07a2540d113444142420710100810461003504064014001e030343c1c41c000c4400303440044070400955600045410782c1c22360100b005100060703180d003030350300003954541c0f000080c2c550320b500503c1456001e00007440161181520001c01040d03003c03400b400a03041590081e0b074410300003040042056620f4a511481d20b1342521446d10091300023940c2e40079941c201c03a441c0e0041034514024030a485c0c2107503c1ca8451b041044004003000003102d00017003190010040d41000d44800000d499880c1040d2138101e07503e922070041881040094040c0201068032051140896100c03242405400c2985000704513040d400308008560540e481c010902c04100c0c01d201d0750065a01c18680002e80c4003840c00c20900d4441809581 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 498802257 1250 498801007 498801103
    0x606050309070b031506030f04031b0317070e0d08070c0e06060702090a110a02100b0a1203030203061c060b130b061803100e070f0806070516020111 65
    0x2101d007414000419034102c2e0343c100d040c5912030f1100d080c5d17003003c1c1400028a41d403180f0084107001c0c00d90f034a90a5540214440d40303655034500555680070048a880190107400b181c51b80a1219040e142011b100354400c00c103140c800e000e40c0801d00054020030040e001506c1030400810440100034001d40d540e03000e880d205880b64101c1c0b9180e8002000c0d032041c0e01000303003d0325585002c2803882096401400300364178084052030b220540c04900a59452a550f106400c09040504204450520710441410380d80c0605022080310b02c0c1d03803825806075002412b00c40d0403820041e07403130000610061040321760a1040d4004281c1c24544020895034401045040070384614041141d1301a9070ba0394100c0311f0b284403000d000322140c100d4400003414000b80c00382d0700f160b803070500d000e48030316007000b040c03d40542c0c1d031040c042c18880c3c2d00ea00c0855560481181c581c80807400402055804140706100440701501c149880046020404103032810300c4074411020111187c0f1b14540c3c2000c070381c280390348400c0c0c51044e038103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 498803507 1250 498802257 498802261
    0x30c1505010f12061104062307121b120c1506081c03060518010e0a020f090103110714100f0b09041209030b150f1f0f050714070906060503 61
    0x400b42803003502c1c420840c00320070340740b081010820706800440503403003181d4016444540d10540980686010a4440807100480c0e10180001d0102d000791281c460f040b58088103030801c0c94109403601140c0f2100300311488aa90510030004603060811051005240e80b840d00003042840c201c2021840700382122034035401d1580c280101840054840c42400c9d0416010842c02080c003002d50091000ea04920f0b0441c03e5501001028038414085a040f9a0040200c01090751240080d00490042001e05049510100814481036120b508141d2060f00f140c002940740605030359a0040312034005c0301502142e00441825084d58003548125010300300c141c03000b400040000800545051030044c401060503030740e20700c048034003481074460794042c2d80e0084410f50241400065020700b0321800b042c2d90b204ac115640300000c1ca00308200c0d100c0215640040e803154100640e101030783c0c00014070481e0420040c040c44654003007411176020558920b000400381454500349034061050314a5900918184101041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 498804757 1250 498803507 498803519
    0x901170f04030f0e09040602042111061309020c0105040203060c131a040b0a05091c050d0f0e0a090516030606020303150d02040603060c17070507030e0409020904030c150501 76
    0x10351580c4030364540360a40409607003100c180c888a0a02c005140c00210000400040208a0b8028000d071070301003d203801a44687c00c00c20041001100d40200f4140c807403412001e0504008000e402c151803092400d1034980d80341c40078a000c0341c000c2d039801e0b5210b82d1240240829410184011034004034604c00c91840c1c6070307105903441c0c002010f41c071441c0d08145103003a02c60341408039a0306680c003030940c005004d5030b140f0040800810540280c0802c07845aa42d10000c0002d580341008017101e00e5510001400ca00d22460a05640c4070211003d560b0078440210900f00e01603580b002c9134409080306442c0021039041c80075004004042e03902814060528000c400e02400d40c0003c01e480c4d212004120045140034000c0204420518200e0b009401a04191012042016507040744101c80c003180e0b01c0044030000c030180c44140c0c001c10755552007c00c03002c01c5401d01180c428500d103c5101c10190000c20b11044603404114110400c9030260005138180c140e4404200102c20b8450040700419024411541002c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 498806007 1250 498804757 498804781
    0x906050601021209060d090507180b1c060b0117100f1401020c120f01020715050a1e090c1703120f010f0e060102010e070801150506070f030305040203071208090117 72
    0x61403605c02d020100341e4800082954019164980d031103820356507a990b81c2c001c040500900485d070340c0006401d14440128600f081346c103c0394628010740381d02150345074940340d55005011b614003290402107000c002c007241c0c41e03400031035a008038001c10751442c2ccd8a02d01083c459103041d01c1e8200001d140003801003a250750382c4c0051301440784081201d010400250020a441c5402e010800e1110a0750001c00e81206004400d031b40c00e25603592060040c4807a50b24048c01c02c081796010188240e401001640c1141c40201542c030151200c0d1142c80c41b00e072103e84074210748543d003000e030295a2aa40c00040c642032084000343d4015080811070300d00284a50600b002082c14410500a0900c114010800201e091781f003508a8400d10541406440c0300e030742c9882540340642541030313800c45c0807407400c0da0002d03485c1040f0080301c92241d00192682590300c10340d68124041c06000e801aa81807250b114041002c40e2110700c400d50b0700c1d206411459a400e001400544106c4d03081d10310325440c042c182d0070060070380d03004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 498807257 1250 498806007 498806017
    0x206040c0e06011b080a0e030a0f1203020f0d02030103030e090c09100c200306090703051005040203030f130612110910020f070602150901060b04092d09060506010212 73
    0xc100c00799207a4600d03004807580c0d00036059404d0400140880882403101c2080203200514255403404900b84900d0240f6584004040780102011001c61001c4041200d40c640c06030244504c0ca0094900202203c0d40003240d00858003030300155130300100403c10586c00012a01c07114205544100d80c0d442d00c1015038600e40030b0000300ca400390084520208629100340c518005890f400600248007142c5a510340c0142c2140314aa50b010741720300340104d81c582e04005022401c4a81c4200204450840300300000003800c00030b0012600b610081c020340c02d2410f071703000191685609075000c4200861510380002e00c00c035440f940c0c140320645400100c3c420004810b01300c83d1000d0054820515012035040100e18021100d081110325006480d00442c4281e80429035072500700700150300e4105900c1e0780b08803900302c030007030b104600380c0c018104000c02c0760008070f13000301c910401607119066200480c003e40c0c0c0c4c2403000c81602007d00968404a8408005052050540095007032004000d817003e440156900391003030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 498808507 1250 498807257 498807269
    0x201050a030e1014040c080f0703020d08090d03081b0906032d1602011508210717031e070f030209030a29070c020102030301050d080903070b0a0f0206040c 68
    0x4802e80e41c400010b0800140c504008584000c1004854603c81040800002c2c0c0b02100e41424420f00094280000074400c10014403000280c070145103142e00300101032402c008112075007042405080c896940d6000c50515560203a00c88144510b00030110282d40362204043c00526107050091856585611b03003603aa1200423424681c00c1d02001c1180c3c251240c00c188078403503280d0703020000c1200d8680040703420194502e0540080c040c10002c404151007410090254030200d60050101101015074105030f00a9000c102c5443c134501015070311010303c039184c04150240b01d00300000510000728110100007603e610604c100304950700700044000c1414030150380d81d804058002c110b0281d0b036501030003400020340d40503540081d0603814070365001c82a01e441c040c40450b41c0049000540c0280500300305070407294140e000c0c0d41b5603070038982082051031480c00c040e140c0b41000d0000c42c0d5a9101040080302030310450803440d889450411000345028141e0035000c0c00c5412810501c40004c0003804807400b80e4507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 498809757 1250 498808507 498808511
    0xc0f0e0a0e01021603020709060e0903030609131401090b0a15090b060f04030c1703070f020d0809030a0309051e01120902060c0d050c1b0108040b042604140307030201050a03 76
    0x80c1d15282280a4041c0b12071280800c4900681c5004054000444e0b070b085421004040c0200384e035070051002a10380441c5c50030601e42041001030800d02e0b014505903485521040700040c80520354076200101d84400702401d400360b40d514122028451540c060a0380016484414404800b071a0740344d408201442c803901e00000e48480c07a003540c80d580e5505071a801ea0782d421485840b03650760704100254444074800d1901c1015248408420070201001f182c0e06150008207036a01d4442c40d0f8280050603950000a032000c500920070411503a800784007001c0c1103030090703444070400c4d82440d041100700340180003003c01001e10a0050145a604501803548052841000140e001424004100d1610490800d017400780a0b0701709112800d5002809070203144000c00403251904035500280b42a45620210036004c2640f050000e4002011044d403181d1003449080f100411325041008104650b806002280c0d11500105051080c02c46038109600107090841c01080401c1c50350b00064514410300740401300300342e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 498811007 1250 498809757 498809771
    0x22050702120a05040f0803041d06180109291503040611190f030c050405060711040e03071509032304230111060c03011202010e1005070c0f0e0a 63
    0x94000d002080408602100441d0b50300c84556000302280d0184c019051224552900450b400c0b000009a40a54904000c41314001121003020000c041000340b0031079100b072800100b00300092460901c540281105000800c082c54a031045290700203001c242c01300040403c0500761000c7e41c40e4000901c0d00201401c043c2e5403501c2d40e040290242032925010711202c40d0014180405804800043d0140c90f00c4c0e0740ca90b031a00c1d40e00e80c8101e040c0c4444c41180c400044013070105102e02e1420030002d0107050702c10400705000400d200049015a0450a0305810940010449a050140034086100000744c1400c04000300c3c10141da02500140b410140ca00e81c0d211700710400040320044000f00c50103001c03032003002924a004006410108051200401c0c0006c43c03000201031540c070001aa00d00a0388400203490070740e82800a03c100400450b00241e04000345441040d1054648103c0c01c010404282c1c2c60580d0381d4403900b0803580200d0180e100010700b440c1800204007112a000045401c06d01d15070b0085405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 498812257 1250 498811007 498811021
    0x41a0f04020d09020901030f21051902030d091b050d05060a090c0e0c0a0f020610060e0303040308130302090c12040b25020703030809010c09030605061507050309040b2205 75
    0x184110f0400030741280100300040140618141c1031558280f2500603001e4100c003c100c1d1070303100b081201e0388601154081c80f5424030b000b4425000903100140d841160b09040c01c0b000103409846003c43d00b980c80141c9d60050b4480091400719150140c501035500c41084c224507901e00340d981c0c130020b10740f820b0107548076150010402c10400c00801070004280945160038110b0310018264400409880403038110f0301c00c1c2003503d00100f039980c42858008001e480c80e44c94520140d801e2410700165951600003001301000280c6a00302a221100d0b0401f00c1701c0045055205011041c1c001030149854004180309072201051062100381d40300794842101490b50321200a045001001c50581c207002d5440031050144546d400030311482224003a540b405010b44464020324200e440340020708002905802c8188003142c002d4001c43e030451400340c03440c841080c080401030065000504121020b81001a00c09824035180c02418503840d07040b2100e50006800301c0c18011040071407074090105585400000e001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 498813507 1250 498812257 498812261
    0x5092103030901020a02100b011b0c0b0f0408010c0801120f0f0c06030b0f040c0212071424060102030a050d150b030a0213080703051e0f0a0809041a0f04020d 69
    0x1095410508580c1c89080100d4054043c0d0404103c043c0117114841e03488103445602c2c014803c1200c0c042c2c54543e0b0500c81d4000103820030901802c103450501032100001240d11548000b0b246108646910945481c2007040b02801d580003552140300f042601001444202048441d026000c5e40c80445805503104502e090041203042d07650183c048940280002807072900340d0480340038000c044480c0049000d0041c02c020450310544036070700c016401000101c2407068501c0041100e10b0103040e01ca03a040c140c65000c01e107040503480100346038440f19a910400160889502c940061090028600f0003414100080c510b00609040c11015034030b580727000b00d160303000079a0385018100302034240e592440c05085030340195104034006030485101840000704004046188810340c1c2d80704001e00b1100083c0521445485103020f01d56200c1d0144445500920320104034406501d44120780f80b0307494264031000c0000310b800c101c6c1080030f4100d090040c5002a40ca8021828280804960050712210030340d9184c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 498814757 1250 498813507 498813559
    0x2b0f020a050709020414040c0f0509030109200a090e030f07030c0605070305100e010518101205010504110303091011030706090507140102030f09010e13050f070306060509010509 78
    0x102a001e4104041683c0b010368004001707465446074003042c03510760102400112900080404009141c08a001101a11a0000740352031400200081410b60103515000407081c80500e81c103510884c0b001040820381018041e01009044483c400c00c402c0d00201030703c1e5102d124034003401490f1400012030400b014080d2124010903600660f0403c81464000c2d800307401001f0990b10070080d0b05e507980c80001c2c07040700401100e0503550080c018029000721907120440a8038042c011541e17041200c030300861800000005809040d000b00c001050500b010b00f009110861a4800036010b90401c00c1012003030b17100d0540b0f200d00b0220510b49140d20a000c0b1001c83d0460284882c010002801d1400f10018010000395200984000b0102c800800d1505030040e6600e20400000c281d8014045c005420251300800c81c01c000204046e040e056403042005000085510890b00c82000f404404140412650b042c400d5030301524580c102245442c00a600203417260045c844918441d0441c002200c4e070120511030008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 498816007 1250 498814757 498814763
    0x3020d050304032007092d02030604090210031422020d0303020c01022109061e04081b03190806130506190b03040605100b030f180d0906022b0f020a 65
    0x1007140313032041a074a444490611a10b0342050400c18040044070600e5613200e448145c107070302c0914810704203213000c1c06500010300040d801503450340350201507101e82d20215481c603510350300002d50417460039802a52000140c0040403048032808100180309444050030505038048942104400c03e41c0b800718043c0c801c0b0800c680965002003100b5a0280d1030807401603040301d00381d071ba0845030b554003100f00d03a603048101c030403440011040c884451680c0d18014110341060007150498640007da0343c0c401c0c0022004080d1083d194070009900c4400b90001d1070840800c0010f252a103083d0a089002440702c2050000710107030303680c1d0b4202140c8941ea42690104030140c181c505800700c0c6603122183d5242d900122000d41d500341c14080001c2242100d1000303402035039078000c80c50303066413510240034000c000c00038654140244440b8905001c2e001c1008038007419605661402926414808001e0070300d0780d00340e1500c2c1d55008210802003001007070440c42100301d90f5817500c1c3caa00c1070185422441c0c0301c0c5800c009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 498817257 1250 498816007 498816047
    0xa0f1802010e120106121406061f050f0a08010e060a0e06040b030c0904060c090816030f1a0405070f080309030304060c05030f28020a0f02040b060705011d0d090303020d05030403 78
    0x459940f810000303003080e4000d0940103400c7e124481c0040c0ca03103030126a00350340200319143e103a100a0141d142500802082c1c900340741030200b95800e0742c8883d03100b1415040030511000c010812400980042c03540500150340c550310003880c00c8640740c5100ca0152803d4480c40c1c0350707440d6070138a4508201da901082e40040040f402410f041c1081030040000302e8524000a951071030120304003c0014405261420040003000c0080c91911030444e13800c401d2208607039480c42c0084501c032003c01d0780b65150040d4010300103030082c5840c208159011280b00e078402240c80c0c00c2070025039026a008016170301102c0c02410801060100c034039100f0306602c07402d054400781c2172000c0340410a0013001b06c180303034002c1882005180803d4082c44140c0c0d80e20318420b4024131580680d9081801420280c0101d10502d8002d056181813a6003640d469095401c50381580c890f0724500c103041c10303200d41c0401c0300142038802070801c00300c1281141c500940307500c030322102070301400360000204d0209846030384500c401501007050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 498818507 1250 498817257 498817259
    0xa1106070b0f07080f0108060403050714030309010605041a130c030603021801052716021009050604060617070905070509040e0c01090605041409040f05010c02060a0f1802010e120106 80
    0x80e0b460315007074800074002100c00e000150f0098030b03884442e042c0c0d4142d40003402c85685581e81180c190b489501e00325254546000c8100f14030380100003943c06900c19074008501c0c14108804e100842e440d0102d00d020141c0020381c000050346071041200e40e80c5824120104c3c0786a103040c02500a00117561009403c10a401034010b00c1c00b540070300550503502e00b100c840c04a840141d04100300c5000c03042c107001c42652100b000c41c40b40c1c413060300030500740c00890055440d4154101d8505049500d0030b2420380701604090b081004100540c4036035000750008075074481100911051042d590303203031400b441d03580380d0713990010a00041c01101a81c0038540003c0091001c800c61624407a00c410702051514040f600d00b03040455058016425241a99150481841040801303010414210070140040d034100009001d0707040403900038015420002010740081146040c000703c1d00b8111080c2c04104204c461504825410b803008121072151103030b40900c1c01003115030300d50380060401c0340c0140041402e50b01e00340b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 498819757 1250 498818507 498818521
    0x180b18030a0f050d050a0f05090f150a02060606070f03140909010314150c190c12201605010c1b030c0602011107021c0c0e090102090f010c050a1106070b 67
    0x18184903440c4160240c444003040c4c140f090f541030240011045c0858110201010054484d202a0000d0b150081015209a00b20008506020082031106840c084001800889550104071044d0403110a40e4001d10b441c0641e00c0388060510700c0d0000404005503403502c00c03418411003060b035401210040120f0301d996901e1038458000703800300302c0281150084e456110700740e00d02520b0340c6104e0415500c0341803405411404546240c6244042501170103c0b07180040302040140307d00401c803103030790748602e010106140500c0c215100b5020b07449480b0360003d0800303500a03618800c0794048a03000c1c02e00f20701091741c9140650f1610401541d07070241d90b084510000c103109240d1541811281c2d13a80080040142d100316100e00ca100b90f0720013079000b03003514850380140c9550042200e07400b13002d44140c5d2a00c98585054030342c00c040980da004503d070340111340c2c0e60712407514100c0d078900c2e06401d00340f0110844a65840c5600e03000c2e40c41000e4403005001501041d03d86548040702ca400350312020303404013880c1c000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 498821007 1250 498819757 498819773
    0x50315281a04050a091a0601020f03031e0c0a02120a0905040f060f050a03021e0f0d05060103120314070e06040902070302160b03060d14010617060610180b18030a 71
    0x2050700d44550f041102281d203500c81032161944990300001059100c4102a0404a42034000f421160446c8106c0d400c03101d0b8044e090000c0e41c06070444401901c4072003005101c0c0018000c010344080b400d54000c21241a030325030009000a200c081c0b1000168071856820404c0d03484071420760002d500182024005d41140509a011500f40d035107903d22800060384840a0013008601d5003c000d400c1940403810010f0558200c400c150f034a00e000b00410400401d140110701407182012044400d030780604014002c10100f40118544100d4900d82004101081b20024002e0301c00507140c501800004420301c1c02540b548000c80b8040c00c1d03000c0c010b5554817854540255180003031010000713203214a60003c076a02142008490003250020700700400f40006444800b425130880846149545d41c4003030008104000b249048030004d2a00050041841c1c0345040c06031280341c1c1202c80c41001824a00e00e806a03c45000701c4054030a9001044c0d100c0c0d61030a02424041c0300d032861140e1500c035405905040205c82 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 498822257 1250 498821007 498821051
    0x13020d03020a060501080118060f0f090f050c030a020904020f0339060a020705060f04080d080118050601091401030e031605071401050d0f0906050405030a030605031528 74
    0x43c0500700002c0c0e0340d0700001c1d4203c803041c140401c08501d1144540340812010741040e140c2d01c00864000403141a81c080038011291280012980c038a03855003401d00b88401404140d00d460020360103044c100c0020781c0060700032440204000d2088507484800d88540c1c40c100041800003141001c6000e121080d071040540504615040301c0724000000100e03002401c04d102510490592500285891401d002c20820b2582100140840800d002c0c0400242200c04102100303580181d500e4400280d410500300c0007152844494420b07002d0304107030a201d0543d034040c00034030455020600413941c0042c40d0b00100c014015102e100caa0710b10011803403242d800d0715085001c4007a84a00d0488178159a1214000c651a94031044603010600034014028901c1103030300015000d204440c40094a9a1260740306001c0b03803415a070650f0790343d2010440707100c52505072040c0e4010f0241100101040f6280155075001c00e030313008101204250f9840340e040c0b00c41d000e640306290100f0303080384180300b0002c0c50183c1c1d101400023 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 498823507 1250 498822257 498822263
    0x1a09040b090721030e240403021c0f060c03110304051e0a03021507170703090b0618011806080718060f0b03071103091908060610080f13020d03020a 65
    0x10b42c007001038600284a071040c15120858a0050004010b440681c2c02603e801903050300303d8081c20f0b6a520b1002c0580303164007140300c00c0380e01c181c94600354010301c081d441c4007120303a14007020030011850110f0010315552604950000c404650040004021405042e42070302507103504101106110400c18040f0f508010310708040001155024001c048964400390404042c0c056003060301a19a06481c0354020340e4885004d041c0003118908004040001c0b81e01211440d000907512000e1108100c414960b26030040b01c11103103030350380d19554556201c1d600d0041c41071b46101d00003892180c0c3c4030012500100010301401090741c115568624041d5040c0c44091201d43c00349190602c0031600116101c00841640d4041c20030b1411640c9852040c0c44810355202c100482e48418000c00540e03982e1300004840d00e0201e007a0403140c9a2401c540a0710300400540800d1282d80009071400440368800b06003980034043d480d01d00101d843e0304403410280109032030042d400c0f10b00e0010f48020305400080651001c2c1c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 498824757 1250 498823507 498823513
    0x130504052b030504170403050318040b0f0409020f0a1512090b011e0b0f0a02010614030307030c060e060c0702091f09020a03020c06011205060a05060a091a09040b09 72
    0x1890456080364810541d80c6094a41e508030140000c40d10a07030006501c41d1081129521041d01700800c20515000365200304d9145d8400170350f0740c7c22148030811521103046d05640500c003083c090070000b4075612080e800540507170b076a02020b10a40d41e03000800b04812001504a04e085034403400c001409024100c6580040b40d4a68006200f003a598407807a170b542608500e4512059081020440400141c00c40d4040d9110000901286c14100303900203110f007068180989503208a42e55000c6d0039150a6800a45441a55942500e454a0210031039060360303414030b410400e280c1c031460300c0300040c004000030b00040d12a010030007a215401d43c004080060080f20f414610ba940c640843d5045500710310481e034586507060042201c00c2580e0042c0040301c1c07103070402504040403100114075010b401d1707101c800502d4000c9034034410f00806204ca035410821942d402d00080c82e0000101e031100c40e6910850725180d903103040201e0010500d03085805907082c003d10140381c1d41000d06154103003400070740b10030307540d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 498826007 1250 498824757 498824773
    0x31208070504080a03030f090b010e10060903051b03070e01092c0a061505090c0405090106050313110103020c1509060a06060c140705030a050102030a05070f0e100e13050405 76
    0x180101c09807070869201400030a046040365030210050401006150a02030f1108003440c00511108a014040d2550720130600840c50040c0d01c11008107143d6002d94144031404209001140d00841c1000c498003229125020b0040248007007407071301040e948101c104e000c00d58004510201c0f141c1000e4060600704441008805802c0f00101d40d0f29000c10002c14a6800203200c000040d8258108144000100c90301d18a059600e0012039000c250448101c0e0520342c5c00223080c07107186450415640500181d140903800c40c50030718110208040102005408191140e00040c1d1a80c484d40440340c4170203006d070a8994070382c40140741d024800400d039484c0d210380c01480300054124200c0c0c0714007011104156680c022810721034850309518984c03810f010195015680340854103440c00c0083c010703003d100b500010703503a1811031103480031660040c003800200407490011500c0254400102500210115421543c0050040c0c00790340c00c80451400ba50800411400d181d201c84143d44454800e5001d24183c034101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 498827257 1250 498826007 498826021
    0x4060b01030507050903030a031d0f0705090906091e03130b09040b030f0a14010b060a1808060411060307020c0a081506041116060204031b031a1006050a05040906031208 74
    0x174001d4107511a050307441403140c80b4440c1e101f9044210031450340390803426007826451800d400c0c1084032041e00c0c80c540c000003041225080455400f035125407040054100c904115007144c1d120413025408c010200310201c60041a410244100d400082d040141c2d48035407966108000740b02d400250945101e07e2801e20101c0c02800c01103442000419042c0c05071080c4822551481e40c507003040c0c0000e840300e660350b068490103030300c8030001841d411915031241ea00001c0881d03131801025445400484664100d2410b0000207080c2c03040c85007207000101d40407516039480c41e01c100d14010080c040c00f81d000e4590350000843e01004102070452010f00e008140d004d0740d810f418001036600d800d0f40c50982030800c11019a0020115100d1100b80e0300c101c2e405454160303030340c4030042c51205220340311318031001c01c0908000f00490320201d20a2841140c81c1d08405140200700101206481d00c41c05082c820b00144149650340f250044401810920008015075612820301090141846c5042008210305102040e42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 498828507 1250 498827257 498827267
    0x30b04020f0301050403140d06120309180c02060c0706090f0305030a0c2c060c011e06051212090409050f0607180f060f0e0607060902010909110301090504020d0b04060b01030507 78
    0x5c40e0340c041c0c507440100807400014012580c0065155584190b54880205e440d41e070105120b00d15038002d6580085840c240142c01068010004039200300e241341a815502d03941e0041606540440800b0309552942e26908041000d44050a030007003500308402000000c00d0f400070007650041000c098100150302c0c13a40429101243c171000010b41c082c14203020242105e0402180102c0124007500305420f10890301f0721103081d14000d0030100007003070f62500320a00011b5070f407080ea801000d08940d1482c0f4801c3c1c0d185c8aa84403110751b00403803c5100e0015000e110303030715182c1040700c1a550040480729220903d0104c240c0351803051b120400040c1c0000002a80d400420b80c004094803c040f10b50070b850f0b031038640140d458440d003c504c001400b015100515696641c2009405d02600820004c6503054803840018881a02c5802a680c2145000e55552500c5203103000d40303040d140c5690000034203032a07070b00000d40f5010030b4143c0100350350081c00410080000b160001498800b0a0b202407009441e59079096039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 498829757 1250 498828507 498828511
    0x10506010527010512250816031505060d02120117030307050309070906060f020705011d090406090f080c060106170a020d0b060d0e120c0703032007030b04020f030105 73
    0x1100c00c0c48822042d04250241c07042d0802c960141401c918101000b0800c0d100690304580b02c00d061030030007500c00c0d048001c851500980421501e89000d85142000396094009421841c0c8000c05030f0f100030042500d2402d013001005070800501080c3c507580d05465000203075100b2a180c00c1d58800000000039445a0300324000107108100000d14110f5a5182d401c03912500024441a618403d60400013543c51070f92103410041c00e2113944050b405421400003070b02d00003059100c54100401c03641015000024a19074500c2d48100711107a082688550615001501002001511001c80079800008201c4004c0061101c0140c3d0402c2d2185aa0b03200f030181c8402444071403100303c805060001a601c007403a50700070940010311010004592002402181c2540c00c41801c0508042d81c5464103144144100f010589584654840342c2c60a03101d42c030600d849644130b1100500380301d85801c03600900c44080020801d8200e4640c1210401585c0342048111070200b0b0f00c09070b00800000001c115141010300a881c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 498831007 1250 498829757 498829777
    0xc03180901030f0b0c1611030105090c031e0304050a1e09110a0e03011404260f0906030403231b0d2a060204030c080c0604030c030609060e0a050607020105060105 71
    0x2e07089400d07031542c40d042c04c2c0050814400f070808000c101c22021210103007144540c02108041c4104904c1000d0500b1220040c018081c0d40c0d01a0b1456070341c941c5d0001e1810100e0390101040300d000c03903101046918501403a000654800c20184001c101c40c0b000c0e40c602021414213510b041400355807401144200c5074050b02e01c0442100410510094a02a03d45000d81e840c020b00001550f15039102d5490122005803001c640000044492091182c5021802001d40001941c050318000d105186120341b4410100c407035009002c04400a403d160142442445075031510014007040c80341e440300c001080d80050900350040c688130311081c00d82d0f030303001070f102c156007095445141c1a55407201401d1070f190108030128044000d51030034480001d41c2c500141008504c1000300e007a000b41020481420440000d8a15002d040180b2003000840e2540810034100c80e04008002000c152a05041c4013a14000404400c1c51141e008d811081020018803940f096505030700821042e01e400300110340d980b2425501c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 498832257 1250 498831007 498831023
    0x30a0209240901080411060a020d080a14160e22110906120a020c010c12060b1204060b0d1a04020f090105130216120216050405010b04090c0c02060c0318090103 70
    0x2d1005540a850200d400c00e0041c4070321011810018001400c5611200044006130400554922059005a030090f000303440c1c0ca409002070b804000c40251001001232400110880031b82061100c079000d55507200c0350000c06416030003001c0d904824280c3c8a543c40080000c0c0710724010406680ca840b800540c0c1d51600e00401040c40d0076103d03402d00e20071100151900c0507150b820130842192200901c21001941c1c1e283c0c42d080109487c44998100b00c400130340c81036001660420105480341100700b1202c3d0b00541c40107000a4020424001c903020941010000b07141d101605941011010200b140c684280d10031281d86d000b8a018400f0302c51204000e1081039002100458100c0810300c0ca600984604111a1407000e2440482d494a981d4500201450005a0001510f4881c41c18135002440c3c058082554240001d51401d10700704503500c04c6104011105668000062280c3c2c8116120285036400421441c0c85030742c006455038407039002c44075001000461240142090030407400c0c0904030390b001912 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 498833507 1250 498832257 498832267
    0xd140301150e030c190302040b0a03080f03040c0e041a090f07091e060b0901080a0e0a030e0126010602100b0a0b03220609060522030e0301020f030a020924 68
    0x19180c200452001c2c5034075005403050404180c598200d1000c03240541a10400603500d10700601003125046400e540c003d03003141c4014008150010200c030422000088010b0385d07a076807401c20501c03400054002000110303190081c0000c7c088055060f80d041c1f015107103038005548403460a141c1d40c510964418000c0e8006800c00c105106060340420807221605c01c076201004007858104046811a420006e0f01703c8010039130f2101942e00850343c65000e0000e450030024002c1c14520300d41c1e501103502005040020b902e0b98606640d1060200700140c0071020741c2441003946111400303500344804d00070000184583e00140702040d1041c06001902100a094059424280700b03100049510081081c107180124135805c00c842c0303001c00d050880b042d004103000210400246404d00507188060000819150b000380e80002940c90b8179030409240798181081108800d4000110340a4000d454000512520102c10002107010301c0e0010b2040030421940305070048140a0719180107030080000180e21241401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 498834757 1250 498833507 498833549
    0x4b0c020d0b0c04050616050f070e06090703090204020d1d030a0507080a0318031106010501050315040e100f0915060b040b0304020a150f030b0303090d06020904090c080d140301 77
    0x40c0880e04610125002ca14040c0c850b00440c18035400b415501c501003640880103030a01606000c80300c4400f0b1940054503c40f0b280c03a214102220014201310711902c0c81c00045000c1c24003a50111000030360181055403030300030459042004011103513511540c03864078160f00349080408800c40d2840b6260340caa00341003281e5502c4907015504072503c000f081c141d45480220b220200d00d0014400903101780e88804203008000041401c0c0b010680c442030502030180148a001e00420420a00280054400141304c00600900c1440c0c40400e41c10325804501c2c200c00c1d88900d80041d0002151180942a05a544a11205100112410380c0310b2004903d2003880140124404c00e002542c005d40000d0045450989880a14417a6068465101c0115518000842c00942c0500034ac2c07840d6107027103015605002015001c0b0b0044501d0000c002d0001e41c0c00640c1042e10355540d0f000c0c03082e003500b1204022409407034100c405c0e61250710020000108110340300b1320074420508411a41070380e003500408001100408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 498836007 1250 498834757 498834773
    0x4050403030209030d031b0e0f090c0301060f0306300b1603060b0f091504050901090230060d080d060f1802270d140d0e010503010f0302014b0c020d 65
    0x145420790003050f681d6007001503690ac418040c02600d00c45010742d602e500d03041014244944640400c5c081c14140380c4100440d0b0a02c00b040921031034540380d507824140220410b8003410000000040918107204103203c0302c800604861402d041c8a518100265034907004141a076002c2e8107c903c042001c200f10071856410401c02000ba6285005040350130a03032144002040107400f6000131982c030394041443c0200d00c019207140178007103440100c0d16000110024100540071401000c49000b40241c080060401640b10220307225030b20381c240c04001e1141c4071030a200408040303100e09408032200d401301701240006482202c644801618050404a26102c94502c5ca002c1039406940d000e10045038260224040180326041c00c0096405050342410303400c40a00561080c98803581001000d0005024002150031800706032074090800084091048007000c0300b00101800381d26950580200a203041d03100d801d54403c041c0300b13480c0035406641b65920222000d9101243c081c1d4880c1c2070300302004c0828008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 498837257 1250 498836007 498836027
    0x50a051c0503120c093318040906060608010501110d0c030e130507110a03080a0b030724140c0d1101180305040806070e030604081804050403030209030d031b 69
    0x10724160303418000c1001010518034402c039503e65043c1000560001240b82c00b05d00c2c0010040c10f100424040f603c241800c1032441c29500d21074016020000300d0b002c21081029580c0c1d510392000b4800e100c48415482c4c5403003d005103124000225082000108166004144001c1c072140280010b024001e014182101c91941181003a01400248503012040d5107035455036003103450207540d02080a081805004205071605000f250341908107074041c200080e800004184c202c0301040020440703c0a100010342800710350341c04a00c50280034600003618003a0300c0d030030b0180302900c0e03191840003812101c144200c07842000742881c083d801500d04d04000600030640541c001d0000f0300000f42c81e00091380741c0e2910018100c41030b40441d001103010000e20600700041039100c1c2d009e03d48080e6021234040460f94170300c0040c000a09101c03000c960304c01a1001ca003000305110a00400600c124180340c14041c2c001e600c081a203038000d005250f401c201c0f09000b4019426000802d40125070031000c000800c42e100b01c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 498838507 1250 498837257 498837263
    0x1407110d1809050c070c0608130222091a010501050403150513020a06030e0f0c181e0a0e0d020f030a05070c0e0705191d04020a020f060a0e07050a051c 66
    0x1c80c000c1041e003620301c01e541c800d0b10791407806a6904c941d4100b003d00079050740c2c004410813117402d0400101a82d45003c0c001441c0d41501c200c5003400c800b502842090400e148016041d0f403500c4d106e00140003800d1032044061a800060000036625000112000c0c0300e28040548004501040034191803207960045034004141d4040c94465001a8000381c0748a041c2da1110000a803240c00310009540e081c4110304011186500400ca4411254046000c04800114804a000c1c0540020700040c00000c05005280d056004074010f901c0c058120304000c040720054003243d0300c540c010403181e02d80000b560070403042c03850004506051030204201d42d607601c95501201c1c420007410b4000b82d01020351074501d0042c041ea88502d51125903995499000d4416140c66100700991200041c25110780c0c08182090040240c5000d6540c00c0008000c1e031620085102c03000c0a40300d040704001a43ca1180d120603000c504c0303c07007600c1c50f045d61501042002c0c4a180500f40d84001d10740f11420b0001689004a095244 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 498839757 1250 498838507 498838547
    0x20118030507060e0103020d2f03060906100203070c0801060608010b1206130e0f03091512040b07030239030903060115020f0307030503060f01170a05060111101407110d 74
    0x5179034a13002d84a03082003914a65071a1080c03005440c9819030349c840c42c408228000380c10b40c2752810000d154000050306030b9003e000d5024062750bc4501c00d000b240c084a07001000b001c09039984030200c42c001d18991003000000b0304240008140400b406c0b04841001d210a5080c61894442d00300b007110051540100d1051a542c503203071203402c0c001c00d0250348094915803001d503403154140c0d800d1210903002480108032031581041078104200c038000c0390300e80294124402d01030550b11658103400034496205130070400303c0308102d0301805d00c468080000c06080c01002201c070440c12800115640e005481441d42d2582146005001c41e41081c980000140c6182c411501030326500300080b0300b075501c034100580010314000204181800d01116100d040c030802e10303211080c5040d00c880e14900341c9000d000142d040b43ca4501083c031a80c8903580084440c0200d03019540c0764042c004000f4000e04c05501503205c0c0501c60380024030b805000e06603503441051148003501f40511103060848000c000407403c4403d950b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 498841007 1250 498839757 498839767
    0x9151e0905130506040c02030903101e0f09020315011a030603070b0a12060b13031103070e0903070b061005070f06140103060902041b050d020d1e09020118030507060e010302 76
    0x10761a60380b0a14034003020400028542000000e02c01a11001c061005c2958002c10541c1801c0d200041e542d0707030920760080d0014850540185840e20030400f40b0554801c1400c180741030118600030750050380041d208030100c2d00130011582c5044901c01c001d100d022098004645107904807603c400c029580441e008043e40c01c01e50301ea180b100420f8212441400c001240e450400306842c200d0303c1001e01410240340700c00c2c00c1c03548112900c50032403090f0100500d44400c0c00e00d090001d0b142041078902410004243c1c52541c60501003450380e0703030005082a039520720214081005420412000b43c1030a1855483ca841c10b001510396164620708003400300da000b81c0e100c0389500e9180054420394043c500c030f6000131030b111805004010541d802c0b801c41600584490b40124020f503040781c01c540482040380c50141e101c041c804c01c00c0d0000c120780c144400c014070f00f407821248821311590100c96174a101341c84411280040400114004540b4040201030f07030710491080c482c0c02e0044941356216501450054640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 498842257 1250 498841007 498841009
    0x120905030706150915060e011106280504080703030c270e07050316110309030a060b1206090d051303080a030501090c11150a0908120709151e0905 64
    0x59481039005440d82c07562401c0014841580322408001410741c0001031001d00c0394189015481c2000303100d070005110780080130440d00d90081380c0701c40703a4a04100a03950079203030040360817410100308003e004e03a61002c00414826555203218050246800003941d5040519590301500181803256402e014880d41c1c41c000740710204403410341001c00300801040c6000320300d420603400311003202806141c148042801003200c0f69246181c0e5001494203450a8544810201040e0f42076100d002006ca4150180d030b0605800d02c00240c100150300501a00e40b0711500104141a07601d03901c00392041d002540062180300303201d0b032180015080b43d4118404401c0d030303103550b86d41e8400e240d4400c150400c0869261300040015005910646501404a05040b00320303403102d54905031500c00b82c5808204000c0c02c2004a01c406903140c0c041c00302540d00c40140d66403540780e010a5007140da42150030b5000641640004144809442d1129488815035140c40f108885848820705100190084800420201003000211 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 498843507 1250 498842257 498842263
    0x4121502041502010b0102100623060f0f0915130e04110d061b08010501020a021201060b070510050907181815090507080c2101060902040e0f060904050c01120905 71
    0x4407480c3c00010354091303154006800c00c10300b0000c1901482c5001010044101c2240c00b60b0803803507070007540380c03241d64810000601a0051445466102401041003101440710500070300b01c80b20101d0b1120300c800010303218203403944144075a10351940300d0048200041e501d06024540c001d480f400a60322104003080106804202481050b103842e41c6902d8070000343c50310b10b510486074002610302440c1c103604100000c0d41d44e050171a002401941000c007460b2801c0c0080d0b2066014100091040345c2c0c5081908049644005a42408214030724000106a8000000584908880450003103400100c4201110b4005156510030020b16201002d00c420014006800d0381240d4800c9080000b0404181c0c01c003546000003980040030705900c03954140c0c1c05580c0704e5036101c00f8840030480e0080c0301ca500e000203601400a40c0c2c8802c0c010344c0041008110142c42c7c1ea50f02d440303404900740d00a4980d842d2030420045007400e55015040750400b412048095104804448011848084c04200088180d50380c0740b13 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 498844757 1250 498843507 498843539
    0x6110708011422030f05070507050a080d14160f0602090301060f0810141f0b0d05072703020f01090e0a0606030c0c0c06260403031b050412150204 64
    0x20500405504100404180382e4404140b608920031043c240e04042e6405403c40c1d03941e0510710b0501101103441c204028080100304c020303020140a80c40480e2303a500c0035941d50403400e81381d10042140351684240080c02c09082d114401c1d0306121401008880d520b4501600021a00c00e880407902085010b6554509001c0c00b4010030302001c0401e011072400159501302424507440d41040350070030510594404c04d242c070a58200814820a031001160009886940740555101c5059001c1c0401c07071031511085035009600c20030807600d61164113144800d01003120441c81c09201507507145e4140504c00b50401122849880c03406041080c0c827141c80301074402d151002122504007880e100c0d0414008207500d03019005001e0810705280c0c800b4005662841d100c0400c5008680420035801d0001184031000081e41546480150400362642890304004003d814106a40c0300c240c0003c401184240c0d12500440d001c48400508511441203d030740e0f4040c404034110211a01c16409020100b1000f8401030020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 498846007 1250 498844757 498844781
    0x100f140f0c071703040b07020f06072a060f0804060c02010b04061806050f060316030603120815060426032a010b04140a0207141b01170403090611070801 67
    0x7081c1c9610f803c040c2a001e049a64610319603030401c0c0410090035895a041c1c680045c0c0c1110403d8642c1c4440b0085400382c0101c04000d4066a1818590500750100600120314003001e4512180c0c000c4d29050240c034184540303c841e10004c3c0000300082c1c04140d150b031015118410f544004948804403400003020385180c1d800030720643c070208030680e10900c002e204150080c43d00b81c0d000075070110410009a1503010040100400c0001d803405103860310b1003540054042c607401603099403100c07007080c80148400360444924a1078020b010240b155898800d00b524101c46c1900080c50244800d10703143d8440fa11603130b4402d200c0748414403e400b001d00c0114516805843c03c030502e10340010a1816641c250742c049040140038a18040303858240600c0701d400243e10090949016030b4501c260700c0c11403150342c02c9000d146000c1c096207100c003050950501007a0304030003090f81c890148900003480302d006c030002039034010301080068904200c0e1a0103801503200000703100003940c20407507a0340645425201c5c0c0503402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 498847257 1250 498846007 498846013
    0x1709150903040810060b04062312060918030f0a0905090a05160302040b090108091609060f0e09150402130e0319050c0a0206030a02070204090503090f100f140f0c 71
    0x10f00038101d041000d04810b00d040f0506000251403c0001c0c01e203407185000314010048507101031545090075660600c0d1090491480316a50000203000c0e960014050ba2000d01c2115004040b486140d080c0208000d01069a40603629042c800804400a54410607140050102402e00080c1c1590350b242d031b50b48604803111022074245011002c002c2118032010b0b41105041c814841032218181400030386070b4143d0207081c42c100359100c9042070752910700e0344c0e0903000c02c0140408020403590700b2900200202c0b0451003000c1c01c815161813000c0c00e14201194071081e03503030001803040181500450424bc105002501d2007102d0460980100d040d980c8100404040e64400200440d180c1000718051144c9906071507c1400c2103203804020340c40d90020701e4083d202c1e15000c03001c511010400e50440784165401041040304448610f8580d4603a00203000403403281c00d002c880302d101424400c924030070300c140c3c55640e001070814000003a074000b1034100100c10001018040c08000c121041c0040059541d00c20003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 498848507 1250 498847257 498847259
    0x50a0909060e0a050d180510090f060509010c08070804120f0201140301060c0303050601021204080109051207081c09020d0f02030d0302040b0a0e0d061104061e170915090304 76
    0x2400a5407030806080903640d0000d80c000c804140046145442644185081c80d081002100c864065041b1600000d502c41e44211030140b00b40e8100d4031003811200540d031101d81a55540364280c1e07403401204465408a0303407002400000450041c0105481c51084900a003000d440d40001c20684005800031140c0d00400010300c010341da04003220556003c41e003002d06185604112006225002200e00201416115002302e0382a81c002e010028a01250407036150311240e031420400c2c06400c1e401016a402c0c001c5088804000030a00111034038103401c0400e052804c01e81403041040515113041c540452991412a030005a91781c06c29440e1302401000031402c40c0c601401011308002c0414040c01c1807502c1008204002c1c418407040c5c81c03103d42a818980c0c1014034040c08140781504801000740214030307014503101d02610040213007080d69082d58640400d40300240315400d1802031a03c902c2e011588001c1c0d1003d072003d4011016034001100310540f05540c038905039480800c401504c01400036000414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 498849757 1250 498848507 498848513
    0xb07020604080604031d0a0533191d06120403020109080f0403030e01030b03100b0d0b0702030307080a1406040507114824040f030c17061f050a0909 65
    0x80d01c070664200c21036100407c545440001804003030182560b48510212001040c07441d03e40d100c0f00000f01c0d800c91010f6035514005418900400903500d00440803c20240c840c1c809900078070001c0c814400040d05903881c007200a01150a0131a00030012011903407030782c0c9818005803240000d041c03800701c0c6007621a1514190300c0c5c0a40360300d6141d001c00d410140703022114070380c955000900c2c1e01400075420700010104500b40c042340c02c03520a464003401c0c4101380000d025071190300000841c070880c4280d540e00c3c1c02d610750000400649501860010818031103002190940c80c2c2075108503000061420f103c10329410203c1807a0520583c4401c0603445441e100da07440245490b4043c0042c5114032110055041c042d840204041c0d5420b184018000d41075540101c080d00c001c1c241800d40e910200c59095155542d031100500c0d800081c0c081154103050304140000d141d460300e6940a41e840800f4094403842d5140d201e6422000718414890340c2615035404002015180c1e03500881c040c000c00d40d00440d03510306a007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 498851007 1250 498849757 498849797
    0x2a060c030f0209130213030206120406180c140409231b130207050a08030f06190b0a0c03030f020406022a10080709050a06080702060a150b0702060408060403 69
    0x41d81a128a80c010003041815944200b0808090701910200503201c02585900c4082c1030a540c00c0250850400500b215607600b0a0114520943c41294280604200f00c003042d0408200403000424170311108205011b00200c62084002e0701002030000900e09469841c0e0300804560074a042c075001a05903042c1c1b040b068240490700042510141e20880c07100c819001c1500c5034000f8a101803415804103148080000600c50010010b811000f216240d09104204440c210800c0e00c80e240305074020b00900c1030401303e40b9560380482d00101c0e030080c1064070042c0c00351880003a04404070308040c0e4810301062200103c2c40500044e141d9540101405101d0340d61a00341d102c00004401c3c1d00d0340307d00005020342d0b03940b60300c5900e60440303a11b402c7c0096224010300361101c41164001c25403044800e0070214103550f00c01e41142c8035031070b507600b220700584074030440200b21501c007010100e5002c1c0c06e075410303c50a0404c40052501a20103070002e864070381d552003036078142482607034220b00103220280c01030300e1400e0706 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 498852257 1250 498851007 498851021
    0x230010605100c060b061b0601060f031104030609140105010b0a02010e070f0b0708090904080a020606010e1c0f0b1006090b0f0a1209061d0d020609030301062a060c03 73
    0x1942c0000c901c0302015000b410303940355110300400039074982240151a45561041e10f042c2c02081c1c11f8140400402001141c4500d024000c03034002075030540102070203030301c41d00692003009102c0c280c1900d0603085483d402d0240c603085109540004488000103409042445032b107001b851200882038841500741c00080c25115a481024160b620a07501488036080ca5a41a8100ea04204d40c20369206a44e2402680d5800752524040e0320042a508001c1848002001084c11b174004c2e07400da81c00c0740d07280c6005580b8400072014040c0c0183d243c01d801141d8412031a00708120f6402030394840d5207400c19984100300307103900300d80a0980d00c6c040241000343c0c540040713150003d060400703060f900f0603c2c080030511450043e840c2e1101000200380070560111103542c002d0000c580c00860a2040c0401140c8421407805150f0081c9010310880c0c010800451021034440c2c000d02101001d0741c81e5901e0200c00f11450a01408943c08035481c1c00c04031310b60740d100000701d0340d43e881c41444045411400c582c0040c00b21120 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 498853507 1250 498852257 498852259
    0x32d0705031e09032d070602091018060f2a0314030903030f15030a0506010618050102071202010e101205160203071b050d15061a0706090230010605 65
    0x152509014103c5408400e80e0340301000100c0e0045040c284d000c0c00d4803115901040307541c6007240020f811042c4044c5800030000300109480401840c0d081d00822181c00c510130b82814249105203000703000c200d2046c8200301d040d20300d501d02000752005c25403010b000c50090400c100c401e032004040342c004044e0041018007010340701c1c001c500e04600d07200058640787e100080c040f246a222040014081c03160889001d1885a0064205d0f078201505145c0103035240000e00640300419500658044c410810b01d4506040d2041030303014146292030420f5144804103a50000c07410f002c1c10910f540342944a503aa0f4502050995a0f44029a00183e00d01d100b1604d02a11440b603140304135030441c6a960f0008110760500350b0168061031051001c4220408901d096000349a016401040c0e200c28481d00050342e1f005c00c40543c1040080d2582d90608a021071644001a01130800c240052004101c581c0c0c42642405e002800d00300e07445008403504140310281c82c200c100900800581c01410314000d129020141c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 498854757 1250 498853507 498853561
    0x1202030708061009111c05061e0d0609081909030b07030c0822080c0a11040c27031e0b0a0519020f0f030108011b080c032d070503 57
    0x3418075105191241a00491400b00d44940195101c5c480d51002c9990084a05600016214900310294050041561041c2c458003a034140712120341498410224280b100400d0000c0590349681c640c3c001c4c6c800003000341d410300c805024026080d080004048030700250f079035400042d0f50540c948140b075080e0192030030040500e440748261042e9000030500c0d401c548035010101540c440c410b42c0c803004c40c4d440980200403480105607001105000951250340074030804000642d85280418082103810114140000546217855442e8802414807203401c108107211007030807000e0301d80d00d8200c100c010f14852036403158000402d400610854104030b50304031080c440240090705000d0050541280d40c0e110b00941c083d030010f215a101c040f0726003296092802045440e85079039642c10124000c150042151004050540d07603c80201e01c194903140c8111103000840c0c4c00c0da1621312b402d003030003100c488001d44104244042c03c01502035407140141316110642d1861b540b880e0480650100115040400405e52 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 498856007 1250 498854757 498854761
    0x261e01030203030d02180a03110f04150b0901200a0204050c0306150a03020d060b040501140c0714040f02070f120c051c03110a02060f100303050a120213120203070806 73
    0xc0c0d03001c0201e41c0d6072501c03104c1c09070b1200f2641c281d0f907182c907150300c03031056010800034000410002e4010320454a0700d400c0b270310b14580703000103170602068840c1c0000c9603c4200002038107000400300c8002912000708107251401034104500c810000720f100000c00d015007a80100500c400710310b898061503900681208421b829400c25a0218401c10016240c52006030000b1440c1414188254161008000c8051091142030f0303a454460140e5409802203d000402c100c440038040c0004108560710402e007040188440c5113001050360103a0188042c41e40c0c02074813060304144035800b0f13002404810b406544203581c24001807405d049080030100070f6105115040b0b160380d01080001c6088800ca0000c00c042030750a8028442c220000d0102c0c072901d225200300803d2425003903a00150143c482c6401d1008010b0795154107958103040591440f0003070000d00100480c1c1902c511590700d101541900450150900115000890010351541c02550040200d4074808041d440c00b00043c500900130304000c4c00b058 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 498857257 1250 498856007 498856009
    0x120d0f05070905062a010908030a0f090f080307140408010b0f030c03120d0b06040312090905010e0414120c03220e0103170d0f020307230415261e010302 67
    0x280540800e10407144000510080170800000d182800c0490b480001c05c0503084514290126810a56004444600c0c06107480515080f611031032145a8000d020708001c071400b80c5d00c00120350b00051406007081265006289407110007005000a000c1d4000081255511803050220461070b41c00300342d200c2c0d4000d0705517003044d84005c50403004002e100646035564160828040e0007030221002065080302c0005000410300c48482c2081c130030460ac5075100c1c410550f550004c4425504203008000b0100500e50200f400651202000e000d9400310005503204c003140c040c480140c503005519407048640001640d480c2150007aa0403030b003200550001d1410050805214580710441404020130400c1e800d140104150300744401c1d11441c166400781840b0468210b03a1000194209a5040010804e81024501d08403a040c4442106256480d00e080c10989003840780400e0221140b809003e0028a0f807a0380c1c100750700302e040d4011044210f1040b1650b8102902d41200700b40f0304106a4000c400c20000600c01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 498858507 1250 498857257 498857269
    0x5010216020108280e0a150212090102070c0b030601020f01060621020309030d111606060509060105090907121d07030c050a03050705010f05122406090d06090302120d0f05070905 78
    0x2034001300c1c0200099111001248918024041d00045c181e2080c40d0000b52151000390000c000340101f008900103251903000b07000307007130780078101c4000e1514074581b40a0200050080103198081414411941d1000181684600f1545150441800561162402e042c02c0ca040f040d40035201d444580b04501c1c510740401d00135100d006c0d00c00403400d8079440d60154521003007410b040e607041105c000c08084200d4024540180209814815a40902203000c0003074000e600402c01e0301c5140c2c0024200620968844604480c200d00c07243d00d4480c0c0d15a6103d02040504402c0800c50260840c034000f4182103080d030802921508081e404a441183c03c03d005000140c0003140101c00c5610a09007207500403d6140d040d11b80b0b011b95a0300b4520a0b4844c0c080042c5032048884180b032031901a041d10310211600c80034821584540c0d11883c0d0003541c0400b0075000070340c1c140d003d10852406441560042c1600803003004807a404070452035804ca440301484806c600b818411186c01400381e0038030801652607c0301083e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 498859757 1250 498858507 498858571
    0x18061806180b0612030415030905070504020712030504020a0b2116140724140a050c040e1905040b070306060f0c230304080a060b06090307150c05010216020108 70
    0x80a64030081c084141c0907000c0003a20040e005541007804c80c0301f4440001802081c25100c142d0fa1882a5100014903042520880e4640b07500a818604c0000d0180810743c080c00c000f030000c0346c0004004400241c540d41c404050083d900030307010340c0c07010f1202410115a10700000762113080f02800e48440e5260740d0360850b02d03600000c242c101e101d1361961158100348180b190342010000c4050500105003850780700c5540f0030342120002820303000d580e41754241703c0c20840d00101c0b000845d814040109202100c4a4000e07245d001c0060380c008003000452414203415a00309550440784040782a050001903505802603802922491030580c80b00d0881f0000146441c0c20601e0180c40100340742901c01c0c030065194091003c25402c44c1c2100d6031113a95181c403540d1200c19000c10784145e8908082c0700268a0724008443d80d80700010001e04100c0e080c219030116400d0003100c00c20078804c200610b580040d10a0015140d03070300002c64958900d9015000142006a005218842030040291940340c0031541c4281c0311 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 498861007 1250 498859757 498859759
    0x30d0b06040803090d2117090d020705010c1502120405070b03061c0f0b0c0c010e0a11060a050d0e0705010906050c0d0e0d0501020403060c030e030c0601050418061806180b06 76
    0x40c0810b1007414a05482041190300100c0c1e0305506030480c0b1701b284c000035118004500a401305c20546c1d00c946580d600c800c070702c02000e80140c1046001704070f00d601c11008417400c58000c150840148401050440403a405030b0840105003028208120502109008510081215010591a5207080c80014802840659800c0300005480011509210070f090b1680c0c4010380c020800492807c1284440c140380d00b01c0c1c1411000c560070200d4000304008003003583c07055180d11041e1341c01e03017031003060402c00143c20110510b020000c1c14000d1070140151802403070a07144a04014018103800c12000420b0504640c10441c280041040b007809049070015002c000282d617403401c0d01d00c0c2c42ea0140022503100c24408050411340c000303d00030082c00032a0b48806802a0213403402c00c412070114001e56142e0040d038058000f00c1d04418010451810940c020708016809408460418101952030000b11110801402200010059400d04006203441030b05c3c070001906801c800068070310b41e070324101d07104010202 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 498862257 1250 498861007 498861019
    0x150301180b01020a0b012303031204020a080d0e04020a020f1603060b0d03200304080a150b010e090424020d02030610090807210503070f030905090403140c0a1202030d0b0604080309 79
    0x30001407901042c40d02003411f005054a03605c3c00e000c1082c41c80c044041e01c0503441140c000d180001c4020b070000703000010151030784a41c5281c6912404000080d0000302820041d07000795401002106810722a8002c05001c40b01c5401c411815418102d003215000c1300d0b6a8040c1c007001d065040400e421000401020f80344111106c400710b1082000382c00c0d0f02075603200c10014801d014071001008051084180d08041c1c84030b08004c645014401114840f000600e40c0c1e82003a412404900070070007010f540050b480c1d01c02002c102400000c07640400300d81c80340b10542c1c400d40d40413050003280e18000f03800c030f0f070303090310916001a115003003001050321140b007845500e080344140f081c3d0070402009445270040c1280c106c07042d0f986500417070520340c5284004a8003100056030003075020800d49020f0740258010303038040da1428150308195070412600c1d4082d44400300c0c98461030385000c000591041e00c40201142c070b540035503228604658104161040c03030009503c140d406001c00c1c489010008295104e1510449003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 498863507 1250 498862257 498862289
    0xd05010b04062c150c0f0601030f1b03170703030b040b06180f061602090901180b041b0602010b600a1d0d020f150301180b01020a0b01 59
    0x1d6414449600c03d040c907001140103103000140c04c20b100103424600041c0003910b01c0d0f58140e580c0d1903194902400002c5c0020a10008100407038001300c0144004a82c401c030819080d03490351110000c0d0319080c07916050049000030000101903150150945401080d00c0c24006022a0340024203d405480004082140040c150005030303911720a03000090600034140640e2040c140c3c10503d100ca03400c000a9014506034800b041703070080d05200310606a180200803100500003070f500c03900d070071802601c1a1507030410407070400d40441510740072400401c3c2c19000061070718014800d1040152200f20310903085841ca14061030849040046030781c640107144907010003420224a003c4803061070110b01100988007611510014a0b544000c3c041000c0c15101c000b9100e02084401240010400310283c00844c1c04600c84011300f0003401d05440e4900040c40340000003045a81c645441c0c200360b005202e6513030240b10114980f003561180000c034001c03c0c405041010095103e81d0024041840384000000e98841 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 498864757 1250 498863507 498863567
    0x705040c030f020409090b0f0f0a0209130c0806031204030503071119120b0a02031513020d090615060207032a05120c010e06040617041104060b0d05010b0406 69
    0x8001c03611903089080031504c5586682c082801040207400448440c8403100100341440c120380d4074284036030300121f1078100650790b07108100042d421011085400102c44031164034152480e0142d034403e091940c0c1c82c150a45081e41c01c05103080c04101c440c0000001c2000f061010074004811144195040b004a04660b403e0401050401d181c00010480501150a0204491001d5280829900d0091100e5000d80d1241c800020483c03000b0380703048444060340010303c60941002004100690350b1451300504041280350a5000d0f90048582211540d90396807110300d0f0300c0c1d0415135600c054811807004003e21030540d540c224006070900030142c0c82180031588103041c0c1b8000d0164101400d400791003040d00659256145903a09002c1200a02182c59144507001741d0600c201510102c440036916104040e07480356201d444600c001d402079a00300e11286100000d0b486a0180d100103042e41c1c6e031165581ca101504600c201ca00c103070070641c0903d401300000c110180d40690300b8402c62504c1c000c1902500400d0b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 498866007 1250 498864757 498864761
    0x3061509030c0a080d14091f02010902040f0c080c130501110703060908091f050a0e010c050a0507061e0903030e0415060809010c02010e03031b0403082701030504050705040c03 77
    0xb40034990000f1100e03408104402e0101e207011a0075880c0e11012070241481030b550701113000c2c0d611001c0c0c206403400448040824011504406200c89000001c0c80301055000310f4155507c040ca0002281d84800e6900c845650007000698480e8140c0c51490030841c006d0b00005800e0381c90300c6500d0400c04030502481e00d2040074050180210f911070307000c0001e4022843d10032070030b400c1380d5042c500c1030b2031b0342183d500084e111901e126072032400d40c0c0d2418505442240c0540759840311044940c1009070440ca164005003081281d848454092402003070010f14201008204903482c8441c6e0701e04605c0d00c44040e140d01d800c00101801d6a925080a184082c500c0d00450000c0000c0210844078606803100015640d801441060059480700b0007484800b10383c117010780c240c402030a2165000c0c1d10800000714214000203520310560200955149029a40e44488821f500540c0c2c2c1c10610802c8a0300d03843e08900b00b4046042d4241080c01e05000c03910300307034541c80c1d2548642e00c03800e8011a00c45000150b82031086d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 498867257 1250 498866007 498866023
    0xe0a051806090d030b0603040203060403110a051006030b0711030d0504060b09040f050c04020c0c04020f0f190306090b18070923040501091506050d0f0501090516050306150903 77
    0x2040350786601d003004019550b41400503100c0c02207468040c60205034100b05046038882c64010b0b00a00c00c54890b59822903a43c100c1e100d44034001d0040c0201c0c0800070340c040c4007400c50b60954041c00300e03510313066050589400700301400d00d0781400203e0081140604000c4250382c01f413000b44000042503a00d504005001c4c010200350140e00c210341c1c030100300c20014035002c400030780f601400031610036540c40c4061100300d20800551540a0f40b09500013041813400341c000304100c00d032400c1007034180b40e008441903065800c40e48203403564440e490031b0040d50ba5494440c41006003e0041c1c2400140680c00c041403c481c0381008445059034200001451240540010300042002e010014001001081c807007158038800404640305505180000410030860b004101d00f105510800c05686450f02d83d060701c16500c0344c40d407040c00340d4540c40c1880500ba014440e60b402007254031400305003403900f12401481440100006800c1c41424401e00c091600e511980d40400540c560701650b540e000ea1000138640440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 498868507 1250 498867257 498867301
    0x1090f061e18150c200f0604080301212a0302030d030609051501020606242a0115120204020403060504030f1b080910050c1e07050a0e0a05 61
    0xc01401140002d0111404081d96001e050518103600031094070320b003520504c0103e0000a1003840401d00f20380c8a010700b03083d41110001c01c49204203403c1c0c0115042400890302a144900088010061000c074051017071031003484c0780c058900d0704009030341c1c0c00d50303035050101d1414404038410450b01510318203400c0c08020b503030002c040b12451142c040b00240584098010914220708110105014039401d4481000d080c0c0d0503006401240d6640c8240020402000e0843c0c126604000c00380c0c000c600318400070480d010b00b58140d20220380c0307911b08822440041e0501301d40d181c1c1c5407500c814203a607610000001642e9040181025205590000401031700a41d04042c021925000c1031204040c2c0040d81150300c0041a00c650715500500c010840f01c440700b58101800710380c0c041094030b04030306d045065900341c40c2146c248141480b010340c460b00c0c075021a600007001901c240760410b5002c00001c000d031100074074013201e064407a0360905680315007114000c1c0075000126241c8010800d500444080520345983c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 498869757 1250 498868507 498868511
    0x80c03010b1c110c0c0a050619050d0e07060908031201090e1e01061d040308060f01030f0c210c0e0d0c3f020d0213060b0a05070b060301090f061e 64
    0x40707681d2103d0700e076210f003c68190510640301d04203101c2c01c1c000088000c65900414450a01640750700d41c01c8102c2d01001e0110402404222500c0c203401325101d81c1c440b0718886c0000f401000d05100010f00018801d4110200a41c030521900100401000f0a01e06460220001250031f25520103154584440403104460b42001d402e0702c5040340b6170562096040b41c5001c1131030446801100c4150b19400310a49028000801100011300503041c5030a003505081c8062400180400319041940c0c12985480c04440000c1c604080d520071b007106448404070888028002000601c0700c020b0040c2c03204159880a07030050400004040a100341c184030742c3c1c003c000c00000d00c005485141140d00c800100443d41500085180e042d000c2c00800341c030869840c056014061407188081d54080189242410310b07181c004507291030003c580c05650b00050078610001c0c0d200c5548500c2d01d440c0c03d161b20303040204614020b84c50000780c240400d102c00c0340d4060442e01b00000103052924250b40380d4881d18442a2031250318 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 498871007 1250 498869757 498869771
    0x90203151e0d0809040b01091206020a23070b090304080c0d060f05010b0c010e01050f040609020301091202031812071206021e070b090d120216020306091c080c03010b1c 74
    0xc400c0500030251320380700b113a08104d80f2480b07a0041d10260007500508200c1703c0d9010071800000e050303600a00e2503038000e0074000860f8242c035040b02000004995840b40490011411404100039011940e0b0880c1b4194003640c01e250600b20101e54400c3c0001d1114841d0b440100344005000392a40704002d00c7c4030700c04081c0503568540300c0d4404164084c8540442035842c040c007020042006121b924014103814040e408503807601d8403000003802c50548166899541e85031040c0010b08a007040c100c0c140815000b0707649400d402005145c1c50500344456038010710f0131295808503d14040f440d8016a401c02e080c44080f50300320700b8201d000340a0301502d0365034204103003d03c0d022210443d0103454072500c12000c21007a40c1d10101116268000c029113400826520640e04a01c801ca03600a000080d8411007600052100c41c0c000030300d808015500c8080c01e403c203040c1c07055115418100c000300c158160401001701c0c1047c03503402d22117110500c00c0b44858040403965404040300d04140e424818401c260500142c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 498872257 1250 498871007 498871013
    0xb0a0207060b0a06092105060a050c0c07030b062407060203041a09070302090a0e060a0b0d0605041a010614030c03070c08030f07020601090b15070615030606030c090203151e0d 77
    0x1401403001c486e420140302c143c0990f400a94000007507103c2e026040703d40b0744c10703001e0014240c007803c54240d501e407e01c00c4031044001005210002e6020f10521504d90074005c09105000854400c0c800c030000c4000c560286c9000b140085441240e4008801640d075991410035401c1203141e200806091400001440003030040003c0c2803050760700031200160385454524071300d42100d003880d840080940155001921888003035206044118028004840b00519650b802048079030407a4207c941c5101d09070809104460444100e0141550782080d0b81c0b104502001002203000084c2020036610b8004009801b15100f1454070311841d60041072692281402d0705039940000d81220300030014415440000382640c0d084c00343c245440b001420410140191140040302c6a2140005940d01600c81d64000b0420f4420501c4000841c054040091518294031341507903a4070469103c1703400140141b0503c0446508140f0940d04208201d038006082c0025280030303889188950000c40e440303d1609104014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 498873507 1250 498872257 498872267
    0xd06060315051312030e0d2313140301020409060b0702090f01050f06071e050706030b0402180438010207171203070905100507020117040b0a0207060b0a06 68
    0x3503a1042151041140100280e502101c0040320f102c241c00358035074441004141019050403502a40c2d2030080f4100d01103a0005280c400c03210100400104110784000b008070000041200c00a40c044036140f5228040400d620368000c0c0e402841c0c90914095100e040300c0e0380c05d5040f180140500b035014000295200c4013828241c12800d01a030050083c4030004500ea200700240328166280140300060050f213010502045801c250412614182010301c4140c0d50f5840340c0d01c450303070301e481600186030007810900001c00345c40c3c595840724011401070003012040144100307c4a6842c4040d507000650f284c0003030305850701d009080c3c40f012070b0303040c502d00404580c3d030307921003900e4140c07403c2c0c085554a03641c85911050390708104815560540000e8454000d080d041c400a54120f00d9616080108603101c00004c2d851406a034000008560002041002c6581003c9494801e03400901c9034400c0345400d882e40c001019005122004e056800a4218200304640e441b480307600801800c1207079081e0b101c180141c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 498874757 1250 498873507 498873509
    0x30b040c0513140117010b040e0610060f0f050a05370c080a0c0c0f060810080d0207090b0a09021b0c090c070b07050408032703120412110d0606 63
    0x1000d007a5902c00d5842d111150301a4140000640c449280c460b80381584402c0c1300314400f0480984c0755240d120100a41e41d860050038500454613000e0903950500100941808403c1e900650a000c0b213040f0a0745040d801c6a10a241003005041c079983d2131600400480710b81c820740540d80e03a0641d90000c141400b200f0423804440e0101e95000300c5950704190349040d1111000040300600c1c04008020070104075110f000416071042c411415884408e40700c0201c0700c0c51601681110000883e02002c120030b000403071582100903c40d0001800318141050703c001d46075030090003078181264407000103102940f01e0010440041400910454890009a6881743c40000982842c00e442c4034280100740c580c03400c81c02c154020344284402514200941d42d401c06540b2000340180c05118080c04001401c1d5018070081000742c4000328401c4204540c0104c25251094501599000740d01c0701034044a820300e03100c202c500f6620710624850400d80189821403c05032030002032604075444501c5a800c014458001308 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 498876007 1250 498874757 498874759
    0x103031404080c0621010306020d0b040608060a0e191a0603010b01090e04020a3c12060b0402071407210209060108060310062304021e0d06030b040c05 66
    0x2505600c40c11030410190180340140c01c40382d040029071101030f24104000300608075400c20320000484540c099000e003040e09900039144241c00003502c586030005071040040d000300855081107200e00b410b0500307a444100402c64100d1650f141c98034003400f4010050100c0b980451401c0840002081c54001c4404420100207240003001c8404213105160600600e515a10182e482140701440c20140c042d05902c060410782c4c2040344d080010030280003d543e90f02002e441400880181c400441a042c406441c44046590340a2040010b000410340c0301c0060140c56040500450760190100000b0002d1044900007001e841700080c46a26211021810400b1551003200107a400d1400d88103c0041c451400c400952102000c0006000382d8010129141c128002404840c1c2c4044108402011115030750840c1a00c0c001e0312042140841c80c01203c0c00411b0b01c01d071404c0d13090a200c0390141c0c245499031000109030240c00300e2080030480c0140c0c0024010368010240c54681d041906109404151501030700d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 498877257 1250 498876007 498876017
    0xd0203010f0e03041e0b0712030603050a0317160509061b070e07020f0f0d0f02010b1509040c0203070c061407060f052e0302041a1201022a1207020604031a010303 71
    0x1800700d984017849000ca411104215141080c0d03503450400420001140300300349036176040c020012030340c10804844080d120b61070382644070b54850213550103000002c10f05910307540e6400301c90368056440010ba4041d04415680f0319100c122181c003698142c800010011010300c81c80e80f000421250b00000c8a003d0300c110303020b584912300f24007810b0f9250116000700c101280e001e21031b04e030840781c8107004030681c6821510002515a00c0b0300b00003103082d00300800c261380c80302c0701042c0d03082e032031809102d10007040c4440d00045180002d213644420880b14644a8038003803001000b03841d80e284050004540c0700c1030b0f0108040100d828440c600400501007903a031803a149410100e111428802502050034905162550341d03620b5185500b00806400f151800d0780c510b946130344a50005440d24400d81c8121020040051388425503d545696400010300d10803065000400240c1c0c14014003007040300c1041410480240e460441d0300124402d441035910040c2103410700e040c1c51101c011050a03540c183d0340329a442d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 498878507 1250 498877257 498877289
    0x1008011416092702190207140a0303090b030702070e04080403051b0d0b071808060a140c0412020301110406020114010b0301140906040906090803071701140d0203010f0e0304 76
    0x4882d1003a4034054a40700089080301c00d400340310001005640c084140001515220680c603902008140e000050f4026900555050210302e055a40045107103e041d2a803a15135440e41c2c900034012032a034818080313030b035100001060b1400d00c00d002901c040d20b0101e500c000d0b9400c192400c45000d034031610058a07240500302154004640345211070340c94010060841c4010340094a80c0401c800c009001681404013000580c403a015050f032000d4014030b1800d000d13049070329105004409480581007402128100c140c20005040040e07025181a10803031790000805003054400300380140702c0c8503103e01d07005501080015415905401c050320f4100c0c1b000b4107940b10390b80c40d4510300c0c81c1c0c00203000303981000c42a5035076503080342006009070790f00502c010404148803a540e00c600040301c2d0078140a0b15041c000008120700c0a400c800006041014460800840c0d0704d002e10404010591100c0305210702e203e00403d41c10766809400032007801032600000c100d0810348090003503807680544900e81411601d804 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 498879757 1250 498878507 498878551
    0x81e040305061311060313020907032906040b0309070f1212020a05030a03150b0408011401060c0201120b040e0106090b0f010806030d1b08030108030307030e03030907060810080114 79
    0x110004da20054031504120101d0800c400f642000305180130205180e40403e0259a030040c4650141d0b5050f01c00240d41c50000104034104006a103120602c40c0e801c070001c3c400c0742c0714071040300c0803030700244c5c1c007992a5100d100200d030030505154442c0c610300a66540115a21007008000d4078014452444100e1a468504061340c4441c1c00800c040e0203600203010203a917140c06508a803d4150b0020204841c1c191100c0104200d0740280d002a00242c0d550002e003200f427646230f120302d40941341605045468555940c0003c001060228540544685842c02039000d51500e4001a2006482e10000d101e41c07070700c460140f0000c3c12075545840c0300b014440340c00107443d4061b030300041c010000038000c0c03c1206080300e81070b200010201d01002c201c1c102c0c0003405c40480c0010025502802c80c4e40d01a55517420282c00080584017003c4160405410800900255000004584003211001d0400f403200703550f070043c403240c00040c981c0101d0081d401c0001c0c180103000d844254601c00d810b0411404c1d44502846 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 498881007 1250 498879757 498879781
    0xa0f0e03010b13050c1b0d02010c080f0c0d02040506070f0201080c0f0d110f04422102071a0903070b0a05061f02030703030e0607120207081e04030506 66
    0xb945034200a41c4508501014004e800250b4030044403a01c0c94540007284150117160b00385241d80e281c0a030024168035122690a0003045006405490f040e2401e04150100140002d40030302046440322000640404c24041501039500415004101d2900c9070428100509002c226482c1280003030b03032140c0010540100c20050b01c4010941800710390510340518125070007441c020145040004007881070100ca01416070080c002360001d081107140921b81400f4010020f80900001707424880c182c81141460388c640c944006155846107004038048500251141c10000d004046140745400010040b09200032890410b440f001d588030002e18940d074000040b903c9015056004158140c41800f04010044540040b60420402030031041d0000101c406032402a007540300110140c0c1000c102601891f8051180c0c1541d2001038010342407520f1b16032401011010f0114590031855800300342d40c0140030aa2050b102c1d03262206602c801141c40e50620342038250441d1000b224244070310000103403403040c44c1c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 498882257 1250 498881007 498881021
    0x50d0311032707050d051501050f0f19030503031005030f010608060c0a0e040507090806090d0806210f030310080d0c031b0210031a01030e070501080c0f0a0f0e0301 72
    0x8844107021500342c10075204145000d841542d00d00c0c820010b000c01c0c1540c03a15503e1703c51520400041c034032a01c110b05620907018050b0701181c420304202c5044881512040200d903403502b0b08446100020b120441210700c620400e81010b0460701c00070081203220040f6603110b10585408508840f2501e0101d003844d03007a40c0765400703040700c5500310b100411010203450000e040300d000d103410425615401c031b20210341221400c82c3c01c0c200180045004000418050010907044403070359014014044000f100500704c0340010b0891402805001d001e801c440b81c00440c1041003d450506441c5802c0328a501203540b44c1064035200005062040001030424000521075050803042e22256003001d46a102650f00448007031852000e0000c4104490041c0e031940c5d600c48050300c25490000d000360080d00d504198401080e0b0301c5060500c2d141c140e9246007400030b03100080f41c00928102480b5035a4045003d03083c02072803195101c521021418000403900b1800505102c403055494205800c00241091309031514 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 498883507 1250 498882257 498882271
    0x703030e011a03160b0712050c012318120f2203050c0a0609051c020409050a0c05030a05150915010b03061813020f0103060f1202030106061106070c060b0607050d031103 74
    0x10440200003d1a9104c802c00307c100900b0414204003900810a0a444100c0f40242039020200146400300184100854000048801c0715107810510510199a14041c0d104c50000000118021040c0c0f1004011141940000c440040d5031a5880102e10142c070401e00003110306000d0344800c032155080074045041102d10325600d4050380b500e4203003440f00b186100c40b410340d40320380499503410150f2145c1c000c06030883c2c03052006281160380b508200c2c1134031402c0d42150348242c101c881d5010125400040300c0c11101e003604600f00c02a20b5405006140400401c01d00e10403021420000540c07001640c05180319480641c0c901c842c2140e10f0f100f8450080088a10700b500c0b4094822880250a20f85c0c4014084e40c010305000801944a03d2020796001c42c55111000007110700c0007000840c02c0c203005280c014031142c1481d0320f20b2a40c1400d00707512034800911101c1040690740c40b030390a00009400540720f9032005044940e40d03009609040d03407210f1000d006040864200038030480924512800c507441082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 498884757 1250 498883507 498883529
    0x501080303071d0a0e0c030702070b0c0307111c0f03080906011a0a0207210302070806040206070b1e0c03160905030d0f020c1306050916080c0703030e011a0316 70
    0x4400c3e000310504205681802d0380000c1c2d1a43d010035040400b200480c010166034400d29240e00d803286c402071900c106500074482900b020322008160030400008e54050039070105a00110404805c0400e0030b22001d40001c0301c0100c0d01e410900203210360300074420003e50195444511943d54410b86980c2c0d0701080c03040c0300c12045039900341417052a1203c00b80007003078100d1058403c0d00e542c40100c4032107054101111040c050361601c00108050701004544000c0981d100a891185803640000398103016041b006041c02c0d100c2c0340005e286e1440d014107080b640c8003d0754440482d080060032100503820484c0c084d62070003000c011901a403405040c0c00e40445400400402c041d5403092002c0340d900f150000903a0561160000c0d400055a0b0220404600746501c0d500240c41494181004480040605440c82c10140d191ba11241c4917030003440c140e0322250300d40c031140d035a11491804600800031008110020351070110b605648048010300000c0c419011070440f07008141d21944044019030500c03e01030090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 498886007 1250 498884757 498884777
    0x60c0408100c050904050103050601150c11091003050105161106060a03110f03070e0402100908030a03090f1a0a1505010203120403111c03050f06240405060d02030901050108030307 79
    0x503540108000c00443e140032801d054012000c5400d450303081e0000c83c1d040d00110010300c610b204501e000341d0020801c1c9003081c1119032685400088503070b84011a8050940000059891402e604241d8021035220000300540c0c80c0042103a25500b251000010018044030340c001e951301c100080d03540c040d80004010124003440c50303480e100200401d504070307a084000c445040341c07184d030b051181c48001d14511054180900d058030400075025171300d40d041d00a215000c0c6051041100000c16508422128100000e111040e42001000081042001840f0f440400c616000400304c04800c0c50017000041d0080c05400d120f0381940740303142424080d89005901c00c1c4075100d110450004c2054105020f03090814a0404105c0d0803030514508109615140e1504508160700035810b01c540c0d6880b51203020b00c5040380c100300000030300243c5d8030010400c482e4800304442844a01d40411200103040c000c0c18550348480c4030401002030340040351040082d501c2c00c0c000140c2c3d28402302c1103900c82c42490784c40708801c3c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 498887257 1250 498886007 498886033
    0xc24110109030c1211030d1b301e0209030f03030f010e0c07080d0209040b0a140d0f0b0103081206030a08090108040c150f030f2c0a060f020910020a0b15010320030405060c0408 77
    0x31050725049c40066622280d1640f6a00d2408840b07041d039090480016030f80e1004071003410724000180d200040503510070000c12000c900b4040304103054408080401503130362902c42680c2034a014031030b8043e02d14200083e140055480c603034001c0c100300c031040c0c0e418401d5032079075010081c110400f48030b66051880d280b151041c41d0301d000811b074000d06119070348580080c0880d440302550004260011208184001810301c0d038841031071040c1d9030254044004117080107095a411046019070445030b030500000c0b8000c038040124890303c6102401c0d003222450014100004002c3c501c480000044e4040303841c2860303801c030710592405a403100059100c0d8014004000c202030010004c1c003440c40c00301900031114010000781d030034003a0500e0504518409a200c0c4200400c00c048041c01245400c15075001201290000d8440406c072079202150361020519118400010303030142c10b0b40150705101802c2d20b41c404030306040010107140107a00940890703a282d030322500c0c081154407907030086a10991201c4003200e80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 498888507 1250 498887257 498887327
    0x60106053103140d0c0213020d09290f060d02190b30070e04240f050105250c24110109030c1211030d1b 46
    0x440307601d64040c000418042007140c1e42440c06007810080501eaa104100248a1032402c4144071030303408006840b180903c0e88014004a5601d50028011039080c400300c0044025a03054440c50380d666103050003984000d01d4034104801940c10310200da6500e11140f8030b500003606640c18440c08240100500c55142c40040002118000342c04a1384010360010700b2103a0300a103201200100002d41c4529114000d11a0400001c05d0f41808094a000300b00700007544103010350340c4036400c45190f08101c0640400907001c500070740707440b030608440040840c01585104401114107021112f84040080c1925145c6004664078400c08218a48100000d1030018a09402800c00e07013610340724045000100d40d5594a031154556810014204009050710240c3c2503900f240c40c01e1588100b07100208031017072590350042d10241058402414082e000c12201681038002c8a0480c1c1942800007140e440300407418041d405080e401036171043e04040a000c43e81500e014006902c10482c2c00108080104038803860b1001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 498889757 1250 498888507 498888517
    0x150c08011806080f0304031e1218080a11030115080735030a020d08131b0306020c030a0311040501080a0e0c120f060609090c060c1501091d010e06010605 67
    0x15125a503600000f40c100d20400049440740280c030040c588452860501515214160786001c5e44c2d60085007074680010206085a070041c040341c01c003a00b40034a94031a05180110741d80143d0840c4c0304006c143d5050000d03440540c2c2801d00300301d000b4480302001a480d01c40c60050b5100b4000701e988a2003003805086a000c12541152090111050001d20383c000b1480740340c00c0d0301c44201d0241d000003455401c640d5050002494801250501480c1820043d058544002640d80e001e0071000c02440c85245084020b5040001983c202809540310140c41003030580781e42c005002c4102191820484920341c034915030546007141e60584034409650b40d4201d0b2070000d0310084030010320342e00403c03440b4030300303a83d80104000e140e40750795008025202d182801e85242040150200d071060b86443c003080560740d070001e408030400e4411b9031025100d1a03101c0e083c500e0046c00e100c040640c481ca00300042410b850680c0031011007074290310040182c1d0240140b0700d088402d0301c03042d01e03020b81082c401805940d010f400140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 498891007 1250 498889757 498889799
    0xa090e07061d03010519140f011a090904081c1406061b07090e1509031e16210309030c0b10030b180606030d020d0e181003150c0801 58
    0x102e030801c0702d2000207007110b01c100e413104c68000b2103400c0f0f40c000b202c0d24803880b201c04240d10000c40d01e40c00c24440d01c441e01c6070f0520540384240f05010300c841440e808613040c1e980c042e00c050022034035401c10b464291718039004904840b16400040405400c25104c5000742000d08814401c40412600c6480034800e20794004102c1c0490810111004800c464040020b48004c182c00a4000b032480c003801d2802e414040c0702c0603292003420002e024081d01c0b11002c411102070076810410201000d5428003229124010240000c1e04050085003600600c0f071001d01c207004070344a10748151400401400e00741e0840394041d10107000103404100342000900c3e100030003038101c3c5e1440711401100360f99580755000d1940c11608071110203a4441403c007034501c100400341c1c104004801600441500440c0207580b8000c2503140801c0281e480c400c102284c42d0212200780274a5805880340da2442c02c4034003005414003a100803200140004e03900344854489214002c2d68080a0f80c400c4450303480c00c0044c0042c89022030b091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 498892257 1250 498891007 498891047
    0xf09011e0c0206070204140a0c0305060f0307090c030e0d02030d18030c0b0403020102040519090513080d0c030204050a1d01060905061204020418051b0103020a1209060b030607030b0a090e0706 84
    0x81f07081c4070000d00800c4d1042e0105140400c9501d19480020140c0e07030050409030051500d515181c0241d9004034250090b40d41d6084002407460080004078080d0900610041e040c0c015015054103490b404030040200e400800003d0220420803d000100c00e5107545c00a40080c40304102c040020b030401c842190003c0c06032001506054172100003802003030003032640c01c900884c860020412441e840c01417540c8050002c81181e03140186498a0319070784100900101203550754400d110342240687d050398040c00c0f0190400c03c1580e01c030401c0c50210703080c20305203101c3c0601c120000180c46216100083c141c81c0060301490411124540f40340000310058000c80c0c3c819101c90a0202050001c0e01100007035004100801000004641f00340104840c54007017410140100851845140c100d030500310020b202010001d0380d0189821711000410340c003110254140503110078000521303450b1b005612108401c5a17040c0903d5074400100c42140c0c046c0c000700889401401040041600951280c21404000c0c080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 498893507 1250 498892257 498892271
    0x100909020301090e0c09070c0b0417030f0f0a0b060415050403080309070e090604020d020d052a041d060a02031f0303120c050304260f0f09011e0c0206070204 69
    0x218005a07002600b11003085a07407100b410b5501e02e0200042d4180b9101070350046045e0070110002042e468035403402402049a0201040400840d02c1400d02045130708001c903038490a10030015401c1d1720003501c2d10910400d2403004140d40403030382e1007200030324100140680d04c0c3c5440e000d0894606d2200c076405600b0f004003803000202251410b40214411070406010789603242c01c0c6080300660f014083c0607003050741e00c01810440144c480c0410030b449943c04035010624624146442840d083ea0120024800c55818401c4402010416018120928212424040c00301c0307011b4034207203050890094403925480140440d900c2040f6030b00464000c228225180264081c8a03003000102115900460006910743c0c103041c0361805505c207040d4036400b203150151541c103058541d03910040180f2800078010040202840d22141c602003100c1c0c03044028a01641c80784030310703494070740315400c00031906c1d01080200e03010030440f0380030641c0f80e02c10510688544039006000c0d000e20074141c0200707408a03009556109 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 498894757 1250 498893507 498893519
    0x1030e071a040504060602030f16080c01150302010906110a0b060415140103060906030b04030e0415061106011205031209030403141e0105090d03050604060306090305030916141009 79
    0x41d8105400c0680581c65640c0d49007205010481e1541d600c640219003003130044610030280c2c0801c170780791220700c1110310003145142c3c1050004c51048a030880025031801440c1445600d020201c1c42c00c40e4001d032100000c00fa80e48809658812013080c0340e1110b134018a500400248a54a4a0b034200001420008240b02003844101c588504c0b078110041a400c10001e1018a40c3e0500890000d0000b15905000b072a15540d0f81118540d4003030401000e1049041c04c0c0c10094407558002040f1121100c41c0e41e4000d1f41d01c00c00500581400c8050329074600400002065808584d103031080a20303400b1004500e881c2000e0194016840080c050401ca8081000000f0220700210741e03811000d0714071006031040e01003045040e24445110000c0720000e0f4184010041c3c2c010001c9800140e18016050104082d52340500140040800d90402003046103031030409414107501501451042c004c4004541d804118070005111000252245030313100c0301744d50180885414080c020200304c1c1030508281100b651155 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 498896007 1250 498894757 498894779
    0xc0a081026060a110d022d0a110307030e3d120605090114010e0d030302031b090306010b09131109010e09060303070b060d120c0606090c0801030201030e07 68
    0x3101110340142071940310100e0030402c2c0580d982240e880402000501140c80200c1901d004050615128650200c0d4805a0044d005400030303009010000e00341c3d14a22151280941e50400140c00000501d018405069602e002048900f150780545840302e10301038550412059100d61140010750311480291185400c400c404031000c144107140618224492680000304031402c0303401003008541c00c0010402042d160b04034030b14156200e800c03403280300d103c00c040140d40d40c80c110b0501c1034105484940c210103040d4168043c0d40200e201500118560218030100180c0340140603050b941034000b103004102421803000180b0481d0009801c6e80741c1002c01c118110104c981d0f01c048601400c030002040c0f070b695a4007003400780d8030711000c1b140515a4200007001c40c2e0f0700c0c01080c000400d42240070021400c83d6403080d400d040030642c0f10f1305c075001c00c80440304d005103c400c03001c000b155480c0c2018004542780a03540109074120145a030742c60026840d5400460142200e500c0c80340040c0910003002c60305265032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 498897257 1250 498896007 498896039
    0x20a09090c0e060609130c02070f031202070512070e0a1b020f2401051c0c031a0a14150a0801061d0c0306010c061a06030a0f0b010201050c0a0810 64
    0x8a1800c0903842c80d000082e0580000200458881c130001c21900c00550750311020314003520f4221400140c40c41e0544070030780c0f600e480c82e0420755072081d00303c000208000d48201d401100d002d050b0700f80c80da4141e841c024031a807030f542003213884a00e0300b080109200e01c0c540617200e1035100d4030252001c42d500480010000302c04039071205d94070041e00080a0200502410403010000401d0140b52502088020b250145d00d0318041c00345074460307050034204d44110b84000c0300c500c04880e0020706002c1c81994a1a1900c003118642d100302c11410b05050000345445194400c2da188001d904086a41ca030b0340b003030f148440550782c59001b207902224208010816010034401c0e000504030300d00c072904007050b00c5c0340300c084a201e005207000900141082003103c40e1340d0007503d14103019070003400800c00420301d56403030b4403440f540960340d03820040100410401c11100e4001030203078500d0784070801c400780851004900382c0d101110300c140005020080305000500c1713000d1050344402c0180780d000850f61141c5c29071040901e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 498898507 1250 498897257 498897263
    0x503070c09090b06010219350408010c02071a030a1514041103070c021539011a0111030c0703050105070801080f10021c0f0606030b010503060906040504020a0909 71
    0xe5251140100005800c03030341c1e0026006d0000788041038450029950b106030001005040d0403c0a504115a25528454443c2c40045e141c20034a50b20480d9007280c001c0c0c003e440b03031428645c2000030300c04d1700c180041180d1084daa216024140550210001005207510180c53b000e031071907031414a00003084080032040054880500300c1e055880b006000c00c015030395001c410107d040010418000079581000b51001040c1d030685044d4045600128460898002c1e9204081c13000b0030304198a5140a00060140c0f043c03540009072211140d42004040c2221424243d107150180001c0c01000e9a41c000c1c100c59800e01c0c0b0380750442c0d02c0c0101d008e20311401d01c000e56200310380c40d80d102c0c014131050071341121525024160b5007008107650000f00a082d030340d03a140c070710054000c1640010191000c003001d4480011489008000780b00c1501d000c4020001858503202d241d001034030b0106030040f10b43c8105c0460380202401040b140341a1504c60401008050190089a03c1010100002032644a6000c0ea518540c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 498899757 1250 498898507 498898511
    0xe0c09062a010605040e0c01030c051204050606010f0203032809020d060b011106040503071704151701060513090b010203250c050f06030a05101e08151603090503070c09 74
    0x1c248201d09648458100703030302c85c0d418900304402d15140010501295602481c1c0800d000c0f0a071a0181c03201d21800c0a41d011071101142040700b403060028805014190aa0f50114032110b0540d00300e80300c0c00240c4041c00d0b800c0900702c1c070003003030140390303034100c0511000400001d820001d40c0d00080100210748001c98503242c450381d41508640e003003018a80c44156180c0580082d00c1e00784c0d6040d88070700c15200002c0c01620850a00e01d00d00d200f440945002c2c00d8400d02040c54600500c4020b009200000c40c1e444881c070700e400000c1041407003801660410306c00342c1070000c1918107210040b0058052561040d0440c4401d004400c8414800141c1948110a80e0007110070803105003081c01045890350010303800f0344040c40300010181c5504084a9004540ca140004c0c140c0b10208a9590b602e00e41d0301002107040b201500f000210039020030380080740c98403411100b021a4603e005c83c1300d44030403920200d03c101040411350041d4003940210300030600c01c200b560700d0002250380d1402084c83c1600000200c603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 498901007 1250 498899757 498899827
    0x8060915282913030f0602040306020c0616050c0705090604020706180507080106150528051201051c0807030905030709020405030f0a02061602041803020c18010e0c0906 74
    0x18030240d041c54140b24411496628000060200c180d00034a1848000d00f0440e8180b00a010301089506980c09154088070555803211801c4032290381d00c206885000344444d10400708001640144200d8180d8410000500001450002041881200204583e0b0026001c000b0203000904c24810313900c05180b0f141d12004280c9160a081c0d19162454100312000c2c0e03d006401c0c007210350742810310004401c131490040e9070313040d140b510310030000400aa000c01003400100301490054004000d406036002540d03008805a07640c1e010003c802845000c0a0240900c1c203241c5400300700440000c1c58500d0280c00d15005066940020a02c1c2002e5944246200b90f0702080620003072405100940c03086185900410550340c1a400148940c41080c405880354941c00c25418115116508a0b0944600344620b2800306445800c0103504d803903240e0000341c031801c1c400d025041d43c12441c0703001c1e0341641c0003085000311503900e80f100e0045913400303c0e4155510580c14440b4000b0f440200b01c00c99500111b00240e86000307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 498902257 1250 498901007 498901049
    0x911060d0603030909290418060614030c06070305030606130e061203090a05041e140103050708030301080a030503270f010f0b13020a0903150b010806091528 69
    0x14580c0343c1000c0c54803403c000c4441b02280c0b50a1103040100400400c4c0382030000300c8800100101074024510001c007011100c1d02c410b0014950124085a13001c2d00d0f6142e1104925040640b10f4060244e0168084402d0000c4004280300d103000d1a401345c0080c00e000e01c0e0503015100c01440b10910303442808006004800c004180c01c190091488480b9139500550070030040303c00242d850360705801140d003d9507a400c0c5884d03400701c59584030040c018010804200182c1c0b00041440c2410090205403402d1140050000704050f000003240d0484001c04c000e0540d110060354219130075400174007a02413a4010608084c141c3c000c0303285105061000c08006c29880c03103561304150940d50030010082806240c2840e04007540c0b60b5200580c600c004104006075950390203d03007642e00365444e07000542034107586141c09000b42d201d603220b03004d10303034090f2201ca0300c60ba1441d00700300510104032442000d103c51a00e400844e4206110712003c6810b0000d5105003003c00c444030341e9502c0341c8540c840d054450a91121400d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 498903507 1250 498902257 498902267
    0x20915041407080f2503050610020c030618010b040e160e0118090521180406240306030203030a030207140a120809030405031006090b010305011401030911060d060303 73
    0x155000040340c0c0c8034186030602e009086070900034902c88880c400c500c001403185940c0170700c0450644e0014a003005003c49520001d0090004844c0b803401426400c2c0094016800001d00c03802d01c900050060500381d07292410204031800d0f1003200581592945140200b42d82d40d8095410f01c4c540c2200240030441054403441d00840c480d0740098081003021b4010b110750502c400000000300c01140e0041190000c901e002d0380307000c0745038903a07003107000355035039507010002c00c58008040c00305007012811901c40e815401c120440302944034802c035410445802d03d10760300c41203007441d000480d241000181c240d80c0740c0109083d40e1041d814040000c1d23001448000f0414000840c00000444d00024400c2410720350318104c0081d4105980300501010a00040e0002410800c55000c0c0c2000b400756400c500d480605040030780079900031001d00c40e00b46121051103510a00c1030504032404211041002e03034000c4c006400500d9552020740d0403000381501805540c0b0303100c000380981030f88010009115455424000e007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 498904757 1250 498903507 498903521
    0x21207080313050f010f270b070c0809091e07051254030c0a1407080307050105010e060102010b030c06130b12010f06081509272a0604120c0302091504 66
    0x1f50381d0f03900c0c1d000c1001107858407805030f40c0305179641030024010380d072810703c1e42060207810005070f030101900c1c081048403103043d4880140e83d6481d542030780c2c5c1911030040c2a2a41d0264854910b6088074100000b85002040c400c5180c0042d11100b401e100052650300290000208001c0c0700341507040301d0819107100700d04081d4450351b908120095800e01c0380707a245140e00ca460141d400307400c0d00d002c070703100c0c0c400100140320348002427480d0380c00c90340d49502d24030780907000c1d010074442c940000c9501800990300794018041c1c40b038001001006003403101128410405141c11024201189403e221400b258006000b401403c422005240d244402d40c1b5000d11010801015000381c1304114103042031040164000144400e44103045819468641e9600403580080407549040f0901c03201c1c2c0c88500312060070226202c00a004001c0c00c403041d4400d44400940d0030102502d40d035800400030042084074007000502c10004500c00c10210309540c1d6660006200c0c1c603001c0c1ca4074616074a994101703001c0c44c80c3c03500c5584 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 498906007 1250 498904757 498904811
    0x6120a060f141e150304030f020c010809030a030510080307140d05070807080705030d02070602180910090509010b06070507080105100e0402040203040212071401021207080313050f010f 81
    0x51400c046000459040416043c0c1884919002d0302280b400340e903601e08a1500c0002103107044d0300e91800b410000c0088181040960240c020060040e40c65441103140b14840d211201c020b503d40b1031407402c103c00800b00104800031581100d507010644c090203100038201c05025000c011301800d00e102c040c0c1d0901510041c050180501000003d00181003141507504890300041c40584440c641c2c18030314254401c600b40d41d031502c0d01c00100401002a42d50107810714207101840c0a52011304a010300103084819111000c200341c41c0c8804004c001c0c800c1d0005a400f2001c00004a01c0c400c1110105070590012001140c50350012a81844105d10901c81c9a40c8200c4000001c00c42c0351802c400c0501d0002c001d08040e00a6800200182c25900c1d00009803031082c24103012242c000d0f079944001900140b009034114014002c101c4d0710200c07940c1c2c000507980425001004280795440c0d03001a08203e0700760031340817074050058503440c00a441e0280305854540382e0300d10001c1100000c00c2168031580300e00d5540170f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 498907257 1250 498906007 498906029
    0x30901080c19051804060b07050c0901300203030307090627090203070c0b01030503040f1202130e07090e0303060901080f0a03030c0507060e0a0b0c0703080f0606120a060f 75
    0x22641c02ca0382c0040701e12102545003480b650312a000d544801d03404c0082110590000c1c2003050000e6045410802420000c1c001c1d0281c1340c245200340c0400a03900d02c28030840179451200d2a03c0001c1500ba50a501c034100d0044094031410982a4080307400c540044441d0030205100000400100f60070210300315594060003030207089030344a03480403440580980500e403202d990120001c1d4041e400f80075114451900524541e080d1f69581c5000350b581c2c0c1c00740c040c1e0300c0e0580041400003180d41000c80d800220a034005c24250040d218403140f18001d0400300e02d450284d10880c00001004c0c0224401c80c2c44900c0400b01469a91a040c4140039501a040e40200c03060f60124885204c044408100030103165458a00401c24004a2074200e505010b01748010b005d0390f20f080b41c600000b110004441001c148915201b5040703554018498281d4001c05d02d000e1b001c22516400103644000d840000c6902ca070380244201e0425000c5440c0704440c41017192130704d50b80caa50b440103015400716031940d080205410030341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 498908507 1250 498907257 498907267
    0x1f0909050f06010b0f071e06090303060504090807060c0519052502011d0411130f09090c0612020f0c010b01080901150902091201090b0a1808030c090a05040c02030901080c 75
    0x3800c1244105e0303601e0070b031070680401d40000300040034203422003a0440c0081e40703211145900b00794004188081040340400e1411000254600307050051660003600101c400307040440e60b85841c000f07012070b208032000708201004980d0782e0407010a12581165095501c441d21092030210000d066208048842007200b84003800e00b00503039000001903413210004042d00a20010440890041d01d09040e0300581c20001080e4100103d00e03032000e1808595401d080030b184565100013544c2201e240403c090000a2101e0080c4015401100d110800702951980149026140701c000c400c0c54005040051482c2d44407040000341d5a03110402c1504407070807200070046505000310812a01260744a6454510707001708012a4941c1c074a046462610148c000a12184010380f8000d0001c0030b04540c0e40307409620703102e1402c2c1c0d04010464140780e4a035000c00502d2440d159400700300d85540004080d00c0d8000310701d000c0441d05440758007440d0140a07181c4c0056031201da60300005800081c00920000c009107003401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 498909757 1250 498908507 498908519
    0x21b0d120b061204030c11030d03020c011404080a2105012312100903201513020d0201051c0c260603250b0408030d060506090906091f0909050f0601 65
    0x1c402078200717915062a002d4030186281000006818031040355241c043e6804005003150582c0041c414400d406000b00300350040907164403954203040d10047d241850511070111080e00508a14401060307806102007a0b0305482c003a070003034038001d0b08101d510f0544160321403900c207002c0103075542a034000c1f00c6003140420f08258141c0e031008142c0065200c183c490f841d0b034050500130605901f5101010100d0101c141c01060515651914051026124420b0b000001c502c0303220360b00702c5e0605075801081c448451400e50011a0240c0140e44900c1c4031424486115461081074802c402c00c40704aa15104d902c001c440940081d200ca0b03c03040f4600a0f8941c1d030400006a501040200001c58540040070301e8805464103036003001a9904020503007000018085060407001000d0b10440e6142d15081c4040c80d21001442110f004500700310ba007203251400810b04524003a0482a8020018072106c4014400e07640444401042c5900c64895076030b4404241b070a01806008050200d68504010022035151070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 498911007 1250 498909757 498909787
    0x1216060b0d020d17090d06050f09060f0103080a090b071505010603090507030816051504020f040614091504061d06030729070b0f0f0f06060904021b0d120b06 69
    0x4900a1021600159841c2c010000c04c00740c403c50000a000c01030358111078a4400e0041a0036a90006110030420004084480014041c0c1c4100c031244010346640e481c641c1c07000b25903040f15645800340000180042174203817048000d4956a03000308151103c07038440b20282000c680f0181c01c81e00426040816000208100190040481c0d6220080542c1d50356000310241d901d4002540051090080310b81a0f05203101c1c011100c1d00450084800002101c030502c00c100071115a44201c0b4074801d6028000c610a25080020640c049809800440000c0300c410008045803a543c01511216540313100003402c1054200585504c100150010522141012909000704152164502c01ea1048003407030390080d0040310540b842c09a20110440c81c1d42800342448801c030500b05d88809041320000700044a004200b42a9070244402515203450b014010061001a42c0044000c0c85140000e003410f20a40004000002e03003032501c0d95a19150900000c0060300707a90351440a40e1085505222002e007000080e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 498912257 1250 498911007 498911029
    0x50706050c2b0b0d05030a02010e061302041e0f1e02130b0a110114060f012a020d1703041511250c03050606210307020904051216060b0d02 61
    0x3419078404040300c0d40c840c600280200c083d0064004840c840080308100000001c0c0040e040c5135002880004482c1000a5950004407014050744c484101c9103000b6080503840844440740d02000307540742c440800596002c0c0c400b414840300c3d007a55200741107440f0024080365100a0300d800c1c1c40540c90082d01108550305255640a03450481e200018004222800b619001943c10243e2000740070000c0300c0c003080040108211081400f500b5559601d4507290320610020304c5108a5251014075641040c0070010703003c9034424120380003001d4040030408035005880c50380c01001001180e80d62450180f400121220781d00041d01d030040d050441034541071105605035030900d0000074441c0030548082d81d81440203100741c5005001c09011a40201c14400c01003032082c0308020540f00480b01440c0e80c00300307540800200902440d903070020702c100401403424050481e0058054000c0312070030b1714640d0b442c40c060392100c0c8122003592528401c9908000e0706000d004904802100c100d031201d2403580109040e8281 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 498913507 1250 498912257 498912307
    0x130501020610090e07090c03231303030f090501090c05030705011106010e0703020d1503020a0f0509010308030447070f0c03050d090c08060901020901050a0509150307050706050c 78
    0x490b403000201020800450004100c806e20900903100340200140050015071803070300801066a1648041405030101d49001e0850090100013910700390320110020600e280c002000141c4904072080881c0e002d0080d41412809811865010740c41d010405203441c5031a40300134107200040d0008012520080b986904641c0064460740c09a0303220b0104900901c6454009181c00b480d10001c0904401c00d5038400741624420346400c08900e4540c141c0c40f45c071000c1841282da0040ea480014800582c3d40c901a44d0024420b5440080a014006860b5040d03000c03084040307016510010b101c0c140318082e01c0250750000d4004504e00b01c40c240100014803100c8402040028001088505001c00d40300780202d848503826041c003001164042d28000c0c4620400d0303c1000d42d944241d9000c280ca140e010b2085800c2160140c440c280b0b0003250310016141034010360515a0300141e00264002d007108448021441003015607106a078424207440c0c039804848020b401003071041400c2c80800420b401d042448094400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 498914757 1250 498913507 498913511
    0x1090e0c1e19050f070807020a03080a08241c02150c0102070201020c030303010e01180f0216061b09051203090316150804020108040809061e13050102061009 69
    0x34905409404500c109549024010101c910300204103407904040c00140c000b5101180441101207401c444900854000c403542c40c00402001000031102401054071500c0036000220155594881c000340c1d401841c090404100003500300704116480c10b469101c410160b00c500c00328105041d0119001401303841a000c102000c64078000306654070300044030381c104d80c0000003d566942d00300d1058080d42110328200d000d445100c55410603881c002c419a8141c6141c400c500b6031b160300c3c003a40711035501403007091001941d503030710403d51180d640c0340000c008a41002c1e8540c450000c0350320b001d004079030102030f480031b00751808240c04141d1584410302e90221034044480500d003641c491141400c1d80b18040e5400ea06200d503204000c803601c1c4444684045400300a2000703a40d80340001c0603500d401c401c0310001e0004c0c0c043c10000d000640c3d00d0014001c50312000c1c2c1a1803c02464005080b88640c410086001c640d401003030f4598003000f0060f20341d01918081c0701810b0b190624100c8281c54441c18044c240c0810703 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 498916007 1250 498914757 498914761
    0xf0c0c0308030612060106031b02030c190f0605040c0e0a0209100305060a091b091d040206160210031a030f1f09020904140706050415030c0201180516050d0201090e 72
    0x50344140084ca61242d00d50152452565500b2024009054814115184100e560700c1c407000c590003c0151200102c1060123000010040c0308800310150005600b01c03500c5410080d00d1001c034005104035449a4810794000e11080d08200c03020024035001844405c040e0300400265403981c030740509002c0ea45d4501e041c003246d1510340c640010b1200c0709541201062034600070345450f94051000341503010015584070030000e10b4a5601e85041d482880e05501030b1103280501040040c141400100030410640e407003011004e070070382c0c001050b142a0075199000251542d81c081c4180582894985041d00c0072801005030070600511035803140300076000469045540503031520b0030324460b00405145540204035a00515051800720150403500740f11003424071030712902040080c010400c58081c1d500d40003106558040500c021409820031486c04003c41d500d484802c405882001082c82d640da201d68041c20221b00640000d071800400b075440188144074217444000580d0700104a40d080e103191031003104081d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 498917257 1250 498916007 498916009
    0x306050a0501020d230d0522031b050312070809010b01020c0f0904020f04020f0d0606020705130903091e0e060f06030115021507080114090c31030b06010f0c0c03080306 74
    0x1100d008052178210700e000040d070041107611540310b18462090008005075000300b006a15861461840000380403905460001038210344002c54031080501c52801c41c1d14102100043c82d007500c0041d180c14010800c0d92042c4841c02c0030a00641369000000c0c070003080b0b039007958400070b4115440750303000c60b00505096000c50b095441c0e14036802241c21021f0815540c41c4800003d500b11540442e86060901e4a40b48010803401d1004c1442d0085502c001e1480907140100d4019400030142808210188001489c000400d0f148000540480a140c1c001e000605450003002e01c99a8034020141c0e4881e1407809088109540d9030001d6905403005000410850500c02000b40d1070301d0200c0e01b003002d00c20301441c01c201c640c640c04000141a240e0001e4280b00e4070002c80140311a2400540d403400b51507a0502ca0a012220801311150100001d04c540c039409015540810b010303c01d0642040d51800c441d01c08000c1f0650700248505001081498003901c0d212940c0c4030b022844a00c2e000080580c2030010105100e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 498918507 1250 498917257 498917297
    0xe1b030606160507060e090108010603030206040b0a02120117012703050a1101020d1e1803051e0c1005090303040f0b04060902060c01050a0b060705030d2004080606010306050a0501020d 81
    0x80b00d50080442c0c0d1065101c0a001d0000c1700c2560100c1d205050190000c2840b20060003400c007129415001040591a259501c0e044481700500301000b0541c203010058038420301c40710b031600070040303a201c3c0d507000300b400b5401600b587d54554002800c00c4441c2a030358a8107068900c00e030a4550585400d41d2541c01c04202254090600c0a09a00315800442c50311824141640038100b0480c0c10046101000c00755514603068034440c40b18089410450741520002c64082c000804150112304086c43e00c5452031407010b401d0750051007000445910031035402e61201780c01e20500b60005c89840c011825490550b44010001050840c014410104600460308218040d0041229503a00070701c500e44404030010018001c00e4225071009104d07041c09005405820260300300c529407a080405503141024102d45040a441040644800c0540346c0310310022051502021308040e1480030060201c80c00c19030001410b0ba1503607000305124a00c00e24080210341e03000101d040c604881c03070401c40c04450800301d606007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 498919757 1250 498918507 498918547
    0x7030804021c3f020d030506120114090601050a0f0b0f0f0307050c070f060c1b0801020a050714030a0f030c110709020a170903040506030a23010e1b030606 68
    0x100f888950221089000b41d004582d44035141c491141002c1d090b0b0610403d10034074207000265001d60001704039248030610036007006034801c2025241907012124041000d08407030940201e40e0318044c090040c0204400280310041c01410121110350f102c034141849510010f450784150540e401c00020156040c03a40181500c1070400d00764034142d124500030038060724a510074820300702d142c010a04042407144d400e81300340060350055900d41048402e256204200c0c0341c0d407001c40700e102c5240343e880004c66100c03d0000740b171280c00660faa99182c0000745400700e642c0300303080302074400d80d0803c0c890781d15810b5012a0440c00104503160216901c07003d0401905c0c89050440c100c000c60003000008601c02015800600100c1e04036034505210340445c0380f403102c503050140c0307405080c0c1d001003004204514004002d190401e202c1c072000204031440140c6040c000a0108d5142420758a2400401030301c500d012299900104161261007040e2201022800c41d10000f0f0401341f00340c40105a5140c440b20204c0541 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 498920863 1106 498919757 498919763
    0x60a0e030904020a050403060207061b0201182003060f0108070503010203040f0609020303040902030a0606080a0212070f020304090e031b0d0504140f100309140307030804021c 77
    0x80b01070f40c44040034004100007071102001044480c401008a5442000c0004048102400c5400000710b107140402c19a490038031010a2082165109011a640070320805061030b00d013a8511100360403c01e07002e4040c4501010408000c12540029040e0b89035081100c10b084d554400301420707407100710f42c020300a0050020f090000750840c1c0009100601c0101520b052513212114203040fa002140c1021266403145001c01c1501d07000007425400c038840c2c00381589400041042d5210381e020141c1a08104034490800420192003072059902400d4140c4091008050b2905029900e401c50041d406d100744407054402d000000004100c1220019505d805081c9482c114200c40c0280030b4909207034000404031101505030340e908149041846090324000b500a8040c1080c141e1181c84c0c0940c00050344c020481080030030740001007d03501c00d40c112a103103d550524011282a40014403000b = true := by decide +kernel

theorem cover : BRFrame.Cov 498741007 498920863 := by
  have h0 := BRFrame.cov_init 498741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 498741007 ≤ n) (h2 : n < 498920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
