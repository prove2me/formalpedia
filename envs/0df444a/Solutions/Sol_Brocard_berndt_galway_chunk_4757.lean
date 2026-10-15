-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4757
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:38:01.949749+00:00
-- url     : https://prove2.me/submissions/2bffd51f-834d-4eda-b918-c3154dbb852e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 855395683 ≤ n < 855575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 855396933 1250 855395683 855395693
    0x90c0201110c0313290d06121a071d0f011106070809150c0d0c110106090b130507081b07170a021b150c01090204090b1503030a050304080d0603080a171003 68
    0x600c3d00e1742003c41e5101141c1a02c1c988101c0c2d0001006001d0881044c0c031030300003461b01d00c103100120042030030400c0b0703404c001a058501901140d82c141200c604a94446070044082004003440400c12504201024048500b401020440c00e40103100d41d40716007140c2c0c40d084c2001d5151204040510068012210074807800640860a40b0080700c0c00d40c0d0080782a0000c1d0b84100d030300628000e094511513003030600000b602c0020340e012201c0705e08240d48041c0307140d03c01c00c042002d46405540d1480090740280c001130a181407199500d86941c0806d9131189000034686a0901c007015402080320100030000b64003c2280d0100640306d9070540306020f008201c41c0c142e00007a65440050050132440300d00080d07190740e0000a60183c640c0c1c0350f0080040003410b2140c01d00c200340c11012589081c2e00c4030071003401c1400340303130010680e601c04156070780d124a035548a81c0c5142c01070300b003552104420340e1100c1010000400304809001e400c022a41c450200840e0310b5901e030351040c009803181c0f0700b190103040c2c1071021078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 855398183 1250 855396933 855396989
    0x30906090c0108070f023408010b1c0f05030a11060603011422060f0209031203060303040909291f0305060711030f0a0c02120c0901090c0201110c0313 66
    0x29007078180891030300d1540b801682424580000b202e41d060083d00c00c001c80c0e14048501e0200c8462012100c7c9445c1c4d21001c01c03034220741c00f1030001980010a0380d402d52641c0c040d4075160b044030f407240e000350a035000c150b5140b5240d13400810000022814614082e215200d007002095848907084000f442844c5012411a02403070015166440400f02c00f280c2e559280e01d081180107100d0741c001010000e800781000f094009400030240e140c407078025030a00c80c400c516603209981c000c0b0740040203146400e19003441d21004000c003680c11110240114507140b40458000c4440c00f6605c07080306603d4643c6056001e00e8014408010100c8444861180600103e40f00186940d808107060900208546600500c0380ca103000380410390506540014a00761016400b80000c2c807014800d589d84254001c803030310300640f43c40302d80c2c01054000c200080100304140258101c00c61850440c000012503d10102841c1c502d980032040c1507801e50700005001105041524000f4020840090b0401429084035222110b174 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 855399433 1250 855398183 855398191
    0xe0609150a052107020724080730050901090f06020306010513080705041a01050d0c03060f030f02030c030c010503040f0303140703290a06081911030906090c0108 71
    0x9100302085004800c1c0c040c0d0111483d084041e00b20402c1d0a081111900c060b120032503503c3c0060240b8200018086902d5907600c0e900158142d82501d0000071840403910050b0080c10207040010202c1001c110600134006509140c901004003100d85200703410781d030142c40000e840340c1c50681c034000c942808640c5045054120682c00000945c0d00d81328900100d40b02d0044a20805c00795015440004501000140d44400c03940b065905016816044205410070602d58003505e01103582005050602c02e001e903c0318080380c240307040002c0e04540314807007030681e4002a0001c45102910b16404029071500700001c080304003048004104031011b1400092075400040e10050010b403500c03040e07104060181e080044c40010400c8480c000f441c0000008000d0403000ca00d0310100c20030b500d11a51551513112030000709400290100010354074065003200c030118014000784202080c54100700056034507004110175649403c00c015260304040305401d0808034040c0c080d40d00c030f50150000545698100010300e82c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 855400683 1250 855399433 855399469
    0x2a070509040804080f031210030f0201180f081f060f03020d1e0b16022806110c010c0f080f162609150f1b0c070b0304030e0609 56
    0x40c1d11145807010b142c1c010354006180a00031150b0344a41d190000015007400c882c40350007629141c80b5255500e401c1d0645000103002c181d1406c0e01c85000d540942e403000c22103180308040e425050356465002d40600d400740c0000000d50450000c0290360481220716060401c240c07481005010b2130b007484081d1401c81440000d0040380410000800d11040b11403118001d421010324400f1101145030540d2031610464032516950501100c2e044000d1000520003200360760500386400301a4004d0b240007603c00311820032103400b5142d00700c1c0c2c0c4039282000e024103080d01f1710900114a1b94a1003034007400300c02c0054600c4042200080400040788c88403c102030708207948050302d101e8414908000c89400d03070421400b08081c01548148011116150420b51040b100d08094610001d452500032103000300c1075502100d04d4001c140410310f03120b0320f001100c5176488005612440e0101c0580110300784629644a80d100c400088104024150029542048104d0488017145050010800103910750501c0e58480c1c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 855401933 1250 855400683 855400699
    0x31006140d170d02041716030201030f02091903061b21110a0c020f150306062505030705010506060f070f111c060b0d031d01020a0b09032a0705 63
    0x106000101011103040300d082c080080e5560005101400a580070b0310800c0075010001e0300c1105d030b1400206580036500ca10007503441c80207240d600114042c000c0741d8246149540e0030800500300303903151486960303100c11250501c040c040c51400d204044074403203c024000202341c281800b0000340e00074402207400d8100090740920120184515004140500c10723036000d4030001806900b003c0d00b00c400440e505200321240540d20304202c2c1444204202c4052a140305d140510200721a40340c034030050002503005003400c1c0c100400400541d5003d0702c103082c080e038981c0c10006040c421f21400b8001e83d54098001d5500d185040c40f0800c0d0003295208100f00904403419074044c84d802c1218115029182002c004c00c0c540b0380c4e5110702d80e10411900d180804030351144c90b002c03000105c3d0400f4111103030300c03a806884143c80700b01c503405800310011179280b419046010318500240040c001c8004079009924034002152a03c203103d4440e00c004408100300c40c1000d0700c040624610540c0001d03d0340644406685483c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 855403183 1250 855401933 855401959
    0xa020d0807080d020409020d061a0403030507020d050607200625030b060c070602010b091b031503011a031605030d050a020307021e01020709020c060a05070c050d080603100614 77
    0x2051074018110110800750000400098044254008e0883e84c4c55410080000c20b40d15880f19514001801d001208840103010800100c0c0c000e101074181035001509020041d140c1c0d07030f140750500300100c488030042104000306000001c130b0032103100030711140000282164200b6480c0d846c03200c0302d400450380340c20366110b003e020442d2203a001038403092001384c4129299610814072a80b1480d46001e4000150f10b4440b0500c414034060b11030324001c40500e0000e40d0a219000d40304d80c2c80e0b030300c004c21800010054007017500441d00d00344548654095411a5560024001c4042604002030b65050001e130304141c40c0c050107540c2d40410401d1850500381062a038605524100fa41180240744000c2d500c05002107a120242e8214541111040c80176400e40d07a40d6900c0307540307060480c011081c1d150350760791100e000228002c1d5958042da4200c01c443c2881002c81c071855640c0e030f1030300300c0080505000500d500d090002e24201002a140170003188407040c0081800c0c400010b986904400724948984208407040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 855404433 1250 855403183 855403193
    0x1208041401030e010912021005160e190605031e04150507110a050d090b030c09010507150e1606110c0d030c051501050a050d030516030e061b0c01020a020d0807 70
    0x10400e07400c1c840000e000c1008203041940c01142486c00b8240036026207210b201c920040b900c1a140304011b0b00d000c440380405000d404a501071007641249400114041900400096582c440402000039a0751b803683e070315180b140c1518488114080c1900810980700b8800040c84a1001c82c2c02d00b140c220300040d00703503100c41088a4125486e610050b507030107440280003c0c094041807105079024280c403075240450f6a024117404510044070304d0050304c2c2087c004206190311510091201c00e009680d50f01040d0000c5030448101c6003c8220300d05543c0c400c0a648503030500b241e212750014591810030101d00310242d038125032505084079804d44540510300c2107108050044100e0503045070040200d4441c41c0581d010f08000d46001c0c002c5511035840b0940000c0c3d1460b0207030740110381c0740d031658030310f070406903440d201100290281008400744030340c070821209203032030740ea02921052450380404034081180c00d074114240303100c035501c07181103410210205d030150703e600001110040d881820030b0790b40e42081c281 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 855405683 1250 855404433 855404441
    0xb0102031b032703160f06030c030b0a060e09010608010501091205031b16050613090b0a03080d02181c0b0405150106030507020f0f0d0e040b12070f120804140103 71
    0xc0421450710f20207041c41103200040c80c070100e82c50190f04940d00c0781410070603250003484a1150f075140e407883c09802e00107948250001241c40c1446c3c1008118004000e0001e42240d002c2d412500010301c200086041c545413180b001030041049043c5880c0950424000800383c00050203941c2004402050348010040c0c10021240b20741c030794212002c0254413101615481780320032107219007900d40b490008985c6190843c02c451002c540700ca802d905251a1641403030150a0407000c459201941c0040040481c5070400240380e54007a903840183c1c1c40d401d2280f61b2501c90348020b040750140c403000440c614500c103607114866071146c00004580f029a035502d069881c2207103001c2000000c042d15800001d859400d50030060140f210f5800351340078400000401d6550300030001000203030b80c0c030200d50101c0c1c180c040c44000005846c040c00c0071412800304008a01002d203046030b441015070007481c08104205010403660701900200c0102c032407408054403030b24154061030054044000201c105a61580c1c080d0348 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 855406933 1250 855405683 855405697
    0xa1101020304030c02090f070f030c030b0a080616020a0f0f080d06080d1101090201120b12151b0c150a02040509190507020c2b080c0105190b0102031b03 67
    0x100030341d528902860010305492000404a0283d01004e0110700d50350245200c141c855902c07540c6a20505d086c80b50210003801d044a02d401c1410755507841050103440c0c18003040c01506042c0000c0c001d074100580d907415403261148146046402c2003000e400001c490980d05110b0982110007054414081d04150b40f042c4140d0083c40d8003140307850030002d00084013080078010450180c4558100c0010801e42c1ea0981e9540c0070001d001a402c0300c3c6095180c081a404004c504c00080c1580f004440312218603468071100510341e0b642091400d042002a04812802070a404003040901e411b11444981300c55030b0301802003080b0b540c1810301c2c3c0015504407450381568010301c4c0041150089052500181410148c1d19400c40c90080c1000c1c000385680e8000100e8070b41c90074000d000801024041034109520041021102d45500544c64030304012501321405802484407000001809003071100407907800c900c0720b001401506060a48240b03450b80c001c41a2207a2482c03241803442840400200c2909611401d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 855408183 1250 855406933 855406967
    0x25030905060f090c1003060e0601050703080f0a180501060f0f120b09010f090605151203040306020c011805151608060d1113240317071505040b0405011a090a020a 71
    0x4854145646c903810000444501d080c005100d600c0d1240111403e200c0c0c4c40c40030b4082110000407845001c00d0707400241c2d00408902000404402e03c1d1001c40e0004900700056131541e4544070180112003032550000700422aa002d4001c07110300d000d8172000715220111020301010180000204050003c3d00041d0404020800400096005107800c01c000e14007901c5103c441030089051811a062110103030549a4000c4011418240b8658580c006075011301c80600340b9540790300301014080a00322030b041c10f240c800c0d40a4420b10071842c02000030b00400408030252909038420449095401800183d0003800540305e007a00f05640c1d0030a1150940c800a03041e4002e12540c0380c400d031180ba02d6005c01c1d00c4000000d4905846031540701ea418420346c15000c054084115200d002401020000c001d04689108107180f0106540c0c91320748404a4000b15003c0e41d841c3c07111010403003040300c03e214188100c0000720a0199010500011501004004055081c141e0b80064017003a00750248101c42c201c181c01c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 855409433 1250 855408183 855408199
    0x14060f041221050106030b04050402031e03090a030f120206130609030203120c04050f030f06070e010c06050403020703020108130c06180314010219020318011404080625030905060f090c 81
    0x6901c00100801c000d100c5d07000041e252032091401442c05010f240e010340d400070b00811500e040294840200d1020305519200d034841003000f0744040c2c03101ca80c9040194060a509000c82446007402080000100961000c41d002142040a010080d12021512135008000024403145500d4142d2444c8240c3e5071300c000320243e04007005042e0b22060000c0003550340596208140c208202c05041d50b0740301d2912042c801d90402000150468420300d07604c0003d40b01403402c000f000300d007510b40e030040714025602500143c010050610555130488012178220b4029078204c400d5415949032003802020501900d8108500d000d0b80c603d644e80080382c00b0016603080f8229480f004800c0f13031014000e40c0710400100e8412411410940f1240c004130642d040c410340c0c500f4808001424a00440c0c03601450302008255403400d00021440001c10002c40b03100e007400c60342c1012841000e0902c100481c50f071800c000c0c10541000c000d40002000425159000b0980a2201d192074541c1c014290401200c41e1025401c0080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 855410683 1250 855409433 855409487
    0x432040f052401080a1a0a0803070203061014010c020609040204081c0f050a0c06060f180f05060a0e0a1407020d0f0509090718030b0c0714060f0412 65
    0x15079010324080d40311402d40c20201520000390108000c20700040d1804545611300041d28040c098102c240304203014010a84c0181d183c1d000605541405d801403141c41c0e01c041808802c6040c00c21a42d90407042e1200800790003403424880e03145401c107902c0b56904103d044030443c02103495644c00e580340070100030001d40d01c2e0350b19034504941e0344803210040340c03603406090041807020340100310341840030000b5603c55140c280e076100c059421800601e070841d881c0f56a207a00090780442c21403075402410030030707080900d0308041003000000c0d500010540742c0c40a1801c0240000340d51001d100c3c2c4201c580e800e040206690364140410010040901d842031041c84100030051800d5004ca0716181102d410340721103100243e0b10004849900684c480d561f0001451008100140d00070801c80101c1c10440034807007000d0f622552003d140358015101003c403c0c00c08240e080c00c005009400b601c50a4488004000500c1d0a5030146480f00016002506c1c0118828001d00042c1c41081c1c0503104103041c80d480e41144030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 855411933 1250 855410683 855410711
    0x7030b010b09040b0f0d0f05190809131401050f010306030506010e01050102100b0102070b07060e070608090c060c060a0e160b1201060309050d110c0d1b0b043204 71
    0xb110b400b00902c1a071a2018090b00341c0382c0707600840e0300d65002a007200e420900a648441020018940584061107080e0280074444241c100080e000c034803400629440b07014807400d0091011824001150032800e107483d9510101c40300d40450b0440b4030441f610106d048090300160b0050030703d90800390031806a03800104040303899505043c1203a00c20703401c64480d10408031090045919019a041c01600000010071098160102410350f050244800281c03c00c6501001440d00702c0f42e9012001003071580c020484014001d0080710345040e01a14903900d00401a25020344608000f000c02181c650b171071013820034050042202610b00b0342030807450540d9a40343d107800700040c0c0003441000501c00d050301c000f003121440b070300604101c280c1c41310082c2810078080c2c00a41e8a2030000d1440d00c003d02c00d4885001181c0e403400c16181150f4000c100c2c4078501c2d0051001032840687e035420584402000f000108026950910400030340c5a500409030f000c20f442d04605441001c0c000d841c9644242801c076103195402d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 855413183 1250 855411933 855411937
    0x515070b040308072d180f090203250f0e0102010c02120a0e220f0905030702100e031204091407020709021809011412010506130504170403030809010b060315010e0307030b010b 77
    0x1000175220001b0b4101044540c0ea030703102442c06825180b410b4040200601043d0350051900b12112540c0c0c0204407800c100801d00c100302c0307140c00e50001500008840c40c0795401038201080100207100a102140301c60b10b019544180c0201419001c2c0340014190a00910813103c81072006801880c2001111b200d00318405030031032680034041446c2ca80042c136514030815109540100d03600c10007860500e07200e0307020000c2910301c1c4c0c0700820500a030350300101036a45d4240400f0002006100034503446605005508044030104075800480c041584203120b60300c0c2c1c00180103400c4031118480980d40704600714942e820000e410500b6a0000f00040010903211203524a4a40e00750701502c809040703802941c01c42d4203907042510107603008008600b400418a1103504010381c014000d0f20303a14900030040c64141881d0344254410307000a84244180324149100380170b103175070010044418500750300785083e11003410f641d001c02c1d190602001d10418030154600740b080c0c0c00155049190794a46681d2031840c1c0c2455 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 855414433 1250 855413183 855413267
    0x3030f0d0f0c210f050108010c0e0607022404030b070c030f0212091905090103050102130e011413200c010b0607080415270515070b04030807 62
    0x814248081e54404001034402d485076a03115a44145410280d0f60801803030000301040300c0000c2c0d881d03078000c801c00e04003802854000c01481d0000615003c0c50100103007556000180c40d072045008000300000341c1e4a060320309003900354104010404400660351104184280e45c0001e01d600401020825410742002503039840b0340c0651508150107035600b10403070700e440f0b01909a40c01000103224803207003414081c0800001c83c401d0405800056120030011350151003d0f8001c039a031b0780d00001d104240f4444071080000400d80c454902c01c9650600e80603000c603050000c1c003a8000c1020020262003c0056000100140081050518000c000c1c4c80c40c01c60719403121001c0e0700d61b5070a00c01d1403415070070000c8c01c980d041380e04100700c107007000d080001f540301d88a8445445410031295400026001e852076035004011810102106d105601c1c10701408002820f88100203419627040c0066070109010743c0c0b245a00540c540303401d444690710a002642c0500c03080c00c00e480030089844914800400003c4006a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 855415683 1250 855414433 855414457
    0xf16030210050a020d11070f140117040b0604090f230f03090a031e120e0a0609060c12200f0c151603031e0b0a080d020703030c1103030f 60
    0xd890207a040c10380b000e200720640b02c00164000b1101c440410710480d20f01c01c5006581041d1850f240c0d03030785410300098855170444185c0c400211100745803580c101a04002030380d000115500c50307191645540e9002c81c801003110f8001d90311100000100018545e161042591203407412100d044004000c80b80700c1d8541e4068410ba00c00c020782d1f401220400000d55030310303081c010700044070741d81142d03100c0d4a8582e9182c8541c1c01e07001141003d50002e8030f0640c0c0d050304000c4c04c0c1c4d40d09801c401c1080400c408024550304c00700c01d02410050a000440c0c0c002000802e15030000c80360800c501c14054201e610070301100700004c407187e074208014110600850590703105a150021079000d0784030b1004102c201940e44001c2603002da0100a0005800d001c80c00c0da850305800313400c0014089680c140c1200f0760640c0c501c080c03801d03569610400000713454076816000c042c0003035034020980300103113213806903075618140405002d0162494240c0200701c40610507290900380903050301c2e200c1381551b400010b29005441c0101c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 855416933 1250 855415683 855415699
    0x306060301050105100c0203030f0a0c0c090606050a110f0f010b0915061909080604140105090610090e030d0f06030c080a0b01090b01031503120905090114010807020f160302 76
    0x615490140501030603a40000c0920a040207a50b50039207149031410700498040c0000e0020321004020314000d0000c26045459601c4401203a190400f264000c1c2d81214060070702e041d5040c03100c00d5105083c0c1d51a0b8015003400c014800700e44401c285020200400304059106074250345c5031214041d0014040104107a4070800c080e10350b00565a1407440c554003154006d50107000c0c0340f8005154a60a031525100350819204090312444c880d810401c044900707442c08143c0003200d4003031803c240b14899001c20f400015044609048800280b2000e50388621a012512101e04008050042c4215030328a8a410707810403411941d4901c1340d0241a0512003559100601c4a00243c050808142c910b2659801009182e41c0e0b8204a08100280120060380d0304140da2141d01000d80702a07420082c014500400e5040d0a206409000500140f000c0d0015030017941c40800400064525850401582c5400d080160b101c0e9075081d0201d14240d0400f8880c80a44a00c040e01c00f69100d001c1444026a802510151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 855418183 1250 855416933 855416941
    0x5071802090603130f050d0e0901090203060a050f0f0301090b04020a0f060f1d06071b060e010e040f0b150703030c080c1e0405060f13062a020609090906060306 70
    0x200890051441040d08a80c04100042c006a410130780802076034419003680e844a8041c3e10b0701840e10700300c4044400410004c507011a82481c0054280e030061400c007000358614270781034000c1200c1800c940f0032940a654400d5a4142640d50010701c0300706c100c0045d000b0000740f0000c0c100300300c0542d410341d8140d0003800d20042c080b500d40488042e40003a81d20039280c910707024074602c200302c411140316261841c20303502600d83d01c02c10390344040061060782d018040700c1d03421482c0c54500041502060784840705000341010204038a9070000040e40300c000044400003108200f10545e0000741090204195111018100301c0701d840c1544000381c140a030180e542000040e81ea00707416501040d06643d1980b442406029604901221915500c11801c208003103604069446001c540103401c51a2004010700700410440403080b4100e0341d1000510302c500d000a0600d8445040603100319000e06100060340004d0ac9000035500c64401312402200b000d0b00100c42403500310042500c84074291415031003802204041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 855419433 1250 855418183 855418229
    0xf15231909080f0c0a150e100501180509190c15080106080f0907090f0b03120f041a04080a060c020c120304141207060315060c05060703050c0d090507 66
    0x107510059400102d0303610305095451000c03103d400056165a061291817411000124607692484888202d0f003004506510701000035410702502a018645680c544001000390303100341500050100c00003c00042e090300d42040107070038503940092032005804c0b02c2d007086e010401c0a2100108a580d440e0700042c0000c900b08045a4904080c8900c0d8001b48980300030074040703004a06159040000042118000c5903509820400d41d6070103a48480c802ea5218000100350078140059040491085a03251900c1510206da0340c0398002ea00818034483c2c02c201c0300094030003d900c01c9402400a81040300d01c4260710b490120090314284054a005020702250702c045420502003075005034400c1005182032600b0300c020f02411030100e001c11544210340d9885158611400c1c06004007401d016940440d0000e0044505106010b00d039200f0010000203880040100e00046030294000040f49000b1543c1c3e15000c0404016005069102d80c416241030546420020002365080403140c1c0800c0c1107040c0b42138907650f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 855420683 1250 855419433 855419441
    0x60906080109020c030a0f020312190b040209031c020a05030c0703120302160b100b0304050f0705030328050702041a03010605010212090d0606080d03140c070f152319 73
    0xc40343d11396000f40807155229000384606134a000040c81242d0800320b4010000035030740400e54501d03210706840c0c3c1b00000f211401d8026540c80aa00f91015880c040300320300820303540ca0071503035100034200d800c013000039900c3e10a0200032043d50f000000c4907165860004910340320421440f080324140050041540024060b0080c4c501803844200d28207003085144d2180e00924800800081c4a01140d11000c54004d1348d11015500680c0600010000d28140110451401c04240c1145110b58400d01074410b0b42c0b45450045401840c3c0d43c5250700205003a0903081c3e0752070088880081d07101d4200111240d0381c000c1c0d50003030240e035030044009100195541005907120054200320320302c5400b00b04101c0159081a2114050b814400c0c00000303080c560700c9840c0b83c20195180c51000009440d081c00c5401804041c98098001c02c44044291a1511683e00d4011401c01030800401038480c0c01840740207041305520100c0020303840004855440300007020410454001c440d000b040480030350300007480e500c0500c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 855421933 1250 855420683 855420697
    0x601080303061e090f07020709060602030912070e010b131502032229071205040f050411192007170105011d0a0f0f1e09080f0a0e040606090608010902 66
    0x10002c030720b440b82d55001131708900043c410360562285540001e444a4580b04010040a20350b02850310703079441c0010410101e40200c1c40765181e45c84a482400b0100005e00d40700c0c1156024003203507a69111052481054000c0c984c0f01441d0b8000382d40c0401078a68021000b4041d0300c0d90346245942e00c100c40ca2252030010858005c004c09900da5405405808141c00c0035004c2e10702d41848518101502c550b0340c00c001308080c0d041c4170000344001c40c08200c000400c01494014240450f000e00481e941404215200d0184a502010442248416942d400d00503460407418060f500043c00040078400c00c044e56a03003c5106420b51003041d1034400d00485c0f418402d5505940000c15904d0301525071550031180744a02820300c0400503074510709803054036036512481c42e003502c9000c00481c3c411040c6a0646030208191075588000d41001c01507000940b110049038841a1000c0d00240c48070401c2c4012580b103060244210303040b0345444d9022820fa504000058103e49083e81e606403180c0c0c848299034103a010709a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 855423183 1250 855421933 855421939
    0x904030206071b0c0b12100506070f080706060906061101090b0a0b1309050d031a0907030f0605060d050a0c0c03020d080a020f1204150c02060f180601080303061e 71
    0x40202d18514459481102030b0032080c000d0a078200b240341c590f0311110388960310441c1141d000142600042d040c100b03040fa4802549140d842c40c45151102283c803e02c45d20074010b1100480c88100010000b085042c0c58a10f07420013010448241c80d020060010302c1c040c000c2001003042491000081032050080030b40056000c6c001c00119290044403001a05404c03140907404118140c452082200d18414070100304d006400800d0141d6a03104040c003203409025004415808052403005507803145082030380c0046891400242ca01503407000d40009001c9900300b290721042c00640404940090b0b0400b44c0182041c24040114140760601528500c01c0041d000300542c000e00c843c1c2100c1402400340da51300c01d4007000050300e042950445155140e02c0b1403840600030f81c00034203020600c1041003d642d80c404002004012400b103c4e40003070350346c201c0141300c141f45006460008000210350101003507200490421541c003541c554820503181d0708111881801030585240450051030b45800c0702d45244005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 855424433 1250 855423183 855423193
    0x60f060302012304080f060103201e0f0d0c09060e16050c0109080a0c03180f0b0904090206031608060f090408090a030c17100204080309131107030e0f09040302 70
    0x421100f910071904401c8003040d8040c0000188054140103c54800c0380440181101e0343c1180f0380030082d00380d821208030304940b5810301e030011521000740070380e17000400d500d82105080d01d0710002681007400f01e5a05803c11420042d0b01d040107a040c12003010f0300c0301205d00b03010f01c0d07848401c1820058811684604003000c41814120f41d02e000b50014101911613800208402045840340003007944005900000508003103e51800d140d480001c461550101d10030302001d40d440c02c490705c42e00705242c0c00303501c1c85648005440c030226500d5a00503071040f84e000c2e108644900d047e0b1300450440c1c0030031100e2404100d184000620300d1401640d400042c03840144200015144d6071a4031180d81c00020701283c0000c04080044003003904141c5000c0104421200949080030642019003404044d2800d1980107005100611440b0404070503980c3c0400c0565801c0304040810000901505001c482d0040901c80010340400389548400350340c5003803006680354688604100244400d00c1400c40300a00140c101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 855425683 1250 855424433 855424457
    0x60d0507060302120108010e19060902152d0405040c0c06051f0803040608010e040609050a050303070e0a08060402060307090e0708070f020f251d04050f07030512030408041809060f06030201 83
    0x600d00c0740b04410300502000820722f4050340450300003500b200007a120190045021803104098144060300d00f00000c05603064144c5030700440c4618000c0d0300130984035940358441a04040d1044000380c81d12a040b0000b44860704181c0b90001e030030002c402c00140c1003091110f02081074030000040301c0c21102c081d40c4030006680380501180c80500041c0c81103400c661164500b401141d810040da1a01601505c0516500c3c2082e050142002c4a080202c50281c0c00c46002003100344e00215046078080d8050f01d4141e540c0d56194011a45904543c000706100040301c818040d015500115540c4114070640380c1150810300c000e8241d9964991958600d219401602c1c00ba541ca5000c40b0040246007800010761070b15505d481180c80380101e84802d00700e41101755005c100078400100702e603c50341810344c40505805811130b11015115060707c1480ca000c140c00001003002c220f002001c560040c580350180e4054240c50794070a002414444000f540c105040000d94404803420788602801c03254141c40710400c0d010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 855426933 1250 855425683 855425713
    0x20102010501051012020901120903090816050a0b07020102121204150212070c020a2313060e0f040f0c030b04050d09140114070c0618080102120c03060d0507060302120108010e 77
    0x7c8508400790400c41e0054080314a440c0d540580750505100e82ca801c00014240b1f444d02c1c0c5458840c4170041d00e90041c0d01420003042e1109036010080d03c01d070300300c41580c1e0540c81c00180c0c5071421411600143c0c5a0029020074103080305040a409180705598808190719170000101c280d02540500e4090740e201e020201d03200a0040c20882141407001d0b001c802041c1d512041c568414000e182040035840300e02804150b00c1c907105030560800500070508014042c140000409640c0e4000d0003581c1d08042200814144907184220001c460760281c1603205417900da02d46040107000c180c2e0211114800c288a2242a40c000e00105040c5c4443c1c02d8070814041e9054011143c50300009106030f1051410001440405d8091041c000a441d0f030352246000304000d03001480100d038441c0d0080101d41d02c14007442c510988140b0585820a54a101c140d03125142c090020b41e02c0a49120000c015100d02940007421030f4148e00030700481c0400d01d0b10000c0c942e981c2c000c00c500380c80c060f4002903100e4001102d1040310503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 855428183 1250 855426933 855426937
    0x30902010e120f1606090b070302030a0c081210080c0108071b020111060c0c0d080903120916080c1905031905190c181a060d022502010201050105101202 67
    0xb156140840310b504294601c401c0c20301101c0583c41c000800e9402c010b0003001d4012085900405007404a81e15142c2c940d18029100e009019400003080307015000541417011140c192581201c8908102485081c00305080b004a8400e1141c980b0600940790311982660203441014802c618a0b220700c00c0c09044400d04000d091035114040781031015810b4041d030360050801405d8464100c0582e99a600d1103104011441c0c200500c003501c00b00084401006a02c810100a81d19005800302c6000070304c1e2074002d116401d100380c00030341801455404100003441c0500007190540b4000c00d40d04400ca140066880c190344518501840d501644121a45000000b1210001f00e20074016030a8582d0713524240582064800c00010036183d004428400b4020004103811241d108281e10f04100b01e05c0d000b180140426000004da564030a000109196032080c410741c04030b031840181c810421a44250550480c083c030101060306900544c6444000304080c00d0aa03844412154583c0b640410301c3c081100c801d01075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 855429433 1250 855428183 855428209
    0x603230604110408061f030312021605060403024206010e0307080d09090516120b0402160b09031e07021906080a110901140c0a02060c0f0c01030902010e 67
    0xd80e9800581ca00d0002c0c640500090b04804001c0c200609002e140b00c044006c9040003c90007940500e41040000d030000c40e0032003803128030f0368090786881c0c0300841e101403d0550000a442400b6031000c00040660200d4202040481e01c00303000c2242004021408400030210940d5141310540c868864060304501c91580c2e1100d4140341c1100958a8000441c0c1003405a0b80400d146c0d92199004c41003480c2c004140c00b014021b000000c103c0352070032014050701010040f0380c000070302a81840c030400ca50400d412040711410090070070355840003000c04d0041c00300120743c2c2c21740d41c1030f000380d0205007a010702104076071511740303182c0c6041d4010b618544461116032007904100d81c00215000c44110200c81084503000410241c2c4a20040d40391400b40708041c3c0b04c40305241d650a2400300322007100c0341e0300710030b640070509540e210300e540321040040002d16100902c0c2001c0e510031000700b814605014001645110b82c10030710151403002d1104c000550940e140c100e40280810305034230781c0c4101400d00384189406 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 855430683 1250 855429433 855429439
    0xc05070204091e1a060105090a1806090219090f080705090a090506180139020304051c033002090f040516020c09010b03040803061f0909050106032306 66
    0x4a202102e203c3c0050840400c41220548659103a041801070314005840d84400300303003403c51601007007000044002e01d01e8042e84225030743e1503800d0595102c0340e90182e00074050b00d00007199202c010004840900c15100040c44c001140d840000c40c80c0740c40d01d0440e90484129900401000c2d05200811690340002031581c048540c1d150710b0340b804260308000b4a0700415000c601c01d9021031718002e03c9400c0d03450003501d00c6444010788003188103c0303d404c0020185c1590140b0f400c8141d24044004074114816a444131742c1c4400428254400d04510b000304a10051107601d071b402c3c1c007070750039252840721040c0501c0300b050710001520102d80c600450740051410a00c01449150130480a00001e0205d500640705030f0162007015545560140d010400038580304411155a400c80d85401918403041c400104003c0050f0b1001c00407488949070036100b96030f0201c08102c03984507000d424000500d06212803060081d045c1c101400010541d000344103180480c68881c0155240750013a003040c505e411005070040360 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 855431933 1250 855430683 855430703
    0xe010b07030c0602041202010905061810023a0f0c02270f180304051c05190615170a1106042105011103130611130305060702100c0507020409 62
    0x14030f144010320142040301c19410320458280001060072090342c0000340140300401074059511100015034107024411210301900c81310b00c4904a04100090009440032030039000c03030001081d030542c000048500702500c861061041e40008440061014241340c000c0b40c0c114a241015040c500e88051368443e001032048030340545203c41421600f021100fa140072700021050041301c41c0c9120f0104c40c07807003c0034000c50800d03041c00d0005d0070300580d51031506c0c0340300e0541c0000340c10054240301c56083e4a4240a03c0410114075082c40c10142400c001c0c0171442250003800800c5481c107804034103400110100c01810070401a0f03a480ca0700983e0302461642c080303002d000005400e600e84140c01c011100c0710200f4401001245019421f580860f010440321707103030a1082109036500c0e1500902002d400a801042510190040d941944507091000d02d002c844100c0200500c040000d90768020100b541c00c5603115400c2103c520101e80c982142c0d440024010014032003d8a0180c000c100c1d41800360341046 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 855433183 1250 855431933 855431957
    0x904080d02070c09090501200d020d0e06010e0907060206070c0b04030e1e03010605100c0b0c090907080f100501091502070f060804032307021003091202160803040e010b0703 76
    0x19500703c440d80009140b0b6104d8003103100300135080c018080002c58007524900b00d2458040707901000e00136540e03181007060780840d07000801c54003a002501201242030644425503140c964984c0701c0d441c11035404045206145001030381610004101e0310840c21681c4030181d14402e0b90360b107608101d016006404010032102c0340d200319583e02d49601041c1d001c0364420300da02c100720800d142c00e540c3e90b580554445c1c03400914212116420044030550240e202e02042240d43c2c40c0e005240040c00307402107494201c0548010025000e4100d120940155800701200016560fa50040660f00b01d95004d4540000d110f003100300440b2407907010020211200d0b006440c101d946803601e007a0104016800034001401e01340c284418103402501148861001010900d500c2058901400903071003000c20082c0030f00c0079192032900151003544144030056200000700c1840501078002550f540447d92620031b4410b1102e00041e07924000000c136400c03204040d0100d03005070318010300b4809039004a0006c0d018400d20007104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 855434433 1250 855433183 855433193
    0x409020d0b03150a0e1b2103040f050a050d050c01030b0406050d0602071a0709060f031e05040c050415050f030a05070314011d0a0f021f0201061e050904080d0207 71
    0xc6030014186442c03d030014a00450075100380c0f0601c140b0741244d608244280201c1c0d41c81d0690408841c0c07030540f01c1c10042440d112100014000040103603100d070201141c04101c81075020b090740c0c1201c00448050698507140d404001c00d412150400410713640c0b00c2d2045062650180d084a80ca491001b00001512640e48010071040008030340c00b101c189500060315802c0103000d40300e80c044d202c4290401425881c2030300b000b0340402c030603000b503600b401b101030008401d16102e90011403589400300d65170f03010340c070503840408060a01a501160813401040000c28103040070710481c0c1c01220b0500760306103064907090501c5450b4848940c0c0e40d03054016618210045a000c0022100440c8134401507042469114486421502d03901c80340310601c648080220300121000900040d842e0b0000070744a0501000e200003203205800c041c0c40f03001002210ba01c2242a44c065000340121504e8100303c5603480713080c02000070380307030400c3c081c1a91200958004c0340c049407000000d0000e5103807810006250a40e02d80b80c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 855435683 1250 855434433 855434443
    0x8040b15101e080c03010b031b0f0a11120d090203030d140109060b03010620070f060c031b0c060f0e1e011808031605070911090111030309030409020d0b03 68
    0x44404034903a0081d0341c503000c80d1290301c2d940c4900203181003034407400c084107021400d1006105060400c3c0010004c04d0603440540c0d089802d0103401c90109503229480c001128540d0001c004103404503988100b04e6a48a03400314051007902c00e481d00152034401c21110b10001403540502c141e805100a12001041e60340c0382c03080f46152591a0428241907140220b070106031461034010402e140024001040110380145403041c000003402d511202c44000000e40de0306c0c048aaa2140405000b00d0384c0c0050603603000700d40e010b0400e0007584c6000ca19041d106404920003c6c0400c000c10f01e130401c0208002c010312502d58520004124900040103044020002c0c1400f170342000300b45c241405c0231088003484e6800c5a0030485500c1101e2030040c01d10f02c3c050307213180c03203020f841d20089440000b464404200b1800780440b9003e4040c820701000422120b0702440817039084400140c0c04900000904600b440b000026a0b00c0b44035003038010352402c0c4c140003101001e5008a0300031501d80382c50306540c0c00c140e07500b804 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 855436933 1250 855435683 855435709
    0x7080709050108060a090b04020d02030c09010f15050708040608130b0123040c120510080f15130b040618020402030a14070504240903050f0a020114090108040b15 71
    0x20302003140d5040c190124107001c3c0250140800f24a003521800000d81c1080750b940e44141c04841c4c095001c0e4180c00400d05042c4c03038000c1076520000400000c142c05070002c11030000e40305030909030409805000e00c03c3e1400c0c440c4050203040000700744820001d00340b254850b40c1e807103c208040d10102c0700e11999090302c400002c3e00002c00c02d01c610b0391175203d0b002030903c3d203d6103038904850034030110039100000340100c1801d01101e07804644030000036503101e2000c480c0c4001003842104464200242c1030b4159210031b41407124810359440e840110790045504000f5042c3e00d0380005100007151100c1d602c0c080104a04404010703000750b0704034000d016a449101961140b1711a03180407801580c40400f10031503120040980060010512003445030748918903281c55a00100d104210003800840419130f007102603503100074610700c219500c4403180d4102203410040c0782e1003a29260700d200302c0e81c2d0104641c6e01603501d206000500c04000a0041014400c0c40d80d009400869100064503080c00410b0354284c0d181 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 855438183 1250 855436933 855436949
    0x70606080a11150f120a0b100810150f0516020a12030e0103061d0603031210060f020604211707020a03081509160912030908010c110c060c070807 64
    0x50421103150501e60603c00710b11180c400f1461030410a1006411140510b031410705207540440002500c0e0340c1e1540c0005c00240000348001d4240d90750680040c4480802c445400301400b498100060340189400d1003040d8000c991141c0d40c104032003520031911604a0724513810b1f0b240e012071881025031107400005001c2c048030380764000e41d0701c403601b805003071181d03a00201410145408130402424000003001c822180100106400d02d40b03c200000c6d240d0300400244605040c0d1800a0103012410754181c08100c403115140c40d840c503c208101a40c0f541411030b40500f40607010603610340f0380d172501045d40a4102c014101910000c101401c40381e09900c0448107000581d2051100a040c5500141956400005084c81081080940c40031919040b000790641007940e41b544070561020340074103411805030569001604800c150b5080080981d0101d1041800741d518011651500300d11900005000c1203002c40100000342c00201400550f9003c001c690f82180039a42011604202c10310125004103608 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 855439433 1250 855438183 855438203
    0x815060607080a18170f0c0105160f020a08010506130903020709090f0609030f02070503010618110f0d092102061504060810090c05030f070311040207080703030915090b0103020402070606080a 84
    0x22070360785490030414641108291f4001100340c10207aa10034103d4171403d1040d0440c03000b0121528040794400300d409402035001c00295130219600c0d405500c500e01c0f0340f900701e03503070340820124200c0041110700c02038020700142c1040300306004000064118000462141611440c640c6840d100c1c4012914220340c1100041c002010325804075504103d01e0000d480201e008014451070000c00709103458110702c10b80d29154540ca11208843e68a609a37021820041c0d04143e03150081000c0c13030010b214a150488400300c80d035581140080e84540c00840690550f00240b1075515403035488400243c030010001d601075120140400d5070300d024490320986041c2d8000208011040b1320300603013081c1544d0000703402580f0412005a00c40710003d00c142c11643c001034081207075008400031901a1003480780180960100051304020580d00d9803150b18020b015000c0108480705800086040c0d030440c00001e024032407031000500140c41d0950040964a1144100140456413224070b1418140303a0003082d02d0384945 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 855440683 1250 855439433 855439469
    0x2041119080402040605032a03030c0a0606030506250815060a020105040b060607080f2101030f0c0e1302010806060904050f1024110f0111040815060607080a18 70
    0x8a401042c02401013200540300f0015215100348499502c020008c5120440010171886518103004480004c00b0090688801d0351190910001a007540d200031030312449480c00243d100c60380c031007200c00c0b04400d882d88040d00c80c1d00114101c42303c03440a0300c1d4100e544200c2400700190b03907a401c000c10b000340d071039000455585000d040051180800038032050068070104101d80c00541c0040884041a48c4101c2c820348503010701d010b0013a103034502c981c1d20b0301000c5040008400c0c040c60b000c80d8401c0318821070b002200e03140c039452400e82c20341c415070301e000590203010036020041d80a521441d5010101610b01420010500009000d0b10019180410704180a006000006015000e14009410081d0f013001124034568070340320b040b420103400b00d410000300c88044200d225040c4020186450800d00903c4240000800c5c030700c0b680c1c0203211300c4c4010f03c110a40c00f021400134242852241c0c02c014102401c061113a100c5a5440d80310034040b00801c580307000b00034440140d0400c0e4402401d40c4040c203038541d0780 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 855441933 1250 855440683 855440689
    0x60414090d1b1a070507020a0306140601020f10180c0f0806090c03060f19050a050601111603030c1e0501150e060d03050a050904020d02090a150c02041119080402 71
    0x1aa03401900e00444a018240200d95203004945505108240c2c680442e42d038410102c17560f0003014402940985005400018401e01c1e42003203004442e0500c500c0310980b964001613903503c04500011005230800303400d00c0100901680403203000803800203407095801c0aaa1003190034491500000c11315000540180003002c1c5c108500fa0380310009000628078400388000180e40c3c2d02000704080c0fa105e0003640020248001c0e444040020440980240540d0a05d030490394060602101c4840c0003610501400b0442c1000181d1034460b85030050708002d403541543c5017251032141d4040d059508140720f4011030101d07005120388158450140000082d0f6000038034040c060410580c0c03142402022140c10310030b0507969440e0220901e80e05081c400d94401c010b09054800c1c0c00342c0440941c0c0144046054181807200c1c2c1c00515050400322064000c09440e00408903106941d03a512400050355214000010304003940001030551000c03040c40d00b4072110312071030340701c1011060380c42000494100c00d01003141 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 855443183 1250 855441933 855441947
    0x1b09091614210c070c0b0306010c02093103051e0418020703030b040603030f03090c050a0e0f07030519020f04050402071104061401050a0e0a0503060c042d0905060414090d 75
    0x140020f03408524020340c64540180303800d014000c244100381c1c0040410700b268000c1500c1319003560b0140445503546054004201e803407450b0707150944020b051468009000c1d1368401507030b400d15819228a41441600300c2c1c0d0845d9090190074521140000300408a0390300009900704440c42e80c2c1c00c1c009684c0c1d90b13451400405440f0343c0e01489000e20b041c40824400241c0003003602320140d0302e6240018010300707142041c103d80d210550105030044030202011a08030b0081c4500351040035603071800e9107280c88001089040324821120010080036500841c8520034658008100e6042410041c0b41002d0321800090300303d03407140b181100c00c4001e001c00c9018130300306802100300410645035400c0b140c101c0714002170064405c0826a01c104807402c1000c1e80c1d160b445d85402c601805024045a00c00e10341340d6046c1240c3c3e882400740626400b416041c286c1e4900c004400348101001c450010408a4502264407010b007601a1606500c242c4034049080b800e5074054a10b480380310607c0060115040d4050050030030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 855444433 1250 855443183 855443191
    0x602031906091e0c0c2909060106350f150d030818070f060c020a0f050a0608180105070302191713030512040b1b0909161421 55
    0x380b0f08020214207070710f402c00e1501491040e642c20202c0e010000210444540503080c20050058022480900d05603464070a175075092000701010446940701e1070001c2d41d40d641e0911030b0f070002a0b600880c3c05136004c0280d4a81040014203009403810160a0349103551040703003111a00c000c041018208070000c8800e800f0b00e210900252840713080382081c0d460003000008010100355a1a80e542e00640313001c0c0f010451003004064113007480781c585807035410080c56001260003da12402400c840820816000d192510489000402200001e45003207400d66414000900070117601c2494015652001c6081c082e56110303240c80e940040c0e540d40174042903690b041c42c4446040400070400581c0009500c542121604090b0042499840c507400346001c5915204000b6000d08500111040c0410007421541c4d01e4094079481700441c6d03113104918145c2403240200c07a041c0c0d0740070324080f001c40c540340d03c0035041c1d8001c8156860003e0034488001107540d5182d0110303540300010400300344585408484030300041c0e04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 855445683 1250 855444433 855444449
    0x41a07080d2a2a0609060605090f010b0304151d070317090303070615030203031c0c1b0f032703110907050a110304091a12240c070602031906 62
    0x1c0e19151035401054255080902001c0034103405005040c0d0300b84500c4405055484007090204040311b181c82d00c0545140d110352130190211074082841084600c090905a071184000745084d80d485445142c0d08040d04421403840e940d8400d80c140d0415103c00365940d80c0383c01c0d10b0060422a00e54a44069011411040b2410000007444061410398002c0b08075009603800040104444000d07a0079130301170306450380c002541441b00150700001001e4084641e400800100d0b8200444415054103a880450064010f0790a5144440082c0007402105008201c18000c1c45d2900020354141b0400608000342d06448440c0c81640200b04100050b1400300b030901e01e025900319405041c0200f02820074010000a5403d005000d0002ea030315041c00c0003a50010042c2c00001c1c4031802c02800316801000095812500640b030030403118030400d0780087c030000422140d0084040b400520303401450594809840d1400481040140c03002050703060001d54010340074034104040541005010034100c520560050b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 855446933 1250 855445683 855445751
    0x617190204090b09250e1f08100806070503010506070501060b0c0307140109030e210d0e03010e0a030813030201020f0f0408061602060f0601030e010e060624041a07080d 74
    0x1056445c1104121001000c0c1451054980700b00b0005003c6400401a101449081140441401d03848810f1074014542e2442c1c46140395142c9070290340356003003143d440b4041b5604000400050811400405904d40101c0000a0342c5490b01400442640200c4804070f655002098031400d02c42c07518003041b81400c02ca0b00812200c81541c1e806041803000d081000d20030480c0700f10010960182b2002c401d4500c61302000d03035854080490018003c1e44940c0b141c03602942c078102c0580c0c01158001405003032950161079109207940c8801c4059450404d010003181155024094546214070200182c21407200518203d5220b40c100822941f51960082a14a0702c02ca024030040d50349030040760382e039004090813003561041d46d200001680a4164104000320b81e41ca043c0134440d0b821000304046002e03040c100c401c49440c1d40d003c45000400d000c0454004d51401d0108402c00c04652006281d60440385407031021800c00da41a11000c0c0143c005041c0700418945440d0a070406200a07498a4036100560700190 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 855448183 1250 855446933 855446971
    0x207061103090d03050c24040624031716060e1615050313050609150a0603110409020a030b090a0209010501050f0d050c0d0903030b090106090617190204090b09 70
    0x1003c1c00700541001c1c00740a80010309505401061203089921080e040001e00444031121400c180b95500300d8098031804c0c82c0004000c0752030b109000288003600c902070b050a2013411900c4080c40003201c0c15038400780b100d0800c400c0300c041507040c50f031184090059000150312900341685609040307220044845106203150140030140c3c41e007242500b0b05103d881c1c42c903201d03074440d40f44c0030070380d030300150040d1091054008204000900180b003105141492000d000c040c0c490318407c3c802d64580b408010000d108030032200916003020f51002c42c0d15400140b003848400d5594440340b601220507101d0380d4164003c512100b0544c20304070720b02c0780105000c1c41c16500e4074000c650800c02a02801e465140035035143c00c0442d1aa1524000361000c5007110a4100481d0270280740c080c00902c40c1180d1617000717800d04000002c099004040200850780315407110607100941a8070840c101d0b0340203250118a903a200b01148907080b040c4080c01c0a0b203c01140000c5902641c0704012010710014411422a60424004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 855449433 1250 855448183 855448189
    0x1202030a0206071209020a0e1504060f1e0515130509040209130c17010c080610050703300605010806040e030426010f060312020a030519050904050106020706110309 72
    0x750f104805281036150803011041c00000f42c4140800a580801112400714640a810340314130300680b2610328003030300c2a00c6402840706548241c46000241c1e41c09060422240130900c00c5c081811088200030150192564002101a000d50904400c3d590011a0380d0744020007000b0720102a03d000ca43d09a518906580002c140f80030042ca4002644441d0021a0402080c900c6e071001034405800490f00103c2044481d500070319852010000090315000814401d06040344024140c1e1842e5844a10f08400742d181959000c001200c0b07840d0300c80590007500c03010000301418500c0b5070400c040214180c0d14080004061000c05031440384070740d24090180d6116200081102c0450b411492084401502c03410101c024031b0711010a90855401c0c41802204401158801400d07039100314910003e02c440034000300d94070010710301d00402145081001e2009402141300c030a0f040c0d507162401d035103020b03660340100d015180281c0c4a40d0159008610074402e886e00034002203010401e0500035401c041d28a000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 855450683 1250 855449433 855449443
    0x291b0702060901051204110301111213031803060507120c090501120f0204030609060c0c110d0206190305090f150f0c1306050403020915030615130f091202030a02 71
    0x24480e000008038001c0b540d004030180e6003829428042e4610303031b140500b000d50ba62070843c1d641620035480c15103c01e11003c8400241c50100c52001c0611105544a41508004480c1001c0a44c244400b2000e0140000c02d40e007a00405036124150100352801c1052014180880c514021034800b4200701055003401c0c0c5c888800d004489091034080041c07818640040010711102c901003001070b000082c00303c00d00c011a080600400c0c403480c0300300492404100304541c4020360b140300501c04528200c0c06030042c900219202e507110b00080c4180d2400700841f00780c00b080c2c41c40303402900c0401d88880c20080f00940600c91111b1f22000c41d400340c20f00b2400d002584188000080c4903901890f40c20010603003070040b8a013580e6030084480d03008400280c4840d40a4920b40191004a05c100000300000f03c1c0d50745c0580300302052000c00f80c010321268a8090b0103611003a1188400b98114007488242c0d9004a69070181074440b6490210004980090b4142258103880510700003013590300401802c146142d0000e1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 855451933 1250 855450683 855450697
    0x20334030201020a1722151b08030411040f09020103050c210a0609240f0b1206030a1b05090a020307141305090412120603080a140403291b 61
    0x1070329007080030146045c5002c0d01c0d030454403d181c0d4041c148030004894400da0b0507603c030800421503082409004a403000c101d40c0c441903580307884048030b000145c042409950014410140031160b800600003003002c551043e00d50f080800e482c0c060310015540c161145540100036030240d149003841d012a8488035041010011085030400400074400c42c060394008000381034059010f02074200c94042c000184c5203045c8131030b01000350307003100042c1c0e43c441d1140b51402c5802541d039640c14400110900200904d005080079054040c440c03880001405500c0a101900340d204c1da20f07a20310341010140841140020030101d0f0a0f4410001c2c0300303076640c00c0b0403034071030f0045605181503440341c02c0380d14440c40c0c44003a40211b420054000030f001c100085113180703142031610f6560705a0100f2075a030f029800c2e2a114072020340406001c00c002000207100b054446030500407485014039195881d501c1c0100c2d03100b02031071800b070002c0004d440c24000f14211121a003220302d15100359440c11564058002034401c6031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 855453183 1250 855451933 855451943
    0xf060a27090206071b060c050c120102120a020307030e010b030c0405221a0717010b03180313030501050601091d18150a0c030213090506030307020334030201020a 71
    0x10451040d69140d0400d5a003541d000c3c002c0d50300c2d000d45191100f00c1d64680d50140725001110b600c08158913204900b80050281c21000070b02c104000881440004004a10b111403255000c002c0707152448101914940224110710300103a5900d0120001000c440b66030a1029150741403040144c4550341c00203011a802c90308480009458581c0c42420f00340c0300e0350b032070030402c010f407a00b54120a105600784003070304103500c440e581100303592401e0044035038462400003080d422070000d0041c01020f040708051a80400401d07080c50700300e00310b001214038541200107030580c24252020207104021083c0100740d0407040a09261001c18207112880c00850711035428071003050b82000001d01d41c1c40c0c4000d000585038441d0410f03180b807502200c4841021490840d41903c3c4c10f4100a41103030b105100f842118510340041121002c0c0c981095481806407001404055162005000000150f6020310551f0396480a44081c2d40302c0180c4815a241a01070186058040c400c0c000300c2040503036004254400550340c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 855454433 1250 855453183 855453239
    0x6070201050f0d23040209100e040b09010f020c07050301112b090f031e020633030303070f0908060705030a021b160501140a200309180f060a 62
    0x706003034001880c3c124441c000581e001ca00745504d4901481c0c1a500842c0280ca4800c40b17551078046105410505110ba610341040c601700040118550740c03000c54200c0c40c04400405d02804000c103c00c1079801002030005103402c420810090703031400b44a05641035580320400307400c14881c0740183d441c1c010450040b0158500101c01c401400000380e01c802011035110700c601444141a05004114002d42c03051481009105103000207064000a80c0e90300c1440d4103459019114040890300842031004450b4040c066012203100120741c1e02400030714441d04050f9036803071407804000c600820501d420b80c00400da1381c003c2400d1082103a827250840740c0c00301c1e0301b030800341e51401d009000d5401c00070080580f1655004030004035910641102001088074002d0b6039114032a90880c1c0010341c54803501c1003040120744140701e4106403005c0002000709080d01101542c1c200848400031800d40152050b950f100f5003510380c10000082c5507103004d2500041d094a0b440c0c503640c1040c0150204d01c80b00308015045200d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 855455683 1250 855454433 855454447
    0x1d09070207032616110909100e100908091c031d060c0111090102010e19021002030c030f030402040e061603020c0a0c03080a030b09070203040506071a13020f06070201050f 75
    0x22080150340140205249980d15078914104100d1100c04e0030846895080b80340e440200e2400c1c0500705d003c0c00c2c00308013070107020741d0550b001c0c001056417074890000740c000e103c9021720000c000d12414034101d000d000c1c0d1540c0c546030a005c00a0b28003042e400039030304880c448806400300b588441c0c0448181c00c03a48200c016003402c000042c9035030040f00c522540ba1360804c9803804400c102140900804402a0002e2000718541450151601052054041c586010189007005440c0013005c022039140c2c02e0040c3da1070314100550507030450340000305041804400001340811414284110410b8503490005441d4900f4100402c00200100260f10b200b01500410360100c900c405221040304503900215988a0300d0b83ca207804003680d0000c280400109250020040d0b0500302a404288142d80e15400740d86003508003410000513402c8501d05940310200c03901d0520041090801c6180507041e000741c1c003500640c00d0b00c1002180004480e41e075003c1c1c0414041d403801030360040c05403042480e0b8580f0143e2100d80c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 855456933 1250 855455683 855455723
    0x30f0f0d20160f09060302091506070c0f0302090703052503110d201911011b080a110f16260403060501050306011d0601020705030d1d0907020703 64
    0x30300c21455414000c8690008150000740380c030b6402c80c0c082d80c030604602c0c0c1e60fa80e10300d0f084030401d21019401c540803000040c81141c00300c80c462040240101040c0c1001c1c01c07074076420302e0590203400c0001013030034003c0c003802580340c4241301c2544110245414442440c104400708503040d200c40f1070b58902210b014004a030b01d8001d0b0000c03070507842510445512202c91b010f2202c050114401010700c007010791840141d0042c1020121842c0a00c10385040003841604213044a00c2c840701b11910025560300c00c42220342e42c815104803200d010b01340e56401154148480c00d4011680910b0348030401d44c40402015aa0004010580e9110303401c1c030310f2810040c1514240943da0400101c441032045181003402650312041c14050015207005039001c000580e00d0300203040d6200c000307000d00d1002c4643e4103102c41194608445c40c0c0e074040c0e410310560301101c2c0d444e000300c2e02e405140080706d00410000d0380c0802036071401c0b00d00c107020b4180845083c02c0764102140f020f0340310a000d000140414615840c0242e902c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 855458183 1250 855456933 855456977
    0x604150e070e0901020d0501051806060307110d030b09060904020a121401060f1d0709091112010b091c02060313031403010801020a030b010509151b1005010302030f0f0d 74
    0x40301000d0b0540c0700e4500700710036030f00035400713032400000303040c9400300210356400d0030484040e000900c80c69005d03140d2264005c1000907040184060100b00c08001c4c26000ba03035061040c0e144514864601240188040c0e080004500006010768041e081c10310410001d40e81c0c107400c04046a008600401207079805092600c1c0d003140c00c01d4104401d6007414400186108645c008000b180c503008080603021000e41030340d4900c1c034010b40d680400115541414400190baa030300c204044203860303211170f20b08664490514031520003644039400c8550007080351382460408896801000d0100410701c0d10342c045980c00a203550101030030280d071607000211000e01701405500400c200e039001c000d4054403580e41d201080e021794000501000081c8c1002e190702c045500480645180003c0204244c458107480e100300417542e0010310142c61013070407064004d004440c0510545000c7c91680c000468a50b0440c01032500c1e1040f9102d01d413a840e030202c2c01c41410f14501240c00d6550030000c1c90841100085200c10324020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 855459433 1250 855458183 855458189
    0x3051918060c111b03162402120405040507052b05090304061e051201030807031709100c1b06200f0a030209040b15070b0606031303030519061205010e0604150e07 71
    0x10351038850040313003607007d04201601139a8222804024048100306c00c9840c1d60303034080f802d4103259043c0014017081c0f905030081980004945411400c200301c1159801e100c1811003244074034954060004d1032006180d015407a8400100402036141c9440c1c1b4100400c2d8406111450713040d8080180c4041082d4865070449064007050111040d182d612030405c038010398040c1c14105d01041100002c1c910180b2550035652060038050040e0140145104c0190302800701c0244c00d03410000060000740709000307122221118140240c0c0300040e0780341ca064212841d203040b030701c007401c0f5160103220780301c0004518000c43d03d240172149005601c40d0040400310300501040c860042d0711903000b4202c6881a00c062002d8840c05000d101c0d404546e840b0b080c24014035100681b640c10800a12143d0100424080d4101a400201c881500000c5180c8042048110f4065070488000040c001480106003c4240548201c5650540c0500b5403402c25903642e40440384001603201d0300c3d03610307802c040d90700c3c1078248060401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 855460683 1250 855459433 855459463
    0x1020c0d1106030108030a1707140a0c08030702160e010302240c01021804050a0504111e0a091506080105010905100201090203010c081008120a03051918060c111b03 72
    0x3ca503184c42d40d0b641c403a00001d4001c2c0c001000480318181d14028809400e001d0290380e1a4040083d2038044000816845080400103100303003585004001861341004611a40d61640a000f1241c0350303007031001021420307500006107040010010300144c0d43c0c003045d046201c510159201d202c0300c240c213405540c40c080d601c4141203039480030a104100e50510b0200c181c504034101c9040020b80d6070544a0f030119201980c0143c030346060007808400a090071042e0001c0c60078258195801c041c0800001142001507400c0902070544401002c0c65003030741ca280900141c24141010301a560601f000200050400d102d101d201c0c1c500003255040311030007940080203150b002f070001d0018541064020b0701c021001c0c3d95200702480740314000102c05002080c105100710506001e145090341003d0300300d0180001400d4041c803042c141c0d01401039113280c5d11803401c0003980e41c9210703d0200b0706420280122901456588240070900701110728480010951003032081e84c040d50364440d5889840400c0c5880c101201d0911 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 855461933 1250 855460683 855460687
    0x2307090c080f060301050f0a0e07210b100806060613180911040b0102150405120304032f0d0c060213080106210f0311120d020310050102010b01020c0d1106 68
    0x103640d55000d10903a10581000d400c00d1026110102498200c43c0110350b0f4a106a1201001c203143c030301070303412880c0344140240c02c0b070b5032554440482c004184003212007c0245410700d102c10080001540810364060808040c2003031003850004c0091311100010111031040b100050040c050070407006095016011001030b60400c1c00a1440e80300003800c0801003500e0501d07071132300072145a00d00380c040d20500f20740c1030340076101c0c2c5903c030703d0f6528184901a02c22945802065408451191000080c510a900070b40d1007000d0200000c2c5135580c90882ca01114040c07205079244038151450010781c02d1040d80142c501081c5143c1c447c00d20070002d024800294001c104503040006841d14150405d00c251441055800f80d0040718200c070a002202d0000c00500b4100400040300100b8020308241a0002c0c486095988487d800141a5803c2d0300c140e01851007a58040280320004019442510241900780020041003080303100103991009513a8000e803090032000700c01000c10003076910f001c60400010b40055 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 855463183 1250 855461933 855461951
    0xc0b07230d0207080601180b03070815040b0108191b0b030109090506150f0d050c1305070318021e0609030312091b1005070602130806090d020a230709 66
    0x103601e031040340200c0001841015804510450049140c40c100e41e501c0b0001c046150702ea02d9a00d02030007075103481e25818015100c0c0040c2422046c0240d0194a844100c100303030381c1c03820380740010b000700c8107800c61003255110507106404243c102010070040e41d001200003040402c0184c00050b01041078000c0c0c5548c1c00081b0000601d42c0382078106400640c801c000751a5144c0d50171508120400c40207c4040d03000e400c5c85600016410040003030040b250285041d184040c85190109000c0300117505d070a508103503030341c04014030345905204000c5401040310390146850042d80019800c0c103a4502107042c41584514910f1460351410100e40001d4070103801d03039441c0c001000640138008030031604d80c0701d64001c22084100b08020207541c503140c02d4000301842c0140300112002c8079250000c030f80458000350b08010083c100c1c9d5480040d08014280c4000910b81403801c151484e0908000014440c295401580f0300d02c0003c500c05034078000d99144440c10790b003100b0316021661400c80542c0c400d00350350b07141a41070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 855464433 1250 855463183 855463253
    0x6030a0b0301060608060a0e240607120c020f01030c12180c03050d140403120c060209220605100801030f0c0b0a090e01121e08040b18030d0201090c0b07 67
    0x521b101d00d004a841e100c1da00d030b035201c16000b4003c0868034009410700904c0089418135481c041082001d0010f0401814a082a40d4101c6a02e000ea4512004554802d1517901103150001060181100a02e4140241480e1201c00703403c40c01c2c1d0100c501519070f107500d01d0381201600e4416000d603540d0800c10900e000c60f0341e42401e030380711020394100718002803092030000d1844600d01c048a045a900580b18000c10311646412503000094140c1201c7c03980e020444050103a540b007441c01d0580f0b43c0100f203282d40c4070030540000115030040c3d00542c02000d042c10f5071020b60360441000c60440b6084001184819524035181404000070307044403c0100c000304111810030740c80f0007000b054030506c507890319081e6250449055001080c12004100900d0494011510002503c4944025106007485404c05860f01b03161442600984910100640c4002074800301d481c1c2044101c1808259000070014219161100c10141c661402201100b050001d150020000050b000c1241780000c0f140354440c00100280b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 855465683 1250 855464433 855464447
    0x60e030a0e12070f030b0c12070509010f021207170d020304210203091f20030a120e0601061b02131e0e030d0f0b0a0603051e0702030906030a0b03010606 67
    0x101400b40140c4401919141000500101130b0390074050511a41032442d43c900c260700038006c0050000c40f0050101800c5071249016042c0140502d403265500d4001c048001002401807095100031507101c5040030242d03075272032412940080d0b0046001c0138000144540d4080c280318501d04c0c502180c0c130000400040c0480410360707030703982e03032481241891141c80040c1c00c070ba581c001e4040d900d5000d00c0a02c804107100c031030b103144040740298900306128807801c3da007408a00c50b5016200145240c00000c0c1950f0481d90198840801c03603400c82c003c00810380c0ca080c0050b92011b050081c401804261084001d80c1a0041c1480c42c0d2154010407030681c07110010a034074041c00813000700301903d4200c007281c48682030440c02703001c0318810004025424000701b905010301030151010500c0780d10340c0d20405100540c40d0f503601040a01029280071030395040903c540c5a2056860078910301004900d0240544a54003100321258113200300c91603502c0c0d880398071001d0020802446855413540c0b8102000400ca500800303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 855466933 1250 855465683 855465707
    0x11030c030f091905100305040302251404110703030b150409091707030206070e1201060e09070609030512210a0603030305090c03120c031b03071509021c060e030a 71
    0x1610000108070414015032002d8500130789502c4003c88540a680703a1095020950160081c411241000c107011110150100e0b030b20003481c0880ca15950a1014490002c1c3e5030303010400a8030308000c040c1d502154106580246840203040640781c000071416503450b003000344041038903008400d5940c0d40c5d5014440007040000305c00c54040c03507100418810b0f00b03585015212250b815402802c400c0c3e64018046660a5103e034107a5884914805400840c00092003003501a01c4800030350501400e220101525140c00340d070001c41045024081400061400700781080102c0d45070384510346071040703040341d25501001e40402e00d10b00148001001501003254210000301c0f400b81e182000b540d16080c0880d0348541d07c0c0b03c10b590301070344140c4802a101511030024400c0c90241420759042c00300c40340c0800700d05080d801d03440398698004140034045c0800f007040c01109121624080141c84081d5000c690807c0740b10321015030100d440203c3c2e00510603203801c02a098a220070903240e4079007202e4800381c800301240c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 855468183 1250 855466933 855466939
    0xa02010f0c1d1002071203050c0c03071805060a1203050304060609020322050f01090b040b0a0614060915030925030302061311180f1005010f11030c030f09 68
    0x25500307811901441078442003682c0020030030310700c8210400340407a030155810200210300c2100800034480000c040c8207002d00b4800e58a4640c0c5042c6e12019038605101d101125100390081407081003141e60300501140b1000100ca00824540d07a04000118006020340c400d00c4002c40c8a05418201907202000394441c8d48645802c1003001e4852050703d00300c3c041126549950a4a4120f00c805c0c0b10501c103041304014852011100640c0c2c0e105405070942d2018207084580c0c00c10071040c40104540d4142550303100818600030480c0518101d0b40c081d008490f500254014980050400744d503480304040206078a14169505a990a00c8001103aa072052100301503207440b10101004900d03811103c0401c1240d070558002c250640382c00a20000315034069508030742c045501030314454180c039021503c4044560f00c44d040f80742450300501d42c1000100042c482c41015640c09401d0102e81e07040000c070104106a442d084420900c4210120b00c3c1d84110703401e01d40703544008101e0b410704070b03044401480800016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 855469433 1250 855468183 855468191
    0x15080912041d0f01050f0f13090f0c0b030c1b1510060311160305161202010b040e010b0d0305160b150f19030f2315070e0112020a0905060a02010f 64
    0x1078020f0b004403c2c400e0140d10340c00383e16006801220b1615100c0502c5082c002042d070280304011040c2c0f1000c94080c0a011110008603002c401c0c1400721007410722f4010890403110038074506e0f055416202611504c400405260b50f01c51440021000800010a41c48a6441082e800e400d000300140e81e81e02151040704000b90601c1e65038102c0410307020035100c400740c40d485620440d100b1070b0b0b025601d90700495816204028091001d00110b2192415640707200341ca0703000082c42d40c81510030320050360810030040e4900da040038010035460720b984107031001080d01440d190307440d000d0003800d00d418a05400e00182c010408030703080c0060b450302071655810205003281c18a480306256028404a82c084030107804d074005401c41d0400100c1c80460750035814620840301603400c01101c844010700d0b00d010b41424000e41d8030000c1c00750b20720070070803103200d4104140e4202000c40b00444c00c0020480001c10119115403030700070952680c50b5000b004024040c2c18000d168589030646039000034024003201904010340c1d0b042c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 855470683 1250 855469433 855469441
    0x18090c0a05030307060f020906120109060b03190c18090b0901080106060203030a0e030715090c080f0c1c0f08030a11040b07021e190e060a15080912041d 67
    0x4003009030801c54501401550401d031a9071038440c010300e009032401c154a44c007001803101e03a41e16440103044084111104c40300550411040400f2105590041c0e0100d850401c1840881d080e0500c10924503228540046500e01c03144c64104e40400380562440124000c0200118a480007074100c107441610036101807503660b030b13100441c0742a14550321a0700c026810030400305459070713500d41205203034845400480340341c0280c580d42c26001d24109200d22506942d90b90b140001c021183c812140244107990017070060500032400c403a03c0b039400448891145401c0103011000d00c2451801e00c3c00160840411411106d003404c011181e50310031114070a00c0380c542640381150340d1b888000d46081e10344182100b4103000580d030a001c0310040d00820b9454000001f03070000990317076031102010107200b402410403c1e2189401c11003039038004068a101c0c03151030384160030f011101441c00e04044485162070800000e44031720150301c3c1024000842040300b00f00c001000720700f041010664129000102814441c25a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 855471933 1250 855470683 855470689
    0x3020405010f290322050d030606020d031104060c06110a02030307140406091a0d0e032d0f030c0f0406081e070c0201031d2a0105040e0406180218090c 66
    0x109012404403e0034050000c40d1092014a520789900c503002000189800200e0712100e2a040920006e24001303034480360b040c00526414002081e50032114101400100306400390030450b40151300800d0100090403c044c42402030720f401404203402c111a0b6140d40c0c03060300c1c100a451b5807088941d0b034003090601c00700c907420b00300030012941100c050341c5d603e402040c10705e010498030021041030102402424010710054540a00c030354102c1c580104000c694a01800c2890100743e10351510000d210104040e061901003011401c9540a0303002d03d18140d40e80d65280c110058a000d0306490030202c1c2008503000c61442d41211000340104100002c0d2840307401c101c1ca102100d000211112400588424042c00065009400014a050703090310450741509414204614119626541d440404006030010058203154101210980006c1c0f83c581d20f82402e001080540b4400588001c02c0300f0354484003010000d0117905100d02883c1d00510b2140f4010036082c1d48500e6480035150228280034280031600030b8a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 855473183 1250 855471933 855471989
    0xf070317040b04020d2d020102300a0c05030c2b020a02040b060409090f021f0f11010b091f0510140c0109050a0302250308040311040603020405010f 65
    0x55202802c8241a43e955081c02404c4041c004215200c03403580341c8003543c0c542c1e103c0e8900c031030000c41d1400c040d41b04468000246002c86030809a44c0d13012600c004198100b801d4100b400c1201c103000c501d41c2c0d81e05010340e411a0000e0140002801c680030214180070704400206014103485400c102e441d04914200d9000900785440000c50405a440001000c0050600d0b800c01c1c10072420040a0b81e041c542d84107443c1d010703141920821100700501c030103034104614102802009007051100300400040c13180e40c018096084a00c403060600078a1070b04064444025041000b0184020308500a02d003855591106180f14144a03002c4003885040003047c035042054000e9a0030032650f58041c01c02e880045000b034660b00c03640c0d035562155240c0c612039011070420000390f103140b032095004020701d15480b080700b50700e801c4002c0404000c0103005401c00205512000b81d5007070725081010904417000100000d0020106540000c0d00281400000500031601d51010700454240e00c4440e00503408010700311030030b4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 855474433 1250 855473183 855473191
    0x11070b030f160528090306020c010e010f02130608191103010305240c0c0313030809011211030c034b060a030f08120c0415020d0906080604020f0f070317 67
    0x9001007100302c4e503500c9002902c110303c048040c1030202c1065103d884001c1a0707032109240003c030740e460740310490301000300b403003800d00445518000710308142d5644219800d0403150301c500360803c1402c0c400701e2002c203208401c0c0070303415140301c8082007459050520b50000d80c02c24230054400e030140708040c903040303001040b440285004c48082c1055070780e1030081c05690b83c0c026078a01c16291209000701600f4801102404002d140103580d41c50301c0380c00c80000100707001c1c1440c0b043d12060742000f605c00b01c0b48a4140079640c0004443c169692a50780386c10890f03590103489400828030703c081a600078100042c12044961901c2103041c1400e40214182460000b6202a0744140e0040394040040001c00c80c4a5400480ca900c10a580c1e8607080401058143c2550300365100314030060300040030400c0c0341481d00590b01c62180c82c0007a000e02000e9400207040e511440c82a0024001c070100000c065580703030340c1100c2c030501071084e80c0b0740c858001101c4140903130040003040f001700fa00030f03400544402030b4000c060303c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 855475683 1250 855474433 855474457
    0xc131e0503060f01091a0415091b1202030406090605070f030c0f0c0f0201020109080a18050108040b0f040606050a0b0d060605040b04091a21060609061011070b030f1605 74
    0x52a440d28200c1d80c02013011b1508185a0a03600140c428180e80e24059010308900482c9060380550400034008111050580101e5151000d4080129503507009905410442c0c0600f01c0181c880d5500d04210014201c4d40700000c14091903c410089140d40040d29086a40300640e030030400b1140a200a88403c2500510322002c40e80e0000c41c0000502e800d2440d0448c0c0f88184000b00d101403a60fa91450190800100c2c0c20210b001711401103a203c80d40d8080078028a0240f03485060380c00e01d034490a80001015041c032100c140c080c030004003402083c2d00040000c103006049461455a40d0508451a400c0003000110392400c04400191aa01c903034141ca05460030100828a0107160107100c00040030711030701c08116511000c01d80c00a44e51000400c08460504d0301c9040b900c540b103070086070b080400c014202071144003170b041406082c5e1070f44400c5c1d003c0c07800325090820100007000303102c0b49050070a6007c2d0b4101080001080603101e1120100c5000c0c02c440381e0a54a078a00224040d00d0301c0c000c00200c03200b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 855476933 1250 855475683 855475711
    0x612060b0d1409210c0708010510060e030a0b0a09170f0d2a12150b09040e010c0e15090d0c0503150702030d24030501060609050a0b030703050c131e050306 68
    0x30304e41e0000b41c02041d04507810300031155041d035240c0300783c3d003522000c4801008511508504100e40c1b0341000c6401c0304841c00300d018258982143da581c1312031240c05066241d0701541d130040711040001c0c13490710840040307070004090f48034004401c00900b154001480400401d00300a501864403070074034409840c00c044100712582d1007901c8201103508001c0b6070780c0d01550507251129110a0780c074010515019020041d10503507221624414041524101d0040a100b03a151141c80b0440740c2d803140c18500c150340c0490300e00f801001c240c509000345000da88030b01c5503c0345c41c0e04071b030008006182051004599050f0b00380d6491030404151315104000403a500c00140c2c00820100d45420542c0d40040351462400c1c1c1900300050f141004c03900440280d4004803400e030742d24041401000d4200e800c180c010102200d10740944c0c0e081607a1030f082c0b800060f0416080c9611000400c011500d00340685000c4600e00d035484240d26511060001581e854451400e82c209040380041000c4c00d0104130a84501c00240381d2701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 855478183 1250 855476933 855476983
    0xf09060b031e06010c060603050606040c020d020d030b030a1505090601121119030816140304030215030606091207030c090209100c110a030501140a090b010612060b0d1409 75
    0x2010001406213040200540e244e00001e805807054a019500038002000389103810000e0204841800700840195480840c6001000e580003c106010040e03a140215120517070b00046881c180220000030070b803500c0000420701c152025803041c0c1c422004101102c10a03683c43d650381d0010b000d40e1001400c1c240c0390070a03001031410f0040056540b804a1541c244282e0f580b5100c16400780c100c6004a086003d1240401040c000540d000040b0514a0b10195240c1895540040c2c03800021034041500c800006c40011001d41e105415540000c1f005001d002d20041d6415086031245024041120341c0c80e550100410041031501c00d03203500c040c0142c843c000700080303100709903204902c0e52070031070b910740000c070f4030903016124088008003c510800000c03424480e01d46003283d120000400c04204140740529107000b1032910144a030446140c3d0a01c0d84064442e00000702c0542800e400c552100000020b070040300c00c02d10381c0301d44400075218040749441c0d1503002c2c52170f4803018401d0000544040c2e600e180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 855479433 1250 855478183 855478231
    0x1203090c0b09061201122d142127090604050405010902060f0406091202030303010b16080f0304020316050f1513030b0106090b03040c0603180605010f09060b03 70
    0x100005400102561300702484040c9801c0c1c02442604082101d0581000c1c03d02000701d00e50044110300e080c1c0c548804019204542c801c0d4118080f480034100c0010702e800e0018540b010310104202d0102180086481172030045413240c1944400176201c851441440041c215030540d5034207880768803006040c0c5000d80c5500301008060000038000b82e0f1155030b40c00d5040010303556040207041c01d19031140c4151300d5074504a400b074404034081e40140d0040c41701482070350060350084102da040d5680c40640c2525445a02148101c404c1c03c00783c02080b1800014035507901c03480c400c02031841644200e080301d01c0d070302110009403440483c2d40f141580186088452000a04d8219202c2c04001d2078404181e007413040d00796015000c441030f0350080c0e640c0b98405006104240c1d104100b04003400d10003560314550305050351948884080340c0300301810555a0540c0c003c00e13203118442940300300d401100c24080d558640404854813445c900c82d4480140c07420303d000a0072180c0c04166807242e51155000e4181d6042009a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 855480683 1250 855479433 855479437
    0xd09061d1302130e090709020711101421010b180609010c1b090b030d0509211e010b010f090b0906040806190c1b030e0a0b0a0203071203090c0b 63
    0xa001540900c8040c140b854801e40300e8000381201c0405140174145560721600781a01c5820040c0701e10300410041c404145000c8500c0e450100c00d60301410840b01d0008200c80500d40300e041b518000400185201c03148840b2446203011a6400721420803030390303031240000302d6445844c0c0341269400e011408110903181c09000382072044010705107050030000302d035210040c0407030000514040b2007407a4024403015011b48501e80c10500c0550050120400d21040505075005114525126050000401c00307180403002c410300d202a06c031411035444000d110402030a10400365581103040d8a0124051820341c42030114240b0100503444460a040c10844202002d0f807211003855009a0304200000d44107004010031071180c18505505507071a1180c0c1140d100340c41052511100304404106600708240780341c0144540280c0c5410500380c00c0c01031038041000c3c040d80e617001000061010075042030a54000c0010084103114180c40440c40a0602040d0100c40003680090001101071506000a85000d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 855481933 1250 855480683 855480709
    0x2030c01080c09030a08120105060306011d0301060e1608060a0f06030b03071a0c010b06130504090201140a03090317040c060804030207050a03350f160c06020d09061d 73
    0x940b940b030048540080b900c0d102c0c0c880003c8900307a1000405071400c4100b21103050241200312811491805c0000009220788007503040303030071000f4029000316615502544400c00400048000b070032145032901a0001380307504400c0c00c1000c1042d0100080307031861320100c0b11040c2d5805641e80301102c0c1c20500118000e08421529582510901c2c00c04100301d64491041c1480c1c0444030f25641c0e50300307006a200360a50f00074a0050340110700600a10150265000d03410041e40c0c000d44000880651a00040790314010402011204040c0011254010343d4180c0088078414007070340301c44141d161751000380f4920142c21a409440343c1002e0605110b03da1146c403a082c1c000c3c1c002e204540c00d0984400010b210a40c096008844149090400020494201c81c00c400d80b0b0074500d840d0b581055100060185602c13441d4007205100c400000c0c226010812001d8044000345c20084940f29140c8548019641e41829803510b408243d1884001a055228107501c0880c1d0080801c0140c05440101c28080110300e811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 855483183 1250 855481933 855481951
    0x1202070f080f0406020f2116060912200a0605061314061309050615120709050a050c03091f09050118120c0f1b08070308030709090902030c0108 63
    0x85400303008580c8020142100da91000000c540d541d02d0018060310380012400340c81c07500d030060b200900e10645030f6054803407044600001e503980d0b40d03401301c000a1b032500c8980c402810030b0300e002c1454040c000c0300100804144001d0311955880361000c58070040d410000031449600703500100300c40001410030382189400040280802890000c0868400181e0380c000f0030031502c21700103500b0018540340494220410500e652800c005450560b1a016207851000348100d48541c40418284050f03110301c2210310144407940240c400c4107484803400d001070201a2280355046040201103805840b40004030390080c1c3e110300050000780d00380003502083d440d46044e6403e02554400600002c00c40c28002d10b101d80692009620f6020418039084001c0b039140f410100811a04500748070001300713102074184400d034025041804900800e000300b11410302e550800c180a010b0200c0000800101d000510b020707035182e0711121400f40d02ca403461803c40d4201c4101940c10b40c400801401194003a0700f0f0941c02001078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 855484433 1250 855483183 855483203
    0x201080a021e0c03040803032a030c070b060f0d03030501030204110c03160312020307110d2c03030705010c020601230901060806040e1b03070b0307021213080105100806130201120207 80
    0x6e40009410340d00100ca000c0d4151101c0c0341c07100c18604440104e0003142c120451024214109442e90000354000c0312002404008001c000c208580c0e6030050301a04031000902c0a501c498280c43c00a001e82400c1c8012409a424540100458000b541c2a0b417070554040f0011410720319030740c40d4001014000c0900b0340c2800003802908043c2c0351140001c520a41e040d0300c800060070307201410301d0b20300003140e040c0b0010002c8200488010260341c10032411600c148101214020083e00006415841180d9004195620b44040d8424403500816814100c1c0c03180c0c005040754613940410800c0395020a4000c981c031003000d400500201e4003440b001500282c02400008440c4202203070989007012460790308001300503020384220189006c012203030280a290703d0141c103501b45000065940e070140d01c0f50080030080401c035109102e80d0740c0d001e4801410326500a00041c1411088003003101d0ae94081c4072414002d1000041010711020840b6402c1030707040c0d407a41404105000c042c002074002c0300048039101e0760 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 855485683 1250 855484433 855484439
    0x100e0a0c020c03060c091c0b010f0302010e0f010806040908040510090501080a0e0303060d15060b09040b240708070c180b03011a01110703150c02010501060219030c0303270201080a021e0c0304 84
    0x10188c5010b40b0519807500700310781c214000945854292030b90184074002c404513240030f50342e04c5000c103a040b840954000c2140c10319883e1001060145402064001180c0d2444280d00e950000b08541191002c3e20340000b15265186000e0680700c00c01458074640d4400c20100e01542070414203441101d009041080216070309441041c04d40d0150b0f40954a044000310718000d851600340306030071000c842242c52510b0030f660540c0d2000010026440354200c441d0201303d110600c034800d011110802c0d4410707101030034243c4400d00b48a005840f44900d0960619117000d000003410f05104800c1e107481c01d45622041521600c004560040d01002c029a0a001d80c076400030005070491803400c0c01d00c4c0c0c140da01199152440030001d007101c2050f40007904640c0955950b240e100c58002c6203920058051400960104450030190044e01b4101d20150b0000e0418a014000c00d0b92202c0c00e039540e81c401d0780c2c0c070a03180e01c4090001c400e83c000c501810b1051003140e82c41d9246020f050004180a2821030281c0e0b0030541d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 855486933 1250 855485683 855485693
    0xf0504120b06030d0302090d300201140109020705100f061211090a050c07030e0105040509010b03060a0609081f1518050a0614010503100e0a0c020c03060c091c 70
    0x1025002110315034507460a019541c40c0034054804008254030f0118180050240006c0ca584d2490308080c00c440c0c1c45c0c80840310540340c05000a160305105268007424102c0f444e000038000c00008040c0709042440c100040ba0000c85030003101c51f100e8011000300b8103000c800d00414000d298074141c0100c01076588800182d00e201e070b1f40044440700d0042d1007034019028620301f403100c0400e005004071412031504080003841412081030301d140c3c0d0780514140d001d078100381c0e0050361144129001150710043c05800003d03100360000086100c0c074015184044c2d641c0ea0703070320144c413068007601071045c0c1500135500903005000920380b161890345806070082180c2002d02141703444c00aea50b401064007001640d5000c1c9540c0c042d07015141c0c010022540403c01546800842c00c2005041720002e4108078001003c14821032401030b10310b000c2d007840140300c209420040f11a600901800c407a50015001e080000b810a2a000c00c41911411426403d145008042020003800b201c410390003402c02013016600201040f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 855488183 1250 855486933 855486959
    0x302040506011e0f110102093613061a0a1a07060212011509140609130c020f0706110c0402031e0717090303100312020a080f031f0f03030f0504 63
    0x255664640518140704c0080040c44003c80c0c03035006250345c2c01008183e00d2622132001841c40170581c0310302000029020700c0c000c030300800b20b001042c45000d514418410200f0a0b5102c890780e00b0320130345041001c01e0304418560010110642c541d42d00c26411242040404449400043d1121140403000e203414040e43e0b81c2c10890b00183d04c07580700741e991080144145000340d000710f11920b1083c10803040760743c640544001d04070010742c561801a0300102c1e50041c6070319035141680c40c40c00c900b40e09000d002815040203545a03280c1c2c0c14000d03035110316007000501500601000d82c1c135014101c00340c00480b0303c2406120180d400034080d10400042050b5240d101d03c01591071038002c0b101c90f651180b13801004110358056800180122003107400801c18071030b00c4681a8004400c8907401152800103240310343d401e0f42040684240035085440003d50100c0c004000c1000358400c244010602e03044840b0304030041c0503008103006000d00001c1008081c4042800381140d04031070407003480d11914054440c08500c1d240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 855489433 1250 855488183 855488237
    0xe0606060d2c0c03030403080405101b03180506090603010b1602030a0b04061d03031305030c01142a0d0f15080102070501110c0c0126190c0216030204050601 69
    0x34254800e42c0b0441140510583d94901d404500a42c1010f04517100c01c031043c8a1071207104c0c8120391005030058113500640301e4100c80982d40c1c54460b12050582005080c00b13900b41c114a0019002c048003180601e018415103c4016000d045a41142c1c00c2400d02144e42d40b05071740f00348070380700301e0007490006942c104500c0d1f05451051030640b14900740b600e0032000b6120f100c10402c4006a03400660000d842c0004142c950200c0420841429001241007507402d51182d00240741c095400e25405011050030301422500541480e15219420006501264000c0c800c00309011481d80c0d04000c92800744126070803921040003a9040001c50342035a01907555690200e80c03000425075004a403c4050060a00c5200c004072603000501d881c042c85213160740e8a0700901b0340043d0603c400d0310500c20070030880b41c400410f440559013003c0a0350a103030002280c001c41c050355400099081a0040c10681d1003c00c0030808102c00b414240021030655081101074200104118104503030380d03100c002d400c0b14602c485194 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 855490683 1250 855489433 855489491
    0x10090c020a1a040b0c13090c02010603031101020a0e01140405100f080a0b0f041d060103080423010801090c0e03060f060f010e3003040b03060a06030e0606060d 70
    0x2181e203245010103465100081e1154540c038030104000108120a201d20350080280d81442d85d0b402e0f0b03094100b4513000301034000c40c031100c2c079040d200004903805503c041c050324000e45036404031030303000380c0180d0a07403003800600b03400035080500031031555008210140d120b0012607081e600f4242c440000c41c61001040310b00c40002810070300405400d90300720882035041000010240710641121010a0840d17940319880c90040d91380b4905030030340d920200080060000c0280c161816565a030070320703a00c180c00901503000501c0c101100c05c100c1c200d03a14a0b6003038044040c0c460b0144c0303a1820385440000c0c4907401d400402e00c00100f4056806550031b1186a114944c90282c009880c1420014045001d11441d0301c141031200c0c101e442070103990b4214015074600986a100a01000c2c82854800c4001a10004000764400070a000c07d22000c5000590b100d11019100c0350742555031440118246d6203d0000001980c100300c0100c1c200c0d00b0701000404600428007008104c80002c2d00c1105c03d40b6403a8421070301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 855491933 1250 855490683 855490693
    0x10e010914060907031203020d0504050a14150703180b0708010e0601030c0c060e01060b04030807060b040b1c0503130306020c060601050a09061d06180a0801061a0310090c02 76
    0x30410808500402003202100a15052400c44420f03070f0744e02c01ca40400f42040e40b03a00c0c07030800d229100f6011144020500c603014001c5003010b182c802c0d41d9014051048508044002c0e428086240000300c10074181007049800140d0740f10b950054005100da50014140882c801c020240821901140240200210b656070b22031356260510700c0321583c0001d0441e6040606200c000441c3c00c1d40124603100454200d4000940e90488070750321b9006114035485482044408280041803103031980107445464001e042c2031000056030f10070013080f1842c0c3c68105501c004d04e1040880604903206001a2141c8200110791600d9582030303100607031024940c011140700740c00241142d0400c01c10710165401c4103003801c180d42801d2080c00050280318640c00341008000c44a14070040800c00000d21008079400605102e40d40d10000d52103074588601a0502400707403134603040024010034144034040490300200c0310144216100e54408000381c1c03000d002407660162003200411500301600c03480e0481441c03600144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 855493183 1250 855491933 855491951
    0x1318030e0d0818210304030212070503120c0609150c0d0f05010b18030d080612010b0603190510080d050a020307021e13060302030c1003020706290303180d14010e01 72
    0x20713402080740403840003200b00f0040e60003072240c00420b03030303090302d0f4100c1701095016a0030307950b02d00d4a880c50780425814480c3c84041d200c2001c8c0c800080c010301c1240001e542069460f4140c8075030b40d850000c0c030444400b20780000514000c0d6600040c00c05010804008103004541c903004005651080c0c00c0704003908800242e40007040d01c0e09241386484079042d8060303e0a000c286401803d500340080c1070354007509405201d014621340a500141605400814aa44a0a1510254005628007200190400e00d0702001c5580b4811059490f81116092070062505070000c00040316a41c00030102d041c1507110520070000107996942446d078501c549015844041c0180d4410095001503e60401c00d003d0301e060000d00c05610041505240e41d0070a072021010a002008210003c2c4035420010300407614122007890b11170740c00c0c002990441204615004081c0c2510200764891050907411100000c0c900321405041c1041c46086070001d00440003445281c0c001441c40b400e441c0c00205c10a035a0755116034070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 855494433 1250 855493183 855493189
    0x31d03090a0e0609010b071509061e090512180904050a110a061710050d0501050601021b061b12030a020319090b04030c0606150309021318030e0d0818 66
    0x501d00401c0695a050224286403012510185044c069028903042c001030310414410000703043d034aa801c03010010000600a03041440090000049400b1078038843e00907418481c48a0040c0102d02d0b40241c050a14032050000403940d42d0b00c4040415140540c0c0c2e04550340d05d6031780c1c9a50520030b5020358082c104003141868441c0000c080301c4080713031103010f500d0014049243d0040b00e8841d602c2005e401c440386078450140c40f1611030155480f01da0310806c08160541006810b401050045100b80c0858101007003407020300f500201945415604501d00348440c41041c59410140d00d080040c0b80155950000311124a08940d80100e41d40d0070b00c282c00105014424070110540022040c0c40720040259100582d00d60044000c0900040d0800c05210070f04800e104007644040018101804c1c0c1001c04c55004201034040d0007070f000e0582c170540c2c282011080b94a60390282061740701c0343c4001c56800c1e5085940c07e50b050303848403c096810482c180035030070000b80d0356402080b040c130440040d9041203200d1010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 855495683 1250 855494433 855494449
    0x10e100c0f020304150e130213050f1c06112817011403010b21070b121914071706010918020c10020409060303081005010816031d0309 59
    0x3001c00c1110581c0c606035640c007005a5054408101200040c902500c000b1a201241c40560302c6d480941a0b11088401040e60300a00602503501c1401c0c107115036650800020303109200003d9041010320301035000101c403008511040600c1800002001c1c0440320303d900291b0080010080c02070050303090511010b985d071500c42000b103a6450324106590314038a82064592040c8500f9400f0145009a8601030f5402c0d00602c0a5450150003a4035426a1281c00902c01d80d00b0101a00c1d00d00829001140301c010f00c03412070316501004490380c1d50b1621080005401e07866030035000b0484a607a064003042101002c802d6601034519a5500ca00500056130f0320b10441501408090601804840400007016074032601c441081002c1d00060716071501103981420520b82c0101c1c5201c0902c0002c0110300000141c4c00403080e40d02036902c5004542c3d41c1403560b1141081401610302140340d200008890007502421130030100c9991030003080b103031000317500c94860303a49450000c0c071242c001156894881c144511 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 855496933 1250 855495683 855495701
    0x10902041203030b0102010902030f060109360203160306051605030403021513021519110c0613030b0403020609010c020c0d020d170f18060702060d1a03010e10 70
    0x42180390518100100301c00308841a001000c0c580c4490604100c4c2c2e0003948100c0e00b09802a0584503003411400b03c1076101c080034011680c80c903142c4540d6414402d000c44030040c00d103001c0c9060250000d03000b03451030027848810108030707414071400d10101032207040819401c0065101c0c000100d05828401d060000c07108290000d9810400240100720203e075000506e030036000501d041c2030b2050380728040c5000002034000c0d8040e401a034101165100c08640c5801042c100d6400450183c1002240208032a4140f446444400c03039440500c8170701c218a0000003c000d107002d0056804e084c01d1b501c0d500c801c00c1c2a4125820b03405a0032001c01c002c905002030041502d03040c121310140c10050a24000642055007401001e0f0007030b0741c1c99198404001000720307034a220035500005a604c0c2c0c000390602000b19403104071120002000d11140c0c0c880e0b828034105551a560707004144074140300903052600010800c4140c2500000d0040000617500d440c00c0c0b060980e160600406000d10214820035282a200454 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 855498183 1250 855496933 855496949
    0xa03050403051c0e0d03050c0f1e070b04090c030209040e03070209062205180604051e07030314160606092007020603391c0b0a060f09030f1a01 63
    0x604030055690b8400312205444900302c2d100780481545d41001c84680c0100d02c2c10079000d11802e800c03614034074000100f400d0184800c4504528440448410580390300e003520580407140c1051005001d00740d9280c020741800d41c8513203001070818008100060a503101c070610026107030800184402541000582264031030402d8681c1008030500c041d0b0301d03052141c210307441640107a564001c11080100405515004050703001243c2107810103040c4a41c5840130121030326404032012001e075a00348030108000e0100c1e034050301c0341001c4056080640c10a684808802c1e02040300c1d02061000082c0320b845840003504d103040d000103113040e00c030407070b031000900f01207031081890780a001100050751884201c80d84501c0002c4050304044049401c80d000000054200d1519068031030290030413414600504101003110b400c2402c51a8440c1d9a4030460b4069410f480e00060000f400344401070040d01034201071441864008041c0e5580d403075985013203511140413038410102d00c03941d6500c0302461410f2030242080c0c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 855499433 1250 855498183 855498223
    0xe060a0504120c05190501140c0a020609060c030a2a050405010905060910050f040801050a0f24060f02030c070801060501092106110f070f020901090b060d09140a0305040305 76
    0x5525030725aa0179000000802d00c95800703050104102c42074200103007102c159900400310b420403007051461500f000c0c40d000c0052168500007400600d0005000b8019402daa00241c03541d02c0c1c11001502400c4401d840c0001c070350041007014a2110502d50507089420300d0f0742ea40761280d01b45000182011144d0740924410b0006110207045070b0350780c680084400080342012603690003806403420081c0121303480510b0a529000c1005481ca00541004422000c203100c1008400e101d401c0320101c405400707000d245d0192080005010b2980240300c0300e40869001d004076410407003101d104900e800056006124aa5105d04003009075513006011300c3d0184c41c820380341d2000b5460843c0034a803c29800d40026103040c0d2a8424401841c80c8801200c2e14042000c013000e681d1601c500300480001c0d14454124003801d0103d00000ba60101c61207942d882c40c0700104030070710f40811160200041c180038035040c4c40084d03500c1e4441009150070400c00c54102e21a4550545881c42c41c00c040303003042c0c41c56032204042196 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 855500683 1250 855499433 855499457
    0x1d01051f0215090c060403030203041404060b161b06020f07090c0f080618010603050402150c030706020304020402130303090f06020309010503070c030c0813030c0506090607080c010e060a050412 85
    0x400c8001054119542c03030200ca65486207003601c0c2c062030f100d156820581c001004000e0550100040c0b007030300c503280c2d6840072050441e01800101c030254840c07620503000a014aa885d42210002c0d00c20380d80c0114982c08001247d00d91101d40c81140d9801400542d000700b40389240290107001100042000c07406c200488880ca50015080c00c0001c018482000900c40000740c45030b0751a0050281e030000d00f92182061344c2c444130040c0062605582c10380c0b082d844c40e110a008080d890044900307402e00600911b062a685940f050048e40010b08100c2e03005809000c00c10b18600b100c4107180c010f50080da5041d22080c9400b03400d8a08041c40e0300a0350464204004d034809a903080780c11079810812a2402d08001c4105050880300f842c1c940000505a100c0043c41600303d00e5030780d5191040d41e004a1b1000b02e241c1d6100d003001287d1242c0b0f01c0c2150400024022403000c1003d20000d01200018400003240700010f01e048507040404c2121160221031365a0b00344018804003243c000144c113000d042550b00004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 855501933 1250 855500683 855500687
    0x16061e02070309052b081e0c0f0c0109050d06140f0717161b0c0603020a032901030b031e0312070c1703090115031a0615090603101d01051f 61
    0x81400c540d4804100e1760440c000412501c8030840d501e000340030b0710400340c0c0c900702c0ca00d41840381d00c448086003251003206034071041100e0110b000040000142c5860306050b2816060214803100e0000c1561020380d21400580c00d1081491560303c01e1060103030f074000518200398003500e005c0c005004141c02d130012604000c801032204514060003c00ea0500048690803918458030914101000520b04100e4205c00600c1d103030180c01402078050703582c030f051110010301408440748104d130003d800b00d902094180200c083d4020b500041500b10f0280030f403042d036486104098003000c071000528295500009800f200d41001c41c05c0ba035042140c600d40703100c3d00d0010b030f11621140c1c0750420404d90484000000304090010941c00300c0801c0d0444204d440885946c1d04106035401c1070f600c0c0a19117001040300085061508403c2c2c00c00c29802410020309144800d814003010f500000e08142a04184c0003002c15a52455214681c8602c20503501080940c1850706100004080f540041c10044094050385407080d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 855503183 1250 855501933 855501979
    0x6030503030402090c0309060c09150705010b09061002060a020c280312020703020307060c021c09080114090a060b01030605060d1a060a05160c0e10030512090616061e0207030905 78
    0x80c00882e813516800102c0000d00bc100d48095000c800360300005008040100640102c1e0304031030100c1d070000f000e50701e13101880141c140488020b8016000000080d1140d806640a44a005807481c100c80e000030450350322080000c0d0107209546110201011242090b900c44109080103542450640c00c10030396540203981d900804100504203900c0d00b0403009914070822414042c424509040204100c00c5400603000e5800ca0250301a654204446030340341d0012203114600a81e241700040c00a20f400e612200300500b00c0c00c48841c10162107460010742d90390780034042c0c411813080704800518001c000c902e88103e41c3d00f401150307000306000e001e9814501d401c4030540d1b07103903101051048040304e100e20f008c211440303413600089040400e070010721a14078000c54014003501e03c21400c8500714402544080094010b07410a1503008101300030754000c0d404140400780b40103200e801d01207038580307a6400c1e282c00b00e02c11442c0001003560102c2c00700107140c1d200f0180d600030f01040d2000c1c0241c032000a00102d9003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 855504433 1250 855503183 855503191
    0x1905060318010c0c0c0e07110102030a0218040507020a150e1e190c05060903010f0203090f060f060d02060a02152e05090a0b130203070903020a141f0504080106030503030402090c030906 81
    0x211b1200000030000c80c003840030345045418010085540c0d1900d0b00b07000b070003500403c4005041000108071443d185c101442084e000e0780300c0b90002d02c00107c05680d03003015840351142001c24076444d100016444002006600d5512810408048548040078a5a85880910782006646941ea590207401003405c007021042030365010b5480c203039188441c1c404640505410a00c030780070b2910000030011035220100b000b401d02d040e07410640345a03440d0005c00396000b95060f00e420703501c0407914107000014604000104016a101c0c0180ca2112131048540103400208a0783e844418000e001a4080c3e119078043c000d1917190450b42d038120341400d02020074162100248205e00c86503460740f083c443c84d41d446558040c0448080815507807490b111030300404210851200324001d1906c2035010a0411400b8071440110070301a204842a044900c04001c500c00d03002c01c038034103001c03040001141b1000207020381c801071400741d001503940e81450310511403850801040555144018002e0088201c40440d280d504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 855505683 1250 855504433 855504449
    0x1407030f0302030a06030812040b010f0605040b03040218070c03020106081603060e0307050d09031e020105160c08030c011508030c0a12050d14040b070f0e1905060318010c0c0c 77
    0x1c0b03540b0139801307034010009600050728174600410031250b0021140c031003a100320710410030400d840c5da0784d2a0144c032404160048201040007440f050042808800c09150302c80e000400c803440800b07124050864551082e9120700c00540303000b00141c01d151b024001c50009210100003031440701e02180380c1c1c40e40a40d843c04014100d03034443c807050800b0001082916400c540010079242c0320000d801d00600800d520344007c58030a4000b407000302d20000341211804100e901030719264030b4441e025050620704001c0501c03c4584200001d00403898900800c040d00c215800300b000000d44200d4900002407030b040d15440588142d2041001450141011400a0084d07030300003529080104441702c265041d01490180703a109910f05502c080070344144202d0240146c2c02004540c01581326034000f194540300d001000000f080401c0074840a608080c5414111240000c001c40740c80364513000003d0341c0b540203a0b44e400641e1031040780d40c0101b807030030300c9008001200343c189045140320303660300d50f44031517071510030208 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 855506933 1250 855505683 855505687
    0x10c0221030a02120c03040c0506040b07030804050f0102190905152704110403120c030e1e030102030405160e040c0605161502040f0b090a090b031e0606011407030f0302 74
    0x7680c2d40240c041d11041c080329110403804c2c0c030309100304c0b030210b8108035405e592030020460300180504041c4212002e40e00c1500b8500d203040d003540c8080e56040700290040b5000e204090000103034038001c0c4003510103040500044880c0c0d0150b10002880d665450704001c0c411304c0c80d0382034a03c0c1040c4010803100941a044054082d0140c00c07071014540350303c1c840d02a600942000f1500001080e20002030060328071840062080d20540d0004507003e2480d140014045421905010707094501044c036000300044800100c00512010030109081e40c0081e20100e480c0d600510440c3c01c1c040500c10940080c1c0001c2081c40264030380b0b61507500045810740718150500078000340c002d5a04080542c034030440340e00900c1c15400d0021403c4a074009511078402c3c440e004c03080110100701100f180080b0b0300e071404018030400d510360410380554003e00f008180c15500d0b205040050303500b503e003880c20040d80c440500250080380341c074000140ca405241000348262000c04c200c520000398000c3c092860030180c91030b0060b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 855508183 1250 855506933 855506941
    0x2040f1d0304141207150e0909150103110d050304030605090d08090606010c1403030f01090b040c0c0b0703200901020d0f2f070b0c010c11060406020304030e060c0f010c022103 77
    0x581030000c1c9070066140c66511406c1000180d030408410481428160b801075125030320f4045040d21004015155041d01c01d0403401000801c0a002c54088200001440c130171030301d1040c0e56294a143c3c0583d04c2103440c00d403194200403810800f8444100c840d01c103030030302414074901007000c1074a038030000340304d54180b00b003100289041c0110503004e501e954001d841240c0d41c03404c00180c0340c690b5050901c500c071441400c003005403800c0d00705401110b40021441c0c03214030035082d442d907800d405085c000784800101a039940181420540d0360501e8440e000291107003c0c0c2d11090800024145582c1e002e42d0380620200001e00134015900c01c0c4c070010840c15044004810b05600101e0b50000038412454003541d105025000c20a03a01c0e6800600c403070320700d40d0020030501500b40d00a46080011264001b030540000d40010007155494009561040c800d1404902c80d180900000320103402241c0021085d9000809070000031509100e0900d4840140c00100031030103002e80d25842c2c1928011030101c503250040042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 855509433 1250 855508183 855508219
    0x3010602030d180221061501020c120115060f0f020c0f041524080112050703080a02030706020a09030510060b0a030b030c0a030605091203160e010c02040f1d030414 72
    0x1583e1400d40c01800303940900c451142c40e440301c0c0c0080244001034000c900100c0c203808201d1491041c65030041e0040c1864240010030444046280d400300200d95480f80034800c400030000e9042c201800b60754580c10006581c5080083c421020b101403502550b2000c882c4101981d5010a1a10301c55000c95000c5000041042c0c040343c08ac660380d00250b041865002601041103ca17000d88180c81c1c0141e40d81a52030307a032092816080301f00840f024080350000340091000c100c100008004050b15401204e0ae0712006540d0a401c81c1c0c061030f0303804006121031509004001d400c1c01208030460010034240401d03810200801211300c101d10609060594510a50701503131018000c00190392001440c17100c1050750390401201410040f50070400318080d10305201d6100440100f81e0f40540080c080068400c0c19121f0141e6100d01d691041c2c2d03040c401c2c2e580d224001a03883c1d0041442142541d100032030443c102020268861141c000c401290360420300041c400d9504158554500441c12101525124150454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 855510683 1250 855509433 855509471
    0x807081207030605131a12070f0f0e0702030901021b0a0b04030804050405130c06030c140c0d030b0103060602100b0103020717190512070e031e0c100503010602030d 72
    0x411400108003000c000c0c481d41c141d80444202c440a4070380c50950018810641d0441c0c0001c0c0701e8585841882130040c10300c2c02c1040c018100d000d100b03821294642e40300ca41d81c07008124950b200c0032000d80e00510038003c80310100d070350b9034001c9040d000950401c1c51500000c4e48411101110002d002085d485914442d80c4180c0c01400520b44140d071142e4540e1242001816070b80306020341d50049043c00c02141f40700141c00420605c003030304130801c000b0450425038114050700205810380100040c4d0207007040282481c600400d155100d6400805004c0300543c0080c06480083c0120303030605207402020460381c0c0d0045205003007904d010100160a103455070044e0028016224007410100c01542c1c0d074801c0c81c2c501c000800c890700303130a001070100f204000c000b11283e109445c010459007103024081703a9440d008403040707012110000c8c01c0d0741c4101001c100d00651005080402107880c0c0c0070220a000d030b07082540c1c0307101b800c21003440e21314950344c141403000e0b550740b141c0006102c44d1a5076000d40c071003c65001d98 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 855511933 1250 855510683 855510697
    0x4092310090c1706060a170721030e0f01051c1d03180d020a06050a14130e0f0405070b07030309050a08361002010e0118150e0a080708 59
    0x31080215207002e08100e00401c85901403004980e00d50510f8000090700003c0d000e10a083c02418008420300b0001822040c0b240400a04020701c00d20f038001c00e0038010100d50b40414170842084040520781414020040160340d40c00502800e041d80100c04566804012107109004010b0040024207441c05040020080c061203450b00361032a1819410554000c00103210505a40c5c5890a980036541c081117161001003000a43c40b00b007400d020886240100040d1800c40140e0a0601c0f00d4410210300d0304459100448407104083d107000180001907503007400580000c00c03100b52510610b029602e06541d4146030243c0c40002da408140c40b001c1520a07003042e44606d502c101600c042101c0c502d0101e0b06900402d03a4041d10110348540300300d0030501c1c03280c04060700b401084840302d03030100401802025042007d001d001c65490312410a5908024095075084846403400d40300301c001d00e8141240700958080e58150881e040407a607220701c0900003070080c44c80d60003565090342d030fa1003032902e201c140c45910 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 855513183 1250 855511933 855511963
    0x121b03061c0c080a0c09060b041703090a091b020c03060a090f0c0f050901060c050c040c0917030d1113030809040e0d0309050705220b0d020d110f040923 67
    0x2001040110010034520b544c0b80c0302d00541c000030340c0c43d0440c490a5400c2802118143c54042c0400c0141d4011000c40c202c190149130709880ca8210041c0c081303207a141d181e030000d8042548a103030140d40c0b0b40050341d041600412920250403210024000642c0302c480150101c41e42d541c0354950b020a10013510b041500442d0304c01d215520090780c4460103102401c45200781c0c0e21a45190340000f41141c000d80701010400c1e448006010801c05000810000380641c120352400c1085020020841e0740506841c0c0850301e01d86801191588168000c0c80180c8004030915010f10742c3c180402d80d03440c7c2400060000b0749030f008001c0c54a403007111300410300420225441d42203910880e101d64120542651080003018003844c20703695619100d9090010031030008080440740c0500384180b9449049030b500180341000018010a98802c1a4002036440707041600d09403880c9460403d1075616103440c805456400e1805d031020301601201e42c80e01c118400e1041001211003401c1c202d00c1050750414010031403c1c070341c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 855514433 1250 855513183 855513203
    0xc141e070507170c040c300e0f06010f1e0b0c010f021206010809012013050d0510050a050c0403030e030a140a0309090e060402010c060e01020f121b03061c 68
    0x1145956501c07000341041d009920704038415003a140304101001036079074081035422a4000000b034004284447c003002c95915a610004801d40d900240071104800c441c00009040950600c1c40e000000d000395440a500024542d000e00720720b042c08040c481c100e0780c00504807904c0e2410240d405014050818061503c0c520024405c414512000b00031400340ca8281d072000f00300e83c2c9400c0300a0072200300714452801da40c45806c2c07034820140040024045c03071004460b01c500700b0780d441d00850001640034070226159040700307a5800701d0701c059100c0d00c0e610001c030b0002803060b4100103c074080030748074a002c040d04101c4014050086900c0402c2180450b80d80002401c032414580012070b51a40c280318012000101c60341c0b0700090700d1246010703d1121400e000c01800c00c5842d55401521404120a41120034a0f00c40c50107603203425080c0301512041500824207a656060004224000f4800602d400d2404882603105001401c5220a580e4047c806403030f425090146136002e40400a60441c0040012601d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 855515683 1250 855514433 855514469
    0x18120a0c03080a030b0118171c0206070f0f050306010c0204020717090f01091d1b0f04180504150506040603020303030a1b170c0f040503100c141e070507 67
    0x1000400c51103903250b40802c00c801c2800011902040c80a1f462241e13030000304000d210700081003160343c00c800c00c0d40707080702c4005c00410f8559179102080050240036030881010000a0741c0c002044507030101640c902440f554041000241c06404080c06260400c182c080e2101c4c00c5448a90440b89100c0c1c2003c0c00a41810380e8036030010059108030700e010300403a515015841c0c694010020282600c2070250703d0220704420b0100d101c604600100050b11083c0009407100002201c10002c2c1a071101c40ac000035512800c120060041400054040b48040e241208010104070703200705880c050100001c02040c5500d41d000010050446030700040d43c14000002807002c440d015901c07410921a100040d09090958080d0a031404192803403048070340b60054000030040b80043e0018008030300b003030070b071300341000d4a07030700803900d40300b200620071800b9582c0d13484c42d0603007a421249807c0702d0801d0a246500e002c6203080c440c0f80180360401500543e0901082c4070013004014000c14019020a03880c00403070f80c0d5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 855516933 1250 855515683 855515693
    0x322080f06071202090a14030312150a05100815151602150a050f03060409121722081827060a12030f0c021215060618120a0c03 56
    0xc1c1a140781c00440c064020320360544819001740e450f419401843c454100789001d070005400582003c000760300d80020450b804000200e402c0d0540940680e00141d035640c0c0000303050240344092900040d100383c000b0480d14003100e134400c08485d0b1200e000c00c000d131118041100441c4c2c8030302180406d020410302c0410b1003003504101c0394081150034000c40e81e840700c080303a0172036280092084030400400a03404015801c11211031000464000902610000300340325181c642150501c45a01d20200003407104802203100c0d002c0410a9401c02c2c00c0030301804501e134118000d8074245032f2010006000d0103000c00c50404440500d41e40f588610006449009091000880c0c140034480300c4050346110001c08000c940d8a0400c2610700c0161111002e030207007211060388090310100e000507448010815003510368030050300e80300f03410011450460001d240300c07420082d01421412000b0240d6000300300a100310001c1c0814040c0024034158190703902b0013190002380c03255091240c2000d000e0b00f003000c1f0b441c0000c04c1007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 855518183 1250 855516933 855516943
    0x703150e090102120c18010c03210b010f0f02190f0b131514060105030a180305090f03010509030d15170703030306090203191a031002031b0a020322080f 67
    0x9840c1e01c2d03282640c0c1703000450110b4000c201d1010403115400d40300c9417040d40221f0125022500905140010b210302a031950342000c0840721000000b40c07506c1c041407080d600420b200c040c0200303e0034440c06860a20900940d10b012444071100c1850070b40204030280180c03040c00002040d00440c4170091850030403054140100e9480c0103d41e07068031840380c0401d00c44240b00e0b03940707903144240290342652903620045840740c00c06031062aa40b6502c6032104100e0703040780600c82885120f40c503102c1d201c2400c2c0c0b04202080c02c442c2521802a414101040004800031003180d0038030201010010344868403290928000589803c0048034150300c040c81b440c040000211042140d1095034144a85130700c40919505a0000743c94001c25034160019a140450507500100100b0f008014010008400180024541400104030b0800558004180011000030ba01030316005809514640e20702030003410025a00e103e4080c8000c00c12500c0d0300140b1040040d0412138004200d12403c0718049600c1089164a030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 855519433 1250 855518183 855518197
    0x40929043207090e070e01050706061d06040f090314070507170606040f02090306040222060b120c0406021e1608010213050f0f0f240c0c06120703150e090102 69
    0x403d44821000582c8800d035210b00d840b50302142e98660510a02d200191242c2d0009101114269111100840e010300708240358a6100900300011009007403c105000031240d040c4400b8441d1410031040b100400c1e00f03c42c031010020326403a0f0170350741c41909041c010b0a00c40141c002846841c00c03030125804040c00012018003403003040f281000182e080000520483c8180510241c164101070001005854034510344043d901814141503c100e5111004a085504903040f0814207100451814030240034106001c4d0b008501c2e40065191604002002c0c5d40d0f1801c91960210981041c4801e40140c0b00a000458214201e0004010882d482c0e500c018040c2d040341c03402c0044040807400000e030340c0c50480c0303003490b18500140c40955110310800900c2400c0d83e683c100c86405c00542d00305040e080070094103c08000b0340c07101d201a2282d494200700c07805d04d5150902148108420311001c0407a480c85042c0340e800400300d0900013449010208891005034082d0301c4400c40c01140010480495410b40080c500 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 855520683 1250 855519433 855519437
    0x70503040501180f151409070303020111041d100302040c0c0209060901050a170705031c140304020f041a03060a05010f050108160f2003040929043207 66
    0x80403e03031021116500820040c2c6401400c20740040400c90a46400c5840d120300c4001103a03081619100c14075480003030303d01c00000d500c90002001495420f10480c00a100414840b524044c545174202c54542c03240c0e541d086803171000001244018240c0c41034400250390282007030181d0a0b00070000b9000342c0800d0001c0e4041e400074000113007549402c9640c0da0607a5001801d00d8111b5081110380284c1036003400703240826105034040403c055a08000150010842d0303124902403c141d520f00800c440340c1e0100d1940245000e0090000603034580d0300105101d075068600081c00000383c4e201582e09040c1c8100b15400d80110340c00d0010b501d006800440c140c51500a14403080d9a89000445800e0022221801c078903846039000340306148500302e003050700350162802c40050041a454070021000c0d0aa072150590b03c0003404005080e50380c0103e0680001d00007161001c0b0409007800b00c1526070400c02c0c5840f8503901c04204c544442c81e203005101240c0c901d842e45941003020200c149010000b07403081c40c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 855521933 1250 855520683 855520691
    0x10090209180103060515040c0207140f090411010f0207061407020a05040f05090712020f24040902070c0e0403020c121e03070b150d0f030e1206070e0105090a030813030b070503040501 80
    0x706c1c9003414000d00358080b20950051481a29100d0486041140b6501c500d920100340c41c1c5608499448260f098080e0b80200c030600c64044c500c10001d0203449c15000d101d419034000c010308200e142d800c0302c0f0781403c400e12079020700d9503002c261000035070495064000d10750042c50684000310071200c580c00300b03114011038404c07550020f40301e40e075108500340102e400075072143c43d11092074440c3c00c2c81b201715001800c525991401d11074005404d000d0581090304a88041d50380802d42100340040b1146030b030018440040028038505107614001d440310001103606000c0c1240d40080d42624104005100f04a4450b000030703541004401c1e171280d103d03408200142d9030320750b0142c01320360303004101d11401090700401801d400481010769112820f4401c8000d058052105990502006032030794060b07030704580130000c050b11040c42c0081016102418115507181007010502040c040c82c2c56403440c0c0d1054a801828040d2128038a1144048140c001e0300010004e0350300c2e0090044a5401601840c01148682c1c001c0c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 855523183 1250 855521933 855521971
    0x120e0a031119060207020d050a030206070210061202060714030406170903340b0a0204051212041a2a1207050715170f010501020d08100902091801030605 67
    0x19960b07001d108004441500b059400d00c0000e800c0354010a100ca102816686000030f580c1c40b4242411556201036015030000c1041000c1583d0500c56542150300110082103100d0501c1568140081413800090044500290340b100384541c088509c0000d134660002c80e03594035140d0714010021903003240d080042006c944045101d820b400700c16070f0140b8a45854500100c41381d424070201d104c042c9900c441c8900a03412100c00407031b5001090038881c0d69484d0300036940e07900d06030074000c1c0130468000f20005600314a0001e00e9280c8590304540c00c503091204910a000c8203a08800300341d10581020349001300b40c49020100745403514420040420300728060302c01040c410705036a6100d01c80d1a8004050b80c020b00e00900c0038207460081e25854440c0c0e4070f80f107603845401034405522030205071500700301e480040c00108155a41044034072090b902d00c0c40d240d00c1d54148031031000703d1054240034003081c0c19008604000644c0f0b4950340d04124420288000e8160350750b0f030074100001e00b400d039140402c08680e07034210 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 855524433 1250 855523183 855523217
    0xf190603121808060c090d06110414040e1c0306051c050118050705090703110c0703050c01020c1807171018110304020919020a08011503050403170601120e0a03 70
    0x1941225400f40180c5400d80c5ea040d0604a01d9101c2c00d401c6611850281c02400400e02c0d510800398408142d0504540e5035050200d5001c0036030841000c140300d9800e00407002040d0300042045150407503980e521070f05110100e00158042c00c031540180340c10540484031045c48d040710046160049010300020001551404c1c11940c01c200e0600025001e80c0c0500300400060901001090740700242e0711b00000c0e88404030f007030074255900140322180d190b0304c036090900c14800d0a00455081e044240003c00c00701c2150720205840194110900030508039000c0040d58282c09900c249441c103242094401c100d181803010708016100710f01a005800f80210001c0310043c80754452010080b03144040503095595607401c1144d41c2c2c400900035141c8003035660781510b40c1519030000e840507a5554a4510682d03050981c4400710140011750a01098200340c1800702080e0800c00a12001d8003205500c003a596800c00140c501440b5105a05034040c40c21045040028000c51460015440396803141420304090b116 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 855525683 1250 855524433 855524477
    0xf0102060708370b0907051c0b03030904020c03120106020304030f11040908040b2203080708030a0e061003020f010801080d051605061612090302060f19060312 70
    0x8690110300e568010a44100b030000d800046005961019000e10596804000e603040300a0000210341c4c2e02d03054084a41c0c0b0f01407003900d0f0b10404500d00b0030300b009100049611480c0400c610524100e40c2c9840000031510103204554030700d540a803056581c0c0764565421036699200310f141d04401d0b603403a000403440c00e1001c41294102c6e50802071602c0c801e080741d1281c1646040140c01141c2c81a17503410183d000607e14170150000b010610840d45d01c03038840301400322000300d1a0740e00403000b0b80c451300300740000b81005060740d82c04d0390003040254407a5520400c5000808020b1801c502e180300300000c00200d170012850a00a4030310954174021460101c10055608580c2070082004582101e5110101148244043e00c49000099031510316980d1a4581c1402c00f003003955044004d01c140c513600f055554109110b036004100754941080f803903001d1785000351103042c090f02580c1610590b0300402ca11043e281d142d801d00200701c000400c4516500c0c5001008070404403100c80c0881c203603034804440314000b144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 855526933 1250 855525683 855525691
    0x607050403110f0102150c030130080304020607060905030307090e0f160504090f0506030c0612060f0d02120d18031e0501021b2104051e0a120b04020f010206 69
    0xa102c4080807508001c010740a030210712418114030400080d149610207041c1054098503074103110903503950412500e0007101004601480030082c01d2406c1100110f111044080e166410160140c0c03030340c03107500c0000c030706c1d2050400103000d103800c10f4a80400d10401100450207070000c0c5d11003040f015960f41c80700c0d10301101198100c4504490300c0003d018a40024a08075003032100f0310308285059204c1c1ea08800700c40615012302480c50b034a03003c218031400c0400c44009211411940c17503081c20340e030070700010042c2002072240f030140f80c6180b402c5030b107500d4149002080a81c014010320310741c0340312807130300d540c54032414048400182a80244694007a594400d10241e80d085690503404500340030610942e0a0340c440c0c100e030703959401c01c41840c01a1101c0f903a150141e404501404080c520960660000078003040b03502480f0f64100f100304070a55803032280c803681411604020030240320b82d200080d070032090790388101203040c1c800c40074100b04004400c01c1e91149100322407071902d0b02c0d4100012030352054126 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 855528183 1250 855526933 855526943
    0x30e030c150f0c1209010b191409090304090b04150e0403020714060a110f0d0807090915050d050a0210050d050c0309061927030815010206010b0711210607050403 71
    0x8031014400740d401180b035004201c500003140035000000440d030110034103031448d00721550402003400005100a014210402c00715003007407007414543c207070030340fa0301c114429034810a03940c1802401b140c40340c1d004004009460004004401c0e0740d401c034003030101022a002c0b0014011a100400c9000c9207480729402008040c10480c14422001c105031341e048a90580031016110710382039914115070802480210a01e1341c1c2da2080c00e802d0107030b0054200c00c100c0c0c100c405001c0c1496000000940000c00c1841107600c00c4603081c250103001c0c01c2c86401c0041801020390071244818030242890b8005008000c03610010408010b03642e109896502c0c41d0005840c0c81c5107a404c0900403860410075110902c00d2404101400920540390030407000d031001585d4041440d05080c8002107060603005902954071080380e10f10200301c2500200003d4542d001402125640e200100b024014404103001714031849001074030405601c00000d040300e000400303665803400c0d80d20a0780002642c1c94400d0040d00c048a42c08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 855529433 1250 855528183 855528187
    0x1803111603150b060f071406090a0206090f131103191b080403090b2a0a0b043e04062106020f0706090b060f0a0308040e07030e030c150f0c 61
    0x90100b00c0081e11040350004d50049051088400c2401124003c05010340301d101c1e28074400c09200c0c00139041500040c004919600502030305000750700e035041110140d2004a510540811960300021985510200f00c88000e9113880c01c011011980003000b1805101d400803108180e07044030b03078008251100c0314036400102d00c11388031104509008203e0560400d10a003000e0855944460741c0c900c4070b812003441110b16205140042141d00d00320320b0101032443c200405000002038584032030111841c09007009100481f00c140d107400309003d030201c1010204080e103580c034052046c44107210b2413000894049118500e088000105100c0320f65101440c800580d0a60918000c20f454200c020340100b0303400000c102040103c440018002d1068055484c8182240d000f9811b06a0a2041d00c3c54a40074003401501054800e1003c03d903800140c6007111510130000e003250f5108a02100605100380004e2060320000c070300403884090100d200307504c5604403807019400c0e130b072841089100c05105071800b800308101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 855530683 1250 855529433 855529463
    0xc030709020a0509100e0a1202061b010b030a050105010806060102300d02070302030d06140604050609030a0c0e0405010516140c16062303011511011803111603 70
    0x40c5402814a0740c5203400c1c503904005407480810004003038a429240001d0042582c01e10519142500c075020b041e150000003450b00240c0c0c042640c5228050071407001840c841030350017500c00e094108100340310010742134841509492078224080c00303003801029000d00400b000901c143d4400101d0341d10160300d10102900030701e0518104564840100300c1c0020250041151841c1c0d01e0ba10f000800503548280e0056544041e04004541100c2290b000002214400c4000510b02c0d40e44000351800d840e8122825551500c011000924004d42c2c10750081c0010502e141c0010090322284d10f4511a078000c0009100d19500c003160384840185107204a40401d030b1280d4034000d000f0422000d4200b0b189898200d9240072040d409030620042c040d801240003401c2e1040040310140c40348811681c0e021071007035050855050130301d40180d061201407030b0410460028401c0704c0e510b109400454201143e8450300f41c6003080343c10020b000c05e00303900704202688901003e441404001c030005104482d0081d031400c6885203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 855531933 1250 855530683 855530699
    0x2030c12150c091005040e060d030e0103021b07030b06011403060109180e06190606031b0c020a1703070309060219021210060b0a0807020624040615110c030c0307 71
    0x40042c11058100000b400382c00a0b0391500b00b480300205046840d015200c0e0301c0c0591060038144010a018007942a104c3d282d0b00007034010b100361aa040c400d00300580c68201200840f1041c01d0981025000c5211718072000060000d0b285e0034500440c2d081e030760f1010b0300041031606401c0b03104c1941c01a0014110180c204180c0d10040c40546000d258040d000c1900110700d5420b9140100585542840d1107248200340043d01da18441c210041005050500196502c18070b0480701c55070082008040c40a400c150400b10b56580c00300c0300c007401d0301403080040d044484d00525501e41052500314040b8079000c0001c0381d650b0001907541051080c401900000ca101682404600542100f240c000761080c1c01c40f03000031141030300840c2c0180151541094807002640001050107038050000001d64201700144050060300c0c012151000ca600b61240803a240180e011030001c241c02c0e80240102118418080c15941e40080701005000303901c7c00301d8200b10203802c20561200c13580401030b9490340c001801080101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 855533183 1250 855531933 855531973
    0x1801030b0c0f071b33051605010504020112060b07030309051e0c04050109060e04030c031404060305090d02010501060507020f041808070b13170d0b04020d0902030c12 73
    0x1802505200707040c10402c0000940036000702c00101d6006620b103d5441c80380320081ca82c80028030342c40308829a20703030380420300081c00600d00d001c10244070075940c104400c0b580100221110142442140300c206030b2503040040c001c2200b62804c0380000c00c021001010082c81d4012801580c0c000010700e840c000c90350307905800916146a00b180c40e4011940344400c01503c0c103000e18442e10941c800b6181c18003401d81040222a4160000041036140800c20302c860000680c0c2c150f0b0003907050609840640c85814103480000814400100020300000c3c0070030302a906130016805121000111600000e150030281d0a80f102400b41100080082c80038402519040400b00500140507000082910a04a0428251862400c243c03082c0ca40010b040c02002114042560322004a4040c151440450350346c0700c040c41d5911800a041c7c03000842d0300c040e03114565005e00c0d20301c0c900510440d40c400368401600040d00c4140001d03486400351000441c00c0c1d04201d00403079600d06242d4040d1601948100c0044441 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 855534433 1250 855533183 855533191
    0x30506160201050c2b14010f0302040b10080106050307090e0c0d0f0c0e01030908040e09010209011e1704081902100e0c090c0a1103160b010b0a170c1608090405061801030b 75
    0xe603168a100000c6c00d505010150180044011803801d960441c0180403c0d54501c01020f03000d0303903400c145070781d18a501c8030541c0d043d1007035858803030b03030740e0b15001e0f41281c500b071698000c40482da03102001e00915200000060045220340841840018503082041040743c0c81c400404002c03903510003030801c2640c841e90024142c0352084404030f0400d51515641c900780802100d071183c0d90303940001da0450719038000e0600b0120b0340c0011220342000c0030042d0028008200084108000921880840d007005000401d651407c840201c81251001c003098000350b0b64802c0a444294171454443c1c0b442228034081032441740c44001800c51003e54803542c16660865105550b948100311030f02c2165014a0350601c001c1854101042c0e0204000400e818081881c0c00182e11444e0041001c209451900b90002c000076100b42045a0036801540d52010300300941c411803140c0305028011100c590208040342024000003c41514200059a0f942c4d080c0055514400440d5001c003484900401c006405100040e40c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 855535683 1250 855534433 855534517
    0x709051009050a050a0608070b090103090c09090f060c0302120c090109080303010b09091e060d0314120a0c0f020a120c150504020114090a120507030506160201050c 72
    0x14107580321880d00860340e040e240301100589410500c460202e150103030901428400000d4180d40e40b07882ca0642141c403407080618141619844c92030248195a40e0120050100c002d043c01050180d1808402d20140d44034111800c0e440c100544204a20910035524082034460b08560309486040403070403503822030704a48c0c0c10804141c9010840c008203001031402800c00d2081075854114040401000d50b034005c110340250800c4085842200000000103901b20100b030307030b00301c2d4202d8072800c0c11516903501860540c40c114001500078002c1a0065401d881100700c050b0412451040e0002201c1405040a00b840140c0c8940f004002152191864000021841c180307003041c5000d681d609186c942841d0341c00342015650740c040100b0f40d40c000d58010049450006041c0c940710030000002c0c400c503000e00840138241c0090341000c00b005001c01040000e1b54100e01203c2480c0703803ea801919020704248100f0055080c0300107d10030400480139100500100d108803001c0c1d0101c4450300b401c10a456240c103007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 855536933 1250 855535683 855535711
    0x1104050916170f150106030e19030c170a020309011d010c0b22210903030816020304090510051905030d051c09030f1b05030406050313140105070818070905 68
    0x400f000c00708806004c070014074022518039031401001404480f40180c0da4001038200b0a00c0c101d00c00d000c0800085083c3d490f040c40301c0c84444074100700703501c607040d080030346110400081c664440741c0d00013005c3c00c0e500c4000d030390f08122454102c5070001d00c0765058070064003181c1e003044031100042141c4c4603281d1007040d49526003005055050b024841c00e6200c14203039002c40f1a03502901014400000401d0300c4421402d0541650703142d95001807091000400601402500e803001500b05403090007114005d0803005030500803414074002e64031071500d60384225441003005044124881e000c3d492034000b21000200982001980310000351950b80c800c0342000c043c0d602d030007100f2001c070b0321520039002054084c0d0b550b2000d10000103c0075100340c04800e002c11984403201074181c0014400400c803400c1d034141d454459101e4941144408016041031001010700c00042c0d0800d103c440e0551207244988055a6a01110b0f103454a00003039403000354140b0307402a0000744080c040c41000e900143d03003017100284211 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 855538183 1250 855536933 855536953
    0x7030605040812010b04060306140108070e01020304030206070b06090106110c040506010c150e0c011b020d060b060708091503130321020d021e040e01060c080f07110405091617 77
    0x101058402d0300070060442010506002050340b40c0708c1d18020746221052b044000070207800190000c3c00050202081000f02c00c1c0035001c0e80d10910951300116409810151901500e00d4500300b035000450301140500740d100300008070780c2d2280c000d01c00c0b0038541a010b0a000306000c01488007030400107001a0501104011080c00150484004010703203e244a000880c40458001e041c10550386a14243c10000345078507072007098954040010115504039000789a000f0b4500e4034002a040d508401583301704040b9031242403080500041c854000c0444206068565003000d400041c08242c0381d101a0000300251800020f02801600c1540c0c000c1c0d4000b03c81610247d04071205076030040315100e26080e004101250001101c6071020075031144003c24500f4641000d00c40e04504105101d581d08011415104006202400d01103484070341c800c0d03001c0c50f40d80007a82020100b00c903a074100030340034920b4080001c0300c034103010805188410300741500c448511320b80002c441c19414504640d407c00d0154240078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 855539433 1250 855538183 855538207
    0x1103060108070e210a0b07091a1e03160215010e0a0c02070504452415180608210904021605070b040e0a0905030c010f0b130905070306050408 62
    0x3e1322904800b10300a1500601c1403504840c03e07503015294800303200c01c940080c0600313242d803101140e22603035081038946c907080f511807884d03801c0b074110710301441e5030200000740442d11140c043d002c0c40062850b000c803180c00c1e80014a000c0d10010074441d021260a0403004201510300d640c00045c10791007035104032540c10b030320360300094121902c092900c803100c10303402032401e04c1c0c1e8008400c0080c42031044940410710345041059400140d2008001405281c0d00045c0d050b0107081800b518400040e03442082261450290031941d070220700707004020400800400c910502641801018182d0704100013030301c00204400010036104108176103220000c1800d020300c001d140c8491004c1c2c5954080b20341c0340004003404e401c000382404e009400001280d1780030001484440c024005503904400300c0c01c2c000819000f40d0070400e0950045195103030540d42401103c00e4150314a1304131740280f240403583c2600300480c008080301214103150000340f0a0304410310401c00703d2031135070005034424002c601040c6070140c44c13004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 855540683 1250 855539433 855539479
    0xc0417061311010e0a180e0a1104020c1603030807030b04050405070512150a02040e250e0a170d110a0201080a0b0d020a0308071208060f0d0213060602030903011103060108070e 77
    0x306003030509481b021000c1c102428041e001c820814480035007207030749960700c90b624400b04544202e03000740e0b000a4a50590311003005641d90100c410000d00c02159100d00c1c0080c82c039502a1f0b0340d500020308007403e418143c600f038441d56000d01e03031220040a03024603203c2802480340c0c03007800c7e10b170640c0202103100101c4881c40400c14415031004000698880c00c0c501c8400c40307054080c085071603400d2908102600129000d444404801d4142456040c000c4084001400809580c000d651510000d8010032001c0c1310005508030781028940360b9030b90802c00e071400156152000c400c081d0015407001c000ca02e815505600110480e140500f140d444894031b41c0100c1c01c1c00400361700c03c40e00311130300144a0040c4810203003000254480c515180d0340900b003130070018413030900c45d00c0514400e0004d0840d40045681e40c406845007030310b480e42c0500540741e5941002e5100c0d04101032042c004d500f441c00384154211000e0884e032042c0d405031030710711054542030380407105113a4014020303420941c0d18501014082c95100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 855541933 1250 855540683 855540689
    0x31b0807020405070504033f0c020405010519090b06090616030f0302070b06041e05150a05030303013803310b0a0f140c0417061311010e0a 61
    0x2062956500c1148188000c0ba80020810000c01005000034030002d01180c8c40d00c2e642d060409881609040c8401042d1220761500409207282012809800341e0300e60840c003a400b01c64000c40302040b05a0b60384050010406500542d036400c594010414002c09006600c40b28110001500d05410903040f40003103000d80c1d02030500c003803224400480100405501110407480341680d803400b9070406240341c0d2010350300344002c7c0a032840303680c40700c041c014042c0002080080407501c208061040d42015481e00c160000e050036100c1c0940360f0a1000b08040c00c1c000103c034101e8883c10f9060300c651203400c070700074014082c0c0043c003500c066240480a80021031302d00558001c00859061489610794034101c2e0044c407801c400c29002d50000002814082404e50302051703405044204045800c00c05c105e403140c0100001416084004001018051a440110090419184c0d07003584948503069042c812640d0310402c843ca0004c41c9046032800002034030f5220f81c00d01320001130402400700801c0000244010090350 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 855543183 1250 855541933 855541943
    0xe0c010e101b0b18060c09010518030c0a1e081b0f1c0602030106201203072d020c0a1a0723010506040b0105130b070c03080301080d0f08160c031b 64
    0x7804d40034010014402c203a00411950012071400e020400040c20300d014002034110303c01a810071214068070103000843c43c40741d0007092400300a8803008451603840b42c0d25007805010114413004107062000048c114900070300d4003a11404100001c0800c6146482c440d64160461006928000c2e0486a1401000030030301c01e103000340c0c4944c1810402801c101c00e03082003083c5100c400c0720100c0500c8010400742da508508040b074682d00c0c1d540d403005072241000320b40b000482c001e208920f02d40141105040518a01c180c0c2c0c02d42e078801c1100ea0802010741a24040c1c00d04524008000082c030640071380007416840d22405c1160900201e603040721001402148a481030342c0d4540c000c225062601d0f00c1040290242424040c2c203013040c04510448100c0c581c0070740f6160b02c900080348000e00415071031450045900c40d10b0640d44c1d6841300d004645401d10300c00b5810108511003003604a160183d08070612500783c420803000035060b03210701280d46406484042d010300815102c4150445905038a140c0301e88d0141c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 855544433 1250 855543183 855543211
    0x901090807050c090c030f0412030b061803120c030a08060112090320070b16050106030b270a0f020105030703060801050c07051c0804030c03020705130e0c010e101b0b 73
    0x10802c0c4002003900905d619003a640c100704124081d06800042c58002c0d422001d109002410000158010581d102d02545d02140110780c1d0049035201c0d44c1000340c600815001c0d103016030681744109500c0d0045403c40d291681040c884d1071242c3d4800c8030001d078002070502d0903030155000791018008a6581c144154001403a89082d8106031a03003421364a40d00284000400c0300510701188200c40e4003603e002c0d1001c0d20700403c136902c2480030035042200510f4009482400e0781c24502da110700c03001146107a0364a0320301d540501c01d016000101d001d00e41c0c15003000c0703101102c03845a0b0044031180e1004090505140c0d0761880411005024404e1724030401c1c0815840303948242034184149400c141425006030448040d80500440b03034000740345d54011740e15040168084803a40303403e83c10020150002a0404203a1034040b4844003250041506e601000c0b003a107140c95820401140d005007410340c0c0b640c008510301e404404042c801c00011040051003440940040d041c3d41d00c020824009492102024a83e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 855545683 1250 855544433 855544453
    0xe121f0911090f070c0c03021e090a02130302010309020409050109050f0f03030124050c1009020f03010c1718030d0209010801210303050a0b091806060f0d020603090109080705 77
    0x4480c0345400042150340072103920744403c490050081c020140000c12000c0c00c400c07070401a0707a4403030301c02a541c001c0810030b241c050311640c02c09031281802c00a02c22040d038804151b02c1d6517144203c401c0101c640e1105112241944c00540240c240003008903046030791542088080344081c454055494480d2024002180441c1081490504c41606d0703c1403a070020001000186d04441034404500d60300301c40e4166102882d03c066070503000f0500709880c2e80c007482d451a4900300103a4080e4408600c2121075102002c8940e050600700d486c00107900b00413862079403503450700300101c000042e07106000c0030440d000d070380c1c0102c0d000e801d40c2c010712000f644954000c54820f10560300480c0301070142642400042054005015410701c0c140306000140c00d0540d100b005c1032031300c8599042050360010207081c0c01c2090400180b00d12a9540380410300d2041d000740400710b88149002d03101250b0b50311004141d071051441036000c201059001078070782c0c0d80540d80d440d446000a010200a004001d00900c054048260 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 855546933 1250 855545683 855545693
    0xa030503120a0c0302090a0e0a020c1519020a021e0c060403080318150412180303020606010f02060c1c060e0403050316050a120203040f08030a1d010c0e121f09 70
    0x40450503e05050041c004001c2d1030300c4075900441200e20510307940c00e25894001b03041d0021b110794000c80206002ba200c1030412605100c0949028164014050094a0825074204101d003e01000403005070007502a4a50021006240120f0720071040107807201c8524000000e00a50b1266204a903515404010041115852201202c4004004d005004e404d4084803801d0000f500c018801404042071341c100c42c1c08584103007050041402d001c0b591150f280d072242401382d5074044c1144c031140050030660002100074404500c2c0c6024001401a00b420180001c0b001e50500c0390081200720740300c3d515500007801d1002941128003440c000e4440680ea41801840c0800d01210203210f1818808200b011198290b404211642540501d800c0142c880e21189481d0041148000c0064041d210100034400e41c20540c1d4815920201c081d00b031959441014101d080c20b03107004090b42004220151280810750800b40034030b01e18008074005540d83e9080281e214009004040ca070300301040d5a03040382e401004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 855548183 1250 855546933 855546941
    0x18030307090528150e06030114030c0a05091602100204090c0f0801060e0402030421110f0c090f1b071a1302090105060a1b08030610080103050307060b0a030503120a 72
    0x3c0c0c40e841c0d400b049654400103541e10202132080c1c0e0814242020074440c01440303071400144040000b4070300b90f84c0c2c2d6500d08213081403802e8400814032a0007075a9100d240c501d44002c2d040c040b14000f6009034595030710060103800c240306842d0b003841503004ea5205c00540690b24402000a0710002c1400280c84d807000b07070010240000b51001c202400460340045c4481901f040490b84007810840340075903a6aa0744c80c0910754460f40c0104c03010f100e8042550308000a400c607036810494803281c400c0700d6440101c10034141e56000c004581c940c0013802003021900d1000148601a03008111002d05460741004212401d405c1e4804003081d038490040003a5081811000300da0242c1100510001200300441500042c95041041c032601c1d2250300c0000741c1500317281c000c01d000680010490404029008103080045060388200c13a49840380803142000150a402034405a0689800c0002942021f0b083d5682c80003c0c00000c2100350f0141e040ea40010000d0170400092041c42e00100000600f4102050364606803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 855549433 1250 855548183 855548209
    0xa090c0b0a02060c07020d0602030702010f0506270c0919031502030105131d030f0903061008030a0e0102010b0603090d032a0c0c0905040813060201050717180303070905 74
    0xd40e04000c4a41090340c0050003940141503410225035078071140c40007480401c01914000c042c00e00110411070384907019401070300d001d05040814006651641c0400800e00840200d84250300404440001285100200c656204c14071891580c58440d84c00d00142c5015417010007034580d1f040b02c0740240100100c410498550540b08203055055505040019545079111a03c002855980e000c2100b400e030781c1416200d20103558403085d2544d0358981070715540903900c0203c0060013880380340702040f103101d50101c0c080102c50008001d507003004090700d01154003590220100381199241e64400c5c02e1582c400b0015406010382400038041c4040b0804c0c05425522072030006150f1f03888070350b01c900c40307001d4082410140941c646802c20005442d8984090300c0b0485030800c8010514000c104030410500c0c10003030003119030180c0c04d110302e0f9650300e40407400c0e26021034641000aa4031000200c40810010021ba00500d10700200c40110364000c0b941461500210750f00800038030301903000c200c54109541e11002e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 855550683 1250 855549433 855549449
    0x18050712120c0f08030601120e210403030206010b0c030f0a1e02060403020d051c0e0d0809060105010504120f050a050601050a0f080304150513080a11010c0f08031e0a090c 75
    0x1480864071110190310f98804058000000000058102ea10030151807103030070758081e0100100749650b80402d03030700c50500043c000c010000503411484900384400780d408803503240d07004010603800c004052000750803040c0440f8041c80188015070780110002c0160401e80d6082d614012011b00c210f10715070450fa414161042550071203010b00000c030382d001c100d400c82030000d03007007aa5071084d0312002c00c2c0011102403981c80500303103003110051a003d00030035451810b200c96683c01d1b45640301c1c40002511500700784110b81c042103040004020310030380c1031030450710a4040d600810140c00b00391a01424070341300e1081216283c011100500a610b005010407014010421800d61010305100180d9600c3c8528000d207841c0074003c1000390071583c0700e07104907100d10a9080400315201e41c1d0f00c441b1581c82c80c400d5400c40702c001700203100580315407040101c0d001c4c503034003c641d4148285082d110704040342d1001c0c041d1815010709001940804190054250191b0350744480090700c81c41c03604000c08c6c0d2400d19000701c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 855551933 1250 855550683 855550697
    0x3180b130b0f040f12110105010305070f0e22020402120403091e050f040b2403010911030c0703080621070e13020102031b030d060b0315010509010f031805071212 71
    0xc0494a8404c003408030380c1d80504e500c128031116100540707150401c50302e855080d41c20080080100a40403400d80d080303421948101c4160303615141c6180c9521011545500900e80160340c03890824102900110500c1c0007402c01444c0c8040c0c00100c5503044011070301a07003c00c01c032407820489101c03041101d4040c00460720210307074140d0600000800e0b4100b5004032170b1003103403900d00f43c1c0340503074419615181801d04c1380115014154500c0807255960030034818540c51918000b17441100252030003c42e03120b600c441e69100d1511003150741c1550400c0300500101e810a50605400e410f41440c4501c0f560100002401407021130b1800040703034408040282511500e241c00e0811f8001030360000140c5503681c0c5880c069207290003a4020310b40c0340d03006d0102000c108c0c604003480040ca030301e1003c000314084c074012400603c0c0e20002da00191001d1180441c81400101c4140706101c1c02c40c800c5d440050304208042d1541c2c20320b40180ca03154a00320680d00001107040b00410440c0800c11200800c031240022820040c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 855553183 1250 855551933 855551941
    0xf03030a0c0605270a03030606030513060e0c0a08010608010b03070b0412061424030c221118101e0813201201051603180b130b0f 57
    0x1c1000420160080030241c40c1d6010805000f40e48580c02e80c400c442c90b0ba9072003580c00c00c1034802da940e8604101500403901c0c0c5400840c2c42d510030b0184521402008144c0c2c00180703495521000103100048103420180103880882e012580c03a520244c0092007008004034031141840040c2e421102c034840c079180b02c0c1d803128008100701c80d501d10545040300d283c102c280340c10a20a041c1030b005004008140341601e801c20081080502240d110700325064188981080c0d0801a0000c0c1035680c4c1e4541543c0b68880044401d003500c10303c1008081c1d26900b07111001181c1400c55071a804840e400101400c65010f07000c2034400c0e680d09000042070760600c26440d125040e0711039103060300d80403001030035800104030240c80007410303a050f80805400c4950303011841e8505c0260000c080e0b14032204512940388610b00d184041c043c8040305000c0c09004401a07650804000c41402041c1c00401481d110030207c0407001c0816000302e104461440e1060002d000e020107071408914007588600c0300101660703402c0304001d0901c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 855554433 1250 855553183 855553187
    0x409050606011d1e0310020a08040b06012309150f250807080304030c0b0406050105031b010801360209030606011b02040f0f0f0e0f010e19150203150f03030a 69
    0x501d0b0081314007032844070b0002d00280420f09203001c11000d90095400001c1540f001c07640881403e01c82e5000b000b0b00c4ac43c6031500401120202407e6101003c00c03060350a1004803015610001c00b050b040c01040003002d403801d880c826085070400710703806d03440c9034021402240c8803200940351040880d48081c01c4865101e00e983c0c904190143e140003409816010002804140c05202c80b1f4031150341042200782c152a0a16000c0040e14003401468064003520500c60b40e400890141c1c4200300e14140c440420507030030500c1060340071480324100d82c3e100c0d524090010241c05201810170324000c01e0780c009a81d0310710410606292000c05011a8104440205044024501c602c18452204c0d8120780c0820401c0d04207079180c014003040001c40c0501490103a07030f240181150350001e0801c410032020390345103c541c028507500b2540c14000054513078106081c000440d10a04031140d8025224540400b04030100c901c0c04001c0f600210b030035a8541d68003030324904403450324801c0d240c6400c00c12001146850b4dd80240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 855555683 1250 855554433 855554449
    0x151e070807030507170114010f0e0a03020d11061306030515090a0e0f010c0207061206030206040e180115080f0d020d0e03250612060608010e0402030c0409050606011d 73
    0x841c0741010354480101d05100d20a0141d072614400d80c00302a001d95031109031156101c6c007004165404510710340300c03c60b812402031f140007517031000040c03031a04041c1c0b80d602880b0020715050341c215685420240000229500c610152505240481c660b0b080c1c0750230090043c044a1016001004520041ca0500303040d50380c200c000c42d408510b100c000700c0c0145402c00c03103d00d07015510310040c8965081076824a00545d0028100d0116141551000e0200d940040d0003812901d45020203508034104000c240403841013450360503040380c489802115140401c40300d01e4211001595100001c0b40fa4000401564804020b1140d09841c1da4010300f40d0f001c08400080d541e41c140d80081c0c0203000d4609203074030b0706076003c0c800c41b00280605100d9074841e284c04100da41040c6468010031001c10044d03000501e034008035100300010345e2610344503400d1990070400b941c5001030006104070f9062042c4045496652034601a850b80e040c8500002e00c1d0b13504122001401c0c010613581d07003800000c40250307900302c1070fa034850f9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 855556933 1250 855555683 855555691
    0x1030b011814070f030e0706052104080a0f0903141c020f0d030b060904150608090a0f0f020d02040207060e0c06090f10110f21120a050a0e151e0708 65
    0x144070149501501c1300f540940700c07a88080e0068082c902d40000c000d900240148000482c440042c00c00c201511185042c01c0c00503240034004050901c411144640500480350031211a03040074140c440e03403903a40c200e00c1680d000c01443c05030012045442c02000c040d01040840c2140e00141265604400d003080d0b0f03803c0314401802c100b50f10307040301a0309501c4034021514540d601420034841c00307000b0110200b0f202c000388591000540d424000400020005c524140c942c1e5024074005031007256600d035034603540401e4002340c1c1d200c8191984c82006070f0382c501c0201100c0d40700e1400880c07040040000c00b414021000c0c0701754001c44041240101700d50361300c50b40d042d60800132218406155016582100c0e100c05c01c41c0d40210714840e01070541404400001c0100390641e140142007000c03d41c40c0390003c0980204031100e005420042c010132014051600705030343c00f403039003680044c240c0c017242442ca28041404036101c11390841803040c00941712220020440c00b000103040031170070f4100712000620640c0700178 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 855558183 1250 855556933 855556937
    0x906050601080c18040f0e010603120f141c0905010b030705010908070b07060f060303022112190e120a0809070501020c130e1e0607020d05030621030301030b01181407 73
    0x204c80409207035180e034030800480c400450100016004d08196a0003404030340402e0b00d01003040c507020303442c40e441014540070482095031007508510941c0c42807c825000100076400034038040c000500d800c8031900c00e02d07800034007039000030925903019014182070001075003180d410000a4a07042c88036200c00a640c0781200c009080141c1d80b490541001801080b0100211036034500307141c1c1c000107065000461280701c01164003078031075002c0c0403c100003d5200304405001002c8150340000c2c020301e101501e0ba45079504c0c020b00401c050344104d040e50b040100c124195480040085548103813554440f50030755000c40400000c0c1152810040040d50318551303890840e200300e034811340381100e040c0250020400c1050f8a0201c4415080700b41150701940c1c0303500044d01151203810000b51180d803000606942c43c1011307480e0640740d40c035030742e040c003102105450000441c0000da00b00d4004011003003004500860050740610819410031100f15000c91031206100040c03800d1515850301c0780044400d042d040302d424 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 855559433 1250 855558183 855558217
    0x40f060e06100b09151809150d0f0213060f080f0f10020307050d0c02070510020c010e010807020312010b0a170c04120c03021c030809010e0c190f030302010906050601080c 75
    0x140000b2050a00c41003031040124020480050111b5419801d80313058004985850700d035590842c0c28074201c8500b500e499884008001988041640d0301c00785590580058820f913030b9900040410006d4402d00d502441c0301014043c0100301c4140207000c00120480200042d000c0700351b180c4440d6543e1251144440001782e400004990001d018508035000303180683e07000d0040c07017000c2e540039407100c04a01c681c6001e601800841e0043d580b0210346148c101b20161290006aa066801107c3c004401800081544010480a00c3c1000d81d00400d0f40207040114800e607841050260040200504c01e5902c6070040380003060001c40c440540545056070211940f0034190390407400c1410904003142d0010f90402c902403081c1e00d0300150010404030090003515149100c0d19031815403400c031040c03180d4102503900300040c111110710f03221101034103281901e00901c0d6015150448281daa54059008074091307950341a118040004e036000c5c1030350021003402c00c99003e103841c198152040c464546408030b81009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 855560683 1250 855559433 855559447
    0x1050903031c0605100302030a0c03110a0804031b141203070807080903040e0a09020a0b0c030901030e0313181506050702130e032106030a02030a031b0b040f060e06100b 74
    0x683d5000400521008024408804d090000a0000e5100f9110040c44a0518540c140014007d00501e0101098501d103180f40108491003155002c402620403010841d1080c0d00c03950403c111406039594500801c0081d1008004244d501e00c2c218194140c400d1a60084c0100000b443e00610030591003401801c110089948081c2400d04510403900208881c0b81c20ac428082d5200031580301c188e00718030a1b40d0010310b0b02d84818040000740a07038808282d4a50042214007c0c2e944283c01c40c46000c0c1040003181e082c82400e00300c10355200b91310382180b001c030610800903064240c154000c504030154003211000503182001801012842035a01c042d008603040c0e205030741c80347c40d030364024440c034914042581e490b8a062481d000000c4040c40c3c0c541401404403000c1081071601048400000364001c000307269007002a601030b00d240112241c0c0b05a5021000c0d0750340c02041aa5001d0792086200301120003458a02c0d02e4820b085442d1507102e00410f9000208001e40042ca154003070042d6481d10910b2525a11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 855561933 1250 855560683 855560737
    0x291b03090406030803090c03150c1804050a02090102100b10140c010e0717010b0d0209100806190501060f08010621092303070b01032904051b0105090303 67
    0x8520310049420902d0000d000051122030780103180648000c07002d803030080f21120105582c85403c044013000e503100c400085103d640c90880149011001003131002c0e00c0300805000202100d000711a51b0504940000300125a17683c10302c02c150420700e01040c10480d1b11b8500f800310307403c070441051900500c002d00b85454451841503041c3d542050b02c1c00028450743c1254401c07603403222828401c003440c003000040020501702040c09504640d82002d400d01242610719020031511000113400401440c07541c0c0c6002c102c0d03181c284031542c070440d5018503010004918001040031958164002e02c20840d410810301d22003a4070441050440f0143d07d0038203140c103170410a40c218613140c00c1b0ac40003021b1900351444100008070b080368421170756085440030039080c3e150040b42c40b03104002008101405801c0148005481c040181c400d0300300b070682031703500004100d42c94640c0800c180d03003d941c2680185107a20035850240c01d0030821150071311f4042e0500f0100d50220350343c0d000305070009c0d01614405c1001c640040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 855563183 1250 855561933 855561937
    0x80403031409071a04240903082b05061011010e01090b09071403030729040b06120712020d021f0906090509060609040203040f0615291b03 61
    0x421580e0300744494101807041a41c0c03a5aa440b420074507069007512604002d5100003502c0c1125040c00700ea0310548200c54001d1086090b0040003800d00480080c08004103071400040c1041101d1102400c90020b803940f04002a1b81c100a0888485403c00042010075101e246a000c107000184c00c0c45003105003440142405001e1008514605600e0300511000b800303003006c0d007207001c1c116540503126030710740380c0c20760010317501c031120240341c040e40100f01260001e5200e03080b0115119034103045c0d100f8400820303501c0c268458142d4050b9007683d803030741c03d01200386800c1c0c080656130b00020300103049581c81c1c82c0c0075072000500800c000e80700c0da40c45d4040300103544034580503003002400012100c1d44900c802034068401d410500603000018101d0501081c581032040d88540030b003c0c000c041900708940402040003030f50005000710b90613200400e5241c005501070240ca0090700c00b9400b410092800c0079884c1014180e0301c50500840d08085520b4a0019090411a14004032a02802e00c1503d82c0307030010341c558 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 855564433 1250 855563183 855563201
    0x9080111071104110d090605160801050d0c09050f04021c0c05061c140403020607080919080d0e0d03110f090d140303100f05030d0f0f03060306090515010608040f020108040303 77
    0x18080018414043d00700311b034001da10700b5104000400c500c1e245d4044115440074100204070104640c68018041ea1500d00001200c0500c03912140c41c00b00d480c0ca0b211b07001e031101520f107028040070b070501780001c525101120610142038440250702050306510780ca040c140b1117101e80d41c041c01d400a41c1d015000c0714810382c01642c40c01410203000c80400e824500708042c40840d4150018080c14001c0341181d407150303120320700032002e100060000c0c0141108003e0a41d00d07071401140c2e0068108042100110140101c0d140d03803004102a22200342c2c0c1c580f0150940b84c90400b07240c03d169040001d00b603c1c904a03400c0c0c83c3c40d03180079079000070014490b180c400d244ca08a0484840584808010008201d034001d41d0300050b123465003d1102c59a079a01c081c5503807051103032646808656050a01ca081e10300c03448003010f421035180350118440e43c1d603072107580c00c03600018003d44d10758100c3e00200204003540703202030340100501d140180c098a850344901d00d83d12140e1034000e0400c00c06030085018035100341c0111600c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 855565683 1250 855564433 855564461
    0x30603050a0f03090803070f0b06010e04090c05010f051204110307120804030204200306121f050115021f0c022107050c011812080c0609060709080111071104 69
    0x81500c2c0c181500401c1005808800140a5080c04030f2491404400d07200d855034000800c50b424074440e0350300707030440000600c49410455001c6014103159180e02030b80110a00420001e42e845043c04001170082d5007a00042c402e211080100003540300b030819400b513029410059200e414140000001c0c00d20704550300c9403004090010780001440281c200a0049a100329002c12600d0b00c040441d0007541805080600010301c107100060850408a02841c51024114207888040c4009100026207141103103040741100e0b503034001480644440300c080328000080340010010b020346403440400d030440040840c5d04d820744500501103514000c100469a10804004410b1180381c00310541219402c198400d5556100b0b0b8914101694083c02a500140404864401c1003a0401084904a009008044500040c200001513a554003400309502451441c0094003140c01d003200300030160a06600304180c1640b401a4040000e448001281c10950b404000c01d41d10f025908002001044104003c00c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 855566933 1250 855565683 855565693
    0xf0503190503090d0c020a03030302090a090f0906060e090d0f11032b0504110f030709020d0e060708060d0b1503070609061404151116091512110108060103060305 71
    0x400d140c1c0001c0958803940700d242c210391084169400c215000e4100c650040e410010307101050000c28031130380091100910103490180c21a03038400e860030803501c9400c0700f00a0180d81d03401d031710104650790258000415140c402603ea50500030100da03260014003060005100031461107000a42c021a100611007a070802900c0e201d0408903a040d80d40210811009128502800c003000c244046100e06401607400210038074018030504284184c05041c10580b5602d44179030b50002494800500003440c29203c000c1c0003064000301c5a02c0c41f4075000000e44842c0a000ca1001041101d40303c0c103012030041c9030401da050340152a0001407091452405080c25014090100c02240e2107402031086422182c0c65965556800f0810104e102d45002c2ea02540d01021380c41301000341030500c11036950681c0013240c01554103000b80c00b108603190741480c0c0e002d0403040c2d490388191000e201c0710364501c1d0000c0891242405140030f8981ea84400c074500020014113202c0c4903404100180d101e0390100b0083c641c0300f4200e030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 855568183 1250 855566933 855566977
    0xc051302040f1e0e010b09150c25030203010614040e0304030b0c070c030203060f1006020a170f09060313030f031a22090501050f0a140112060f0c0c05060603030c0a0f0503 75
    0x9541c49507da6038001e40c991075003482910001c13070464524030348120207084d4003020002d003529298051103401c40300310141030340440035039004c0c483d240041195080c000003100509042c03005540740c40a000301c0396001030004001156038034852130351080d4001803d51b61240c280c607041200c021650001380d0503109000400041c044001140e50152820044049034076035148000c03070b50342e80188401441520b01c6400103020085402c09008035045810199061000e4500483d0294100711790301d003400c0e44000e07000c00a040e00550600180c002074034050010915001c140b0162a04420100d4055103a41c200d0702c1c2454070042030b000380300d071040d0400d100d815114180300c0d0183c10150f03004140c4905150102e04010128030400c07800d0550401d034800c2c0c5c2d03071030102007010940c44042c0903914291150b82d4205403440030310a141c00803415444041c0c0030601d60400c9817618030028440c50103035104020341c14040e18000341c80b2007410391005100380911800c1c5452800c6004480d40a42c20403c040045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 855569433 1250 855568183 855568199
    0xd02030a0213150e0103050405010b0415140306150907210b1f0c141f0609180b1512010f050412020715050306010302160c051302040f1e0e01 62
    0x8103142c0003104601c00e0543d48400008200c010080420030120360041c140c03d025502940003554014002c0b400020386034801c10101c2c050b81c03865100c0d2140c019008000740310582c9413110b01d00411b4400d40080000c4e1034098020154982e07080b0039944501200300001e1700107440748003403a8003184a2038041690120300c05820300a85a04134001e807140da005841e50320301c01072218042562101e50303940c040010025458500f40124100ca0002684c0a6030314030300d903070b403c1c01214034200100034200007404601d098203610488281e41c140c40081080d903500000400c0201c1200f540001c2d10007451282003214600060b00403241d240c0f5a180b95007050505c4d45144502c2d40418400d030f000b01382d05691400710b1142280c5454032030043c42e0500118044c5010507504c030320041c2d075201d01d044c140186030003808028103c480e074203090110717207501c29213109011600700030601c103031192484001507050601b007c80c42c0441182034010340311242ca500c414507007036520302c541c070100600078083d42d944cd0396120081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 855570683 1250 855569433 855569437
    0x316090510051807081e10030c090e07181d0d03060b0a02071e03210306060507030c111c08040e070c260c010c0c0c05030307020918030d02030a02 64
    0x4084802950000700184504110b00188000e0320740290319015540c038100c0079194610003030115000d29001d000c0c1012840704460403075009507650100083c01d14074614150707064040d05d4000b95601414029501d182800004040b0309030344458a00304540c07201c203100301000b4643d0911903100e000040d40781c920681800300c2d8108a01c40660b40501540362a48070b0300001e0f1050321025401640003241c10000d40d8850301403041d1061821540d0200309540e601c81004205840e800340200b003030148403240425416103d840014607082c00c1140c20000d00d41c4001d09060b050b20300180c001ea5140c1802c040c90798032010130503003090900c40c44182500e201c1c1007800341600103000c0ca00301040e07400302084005000b1401d01c6440ca90185103000200034003500060941006020234410040a0065070640e020a004c2c22000d404140d40318490710b1400e051202206140b640b005001e500100032250141c0c850242040c0d1041c0c0312503107a2040725010412500c0e6105006208070355502c088148600c84240d600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 855571933 1250 855570683 855570691
    0x213022505100213140301060302040504060203070305090c010c03181a031009052203030e0303070e0f06040b1b0a0813050f030714040f0605040908190f0906030b03160905 75
    0x311860400160064000ca00c00c1010b51300c2440c0240704100448000030880f5844481c000d800800c0c130642e241c0c042800d4400a681c1216110b0f000310801c0700043e418468590720410b010003d003c140c558030006045400507407030140400c116a0550041c2c99000381e524001409102e5010030008044860380e03903103400030b54204455034160b01c4002400344490098501401c1c846080020000003d118501d40032403982007201131640b10b40c030344141003070107201451084805403140080d042c01c0000304600030a00c8400c0a00c2010140300034031404103818241c900030781100201c0141d0a01b5941180d15000406030003d1240f00001a56400c01c4040841403040b2402aa018800c036044a800c0680703c0d80103009411881580802d210b0a40c98240c2010807810280f00c0d001405984540200b0b095441d0003c090340c00c52000a20030104560b0a00d481c0714480440c43d14032449240154018a8184940300d560105511110032602940d01400101c800840c4600c408008940d031352005800341078111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 855573183 1250 855571933 855571943
    0x2805030a0c030b010b0705070e06041503050d09091401030609050327040609020715052d0f1e0601140d020a0e03010b0d0f140102070804080f0705010905030a02130225 73
    0x101c000104c00114000b65000d0a83c410301800800d409c005400075001e0005203c4c42d4800d0711b42003601c01584000d04050091406440a00404400c44502501400c4c25a0020001602d0503035440c0d04007540c001d08a040d2980150301046038103050405604d1401040348408a644c035005106495801c0c01e0403000030003206403418131201e5915000c4408034010080302a10034580801480f103101d450b03500251340280001e000c0000307142d90311000d030b903d4014183d0320041e1000d10028000d02e403002d10122544001d0151010800304440a48404030400103441541440303802c1880c0c0700000e20311401d80e607440c10703101d0045483d050649001041c0f00e0344031007003a011394030b800c544000701d040010716004150f800040640c1d12144c15a522032070f443c4101100728803550309200c00c42c00204c0b2440280020303c5c0c2030300108810b000e00c1200a00b490460361109050083d82c040401107528081071069119404807030302e454240a21901c9006072080140020034100b44800c401c54003a601241041c45034080c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 855574433 1250 855573183 855573203
    0x30b04060e0f031c140c0a030b01140a050408120712030504020114030702010b0910080721021c03081612051302030619050a02091f02010216082104022805030a0c03 72
    0x34404104800c80035113800e905220304000c2c21f0710705030103604908861841850f1107842200e030500ba0284503040702124000003030300003400b00199101000004400103d500c4440d107080001e50340c03901e105003107030341d22803e068030313000040c01356030050a221420011940031640e41c0d260542000b4002c101403220184110b030207101080c4d0b04084814000c06803040500101085800d00b0107040d039140d20012000360110281030300c103005031030302c849c04502c46452003603080b06d0401515019080d0000104a1100c485000c5030391400300781e0202c0b0310030480c0c1111030001843c0d1030328403460703484051462001c1d4040c4504800d01020040041806038040507500c02002151603406040c1309a2161600203644103440105022940d8100020b080c0c10101c0d90000520703000d660010300100c4404080d042d82e02807408070b030302c0714010b0540d2050b4080f40b440c105070143e2031500340d0011f4084009c210710020448008203500181c0500d000c501c4010308801411603504440c46e244c1041a00d0f003a0004032015085 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 855575539 1106 855574433 855574451
    0x3091c060e030301080d03021206040506010c050f0606010f0c110f0307032a060201020a08010b1e190f0807080109050a0204090c090501020c0307030b04060e0f031c 72
    0x1d000091900d80d0314200183e07082c480b07840425400d0600400800d40c25040c042c1040e81d00410803100010180c4440004039802c881c04080201035110350390255000751070018809114140981e076074000c1e00c0041000715a40307020140c0007000304100031a906403d140941c07559424080c0682140c1c0f10715502d40301c10300d50000c05102d41c42412500d030b444020000441d01c1880203444180000c0d860801c0003040206040742c1440b540d00c0140e00130851200310301040c241c00000d0561081240d845104100d0303080a40322001c8050720200302c400c00054400b5000d21076141c4101c500d5120040668a05050400903240080441461079802c21012910701010310840000e058070303940d07002c40d15083c1000686800d2600e80158880d501003c0104005800406d005d44c0c0039078020004140d0031000004036180241022500d81a13010100e1030001081c441c003400903c90203564414011440 = true := by decide +kernel

theorem cover : BRFrame.Cov 855395683 855575539 := by
  have h0 := BRFrame.cov_init 855395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 855395683 ≤ n) (h2 : n < 855575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
