-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4734
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:33:40.286632+00:00
-- url     : https://prove2.me/submissions/414a44b9-73b4-473e-965e-e415fcf4373c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 851258992 ≤ n < 851438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 851260242 1250 851258992 851258999
    0x15110403060e0a05011434052809090b120606091527010b04030c05040c050f1605061b25020909010501051e011b0c23130603050a080307020115 63
    0x34006d04a10404460412480c08400d480200304114001050121601400c8802402c0a0310075000340ca00000b042c40420070303035451044039840326007220300807a001820040341407150782c58600414907030341801d0b00c50765031040d4001d0b0410380310350300104543d00442460000581c0704403081d890085a01d400761260340f58030554810b000110a2103071006800c04904800000d01c0c05c070000c1187c0032a908070440c0c90b80541850200700c00b034040c00d00a0300411406100c0090008030110007130254103148101c0603000c40180c540341d82440c0c0020800305d8150914030303245205403815000c03117002d0300721015141c805684107403001c00440003004000c0c4d000010034007040f5050105603c498140d440c112440c401080e02050b4072210303c120762003500d00281c1180000307103070304400c1950301604912441c0e220321079640f10300700355042e030000120070880c80b045010700e103005080071641040514a00e60b0300b44045405c5880b4a50750b1240018001c0030b1080002c0020f075854403e501003540ca070100a006011a5035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 851261492 1250 851260242 851260271
    0x120c100b031f1b03090c120506011a09060a0f17010f0b090a0e040308150d023d0c06140402030a0b0c0f270d1101030906090507030f15110403060e0a0501 67
    0x1091001b00c420380501070740071a811100401c061302c403a40c004000d00d40d44e801c0181010030009903401a002040c002d00c2400000c2d540c45000c0c03d09906140ea9518850a0302d5500a00d1042304105201c90b86401d100180202205003034498203907500d20840907501e402620204001c00e10a61168013804c4003c0c003480708055000018900030402c00e0411030707041910344104000d43d181c40e130b4002c0d88106004070300c0c5c0350441401004c2c000c80440240164108000034661900c035040c0c440128002242c41c5441400c0160360701c075400c011607085115101742e161940c0403a5545005000280402912a00003a20b0441c101d080361802804900c1413074030740091034104030558944806003000b4035507420b6114010304101c0301180825801414030710811920300c00640062040d6401070340d210f07880b6807241000c00c40070442d0710001c40c491011104080c0c0c00b802d25012207500c9656602c0c0103418100302e012041c03103500a66017502e801c101300045248002145c140381c5520b40e00d004004c2c3d4249100c00c840241c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 851262742 1250 851261492 851261501
    0xc03040305160e0907120209070c12020d1403040203030d0213030609050a0213020a0f08180313060206130510110d1505150901081303090305120c100b031f1b03 70
    0xa840c01c00c1080d4503198900e11039140c0d0280c3c0036110038000c0c0441c40c080923180450089403c9005414a075000d5207954580b0a9550445a20034025034841202100c116511260056180e07403074024250039418a0703800203843c3e1068449801b255134000c02c3c0c2100b01034800031524000d41d40084200301500240c41d1144e200c1e0001082603200301c8001c1c40c14003c402c828000c03206080d0b440ea0302c00106441d01602035482c004060500440840d21015817024044104000e140d44010300c84007d012500d041002480c01c44000d0403080310700207008407a00000d400140c030325101c102d1100c5c04980861902c44040c4c0c64001c094801c0b2500c1c3c01e10070014032003111600c2c0901612001c2e281d66071442c030100070600f00c1e48580441d16002403500d07000554213080c2500a144070611918109801559a882c0c0d5850280d2184850340790200000f0701c251003040400c112032105988441c10b0000f2400f4000003629a2840b440100d441d01d00190546050155a400780950000c860306141c101c1c001e5540040061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 851263992 1250 851262742 851262749
    0x19030306030b01092c030d020a0306090b0337020d150c030204050a030303050c30010504110d0e07031b0f09090803010b2203140105070f050f0c0304030516 68
    0x218400300002c110301105000b40d481ca800d1518108944546080c1d481602c0c0b501c050080085c1d010901c00201c0203da540010800c03441c1c941d5010644034103099640048495a000311440f940c0a2480881d9140800340a40080c24800a25540010000700b0101d01604020002580301c0c0200380300c102040001c1c40c81807090409800c0805c003517185510107800724482e038020076910005250302000004c0c4650031803988255495507003410316080c0d40524005001c241c17082c2e40307a0401d210307480030305140742c004250040404403005e00038400d203d96202410311810f5980c5040585070490f6110841c0e08200d00001141d001c4500100808000e004141c10042400b070b0800402a03140000b54407a5240610550b0300c2d00720f0000c910710303483e104444240341d1020040c02e1401e2072032050001c0d410051026540254001da00c1c20301e40e02005031249086900c01002c11051040c81c1003901c901075030102c16904100c0041d820f9560307075404494050301d1030083d070780000c0c000d2003121010352103440ba07520703a00d088 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 851265242 1250 851263992 851264003
    0x30d1b0210080a0b030c1f21050105120a020901030f08070f080904150b030a050618010909020f180711030705070b0a0e240304020f0d030e090105180c0304051903030603 74
    0x540e15000e00f015155841c0c1080b0307e901a0074050b00280c3c090f00d603031210790708440741c0c101090200c18260f081111511030744260882c6a0742e840041001d41400710b0107001c01d013907610244c8a414115030028900a6040c08060095200c8151003000c224003d0200d4400b20f800018812000040c3d02d032000c45944480e0b00580a45e080c010852140082500e0120589800206090540d1b40d10002c00b002814003c1901d94895948005506038043d22400540a810120404513900140e40103021000394541d060303c0c00b6240441000140311480c881e215000107151a100e0032010100040a01c2c501580d800502980611540041c600e0074000c0246041851610341145901c00d40c006c115012a12101104070110301041400070315200f6001164003610082c0030134005a4030364040ba200100c50001200412004000401079203054011240100f03c10be401801030380100300312101008014169080e09900030010904016050055415403c0c84810f01c0d54000d825041c000d021304000e1100740c90 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 851266492 1250 851265242 851265251
    0x30b09090604050c10020304030615030212010507140f1218030a020f0c040c14090d0602070305030a06080303010501050d0e190c0e16080705070213020d06030b1005030d1b0210080a 79
    0x2000e08020341402805c02140c1c0103103040a2460b00c6482c0a08940840310f48445032070318001c00184e9444000d0820060302c5000014903141080010700302240001444240360418409004014000380c200c942074286110b0282da41c1d00c8908420111062031203500d4050300001c143c0b03070f0410b580051901c2600c04414215007003240c250003170200f10b0312010746000028002d160614142000c0a004155508000d0040e95a4010a444100c12600124011400580000b09000d04101d02d40200005080074002951540d4900400039150307101f00b12441d82100c0e115030f040042010180541c0c4000001c2008540740300540b45001e0114010303d00030000000305480229680318584d0548111103a40c5454505050319001420303070780b80c1c214900481e44030411020980e07031602c440c0003070141d54140d030601180403420352804501d0300b100180440d106040b800c10402003650700160700501901c3c40e00f00424001880b075948000c81c10860000f03900003044101404010b580035a070584504e01c1140b0800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 851267742 1250 851266492 851266513
    0x513020f2101270b0126060a0b0102010f06210212030f040602060a061401111f060626130c03060203011d0a09050c01120609050103111c0f0b0403030b0909060405 71
    0x348010f820a0020305800010030040c0301d181207540c14416000c680720400501d0380d140348000d40c500003046403069540c4d43c803040c2c15111940c0902550820700383e0382500b03108084c1010940160713010748840b540380d1100010880d40945d01d135502d0901102e0355080560f41c3c0d501454010010340d5000d84200b030014424200010f11180e01486000c05403080780d4410391110701098011034214007100700300113507030182d128848204902d0401d08100151682c1d404145a40340c00e1014004004078400040c03444030240c9590200c40e90701e0280c9070720484051b11981110424105103c42001641000b480c0504c0000040380802e204407030010261a41b00440c4845e0741e0b09540c0c0c1023515058180181164421101e0405545c05a07400b61101c540c0c040000409139070b036a081d103099440c02c4c3d2041d41d0003400020740b104281821b203800540c0320488800c500c0911415984c8090841c900d00c4050305955009001ca410136100740c20042000b900200004040d082c03690380c40791200343c20740701217031f2902c40c80000c00f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 851268992 1250 851267742 851267801
    0x50616020f010c0b13021f0207080f030c030322140a0c1a030f04020301151d1605040b0705120301170d020d02030d09050a05031b07090513020f2101 65
    0x4a4020381c8007040103134680b030307004400601c52102802282e010002580440341544810310145248505900030460285401031003400d21290814800d85c5030410018007490020000842c0e42240c56035800800e5000c1c10100d500d0006004030006000c900c41801d07031601a1800213080041501640c083d10074070f42c1d201c04d170703004004500c1901001107109100003880c2c150a1484a6880b9001400203d046c00090712001031121030f80c2c100c000a292002403000c82240381d0445d00d41d00550050000400700401e2001415030f00a500c5922082c1c4e00010b4800100072082c80805074803d10410703007580743e50b103d0304158040074040315440702070300c03c0c1e030f690743c40e510310000710300744106056000745241c055403400601c00307040b2000c01650944991b12030070001031810801003004283c40c403a6650f044000b41d800c40d00b410280c1c3e110a01c11360500c0f050000140748d50304a05001641103440052035003e48000c00d051001a2041041703070002d0f00080e920995040d04184642c1030841d040b050f11480c00400c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 851270242 1250 851268992 851269007
    0xa0f320108010302010513081608100905210409110309010c080609061c0510050f01080606090f0a0b030a0c080709021309020703050706050c04031e2406050616020f01 73
    0xa150005050900400140d406000104800119010442031458540382d44130f00d406004407168003150640c98040200c88020701c045054001004420312241c2d2260b141d0aa80356000362000c1c410001241c10041c1c90002e80b01102c000b001c140300248011a80e003062000903070000c07500d801c059402d02da01c003103100303120b1805140f060800400244c456104d120620100481b800b0210070050700e050891804141c0c104501512452481c00c081030038a00f00005d5100503a0680c40b82a103540403205100301d9644400250742e1182381488a03240a131b840038440e0f4082d044403411a60180146210241409140d03038556041c1c1d04403008031003940e0b41d00c8026000301e1080e0000910105d141c64414480b84806800500016000740fa0050070104943c6602040310340030b441ca0140c01c04001410001c1003140c40307005981149134a00d8128120154443c0302c00004038a058041500034816440c2540c403013a845207014100242c103440d100c2d80c1c50740b5607021206d05500142d1081103004014480f40d8815a070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 851271492 1250 851270242 851270339
    0x60801171c03020a1701090c1119020108130b090c1f0804020d050a020315061009080c040c201b0409150b060904050a090605070216030209060a0f 64
    0x4008071128140500310002d40180341d00c0400c1105441d603100d1480714010b1400c0c0071340320b00310f80040d001e0080080586228031604095015800c05036022458080049006000c282c080c01c2021079540e81200b03080d181f148180004040600d504c05000c1c02000008107a0301001d42990041d0342040d00c4e07820441c903c81820400c1c0c0004401e0b0b0000f50041c1031030301c1e01d00344143c400d10032030340c0c9034841e0380c002800d086501b40c1560703003054140708000381c0b0718007504001c1044d800c9040180e4403609001804d03864899468180d8000c03525a504000344500c00d501046800b641805c2401e0b03040030340c00225031964a421030010031044095100e1091b80303403511a0740c9210340d104042d0000841a014541d0240454913560341c3d11032014000100309495600845104002005000501055a24040040320b0000d000310f011580700c44401d104140c1c15915003016240c0480e010452640c900313002503583d1105812580c0005800f00001419241040a41040480c00c8036850502e144001ca0316644c88800d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 851272742 1250 851271492 851271523
    0x1103090c0607080d1b120b0109091a0a0602011e0c210204050306131e15020c0703080a18060e0d0b06030f0a11010f080c3106080117 58
    0x500006914001c001007500c1c500c00c1901da800c01c0c0643c0e52000448445400254005991180c81028030340e11901070b00785c202102c0c408010a03d05000000d015401034007581d041c80b595900040c0c680c59001802d03541000004241c000c1da07a07100e03c03000340a424951252100380f00c10000a12600c103143c003c7c900749040940d2440d00025241c46140e03413000d450020095000d900300000316946c1c4081c000280b240340003640c5050310700c0141c5440199442c0503450f55103d044403680c05000500c0b40042800b8000342c1010240c0c0300c50310300805504000c0142e000502800d4006800044550404d051029000142883e031143c1542c075501a140544100c02042d03100766062032030000103400101c2d09401000c050201d6040310040c16629280130419a010394595580c199000302c81c2d030340900184d40d8101a850402e05900340300f10094524054000102011074050500c0c3c80c6900d008600c1502800240516040312581c03048041c290200030301800007601900d100c8040c841c4000200b10040c0c02c80c1c103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 851273992 1250 851272742 851272753
    0x5010e0a1202010e12070b0405011214011514040914010b0a080a1a06030f09060a020a0207031e0b04150605060a080406150b040e01050a090c020d0c03050f0301030503030a110309 78
    0x30b03030044590140d80200540c0c00003845021201d050010080f10010301021001d0954071400c14001604101e03550650350001030414290030741c0907a207005114115030108240d845085041041507524120a210204120402040000d0000100c0d0085241101100b5081e925a40c0382d019140a0780300344010100070610500204024600d594040410f103103c200305100700f4400e044c0050f5840e07201b0384014003101101014058201801c1c4000d0f508503074030007000c61a007064240040d440c1e442600c0302070409400d0045401480d0f6202000a2031660302c15801281441e06182050001843d00d02d050a00c82c9810408155800d00034120349500d032494460914030342e9559507c202510f040038210710a40f98030704000400c2d006850151000c4c15035180195443d40c142002d22071110300b280e02201515090020b55800d058001c22000c0012400345000f1910380e82034101075816204218801c94611030000000090050100265004050780d003420721001e610031544c041c0c03500054074505000d4020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 851275242 1250 851273992 851274029
    0xb01080403050705030405040c030e1612080c10091b06020604020a090f0b0402191103040b0403260a030e012003070e130528020406080c0c01180c05010e0a 68
    0x20300d003d81265440764040300c0c64030f41c40ba800700d03041c0d03002400c0c0302000c00d8840c07880c1803020006000401200c0003c948003403001c0d01d86807102140038070a40300603003c144001444821042c003882020001c082c4544240030b81c841c0340c94620802c001079135004410074601c08001c80c4072440803400030b0043c0d40041c1415a4242400b8200f0024102c078440c0d0070740301d503450601c1a03168070340307002074441201c04c4111400b0001110350301900d0144018149803081c0c00070003040c881d01364810196026250019078220040300703561003454908038401201c028801d00450507008083e810382004103030100400090020554007105038103036405004454103e0413050000440d898450007000010040003000d00d03082e03031081c1648a0841d9400d880700144001a000c0e80000000700b078518140b02c1c20f2000c021440c2616004000700301d00005003d8584514000481c602c0e15442508145484170000c002d1241c869070600e4076483e0341845119070760200f42c00d440f42ca0801d1901d9002803080300d02c0c240014049040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 851276492 1250 851275242 851275247
    0x15030c0906120e0a110a05040504200d0c0902070c140d080c010b040e0a14030f16030e061809070207270204121101170112030c170d050a0f0b01080403 66
    0x6440704020b081c10760352505003640d82d0040141000c10741c00ba01000182e00781d198244001803100740c21441c001ca0504003844001242900c0c02d03000c070802c4e840e0b413082104001001644003030429001924810700070301d001c140d8002e150300510140744079207001c484450707a501d61a500d562070201059480786031f000c90304010078041d00041001c980e80d580001100d02c0a0800101111075004000c081540132440c11020042e10701b8281d44a10100ca0007181403403103510b19a025032040318215060384e0f4030841c90008150080d40b20341d62020380207018503110450b4410407400c641250301510700c1003030711602160685002060390415501d1101c521034200118021080313110841259004500b075080000180101d9060144110789210f004035902c0f40c0750a40c001021031505803003411101190200401600441c40c1c0c10842065050511108000d00c80c10310007640c440c02c5812450040000a4501000003950b020314461608910200444190012004100c0701c101d80c15a01040044000c503010a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 851277742 1250 851276492 851276507
    0x806011b06090c0b040936060f020f07110918030703080c090a080a11042d1104091d01050f0601200d08071e020714010e12030415030c0906 61
    0x7400f03411420052952003018900704c0e805036004c04a290740e0344000e00e2919401c540d1001d81c0076034480980401040058816000010403032000389125511982c00e0300071030168050301d681c5081c01c103080d9252402030800302c51421090303420703c1c86980f04100041c11520a007a5239a00c0e01005c5000350305000480c1c1d4151215000500884507002c010f1115541e01c4e030b0784a420b4006000880080c000c500500d140020464509021240c86070b0308140c070492030060725080d11500d548418070100d19150501005200500e220900510030a4002902041e04000354100e010581082c00341841c40c4442c64421a003201c60680340d540da050b0103100861800e40c41520015403e2204804440040d40f42003803407032400c11160280004180200f00b0407401d1600144081051443c080d0a09200072071f041e0004c0d00d404690044d04251032031050120040c0e4460160714403001c0014190301d00c10342e020000e032a90fa80040c030500880c3c20300707940344001103882070050148003c007035240c9010715070400d5401e45418 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 851278992 1250 851277742 851277761
    0xc0a0b0a1805190314010b030307020402180d2009101202151c05090f070b0d110706060317130b0304032c0102011d2d0708030a0806011b06 61
    0x2031041e040480c903607550303021060b04a00380e0000f450086145141030159021a003407480c2003a49030601c11402c64902008840303007a0344c101c50043ea51721120402400c4e00502c0100550007040c0c5002c1607040044202c20091a9142c00440c40e00a91442040114003130341190351074031016110508114113840440c501131082c2c40104829084038080341c40403583c0d00058110781c24600c445c444454070b61168811684c100324009d010b01880348420046503501c41c01486108040d44001516182d0350b0302d507901c0500c0c02c0c0b941c1070401e642d4001c00d0805030003401e0305d400162911094041c0c82d0211502d400c0481d008103551501c101e041c0d900c2c0940c111050381009000390144410b440c814550744134101410010350142d040600900b2200c0c100080c216031301107140081d1005034007003080c3c0c10f40001480c510034284446d891801c0c4100c00c0360040d04841c002d86c416210384a001000300c0c10742404400f600804010783e65840307403565003600450310102a412600b000711041c7c2c0c2c601000c40d241d40c10041d0391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 851280242 1250 851278992 851279027
    0x1050708070201031b05090f010c03051c020408160801050f040b040b1b210c0301060516110a30020a090c020c030d0e041d030a050d0902040609060302030c0a0b0a 71
    0x103403140d1030515445441780c40c80c2c100024000a68600c3c3d43c40c00d107a281014034020b1910310550340341990090003900c119410554803030031820f8800c0e95101c3d80d03011036015044100a5a030280e445502019800c105d5000d0000154202000108201e5200c50443c4c41141c0040d214020340d00e494076030020058016015417100c222030000e5092156132400200007210041940103ea401520740120b0b12003000361846401e44070400c0100050340c1d03c0802d80f03900038800340050340510024542f4040442c1149416500f00d5040240002d405050003010300351150f9201c0d00c444100f00c881065000f0101441700290b00507607030507091080c10b50b16813020f400b0207060f004680366180800d00091425001413424000240c00041d98400c0342480d01031483c40c2e2404540c0c080d294041e1062440d101d014892201041000106008080d00c5090708a0450150050000c0103169101c513407010150405000907030007440b81210340389103820040000012551b088001c5070401c0303036022003141d09104038007a0452 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 851281492 1250 851280242 851280251
    0x41110020703020d0c180b0120070f06030e0601090b01080103060c030e120c0f01051501052b06051c030c02040b030109020a2d0e010b1308010c030f18020105070807020103 75
    0x1610b81354040c540b01ca01490071001c1d042c1c5407140151110398400c0130403407014208404550b00d6600030b464003404500001c0d002a1a074111402140b4009842e40446581a46000005011501507002c2c8580351540029212240c0c1c8943c0d40d1029174928150150009504100404c0802c05a40c0040b8642200e4070b000310f05aa00c02400a15010740e8154542c075000c00054030001201e401c001c5825400c0b1000000d0225251503401550f0380607000390128140800050a41a0f003648050701109804c40c0e1f601c0d51407840c1e126410740740104603901070a03000b017500e002c0d4074004800d002291102d0030b03031561310310261030301950a00002c1c0000c0d0071000e4166403124456001030752101c0020003c1d124080300c445403e90804010058980400c1c200c808210b000b9400348000c000d500c640c9810b484401e82c1031603554185400c10441e402055000d00300d0b0b5484c140f22400040d40c582c01100c00b140b0030b00f00901150010100c500001850300d180240410010804c280006800e1000751440c140141000075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 851282742 1250 851281492 851281499
    0xb010509160315261e12030901150314120f18030c060d1a150703051c0c110d11100e0319120522060905010615030c0212030411100207 59
    0x144c0b0014500d4100070030409440000d01801d41c01c0040d0240131710104064024120511407003600c850b0320380a1640e00c00c40002c0050400c01c02500f1440c0400031502190044560700c0c10900b90107141c0132425481400390740c0140844250400644400340001c0d004103103014200808808100c2401a04e80d40600076802114030a9486001800d0b801c3c1014102144901c54948201410454200b11521411201100807200001d00c0c3c1510060ba5050a0441d40d411514800006002c5051284d9100a0802c1120414158003016503c0744120420403144020001c40054800c0a000f400703068899005011a41412400e9009a0303124000c034010b50f4506040c1e0511005d1202c0c0e41043c0d54042a105290510028600d00c11035a00034203d61011100d00340c0d001100300ca0900d428000b42519032641044400e0090030b600030b00003050070071401d20001c1061403018000d007503048060400360056981c518555140f03542104e124640c044080050200c5103030820640f041d440c000c1c002180725400012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 851283992 1250 851282742 851282759
    0x4050709020415200307021c05061003140105160c03031425030b0d0b060f0315060a0e0105030a02010513151205070215010510021011070b010509160315 67
    0x34400303007a60100e82543c000403040080c0500004c82441c001400002c4e00701510004040291002e83da8100e600c2e41042c0380d4003010107079154014402501d14028002846081120120354100b120701c85d000c40100c61019081c42d070f0803036078121403207210000d0115206620030301c1018500001446800d0019151807520650701400c0c000720b42410711480d0280c48400d0703100c00d0506d440c1c01082c0b50316003400001465000303d03440305646240106403079400004a091590f80f008514078102c40601104d0f02d0303a080000b040e5441c1001d413881e03401240104008143c850a104205041e514080d0080402860316801183c56910110b840d048445103104041018840e840344601400b599665441156050360b0303060742101d2026110406644c0100d1052140e05003442c800c40c1125000c680e05419858200c8050382062158010143c0045c540000e0a00c00f040c0c6002429840307004001800117030707884505000c440038054030000c1599640e49003542e800340c40707034005030307011001425640444d82d600c1044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 851285242 1250 851283992 851283997
    0x20a05010f05010f17071505040e04060f0b0303090a03080f04170303090d09050d020f06041805090606010c0b0a05070216081f020901050708030c04120c0602060106030212010e0405070902 82
    0x1071848544900040041064100c200f03009008020190700c0286070fa981d09941e00c00140c80360700c0f000c90401030344c0132a40303000b00161001891508115502860185840002800c030341c2d80c480c582a01e884e0104915042c00015140041d03c050502c0f00f0490640d00d42e0801e50b000b0754003600307507e0700400000c20707000005040e401c0448104002191681860030b000c1d42000701c00031a0404000300c540c000c020b641d48007944014190b405441810b0b2802c0740000ac10f5061181c1c1d000030103102942c9440d440000d03c40d5101521898a10080c1d90b159240d82c030044808484c14140036140e80884404524506100e0b400150071640600480300000203100c450701003103401b94041d181c1604161104070307654280b4088241c1c41c1244100c214a02101c01c0c0018007503004010025000603004800a1204034410086502502103051210062440c9203091201c03a60140954001800303040000201207010703001b030b03850104028001d10a66030800d41c8008030080f0040054400b40305981c800250b51060740b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 851286492 1250 851285242 851285261
    0x90609120206041a04120509210f0c030706020303040b10050306041a06040b0604060309080c01050c0714030702060409020a1e0201150e06090106080603030d020f0d06120b0412020a0501 81
    0x542050703d0316060504125034243d11076a111004c0c04200000940c60080c3c0801c141c2050410136250203080003c5140702414080b000b5000b03011041640301542c000a0355217080740544110307250110204145a180c45092040a001d6401440814006074484400c9079000d00796059040403282d480001925101c800c1c0c0d415903509250300340c1701d007843d202c0c164500c1d032004065a0030710181088501051491240744664400c1580e078a8040d07081108980481f1805840ca0000b4051030508071307003058083d400300c0c20485035283c445e588142c003040c022041d070301e540d1f030018011800c103458541003201039800003106004101da225117481d0344001181034000d900c412a400040c51081c18011026901020303000740b010600b40038104000b50b5510b0000605583c0c403454107110503210765000c070f0301d0743c040c1c0c0d80c00c4441d05002180c003026503120300e80030704054200d00c001401981d580d4100701c440c01034400c1c00549880d814400180100320011100001c190440c0704444525649032246800c4030b00000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 851287742 1250 851286492 851286497
    0x10203010e2d0610020a021206060111061b180306070c0210030e120c0a0c03080304030f0309050318030709060902040905060f060a0f0e220e0102130909060912 70
    0x105000c0e8a5454050060555080392031400760702c044240341c1c0c0d048403001041c0611450300404011291482030005151455019024400740400c1191054444004617900c5000880603405902544000944503000d09910503c41840c10070440340b94626500448a032025020142c60100041e04c040284138444c0c0c81d2903569200323413420f900c100007090180c011134404050803e1380c40746410700040f8148030b080c14500881c948c0d8400c2044100d003041c90a00010304102442400001801207000085100d0742c807076501d440042da2101c00035002c440d90410041e20304c1e842445814030030300003409070341c840c1d210040031180d8950741d03440b014040d070b030380d50b00015401078010400704580801e80c021b0581200040311041000040d40c0c0205a03107024040041040046a800e0140400d004044401c864031000c0d0220710915030070055000d41090855108104520701003c0d500442c5c03040c429030341c1c0e2607480349030b43c031200d0300c0d0071142c40140201400a481d150b41c0c68100c4000580300b00a030320307003004c120b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 851288992 1250 851287742 851287769
    0x301110318010e03030606180a090e06041e0f02010c050c1905040f06030809060d0b04050a02300a020a0201060f030f02240702010318060614030706091d060d0501020301 74
    0x1c58656094480f8154a55800d6100380305004180d41c800741a281444c0c01610481c0704811240e0015540c050315030300c111070b6076140003455050701a001c103083c1d105500a2000c080075413148001048040e45008004c0c01101c40c0c1a001401984500303145848030b4010821100c280c10094001014003685441c8006c0c011a203034000c0102d07003094004c041c0fa0070301260b0104001451a12901c1381071040424941c031501000407044c3e44050340d50700c4242e070054040c0c41005685402c400040c0203504c07983e142d2030003007a50b2014124862401c03211408410301094094500d4480080c4880a5002041d50381c096540300c03600030440b801166076900081d03000b20031344104c40390b40d80188511038001d02d0383c0c0b004402801c12905034140300380c800c1344c1f0031a5081ca0009000f03110032541c004504840301c0000d0000d418501c2c006551042202010901c0f01e04030142c40407103a0310802a035a15415210300d080050312204100180000801a03076440039010b0020307644c1307001980d500f0782240c2c000d0b0070070304148415 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 851290242 1250 851288992 851289031
    0xc020a0f080d090803030a0b01120212191a1009080613030f090614030c04170601080c040e15100302060706051005040603021e1203120f13030f050903011103 69
    0x10020501c0ba4045400c1c503005442c14200032076101c1c0f0000700080c0d4455112411400503900c00c4074400031403519a0021525001d40749803942e5100c4040e00d45c0a07000c505000d12030100c441521810b03904080030078026402036075640c144514000d60004050910003801000140124244259449401540004080c001040c41e001c0c4c0040001c0c01c4000c00c10120000500005400047c0c40c0d00c5c90440c070007016100d50b9481061581e900c00c0b500f020a0b456005142e00c3c061060000780e07241030f50008c0e003d44000c11164800e02c01103031401c070410002c50340295200a0200098107181e50810a14240e41c4c980c2134980d00800d003694031503242141c04560f983d040003405d142c01c640700005044215030502440386141c00080c0745a903058645501840306040c51440ca503103c0104810b0b0086030b00070380f620303403050f1591038420384011101c41e00d00c8258500020604203a50403003503986903264aa19100c1e820317000c000c0b2130761303042040520f070035658a102d5070305c10700800d901441c8554607040350381c5005242e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 851291492 1250 851290242 851290259
    0x1c020109061d060109020c032701120c210b120f0601060206100b1b0f0109020301060906050a060809010902030625090e070509041503080406091509030204020a0c020a0f 74
    0x6280103802c6450b101181a540040c0d4041803d504441c01c000300561101609100103055125161050b4090ba12480003902c84100c203101403170070f003003090720782d0400d80c070380c10405a09641a00d03110b400000d45c040030008050b07807100c1540308039403c5000d0026400c0c2c1d00c1800314440c01c580c40283c4401e41d2040e0000d14840008100f52805040c11384013038817070360074810f0b00703003945502a0141e18403024022620100c160315402c841403542c000f02007202c1038081c0e101c980350300a240d500302c02e90084d42032400101c1c2e02d102e240105011030b071015040c2140c1d18580681225040406031030320345c242d504d0b040040c0260398200841406007003920340c80310f0780c035000e41e01c13101c005400041540b003400038004042103204400b88560b50701135081d0500c103a03118180310006005007042c0c601300c101c86031805004410b0100d050081d0040c2c40c000d4488543d4151200e07641c101c076048400000d40012140d0905100505003a000b51003515460f0609240c2607400d50b00142206078107400001c2482c0300c802d0100310888 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 851292742 1250 851291492 851291501
    0x30406030207170403110f1801180f02040b0d05091905150619050405070203070b09010b0f0a0b0a050d0219020c03060c070c0314030f0a0203041e0e070309051c02010906 74
    0x240d143e098249054595540c0005c1d03034010b500e4551081440200e40c41c2e6517158051a084a4511401840340d1580c40d1a0740c1c4000450540c8540c21951501c010b01050701120720071201030354200e0310b015040440c229010005403600518056407402000d04003118059a44030310302040b44510f0160560320340003100c0c800d6a15000340341c2031088121034018040400301c107406c0e105a40c4144c0380400c0603030341c58205078510310031114002d060500110801134840c030194080c1c0c101241c221207903217170702c26048100440800310b4042c41d61800401c0140007580e0f8082c00080160303003549000542400313540300003211549094031051002da040800500c00905e030900000c1d90280003009401e08013051501c405400e40814040100f03546c800d040c030b142d401e4508105407100039a2500302c01c1d5507540030a100070740f01d030441e1040c8596802030b110f0f80c1e01682100b102c040182c0c3c000140c40c050365a2a0300003100905038890054596001e40e40628030405001d036030400c000c400f5500040b4076122075140038011203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 851293992 1250 851292742 851292773
    0x3032503050f04060b04060812040305120328181109010603200d0b040501031208100e0a090c0f080106030b01120b04030f021009030801050103050723070311030406030207 75
    0x9490801002030781c030300340b14801d40c0040c0c00c00c50000c0c904006102080003800c103900400d815105510f44440b0709011200140140c074420b1b001e1b07a80d201448040700c0928001694186030349030040c10100317210100c040c01d0f0290711242c00c1c40802c00b035981000841ca0300440b40010f8840b0042c0d01c21071032641c2060b51001d03005050174502000a100d00140051560404a47c08400c0d55400142c03111541c00e60740040c1200080141300708035035603480c500814000310100d11813020840e01000500c591100800d80400c40c1d40d40d8203201340542d1414070b94002481022012142d1b0b0101d20b0001c00c0389041d003804c0308081d01c0120000162070341141410702404005a200800c03032800c04094500048542c003089030441d606003403004240203900d206a0030000c01d00c1d01912030500c0d1540d07000c02c3c50f9000303015034100c0f0400e803400c01150b21820300440b44c041c98804840304c004200280d0811244100c001001d10a00a1401031008040b01c40c1136400d540c0240d0001e00000e80100c0c0300814403401d416240c002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 851295242 1250 851293992 851293997
    0x405060708010b0a0f14040f03020a0e041211160905060411090d030f111f050a050f010513020d05012309040302070e180307120207060e0d06021b030325 67
    0x70390316204240d10070707210341002c120420201c00c1078600f0050244103d0801d60801450103610303a525034180400d40c207030510040e031007034000f00c000140c903900520b241806580c100300800c911954040041d00c040d0041460301c0f14910030764502c031480c1c482c17221203440600b424040c040340d5810480100001d490440c1c1400308960003c000805042d9103106036a02400c0e414145258680b40c0c0600c141e801140c041c00c2c00c0720074000c44183e0400451418410a2104104582086182c4845807101d0031600b0071245030a005000d080148001c2c0781c0015401c22546c0101405880c141c0b04000c1c1400307460082c0d11600c4804198004500c018000c0041440c85201c151124000c500c1d01e620b00956031605445640110030f230841c04503040f03440781215103031245c4c0e05604481d135600d4549420581d10f60400d007040d00600400402281d01403141c20755207080e606c010070241e030000c00c0341c8424000b03500ae10500110a00d8001c50108000810f20145120782d038080c40101c1c45081030008415010090b200300e004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 851296492 1250 851295242 851295257
    0xf0612040b0603161e05030a0812071719020c0129061201090e07210b0a02040b04050f12010c0512090616050c011e020702040f02090f0105032a0304050607 68
    0x1001042c2d90902d01101c010141e800300c0303800010f45c02c03082c80d2502c0c0c012a426010b01200401405000f83c000c3c0266159101170f01701580d51082c0c00c450b00d4200c21214000c010740300001c6080c10508100001700100031a41c01480c00e00c0c000c1e00f0a08540c1d41d01081041010f0f0074240300c0c40105407408800c0b0000090358140d01d804c0d08466180c1e9030b00d405000d01c000060351031007034100c42c2908200c07007800361044566101c941c00c00d051042940c141b902c001203404806400019040022500940b000c46d0f1080d09403c0c2401e0400f010441215007000e81560043c0c0c4407000d5006c4080240a1301c0581c4113652134040d40c0701d070f034902c0c101c03042d00005200c900507a01050600003010002d10444c2d90744800c5140403520b0f000082030700c5000d48035078510200e00c55080d0f0101080c220f81303540100190380c401c031317010001280c070500e0310004e81c06084082a071140a1402c0800b107540510000c541c440145080c1e95200101d4007450bc0e200841100c02c40c0081e600172003040b040001c20800396802c03034090705050701e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 851297742 1250 851296492 851296513
    0x50723011103071e0c030f061b0c020102070501050d020706020d0603140616080601021f020309070e360607020a06050105040b030703030f110f2b0801090504020f0612040b0603 77
    0xb014180030580d13282a0f0415102c44014800b286200001842d44194120350544c500c2c10018058140800c400c1500e221707130780c00000228000d0011007081607068005c0e10301c0034900401501c0782d800140000400307a40810040340011421310041c80101c1d0014000a0442d05609003480600e001d80355003902980448248928100a45482c240c200300e00e1030140c202d6594013004130308000d0003c418800d03010f500711900045001c2c503005988212030160848004031707a90691000071600a0300c840350148603c1c04081300c00504010414a030700c5095101809906100c4110345c60600c003141e0500c010380045912104100300c40c0601401042c041380c091020060303820009489a220b0700c0000c0911040e60f2841c10800c1c0030700b050301c4412400300b0a50f4a034500b20903191b625009081c202d40c00e4401d45207081d41c2c0ea4507030006e1542248580e0354490025038203001040004240c060000d03a44100e81d51039107a4950760702c100030f1440001070340500302e1905092a01104511024141500c41d4110210f840c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 851298992 1250 851297742 851297753
    0x3080601180302130e0f0a140a03170604020f0d060e060603040b15040b0d1a0117061303030f0519270204150803130602070f030206040e0405072301110307 68
    0x1075003680c0d011198038128035180481c1c0002031030424582c80003402180b03007043c844007012420700a46030041080603c2228542c2c84c060303e86d0700740400207010445801400e803924107026041c607032103000940018601000c0880c60102a00092140a241c1d40c4950051042e184180d1109400c500d066504a0540c2415558a810303121700134101c940e64608424100610b5540b074100d1156008042c3c030002c0b1040b0a41841800c0050b051030002090001c01c0c00082d1000c0d070302c1c156a4010f4a900082c051684582226000c90300042c003050b400c05850b000004035020091150b18017500c0c60000c1d2400001aa4901006a0700d120405200102240d4803104500d407241001803c0164101c1d00098068500400914241c1c43d5400c12000c40c44042030b1240700151b503030000800d03160700b6022502c1103a501c4071418140d25490200a400080500080007881c0c03562120310740040c03151080d1080b06403240590701d4180021000800c19a002a08010700c55030008990000d42c01800050351820712030b0f8454 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 851300242 1250 851298992 851299037
    0x9031e0f0f1b01020123060a1809020f0904020a17030409060b071407060801051201020705070305030a0909050402010504060c0302010b102316170403051902273603030403080601 78
    0x8a0b442929400000c05a613100e00a81018244106622740e44020380d020f0b0100030300f4848022405180800b076a80e8a9181429207103120f154002c00c500340c0305007012840140c050905910404c0d501c410312000c10300141a000e844003600d014880c80361074100a0901c00326204680308506055085902c0c203101c850740c07241c91a415524261082c800071a40580500e00a10035003401600a0181410100401c80044020200d000d03490356003003801501c0fa800c07441110411384000b0302051042004002c1a4040d120b848a50ba0080c00005a80c8a021001c52100d00b50056010009803034240d0880994504100400c140103170490818100701701d000701183c02440721310000d081e0f145411540c0540f40c8140703007110092365003d029180380610022500c0c0442c8007040e0124403d1507401c010003000f60075840d600303000c003808080301c00b6a5203a1034102040c1c2507120600d12070140b4411807401500780c000080c40c2511810300001c55a0f46014180244802ca0241041d030400c9440401881c2584050a6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 851301492 1250 851300242 851300291
    0xa050105030f0601082211090603300c150601030f02120606090f060a0c0506070c030c030e04060b1c0f110d36060506030309031e0f0f1b010201 63
    0x7020320340d030b4544580f40042000180081000c6c51542c07140c0c0001c101c60080c1030803d50005503504c2205840f4141016107070300a06505104060a252009402891002e000232140029102403458040500d65403401c05034040d5002442d81c001c00709203c1e055906129041d0101602c010450414807011004400d03281b014020901c0380e000410349100c00d030703035081c80481d90210081c51590388091090003e0310041041c170781602d50340034410015025070f015400381d007001030b81070351200c088810303559040e1964070b41c440146400907078555002c130f0854000c0c0024010300d100048188054a092611314090791840b80b1400060741c02c065042c3c5070501e0000c2034440d0685060320120f202a10300b04040800196429030226403140d5180c800e032443c4c01c0680c2421114001c0748203001607620001895903900c2555511034150380b010704018904481d10303d82c2151418400155034015603041c0d007151402e0040c1c0300d0b0824035008041000040c1c15504a4400d5a00e02800280500d84507542c91030b03100345066a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 851302742 1250 851301492 851301497
    0x5190503330925020601150509154014010203030402150c0d052205210f01020f0301051906050f090111010c11011401050604030f230c0a050105030f0601 67
    0x402242d00995800d0b02180795030300640522416120f030b810300a6a6641c203100384910600c1c999148180544210221001c42e00080c000024030840d02c45840c1ca264401500401e011411001f844403d03054010010b0303888056100c0e4480f4036440325009804030380c09078002d0a05144030144201a030360080203490703119070101c4600a400d0f0001b03440c500c0f90311a00340007200c03500880200d110520380010103415035405000c690b04508070b407000c8100f0882000c0c01031540c4502d400000161805400400002000c458000da0314442c102a4420303080e0380101900b1604100c020005100b036082c680354119000c00c460410110040c94076001608078401d01e120700480240005d01038609902400059100911041c000c204a4411041c014807020203140a42169400c01c83c0c185110b03040b10030090f0686000504661416207195a002c0508840c80070440e089180e00c50000fa44030180c034840c910052145003c0c21280c409802000500009900401e051040c207206001c0d4011000d0f50081d440b80b400e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 851303992 1250 851302742 851302759
    0x51003090c0e04050d0f0203090310180206030f06040c02060411010804140f0105010303030518070e062202030108010609050f06010305092104080d2303070519050333 73
    0x90410400c21401c5800c103031556a112418482000030010b1150182401d540e41d40551032242003040761030348940d041459241d40080d440f2595464142e000741c080340d0140c102d07856100000e5000c00d520340c0080b00e4801d01303800c02a04010386400d041c06078031281460380c406030103581351035074410014030070b80600c0d90b04110180c00060100700e05064140141d900760750840b0601d5200503000c601030701c0309000890020381000003042c4809003d0000080f0740e414400070f403c4a900304144100860740c0100b8140c2e000c1e1544107008007124a140e0400700440daa128003680e01d40c1461002d60940340107512600c506454102082560740c08480e8664010307009107400b081039204c040030240380c0401041c0464111040400f92440c0101200060044803d0b22003955818901c0150684200f8034000e00302c1002110070043c2d84440e201a00219400f1131582409401c0444140e056040c00581108440c0822800001c3c4100c8040821a040100004025070305032113408003041204d190b05120b10328002c8080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 851305242 1250 851303992 851304011
    0xb130608010b040e06180108241005040e07090c02031b0307110415030b160306242123180c100c020d0609120201060317071104050103032106051003 65
    0x40d00110388051981c3c001b80151561545080e50b1511b407002c041c00002107086a0358010224070400c61440741c2c00a04034019901d1400d4244000b51030101c48440280c0200c003004210000f10744031742013036101180d0044d6250b203091840140b8038070031000700340c0196206202107000138589000c41c1220303d00598004c43c0000301d00a1580b0041c0b010b401c01030255007104100140c0c4021100c0c19984a5101d41d4103000040c0e03140d215082505007984d2a508100020350b1542d6a14000e4061450030b0141d00415083c004000b0207075011949445000c90103e1001c244034031000942600803074201ca107541c0e441140610500794076582c2c081401c8a58083c00c00b07001140782c3c0700e0151444104c820340143c000d1f400510a8a01880242000102110011030b00e400301004144140301e000d080c1d030340c408806181d0490020711169140c01c210b504940a209330322940101d0b8980f40500c9001f54840c2e194a400d1040b82800046580c102813800500180f4241c02006140d0f541c0024419150b0981000540f8004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 851306492 1250 851305242 851305249
    0x6050a270e0705120321090d08060904060e121603030606020c03070522050f0717040807060510091505090a020909040209100b0a021c0503041a061201060b130608010b040e06 76
    0xc0d015200700c611569400c2c03004c501038004e13803961141c0811401d42d03040b0300d0490000c9d80d01c045c2c1602c038160002810400100003400c035038000c1c200403003e08200c9003203485140808030698004074401c00c0d030a05000034203080640602074400602414009000c0349252000071980e202c8541c8a0700e8803559004c0300e90390828074154440301a07130511400511581c0742001d02c86a1070101503e0358800201c5080070300704951528042c207401143d1281485140c029141c4540b00646000750822096003038804000400c0d144520584000380418402d4048191410040003101d2000a18543e41103004200035243e903070342c2c9244039034040d90443d6017003000e03180ea14031030b003000859400c0b00c400b00000161a803035031074001480341d9924800d199403807946080303000c089a40340800e40d07004100000c000b403003c01e0403034403042259010402400d11841d40c0211080039096403034540c4178201c41e080000e0031030b00d07040b2030380040c00143c0194186109203516040d90303c441c512540c400c10407200701c03180102d0780598 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 851307742 1250 851306492 851306497
    0x6060608010e0a051b0f131a0f0c01290109140a090e10150306050a0b060a050903011113030b060d11010807030b06040e011d1005011206050a270e07051203 68
    0x803455817584441d4001c0d85510b441e803210086040106601d600000c520141c09200500ca0400e00c0c2564141308144d50054030542040982200d01c2d500e61180690700c054156040c00003155503113024643e00c10300d0300050400d058030303040001440303c018240030541d261084107208940804100064081d1a2088281400d070340040781340318a4102600ca610141c030640c041001d5a004281c1040700761200ea250b001201c52552180d60402800d01900700024040e1000d0518200c000d0004620540c3c203250080250740802c00f20307500b00543d51000e00911800d580f07400d5200c1c00c151140130540d107058881c90a1000300700c1c1f10904200c1e0200028004901c241c00a01541c0380280c4400d44454039520300f49a032071000d01401c0c0703004400402e0351105586911a5038001d2008000003040749091000440d05820020218165151a00c070001280d0b214030399403000805107901c030500c48041c06030419015400724000c090505007012001d0141180204610003100d104461344508100e07404007041c25030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 851308992 1250 851307742 851307781
    0xf0919050705130903020d020c0a050d0602120901020c0f120327120a0f030b01080f0c0705060103050c04053114010c030504140307050a1b05090a020706060608010e0a05 74
    0x200007003000803000802138000c001d215100e0f8090f540700d54041d07881240d40319551ba4105a201259900410850410700d8074004c0c03403400368001520300b1100e0120700c501f0039015107009005a41c001596401c90700b0520030702c01000c1c3e44c00094010901c18a885925500014140c00c03007000c0c05c5288144501480e05610001c4580c01082d00c11029261611140c00e421082c01240030691041031522503510a10030640c43c180140c4031128140c444c201c0c0383c01824001881c64111410401000c800705800300301040c000e40c450001071401c2e5021109010503a08080e24511041c02602842d0300b20101c101c2c2021b9414190400c0000343e041582498855050f40b0781401c080c55280c15031000320264180c20051190380260400079680c085c8000d0b06070307240301d400c2001d0a140c000d500c0c04000580300c410342800c41307829400c4410b411a100c400080d4107500c1501c080d90140d50020314a0200101c0303025203c010002c2d400d100c0c0b0340d5854008a4004d0040042c0040c2a40703a507040050084000c00e0a170140d007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 851310242 1250 851308992 851308999
    0x601110d08070e0a061e020709110d0b010903120503090a08030708040201090501050f09060d060305010e060708010806040f030c0f170903160f0b070312091a0f0919050705 75
    0x44060340003001c0d19104041e68608000b480000c01001503042251000c0d0842e0031036507892a56401440340050040c6100c500481140198000080d80c800f4078006d08507502840348100c0d548201d0110503d00300d807080080541400618041040440d0480c444002202018101556682d440c1124981080c03004107005042c5a8003100b840072569002c1e04941c405c038401e0b01c85907000d03a2210015215030290b00c9000307202500030004000741c0d00303100c40a08944c0c0101f5401190b000d889903078007401c5d20321000c696001507024404002d001c039440390b84140100407410180c8841e04050301e80d2400c8500300b40000e418081c03803102c0704c000c11120004001c80c01d50889540c1c0401018004041c0907035002c00f0040784a8802c50b0744a55102e10102d880d01c085503495510000b6981c684144038115400103d41501806003124007086112582d01401c0103c6103d001844248020304003e401952005013044524000000401110307180008064807035000e06010502a05005d2030118a41403030754025542 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 851311492 1250 851310242 851310253
    0x6210c060d0501060807030b1e0112060b12070f0f0e0105070b010303030605130e0c0d02060c100207021002030a0f05090f031b010e1c03030f24091a09010e060111 71
    0x64910850740318905a0b49131340e5a4030250340721034004400761814034003100d5000c040d10500500034071074464200100340d0107042c403030441604c01c08100100c0b021580071103955000050010500c010707032450503612401174105410003804c00c1364010074403601c01d14110240142d082802000d60701840948001a91144003c4030a44c0c60340342c010041c3c5602d10489010700c005001c2c1d9500051a40103805d2040b55400040c03c80102c01410003da070f605034501680c12600401001c0d0f603c60050114501e00c5e00321403005030703851395a44180a60481d00d043d8180441d0000d0040050b0140c0c0100844a803089a160841c0c8402e0300b58001140304d10058080b40e89817081400000348404a22007500700390100340c0340c031140b00180c9410b104505032998500c40b41001c0d500700e03d80c0003034040c0d800006481221540014181e2a0160100c1d54218002d071010741154103100c1000058500e02401d07101482000780d5001c940d9540020418804040c0502000c0c0c4207510000b601691082d0030051000c22608201c81 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 851312742 1250 851311492 851311507
    0xf0602031005030f07180207210309020a0e060a06050414040c11010f09060e150112030509120a0b0a060501050a0309020622030606060806010f030902150301060207061706210c06 78
    0x5d0356145503210baa00302005520704154640428403d4a40d4030343c01c000c1d04050300304c6150381d400003c440300d00780705e003410382e110550405629242c0202e40980401d9210000b642004810025002c0f04c80d4020410071808000c1880709031901c00c1040711716401590080b40e40d0030b20030000d17101c0044c00203881000c0c1d03191072a1160409140c0d009101c2c564002d2030100050114200003a40324680b4980721340b5144104c0b801000507112012020020500900d0f1841c1001c41082c005003070408050150314041c0c0c0043d40b10300611030103d114540048480304208045480d00e000a84907000d904140002c1c5503507600d000055403a100d0031545800030060b42207071003406d04c01c240b031411702d4903000640e4402d180c0071011a020703020702c4001d4000c04050315140304059510760110080c04c11900120307080351051140b07280264121000c0c41c0a0b08003034001d40607140c2000c0b002001301c2c1c02e5040400c000c1e07802c1000d06c0802d8454003000c451480c143d003030700c0a901003000101e03490310740f143d02d003150015030000784031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 851313992 1250 851312742 851312773
    0x1e0121110a0e0d0b0106050a0318110405070c030206221401020c0f0d0206061315031101030e19080c1509011509200a021e0c09070c0f060203100503 65
    0x20300030301e031040e11180c0c0011040d0040c091025180782008240080300380050144d40d015101a000c855010320780890138103107900b5880455241e50504a03049050300b044041d0a141030700405510029502e09241760f101c0a4800071755908003d002303c01c144031814140c0000d21107088008842a0708800c42c0c12402050f104801d00070342c00b400089280c0c0c0600c0400315520710001c06c2665022100b68001e10090310380504001c12035903500c5080200075038428240e06600e44c07444040300214000c50f500c2c2c06c54104000090300740c031100050001542c2021104c07820f1090748101103086140c01c005281d031128280b0201c41c2c5441032400c21009991001c038100000443d0541102c2d446081c0c0c81c0c0d1801400d03954468101c2500c0d41100011440303ca65032114001e100e010028041545482c41182c0c841e0707907812096a40d00d10003a0002c24650081060401d05041c44103d8a801203070301c0c0342120700541c3d0f64440400b02004420020501c0340c002010903050300d52040303040c0252000406441e031200c0441540c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 851315242 1250 851313992 851313997
    0x28021206012402100c03020d0e01140606251a19060608070c110604050d0605060301140603060406240b031501050315060c03040b0403050706030b1e012111 68
    0x1c40d60241d01520b850b032503001030704040c0000107210341c0050000c04004004203001d4442200c0303600826509100005804131940203441000c120715000145d69141e00180300d8503d84010590341c02000f042080303400d181a1122007a0301c052031981e00b00c100101521303110010a40040304042d250030076400b44011483c0c0d00e9500300c0c4010f0b2100080100940d145030580d14845c089603040041003020308001c0106194144058200700010102840c01d5281d00000b6048001c0080541d4080e660750704106017401d0910442400c2c07000c543c00c540c0c00b40350a0000980e11240184000e003281d071a6030440070075240001071224000715101c40812082d03111107041106810894001c50304c0c580b01d226968a43d40901d003100d015400b50280080c0304024503091140c0d9078810400c600852004000010b00c500700a0080e001844c031602c05070002c98030b01100101550340d5512a40d201c3d0130f00408100d0707403407400c004c1440404820308107103040c011105070000491002c41d8841c001f40782042041904c0c501002c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 851316492 1250 851315242 851315249
    0xe010305150301050408270f0f01030e0607050c12070b07320a02100504020609044d04060813050102070f0c05040e030306031203091f0506040f0207052802120601 71
    0x50341c800c400c00200d00304150b030024404454100c80d030307107981d0482c3c9d00380401c51640c4000c0604001c034402d0400c01080c0c1c0b41c05412640c0c000003c0300894000b0a049080c4000000f004500700c2243c2020980c0e180d409002d00302502c100180205104085c44011070b003c0054007140c403003d03401e04c11a84440703c0b160706611640c1c017180140583c0e140c0c03445100d620300c01c150080390064015410207090500384001054503041440461980305901c00000580c04903c201c01c0715100d800066900c48a82c064070180031501154240d41018002400129401205250b000341c0d04803041e81071840341d003849402441451400f50070741303d0443d518001d000c0300d120b4040450310240d1382041030346030340741026841e80030a503045a4190001c0c00b40000345140c41c0c020310382011000058410130442ca084415140700048804684142c4450030030189150034071442d000300da91240292324000366a0f035480d403204101c0f0503540100340e24400c1500c200518800b400c41040c2d0180090245250841c22a82e440c0c501b480b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 851317742 1250 851316492 851316517
    0x90f010212070e030303070206010e06131b0206010803032e0b07060b030606030304060203160c0509180c040501290d1a100e010906080606120106050a020d09060e010305150301050408 80
    0x140483c80a040000031240303d42d2656025103100d90a0200003009000040c006652001310750141300503030149845211002080f40302c240c050500c43c0500a0b080070b00580c800e1000b0f400a00402c581645996030300030b48a010303051118840c48500e030308144007030031603040011414000301b05030301005656401000240011000c03101256100c038101980d034851402144010b0700144000e12000804220060800303214000ca003070030607100c401154a02d5421288183e22800288510381150418000c4140c8441c05032000e003c25814200d003804100c5034903290780c0d1021032440c0c9076001140140295481c0e181442c109014840000e0007110899440720466449048d00c04091042d090180580e07c1302c00406844040c4103d203840016244540028403858111100300110840764403206195400780c00310f41c03282c50722241c015400074600b08050510700113110f110b0205100503900301020340c420074024a800300d0b090352848002c0381941c0e040d0744a19011340c00d00c4140800c01022030302a0440780c072581d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 851318992 1250 851317742 851317757
    0x902030d0c1730010f03030e0301020408010c080f01060306121b050303160506060904021804150203042a080304181b02010b18060901060f03090203061015081e090f01021207 76
    0x1540401040f2020f05c1403010806100030b0800000c0d0040048404508000700010304003a91100d4407400d4a02103e0078000003110720307040044c800d05281d005400b51000e171030100003076824048400d4100016901c040c0c04550b0100142d01c0040003110300001421001e0292034444d1000d401000b0f0860725000c040710b082c040c40000810900b8107081c1c4911454008085800e007201201c0d080843c0e0101a0043e280284002083d0b00011070f02e000442c0914401c044619188003080c00803982440300744480300d03060944003410001c2101c00000d031415641600e010300c0c0d041c002801503000030000c840100d5000030100700c2040e4070340e070190310024040d201521161086403180560440d1401d040301e00c20b03806010a00103000c220311904038114100101e050005030241e25400080c5403690886085c00f140081450610410980007a06401c4002c2030800540c64142103004d144d200f1705032601c5125402060000480e052800c12000c582620300c0c0340215600c001341c4000480780304080707a041c1c0104806 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 851320242 1250 851318992 851319067
    0xa0c0b09011d061b03070b040b060f09070c020609030c1f0801060f020703030c15090f061808090d0305041a0310050d050606040f02040b1810030902030d0c17 69
    0x42c20090400d070300003440c240c5403035840742102c21004c120b249a841a4032051100000054000c0f800328011070085114000c103190035003c0240c00300b8000b08060040280c2c0f0248400d035a00310301e189080b06d6040700e0b00340d1900c0b03080004c42e20344900010000e5000d21070301e83d844e0036000c03011140300c4200c149944400490b07132284000d50361070310b03030000c80c80050348046410000720b0302c070356000c90481c1d1240341240850501d031207180003a18807402066500c1c160300c52600e810840c2c0d5201d6008201c0781c241039043c907044183c461201710701603000307298040c40b8203a070640704045c81103003142d01a004d0071550102c8503c51320042c01c0180c1080300c0c10751000496110104203494111490280c00e03502c44c000b070003259112820f00025001c440c41d41880650240404900e04201001a0002c0c248200c4aa1109440c0a04001c9402114848002414074024200f0007688000c990100b5103485401d044c1810301862800404208015540c40360b031003404a1404070f010b540113450f4440684450b41d82c101c50300d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 851321492 1250 851320242 851320277
    0x307050108190207050c040203011403070e190b03120a0f1112030c0903160909030206011d0112030c020a03030e1f020303011703130b03060a15120209030a0c0b0901 72
    0x140c521141070b03600080c1c07100d154802e41c1c009041961040301902c0903c3d20401c049402d07a042030f0000c0a00015120000c3c0f0a400c04005030300c000e040f44103080505040c1400f400c08151501c000702d50b20740e40c070303090780032015101006041380500342c00d00d03140c0c1d6a083c1e42a000700300f0092958030700300154420030707900e000000c0041d141d4180742c02c101402d03245848070315030600e25510281da05909030003070030b801c1e8014003c04c0345032000400d00c410011403e403c1600d03000f03043c40c805810110455a0720b45102da10003114081842c1925000c00c42000040c03000d041c2a1118a04000b0081d4071185202e008010954402817050410320181c480545032200c0e01007400340c0924060040005a0045c4010408686050307000302c9040c00c44000e07a8541040c4a1095a030040342d6080b06d41ca0850002c103029040c102040490020044010038040b03104600310014840c1c48610030a0450540106201c49140d0b400d000b001e148a80c080e40e0b260446540b50000f460941000c0140c6000c0b03004d40d0344003000d0b010b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 851322742 1250 851321492 851321507
    0xb07020c0310020c1f1a03010213030204410c16030f0e03060f0105121c030902010905060313231c0309050607110706050c1b0f04020f0903070501 64
    0xc030010701800d00c01c0c02090288000f9085801c1900383c0788104003584502c9100c0101702e003548100e460b07001c1840c0304c1524444c09811042c0f000607000b42e204000b0b5200080c000101a0f090740d504580100c1c0561060518911410b000c0b0b03d06050a0400c0400d003405550300028101401d8200c40c0104060b80c412440000038010542030507100d0b821510941c002911840424514940d20308007441d04003c0c00e00428542981254843e030300b072010000500841c0742401c05490440380041c001c01482000720200400007002c003003150107250b1243c0100045a0180541601508020309030640701c2c9032006000b84c2e45425040c054440c02d0f00410b46071025017010710300840344907031000104441d89000240684002c0c480096a080507a00c20070307800025028088140507035003e42d50228001c124108803400c0c021103901200074800700700683c2e03402003004500750f00c44032822449051200e002038045030b0683c003440805a0700501c000b03010700e80c6a071a40d014103503400c001d0302281c034250388030001502c514 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 851323992 1250 851322742 851322763
    0x6060f05071511040b0c070311120a110303070f031809020c0a0312090c080706020d0513060e12060a0906050105090112380604150608070f050c06040f0b0702 69
    0x301001280b0320140501c1d5005a440000a00307540d42c44d10799a1910340c0181d400c5503074030800c1c5812806003041409855400d80c1c845003402c6801000369107850301c3d0306e42c0e5205010700c000e005003121650340b41c240d5024030981e409650040100c1c0746000c0f15140080800c0d0b44150600c4a6203121034011406016070f20981d51b00028417070084c52240281c0d00d0a03134400a0111a02c0701c01600c99030303160b001459a18182d030040c8444030007805001c0c03c140c40a803c01007002040c2c17040000c10311a0348040103503055050b013250303114100340b9054114080424864051002d1030b4090344561001d0041205c41603001c9040b980c080c500420080e6200c00421030118420300c5449800c40b00032021001285e80102840d100045140b01c018514414619050340500102480048002c003101041094281170098008684800c0310744d103542800d0041c0a0046070303015152400300f11450864400c9035000340308881a5140040c221211413400b850b01000036078140704d04070b03400d20448020581e214000940c50b20340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 851325242 1250 851323992 851324003
    0x303110a1106090c10051c020f07021f12110c0703050f1905070306180b100303030f1407111e0303160c0503030109050c190305040b100506160c0e0a06060f0507 70
    0x142c0c070000c8a42e600403c0c9640c804141f80f5001415811261004092501e24850071580b50402801006419155101c905403540c010700c8284800e50341c04803c0d0040302c0d03404017002601281c1c4c100c0d5680c81e40141204100705201d51b140110074804000b0303203011401c0701da4085820b258250a490100d4a2401c10028500e901c500c3c814000900c4640056035100d481355042003090708a074a891500e000142d84420071404524410300c00d0542c98068075580310741561043c01303008100e480c0c103102500000c1c49681081b400580500301c0100502c00d4214000c000e040c0001d00d500745841045d2203501c1510066400640c0d60490001e55000d4603204a8468108010f1806d683c80d0080d0350024090080c1501142d40c03003001306503008200b070038582456002e0340d50001203e280c00d10b0403e00104014001110000d1054410030080d65024100c400c15400405080c140480a00e00311083d45583e40015040706c0b2440c0810540210302e900c020101d42c030b15911145c0388824818152058461008081d10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 851326492 1250 851325242 851325259
    0x21c050a11033c03090a0e01300201030b0303160b0621120904091a0a05011a1614190303050703140121050d0509210a0f0303110a1106090c 61
    0x4480400f94210740044031100b50303894105500001041d510403a00b00d0400c1d01c111a006001030601c034110a000782d0140720101c202c0c4040d501001d1446008908000d04250305d0b804408030540701807064030131007004410300034280e2509240c4102d604004540b11030180240411307900000c48071000b580802030802d005401c0ca81c0b0001d42187c1258002c1401039002520340441340009500c8900c1340720008003a20901e4264107040d04007205460040e481001c002d01c1e1161103c20b01079001d002c0381d042d201a409907852104132850110040195a50304095a0260700c070303d1490510500607004030f00e072003950b007004580d43d03a03c010b40841e00c13200403103c0150019130040c0048261a009003803450341d192034483c01c0c1d00300b40c1d0b5090319000000468500062010500c12000d040c041c5101d014581400190301d48440002c100560306d030b08407100905062070403180c4906060003a4000303030310301104c00c210707035a10050060050714140000781400018480c2c9000558041c00100311540e200900415001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 851327742 1250 851326492 851326573
    0x1820180c07021203070b1014030c092a0f040513060e06010e030a0c09150f0e060409080d020d050f0901140402010f0923030106051903021c050a1103 65
    0x80d1000f90502d403d2510b100c200010404039402e03901007481030100c1c2c0c5070940c05504108c0a20b00c24420950668081c0c1d020703d000400b82c0d540c8009156018020704240c104480111100040300c082c1041d100c0c8201400081039603071040164010070542ea000e9485450904900c182c200c101c2d655807140c0d900000d5040c0100700303190720800400410036001021500000c43c15240c0301d00a0009900c000e07545540d4030b486c3d190885640e403801000b09a103034510701d4124a001c2000b032591000070201445107666174444030030806040c082d203ca12008410840d1034650301c0160308000e0074266118403080c4c08241c006064194140103600d4011401c00d9101d4443e1074a900544105400c280c1c044148017011102150b078210030f41c1007403000c40000d4442504002d0501c103043c21524a5000f07035000b40854044241900032101c0880c04032039054034651080c48101954410321910f4240003059401800511000e00a503503150340e1000700101d041d21070030384400381ca450040c91030048890311680f44406030f0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 851328992 1250 851327742 851327749
    0x10f0b0a030b131506260a022205180105130510050d1505091c050d09330204151206080a050a050c0303070f061820180c0702 55
    0x40a5a480c1410045903003032101000610190401011010b069552080c0140c44102d88144e20014001410300c0d85134418040c2c41d003a4090003000007000b00e810f40d01d01042c003943c0a64119503401c0f0030354442c18982801d05d030300b503910302d503007445018410680240b00380c2d46402c005240c241255002401410b1032411070400c00003501008041d8031142c030a80c0302c0050303142c6400d484620414480c4249800020712803002208858014010000300d80c09100031281110f902c000500511070396041c0b8940394500940743c031024121000000b00000a00781200703110721000b04410707014041c1c0c010845100d0020030543e401302e004912840158020003003000740c180340595007985000c1c144510214069880e090710918040d400a0101d803603034001c0000005218050180c500140f000300d02842c6004016183c460b4035121503280600380075520307141c40d400300c0080c505003400150f00049100507210070090344018004188081da00410340c0d0525407849410300c030342080c406c0a10407181400c18610350280b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 851330242 1250 851328992 851328997
    0x8091228090e0604050601030f022a03091507060e030f040305100c02101104080312060a06020c030a080d0e010f0f060501090e0a2012010311060304050d181703071a010f0b 75
    0xe06e044c143c0c3c0c0d0005045880e22800203010440e401c4bc050710b9414005103030700b0081d4051140d22181c075002804815125591000864031a10b50f0340c0c506c03a11080380d801c1407002060361a90756115480001500028022410b001d402168040c205844d194400d0720180c0382a40d00d82803a003c0140c001c3c03042620060502e5100d00c4060410240c424103190311201d0891031a881303a0060f080c0320f003034903040041030318005007400e000e0a0325102611f04803414201081c0e4a01100ba4000c01e0050b01040104410400d580441089094a07000344030300c8800040b44c800805442264080036410040c012a00c8d5020354030881c01c855070f20b210381d0280e5a9079100100101070b140e03a4884c8400d00e0030f088048a000c041e014044a5180b1207035014154514a400c0d080c11030780d1186240640030a0003084003260011915094202c00d83c1800300e06843e5814402070010076079004221403040d0f00c8039241c201030001000d4403e203440b41c0800d5481c1e00418100c042a18030910400d190f0350300d41e40c07042c001604140003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 851331492 1250 851330242 851330251
    0x2711090108031c11041a120603032104082107120624090f03030908060703050403021f06050307080714221e0911010f03150608091228090e060405 64
    0xd01c1405d05403281d05142e110002e00e1440341c0d140320f000c074150b4000c2c42040d54094001c0e40440003586001d0f820b0103004152011945210609080440080c0601507804200d8180351400780c180038590a00444059001c201581c0709000143d0401038148003103014810b64060791704c140c0d9201417183ca004406041241240d4a880400040200004012a04003c810050f51082c1c644800590601c8031452801c00014460070800d8240000e0201203600440d0002c44403803403a80d640c48800c403020f100300c09001950302081d0544101c1c04000344c4448082981010b03034140da001c840301c2c251103100f0043c1c3c1d00f4402c1d02003413030f81c001a2000c4884204580c41080a80c44d05420754008048000030101201d8a4140540e040c11101302c00030301640e4002d04120060040d0700302044580c1100c0280000d200380da028071014031060201182c40401c3c01c00c0240d1920f0000d80c000c503601c260022a0943c0b02c0d0046600b80c076134207060341d20441ca076030040000134180c6402131a8007415903174080400003d40406070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 851332742 1250 851331492 851331521
    0x9060f2202061201181109090408090d0b091506040b0a150e040c0e030613031d0a0b0726030402030a06180507030305040515030402132711090108031c 66
    0x40240004200c0162550081c410000031004001748025220191034103580c103c070804100b004102200d1303451200441d081034201c0a429150441c42001c2803500c00d001d03030050302c0c082c056010003002c200c000079060881c02c26403940301e40503280c2c9400d01054071001052a40c1c420b0640c0008c0c400b01c86204490300f00c60400d850300503a04241d12010500300d9501004e00c000198411000203000e00b02040401d8000d00701e6000d541d40884251001013101d0803110840401400000518900d41e45140c1e207440a081c814003915943c2d000d501d4511080300035000d1400c21641c50120800440120790207903845250003070094060000e6554504000700f04001c3e110080c8255a0b000c40041401080702d1b4010f180b098558590304ca0500f41000807140c00d01030b551101342d00400130080180c4a07901a6403d00f1072011010440051200070001469801c00d4604d02011480b80c501050002d20a1220b60100080e0740f03952243c0d80340c0c403c041d120b00c81d003218201c0700320201054030410b100e568402c055855569 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 851333992 1250 851332742 851332747
    0x1602010f0c0b130b070509010914060f130302030106050a033c14070807030201021c020a0206190305070302250201270e010803040501020a030e1804030809060f220206 73
    0x40c0c1e2001078604007510302c1400b0010181c070742c204100703a13081c1c00303504414141410b600b03110225000030461a500d002da168901c1551210000d162100c00c1541c082148a0000c6a140c84030091920380d0001d540c40143d00c01d43c202000028241003801081e0256138002000d0083c420300e030684500c1d540b185c1c1661000910003003410154203186410b0620095120322005201188001c010324a0107540340c0020415070131030001080142e0700010010300610041210000c201c0d1248816401c0241003400650030038400903050041000900d208800780071107490400180c1c48184048040780121034002851100c21007203860100f504086888456205261a05403a610300c0c0c215900c40c01c10300544e42d81c810303480c1810310508044a09540c00352204c0f80045080c01c5c6004c0000f5991241d0071000740c107208100303104916a851f01e84010882c04504d444148a40c1400d02d00209582000c803010761580c080c2c4804034440b05d0002c840e00340102c0300c402410740b19000640c609142c3d07070b454501c104d900a43c01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 851335242 1250 851333992 851334017
    0x2060d0c030b18090c01030e2d1c090e250306091802030d1b05030406111b060315030307020405041a1b030a021b01050c0d0609021602010f 61
    0x2501480c8040d0300340e56000b24070b5408400501c9404025280c03a002811024401c11001c0c03000001c19903500402441d0120307001d0010540d44d410403256054154216001c076040620608102411040c1c10a91908498002c4801044030705010b0690003544001424400e082000403001c054040c0c01100d1030141700d0722400e00800000100b80c210b002d031804685c5441080080803030610aa00f00c0400e11009040280c0e01d41d400252075650030300e40c690034820a01180100000346609141109038060200c03076079151a408047d000000201502da000d21820200364403185d416030a007001d4901c0901880d04540b910040300480d040d04400c0315805100520820001d030f669406450701070303802004400345001c280d21720100441002023608906100d010301500802341610101e9910845409005865142940310110b0485441030062030540c208000d109610403044001c00e00e01103104000c01805070f49405c00c100b64007031306980160707102e010503001004d94000c40d6038981480203494004503004a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 851336492 1250 851335242 851335267
    0x2012604060501080c030309060901050a0215040602071202010b130230060a15020a0b04020d1506080709230a0b0603010306090b0708150d060219080a060e0c040b03040206 75
    0x104860503108162980c0c0100280c120900041740d00300e034150061407401e0103032404a50705100707516580341000720010b00002d5042c400e01ca0151f0300440d511b1141450300300f03804c044001c1d4100381000d48940c0955846101c41d113005105441194102802402e540c440f00c0c000b0400039000801d00e20600c04c6000b41005c48a16020741c070014900389800d5030700803800d0500a2181318031142d042911101c81202884804c4c3e900050400d0000d5804903240207180e8480c408a14864094200184503c2c040454030725460080c0e04942c050b00c903003000b25107620340d607401501c09541f0031748014261502d4050f0110310000402e024183e0040e00244045031112115004c80c1c0c0070380c002da00c00d50304d5a690340c50a20400c002207a049802c00043e18101100e03040c203014a980e041d25000501e4031400701500e0020030400f10f03030141c80304070b80c2c80801034503045c1003000040c280e424100c0380c00c04990f1030064040341ca000c003c00340750300803c0c0805896050505260014801c1d0344003400580c1d0001d8188481000043c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 851337742 1250 851336492 851336567
    0xc02010e012a0206070816030b1002210301052209080f0703090b1213050a06050115080c0c0607110c060d0b1305060906060d060e0c0a020f010501120201 67
    0x3008001c100610342203072203040c8040d0040840700b000719003014040c458002d0384088500d80000c50b400d49411000500c000a9000b0423546603013980040500707200c1c01b0b9050b00454150191003584549140215903000c501d400c40c8800d00a4a500c0704a0101034000b8001c942c01030741c20f812000000203078030b5030710391110001c0d6000300307800f40401e0700d0001d000810103501441300ea00800074042c805040149403040d580100d18000e01c1d070100c0c480b4082c80e00051000410061008035080360040003e561a1030f00d0204444048060b030011401c94404505202494004c031250250280040c0000d915400302c204c1e2441001074550105101e604070781c400070b54891008042c0c001042500042d4150050140301c04d404429064080d00e51400f4100511500c5200902d548a8000c403101c550b00c00001903108010100c603042014120741d00e1081000d90f001d11001002030ac1640d03005c4130000300c0b50300e501d00c0c00d80f03100340100000d849a17140c40e80700550040b41102d070b0f2154140741525940c02464007011499 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 851338992 1250 851337742 851337761
    0x1608070602040614070c050d0302031c1a0603090705091003060f0b2d060328020403050618122a0c12011a12011e0b03061005010e01030c02010e01 64
    0x503a4005803c019040d04018000f40b00c50f80040340300e042c0440c1d500d031440e0004251103402e0142114810040c1014400d01c1114803865050f00d1101041501d84403110045ca00c0c069a000d00320141c03620004c0364034169043c4c910a41c804001450090305103030510540e074030301074025444a08007000107c0000c0d0039000c4d000d40c003840380c07900080040b451000c2141d011580701c0b030308154500d1441c0b203022116010032811020082550100c1d940c3d00e502d488028072170050040c1d039444500b2a14440030b61070458005000722401003084075100c0c0c0301e140410031031508151481d407007a881034a00106a022700805001c209243c11004a0300c0d0000d901600704003110b10038058520740220f4581030b1140b62001a2001c030000783c074020045440b040010740381044640780c41c24490001040a000050b00035001520307421400400c83d19410a9049814050900114014424002c600004160702e8001903510220f9105a460705002c4014400540c02050540c200d1000c40d500e40e503681e10050030034090352922 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 851340242 1250 851338992 851339003
    0x40c021f090606050a0308030403080c0d15031203020f16050115061e02030301081e0f031606060515040306090c0e01060e010909020c0c061815120601081605160807 72
    0x7244a890080101e42150f0440b0f07115000400b401d00103e00f012042d2944240e060a15410548880f454420203020303914254021311709041880c83d06240f002000c000b200d01c12801c45400340e072141400e90581c01581102c102103402400141e2002c285000300c054064000d8000003444c001500d0525902c0840360040d90104254650b41d0000c00300720101588240c0c00d0b4805182554140f241c01911115040740071210321540a1001e000c0f03810070712059880104074000c44c0e581d003d610051807100f500103902600c0e00781c60140c00140c50f04000c001d04a4100c00000c803c0d18042c1181d403040e00608901a050303551000010b008030701c10340c11003040f0380a41144d03100c5010f40c40a407000100b48003000d4001c00201801400101c41d200e0f80055203851405003142d0541d16900030700e8101484100c042440303588038020404115007250000010701d00001c800d000716045a035020300642c0d152a050b507400c59110000b141014a00d4403440c0a80480504c4140b0030170955900e450b100c40340e4010303c0082d281d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 851341492 1250 851340242 851340251
    0x1f09081b060609221a01091e020f0426070b0c0c191203121410050306060108070318080315040e0706120213092c1209040c021f 56
    0x203008081040c140d0052044440d5101803900d035400640306800d0100306600210070401c26820885601000380c200c00380a1075003030066030360b1601100580029036a80b080f4080c900482e242c850218004c0b40d02110540303080c00d24003490b101a900d9407864080b148507049100701c210790200001070110400903c0b44925403500c4000d032100160410002007011482481c2c840c408401126800a040046468210241c007022505017010340345d200c50703403c60001c40c3e840c0850042081c581d10f183d960060400300c0e80c0511643c1c48a0034142e0742c100566085002c5044540055000384c481d410018001e0440700503103a130000d0a40d140e000507041030b2a03040c500c0717810002d5800c241c10a44500c000c4c44c01c0f0540100649850010054528422004803522542e00010420410031b02d41d1100030042c548443c0820050f41c00c842d240c0d50001d46081401d100d0640201160007541e400255070b0564560600100d03e0070403030404200c014503180744040250300410aa20100003c0740d08182e40c1c400d544e4a0204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 851342742 1250 851341492 851341537
    0x1512021606150b0711100e030304060201140a0c050d0b120307060906140408180105040510020307140c1c1502070c03050601060504030b0a020901031d07261f0908 71
    0xd4100c403007600244030341c1500f400036401140700704105401c80f007006d1302c80900079024820f04840401e050b08a4036014400010000f90071030381503003c000c40340303500303d60202c2c83d03111005050b094071a104460000201e091240138038240560380484a8200010a81e1035201001ca00c401d056800031401901c049503540c181105020a90180c10003841d070003030220b802480c00d940c03048100e00505440660075505581201c0459016030111806000c004014032220b205004e0002d640750300580c42251700c01a1a80895501280000ca1610040000740891603a498180002c240c2c40801141521403025030100100701480c18401445228003030b01c003400360581141819450003a06a04c800304014003004100080b441e59145a5048160b00c400940e4031500040128064021050204041865042103030604c4200003646011a0645042c017142c203000c00d580e20000089041035020150000b11500348400b000c18440c4419001071100000c4100240d121146941c00031000a1207107228212002e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 851343992 1250 851342742 851342771
    0x9030c02120703141515150d0b0a091d0a11010e0103091202160b19030f1d0d0e010305011503021b0601090c08011202011e0201061211040b01091512021606 68
    0xc03507118481c00c4c04c040f85050b07800041102091210b400a01f0b244011600d010b5040541c7c21050b08500000c00d05110507881d8010700700180b94890012003240344144420080d443c01240c0203541c66040805020050071003001590168503042c062030401d95259000000035601803142400008158014061050881100c034030580c1c8640086108842c107120008001030300800401100d071141c540412500540c0c01d00c04003078580c8405c00c1d40001c14250343d01012440020300c2070038216065891407810b48000c00150121442801080c0250500c000792a15950090300140441802030b405283e0100f03094510905100c82a00080c038050349038920103102035840b0040300d0140004d1242d04424240f140d00291060100000741c607881403a440104801350300030b5000100070704401c1c44480000c00e0302e01d8107210511400440307601c280d00c1c14902003095440b41c00d00c3c1056404200701054081d41b016400e172000018060f68140309d9400b000500350340c1c01c0c203000000c800c07840b48201003000880f07181074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 851345242 1250 851343992 851344033
    0x309170322060c110a20060d290a081e15010b0d0f0506090424090f05011b1b020a05130c0f0f050409090609020a0b03041101020109030c0212070314 65
    0x713210b042d8810340d6604041420311041d580d6840c50501222080d03140b400100c0c51034000d132040c41290303030315000007941c4025101211040300200e001404440030428010480c865406015880e6150300c4201311501c0000101280c550964040089801c0c075180110f40c2000e4403000d030002e40c03401801042e600003040241c0610316000803041e03030620052418501088448078010300281c072104140b928422401c0414054681c1108654000d000c000c40b9400c224003010820002104c840d8a8031440750030000220303105200841c3c480d1342c0e825480038034a070301000345524020260380c421034900000807159200c2d1041034900e0200d0310b01107850104ca00300900300008003680308081c0801040d1b00c41a56500501f10340c05d44100700000585c03603c090400314000e0103104d000941082e41604c1c045607000c900405140b0841c4034440304600c1d0485d00004a0030307580e85035070040101d40d11600ca00d00600d40500c00070f501542113411070f0b00d216901d868103081184e40c0c4109401e9a0410880401e207200c01140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 851346492 1250 851345242 851345267
    0x1021903050636090304060c030c021f11070b09010827030d0e102711060c0705031911121903110d1b080c030f07030f0806010309170322060c 62
    0x2440c1010314104020b815502da500b0020b0401003401100000c550300e033401c64590030200780801c102c1a40c10380c0040c0404100050001080c82003280014074003a82c401200c2e10207006035201c20741902d8801c0d0742e4003c0f5040d841410349032810742084d104040c038100040c260400142002051011442400504007800140880c0e181400d01e002c1d404001900102d45000513038000680402c54694201807110855081f15940e0103a00099000a28400080d50794284d4000302c086d030390820144203c48200b80307100b150040c00f06c480782e55008010f24201d03072200240b00422040d142040c1da0320108801c2c0c00c0503288120b02203100f0544001500e14108010426090307903040c002c803c485401c8142c140380180c008010400040020400e041440500a9030b402100b001650b40c4c4907000d07442e02808803c00e40d10594001840c00c03000030b0082d840b90146504954100c032048100e00b03010307420f41500307034401031048550b400310350145000001c104800013a0113014603400600c00b000140014060440c0c0c20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 851347742 1250 851346492 851346511
    0x30604030f1b0c0b130815010510140d060305011a0306061c12021f18200a03080d0c110d0c020f0a0e0a05060301021903050636 56
    0x402001035003003001030206290a040001d04900320015080b426140500010105401c582002600011580c003400005103180d0160340c00b80d880d0b1010598131051407400d140c511310154010055810030501441d00d40a09151003200b5208a00c0b4045055201001150b54a95507900800c14084284610000d110310100075103155524040083d68805028241e80d00c0b58401400c5015002e11056500c0304050f84901189402169988065201c502a0110784004500c0031a00e850900e421303c07426012041001d1034800403405a00c0320241d00b4000920440300320540700c202d1209649050180000b10b202c4d01406561300d070a51046020788030400c080b00c0900000d40f851a98644002c01d40c8042500145032010702151035000103a02c2d4000c181c542c41e0404041710002c9418001c24524030b12840e40b03400107009940382c80c2c0a1608034801c0426000322100c0020040740d00078865040580c10a000401d05401161603000c9200301600042c209043c4000f01c6028901c189440c0d01210760080202 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 851348992 1250 851347742 851347753
    0x103060f05061e19020a0b07030902010f081519180203100302060a030902091806070c020918160608040215070819050c070602060711070f0608090a0506090d080603 72
    0x10300400c60500402c000f421020400c001568101c8a510040e640c98003151407001d1654010540b010751288900981a00c122107240c0010745400d010340104002564183e40b03444051070b4042c411520400040c005810100d0300c030500000f180d803010209401c640e0100c4100320440c1c50b1085140c001c504240004104500600c10084035800140088049075010f03100903541e035520000860092440900c000d52040801c000e014221528403845c20842800504940907529141070586601040c44e60095120744039400281402000c180441e010074414022150345403608100383d6614012a0440c50010300ca481c10402903251000090a04640485403540303048510b03150000f0500ca003001805805000b400319900d0b440c4100111008285034106a818558030385000a480310000c0e00c0c104c0010b500001d48011910004c54148102d44010440040c07451400c0b4058600a90081c1a44028010100b41001280091000034401d50140000d0810140075640140100002400d054080d40c8072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 851350242 1250 851348992 851348999
    0xb07020f09010608270c010e06041805150102010e0c040b030708030d1a010507050a060b06160c0f08150402211b0a0609120318080a2d1205090d0803090307020103060f 73
    0x401d142020420070f1030f0240c82c3e940e4040108450344110307482f044c00301036110180d0301c1050613684030342d004030740b5a042c0030040b50500f40124242c0b2240c0310140450380280b1031139a514a800d60116541040103000e4601c59540d86030014107680104080040590f1520301020200e03100b0301d038508001c482400c106003003400315201c10f503035182d070385100429182e51448104002e54821003642c0c07181c1400c200d046842e1145142064503041d03240306000108000070408148044086240c004031010700c10520055a142e80030000104020302050a02c04412172509000d600140b04131905820064201c07d807109140e014403a04010542c48842040401c10081c880d54840808855985800d4903204030070b108100541c01540c0e443e07900441d038504c02e9a560500300031500ca80c01000700004040b070150070816088c1445640d61031400100811460341d00555140c0c0194003511215202030106940c5100580e81c40340304ea030040e210382080c1c5e40045107030b01c115a0302d03006e10006002140f00d800010f070314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 851351492 1250 851350242 851350321
    0x4020711130608151b03010b0903010e03030105060f130302090f0117070b03160315080f060a0612150b0607061a010c050d1d03070603090212160b07020f09010608 71
    0xc06205491050f80340b501241e1794198015016000791003103071800781e80713503500c055641d09a4040b01c00e840c041e50900701c60703010400010050324121500a4003041c9070048200c1c0030080d0364090340041840e642d9086011000d03841c0d0080851090306e4500c5541da05504206001c60700c141140303510005a4403101090013003250a81c1a2038001d43c400e903c00c1c0a485044009030080e2005d20303003101c100c5540b040c0c005103070080015140c561542c40c4003070300c1c41900c0d108220010381d19503001c0e0349044050002e0103c0001c40701d2601e0001c41003800c2d0001281d16045002502541c803140c425202e264803980500030401145842094061003400d20380b0389049166151a00c03500e00480a806211030101c080300016403c40103841c10f034500030b0a4600042c0c031106c001d4001c104803501a4040c40d80c4412101060754000384110358005c0569151009074a0600c0b480b040b0b5101c44800c076041440d51a504c2e0071341e144e06180c10302030019511100024501030159003401b9081c451ba0309102264289901c20728078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 851352742 1250 851351492 851351503
    0x31214010e1803180d02120607030c0905150f04120b012409050f0f0301090515060604060504050d02010306090207060b10032c01110d1b051c05060f04020711130608 72
    0x3044d540c00f440c0a030b407501c0c00140c40030400e058065040b8050303400c207030303140007001c54160b03c120401d4804004214442e101218211428010705410080080c884d031030f1040a5005081d920b0070342c1c0840e034545070321619120b56041c405031045410045400041c8010421400d64841c030348080f04018a2180e1030b240c0042200c0006e10456014124000d0020003548441c9400d500001c40900280a200b0462801c0740d514031100030414518003040300800e00d28a0725030b00300c40484a40b55a11400e0a00308010480c20a1020100300c1c1807560310100000c00301000d0000e450403078020000001c2040a03d07090140b0086022030703420030585040780d07038820041904520402c09210710311803507001104444042c01849103010068511001107501c02c85d400d4950040c50000510315811414910041020f507114020802c18a00240c0c500300c078048950b240303a02039075100c070b00100355034001d1014802080407607204660590344410442c4a224880c1441c860b00c43c02c040c1804400c001682c600900301d51640c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 851353992 1250 851352742 851352757
    0x606030209012c06070f0203011a090127061e090216060b0f06041502160f060305040201020114010b120c0301030b07181d06180c0a0c031214010e1803 66
    0x102c5540c400000c4400c43c0c010303403814000b5000070341d1400c081c144040c0d06104041c0483c807940c204100300b20b181c1d102c0c4070304003007000c0c015049020617420070382200319800d40c6003100e09901981100c012084640313030048134018601c0c0e0000300a03c1840b1141a02c400c0f074550020440203004100300da0f00002051210340c1c4103608060f00261024840300003504405410f04c866a110401040219a030400c11030b45040488442d002c4542510980c0203074500241ca500c2440c20741038400204006c040e029410450344031b1320500c00051841a00a903030b00a0781c00030b811061482101017600c005a0340300705a8039410480b10810581550300d955200780610f40020140010030003030390381c5a080384551040c13006c06040b1020300f14450b000f44110391407040d40200c40c00c41c4a01901441074803203102280b400303400b4051180381540350004030302080e201400c4601046003002000241644a10540e01c580c00418230050159141c40d40740c16500d050b0303900c0c040c00c1203a521034900000c1641000001c11240321 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 851355242 1250 851353992 851354027
    0x90402090a030209010f1d0402060316020307020d08040801063c08010608150f0714090303120a0504060e0d020d080417030a05070216031e0501110d02070501060603020901 75
    0x603a850346020988200c0703a0b6000039006000c11001103400c22a811205055542503080340c40104103200c1c80c45a42441aa0040c1d004102000881c030031244100d0020030018041c01242e01d400300c2680490000c060315501540c454401140c203002030a820f0003441c00800c80a1650301081c41d182c0780d40394000d241d210b400c0880d1400410031640a581701c00c0c0c10402002d03410000c2000a0740c681d0303240c0e10b41da00f0922f000700360b40c50b8000040c10703031a410f44140e005a0b11a5107010501101d40e010899940c0400a000e506100610015003000c02801845209031040080480c150800c0e01d01001900c4030002c0400050300040601408140e0004090002110b185072924940d19a800c1c9060b0603c49200414080c1c140081004904155500080e0040d802503084444030440e00c030500e0108503c6000c000d19210084040c45150160302080341400c038010000000c030084c022105520540c0100c4030074a0340754021900ca1b080c00300c20712507140203140707d050951401a800000070305100114854440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 851356492 1250 851355242 851355247
    0x10f0f06050f2a07060e010507150515040e010b0f010306031703070903170327100902060c070f0e010e010e1603090b280b030309060c0109050a0602071a0606090402 72
    0x4409804140300186203503642c3c0380010400520700600d803590081e020700804103c0b80551502d841d441002240c4020b500300070700a000c0703026201084098a00584021004900f4600b01c4049a03124814040d80365811800040c0c49144c880c144680310101510b51414180361110410102e01c1c031019140c031001a01c02c1880e526900c0310b074140da00e98400e41015104d11400359004c480706d89004011405201da4a580b800038603120380c01c0c80c0d8501074001003134903540c02040e8a9045000305400064001d4402010705d4105190407a943d403030041a40e000c11401400e100c0c003080101210304403a4054550102e8214071503040410385003908401401441c402010350580c000d8003482a0700440388180d00a0100000b82885003504104107590749008045203456002d408840c1041d00c228500c8105c050040c41c02d0065403c20020340307400141c40704071555200c48150000580600800c54450b20403580141c031081c40d401c0c24914031624280d142c0258000383d0511003255036000560b9a00c2030126000759 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 851357742 1250 851356492 851356507
    0x15050706050103030e010e0f0619050403021801061205131e060f060f0e10260a030305070314060904080a0302131d09120909040c080f0105010f0f06050f 67
    0x444a1088a40142009241100201c1015400188000144002d13a03a100c0181e00640030401d4840d6118080c0d5400318017080f0140314544e81c0f0580da1a11217441c10200e0600356030f5000304000c00784030a8403008100009005204031604441e6440c0000f81d42d0307500b0003003460401007080340f01d859a00c01a0000e50007882c0300b4010717410301944480c82070b03014a040c0301c10035900c031a0501402840c026240034000c1d80d000070940c00e00c01e1442602c94600c0d0303518005220300d0f0002c07003080440b001006043d0705c0e05007444106e81d03060070003203610141c0c0700ba42d00180c0c0b40b420800080c1142d15a0720001c43c0840c0a105100707040da90429a0754009400c02030440c0e98030341c0f601e0290024030509001c40400e0302100710001d4540c000c1c0c0c40510003901001080d0074903a40d01455140c0b11500c2c50140b428400302403007070032154145031f0700c086e40c01441980001b18803611440454904400c1d40b601940b1691584011702c1207092401020008041040882c2d200310b0424002034200e020707008a03114004408a00e49 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 851358992 1250 851357742 851357747
    0x60c0b070c110d0b07080109021219091a15060c0c10020c0d0309090f0e1002090a050603040f06060602060702030f071a010602030a020708030f041206060b0c0f060117030415 76
    0xc10902d40001d110030f407041e116240010a400c412140070001c00c007041c00001e0451480d00031205960503840148595039034000c68801c820f12008141c80489640d801e540340080e6a407045a2030020f0080d21116051034072031090721403981c1c0c2201a1b401180180440d424104c4000b540c81203078442182c29821088144104034a03144814545650007040d180482062507004a07015003079414440c1e083c400b1110981104003075907010040e80703c042e03101600c0800ca40c3c440e5800341c41e44550051030300e0182c9030380303400191540c0c01c2544d0aa1719034418540300800c2140f5486000c00502c0180054440740c40c00c0c00019407a40a10a8040c1e10780d140012503100f00001501d110809140c42901107509585902000303580381c005002d881c0152103840307070201321048004152028500070ba0007403031030641482c8140f407024141080c01c40790a5203e420108003c0d4414003c0c0180d00d8140380102103440c941d250b0703146401c00c180e2101a24001500c0140c0c0030325408000c55040e01e5412003140084a18030504 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 851360242 1250 851358992 851359013
    0x90c0a0905070e130b040b03060106080f25110c031c230d092d02101e27050904020603070c080708040302041d060403030c030e2401060c0b070c 63
    0x82ca0b409603513528038000c0719003103030320100b00380720190b8040000c601202e09043e9141e84c28000e0b174010541e950001401d00c19001516580210421402000b04072482c00f0360481c8003090145002048a040e031300c03030000301d0800640440040842c0284807550405502d1525003003000400820040c049a10744c0040d80500c54107244081c40302c8803140d54000044000000306100e05045407103800c50340c2c6020b20240c2c800e00c101208034140441c0814000c80ea402c101916010744607580a100d501d00444845200030030001224500035210000da11211503107030350388a032a0401c0e0a41200c83c1800c02c0c0129251081900d41c8168152103880d0380e42c03a490b2007556a00a0a50010030b088000280e02c2c00700b2140001910171203100340c0d420301829941460b104401201ca10051005e64029400900800d1003500219945407081c2000586040f0040c40b170350a091907003923209a152090442d4031020400070f11308600400701490b1102c81c2040704d944120708410003801c0d000c200000d1140303610074464121308 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 851361492 1250 851360242 851360267
    0x1813060305031306180305060a0b010c020319050616081501091511060604020309030703030c03060f060c0b0105040203061003020306010e040203040614090309010c14030c01020c15090c0a090507 85
    0xc490b2540c0003824410b0f076901c030328090240002c403408042c400d49500803945500b6203500c1030150855940d1001d44600078080d03180c207541080716440c68100541c4040c48852400c0318050f0030301080c2d200b0b50601900d0a00003400d08110748007000301c0384202e254860700c99900034230b078800005540451075004075612500c5420120207009000b00c0b203084150010085607041c00d2a00a81c3c04503a10501040204d01040321804540d40003000b0640c0041d01c030340e101244000540c100012250b840748494032209485801501c00f169050002d14103000001e68120300414080b501945145041004030350500c21042c140c0b403e0540100100301140e01804004000407805042191286450700b0130201a040c400401078500b842500071840042010048520011060712800c0c0364000c15a04d01e28880030ba0051003405d80010700402e0000380d02030009141c0b0344189401004550040a0307111400c0001030718105496014402042d0b1503141c500301171007214100c0b07500044550380c0d000280c40061811310b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 851362742 1250 851361492 851361503
    0x309061b090b07060e010e03041508040809060d140a14060a030c03080d0b131a01020c241204030206160219080d0e0a0c060906030204030c0b0702030322150518130603 73
    0x41040440d00c7c0d000025100725681d101c40528241107206064810b5101650080c12403a010010030310242400c030000c3c032440103000340005d90001c22a641000c0c04906541468a1544906010700482d6601ca030b2141c00001c122141c0381402c0c555641c1c80e0080c9000d101c0200700320400b091034002030380f0960000380c0340750300a080e1000e5140000c003400001c04100c9214942951a80d0703d15060707510004184040c4040541b0300c0304820400d250411000a0075404030342500002c010320303110404882c4605000e01d01c01c2c0c0040030740c0d00307108400e1035040300ca90241070110b50000c82d40c01d00461100800c40141130304510300a03030310ba9050010201500040c1101c00d0148101c3c50150100040519440100c851981c1c802c1c4241d42c54000c210160f1146200180c883d1065442c2070241e10000740c0280102480102141c0c0750452058100000340c002004080310301da038610007003255400c20004900307100d0032482e1a030b2414081554800c113981e861101d1900443c2c5400300c0301901d44059000c4400ba54110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 851363992 1250 851362742 851362751
    0x11b05100e1b280305030306010923040b040207060908070b130f02010323070804061505012703020d1b1409041b180e07050a0605030c0a0e100309061b090b07060e01 72
    0x170305003180c1c3c0e80d000b0340d4114006150380707800149000380422000300300c51010111116084032a000c03c4040c00d8100345155001e0390070420700000030900e10410020b64801d0700001c0e20355101d401c1540c4a494000c0202c40c920703d400e010030000130481c001440c41ea560900340021180395502c9100d2200391400c80d5002c1240d103150500030103a42100d0407901c514072845050003c0c07020789a11241051480c45000d0204020001238801500780007030000880074103102c50744149a907600061307500441d0304c905550060303040203e408540d4054007100050440101c25604801d652404103141c150004c1000e0030003601c1c0001001c01c0710000360080000c0074902c00220f40f0121555481c4020b1000080c8100c0c18807910788002064140b000c100d0703007110f009403951419940c0d07415030305885e58002d2000300200805400d07500215916004110007400740c80e40c0000301d69906107805000c0310110b10201c00b0805003150350418540d8020781c1041540c2c00d501c01c02e034442d14185806000b909050040110550a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 851365242 1250 851363992 851363999
    0x14061914120a020d0c090501090329040309030303060b0304020a030602071104050a0c270e150d1202010c11070504090212010218091308090d02011b05100e1b28 70
    0x1a030094000048400c604000c0175208070b9003650381c200300c0c1c0714090110b40865410404641e2403030700d941d601d8441c09040019441044e405c04213200701110120041450b12500f4414160b1601c0340b84050102d06a00c175203503080640004443c04141c4c44001e1965400050f200200038100c09803990702840070304180114109510040c020f0458010f400001132484902c3c00b01044c00d1181e020113411619408074026818882c6400d010880107115803440d40100b030b43e100c4903131241c08000744524000c4002580c10003907030074024251019203c0210800111403404a42c100004c120380d421200100d0b0002035401c0d00d0f2001c11030140d031640c0311103103651002c651148100c4d00000542c51007001210300310425070b50540e1081002c100303a01c010f810110180706001c0c043c201141c15034045801418401c080a10703181814000c41d1030410102da058110b40e680407148002e900503000003501d04805003d100c0385c60720214404911039110703035101d140807010108031251a1586118030940081e194100c450301c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 851366492 1250 851365242 851365261
    0x20c030c0a20090606070f020109030503070b011a1908090106032001020c090f060f0a0e09070f12030206060607031e0906080a06270e03040f1406191412 67
    0xc0d00a014003482011244220601d00070619030701c6040001c1100e1b0038444951146052209018401c030306215117801c3c040003003234082015018680c4600411f0140c2e42c10f01507ea1008050020082490700d0705100344c0034550300510401119940524003050103503681d03034dc8180900b01d95800604000b01c11590442e40094030100321003015020f0702110f1301340c1c00b06414068402006c580381c1e6070f0801e00e0004101d0502d400012089a0140204801e819640358002d4030b25510080e207445945902000c2c08000c041c00c040d080038020810300d490b440104000340c40294030f0390401040503100700700000d030290400d03000303a07640c0c00a1030f6065800e900d902040840980b520007680600d5020070b1071000014280b03509405820709540030f14182003550140e02000c948240c55010b038020792281c542166849100d000c0000e00000c0078802008031040785000c118801709802240703d00d009010810002501d000c01c0c07046c0000c02601868800c2414030010450f1003d80280c11248038180b5041090050900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 851367742 1250 851366492 851366513
    0x10090c11070f061e050f0d1d0d170a06031a0103050118082b0e0a110904030f0c0510050c0702091003030e060a03060306090c0305070603050c0d020c030c0a 68
    0x354601107603541c1d9140e500b034100480c2070780b0450b40028400034856100076000c1c01049042807103418500d003042c203284280c034101d03040b048407990120380d210340c003800700d030f418180420092000602418800c000c2c01c1e030081100095082e00d00c8640351401c049038884801d6408400256000b103400d001248001e011591808800c1c4800d884a60810f0944c0c1c811000e4460082c89103640240e03034918107203103a1f402d02d000c601c40c1d240910002001002d1400300304202d004001d2144d4003035010380042c19040c034009003030324041c2d000d281c01004070030100000039805c540320382c0c60b85040d4208010b121045181071451312801d401041c00d0f290824040c01045003c807005011118800c40310b00c21582c1e180031070815494918030001c0c0004a000c1c0c001d100d50b08211000741807152072072801041168aa4650700d0a541001c03034100d80c0c000c0c520b8420410700c0340a00000014012078a000d000f6400c100d01c6c40c5c0924001d0040c0c001030a136001860840300a404c0040b0b6076051101820754200b10b400341800581c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 851368992 1250 851367742 851367767
    0x80409090b091603021002010209091f14090403032c010b1e09010302010e131d010b0a061e0302040e090109170909041e02150306010e0d051510090c 65
    0x6000700340803907005040800c007008281415400754003500d10316000c2150000744030b0010429958204034507401904c96003c00d601c40c0340c6906494029801c0e5040d186041c10703040c2c0c810032619004030340c000081e6480001d0640c00c6909803401041d2142948107110aa034a205450002d004103643d107800c5986040d00840e0b50500115404600c6484118407410028485850750384e100510b280144010341c0541d800380880c420260180f9880e8407009448800c40c1c01203070325a94403003521b9220205024003400fa40806110a548514a5503e072480141811005c000c95041c049414042101742e24426415640104980700340b41d400760404d080c19500074036200c5025500c1010031400f21020440c420b00712200010080e00c0d40c1c6d4141d0762515103407042c441d084410381c3d1826030340301288003503a00c3c1910400d02c40511103405503242807000c00902326080480c075aa000d002e03840b40c01004502c0c0840c201001d0740022500003102d0b40c505100300040031084c1c0100071503501e0920342d41190b0b41c1c80514081e21 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 851370242 1250 851368992 851369003
    0xc070806070801030506071202040503011815020f0f0d23060a090c051204020a08010501030b0a18020105040308090a0503010c0f02010e011505060c0a060507170a050c0a03020a0c08040909 82
    0x119218041c0072102540c00b400090690381c45000031a43e2180306104103400d1440010005003401c0d200d000190944900702c0c0c2d8010750700451041da40511090114404001c2e41200085141441e2440e0900d01d501454680c05d540d1500880c1c101d4011800740c01c0038806034260a02c4501c8900b19540c0008080b00c255101402028040e402060a034154820b500c01082c1c95140d081c01c101e8015190112400b005000b03d07080900c87c100020310010074080c45010b944036084020991415412007000c030303000c0040d0056131401140c0c4210160360002c0454040e80d80100800c2d40d50344d22030780400d000741159803040f500f5610303100c0340078519a400340344040002041c0d80244030644040c42418203841c4400400310403c0002c3c0e0040029142110003408050043c00981d51245000d84ad04000c0741c80031076098010540e8030100000354070050380d030198444070001c420881c90820000140c80c500503509400103050f40003511040d1240580480b089582c3c1c4060f10350b50355501c1720303003034009040c100320b040b42c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 851371492 1250 851370242 851370253
    0x702150103061b030c1b0309080604030f08250c020409140c0117160c0f0602040b0d11030411011d03011107120c050a0314040b07110907050f0403020f150c0708 70
    0x10389201740210760022280b56140c164500440c50300718041c6c040c0d2030f070441c244104080e001131110410300c8100c2c8030b14040d88864441c020410780191546800800308140d0420403940b010700b02110400c030340d0b180002841c080c00d0040b15480460001e040440c1c0140600c84c00205100341d4a00008191071140804c0e40c80300214a000940701d08800310076500030302e140340c4104008001910030680003410328005e80b489543c481690700c406d804c0b68401d4001d10340000e0002030744c1480ca00740e80544071030f032802f8110161843c1750545603280d072148410101d504011100180c424803c601c446030b4402010014001c00c00b00c0d00500c0d031280cac154000b4400700c64240800500c0b1480381d000d207041c800b601c3c0e0884c02900003003c1503582100c0d01d00f6032a650048204013844082900010280503050f06031003803184c0d41c0210140c81c104080307000000d025200308401040100090342c00301c01907904903541a6020154951203500045098800030b9041000c4040803400c080e01101c009207007011104800143c98 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 851372742 1250 851371492 851371541
    0x40504080903071a0a12240929040209010e13052505030a1d0102040f030b0a0c02030301090b0109030b09030324100c050102090d0305211b0d11190e0613050108070215010306 76
    0x4904500c03e403d200717540640c2744c0849041a03001449100014074204010b00c2d014400551070304140410545901e5444007003150203002c14079207081d541861100305a0042c25a00024035601c0000c02c542d41c00c54803100251051051400b03a4070485d84084001c0d91203035220200b8001400c114407066071210440c1010880501a5100c0c1c512660501c4d800340d131440e0300309040c8101801311040744a04100914100002144c2c40c2d400d00b034001c0301d000e40619030380c0c10f0205490381d10580072450b40702e403065500f54100465840640f26003003840d540c1000c0001040c0380c10304500a000b00c02900c0d4004002c4d4105004140d88500103122401e10000e00c07228620380c21228050000301154200c0c80c40b44811072511030940b10202902004482d190045004541c9005007002504020207043d082401686855110b035084000c0341d007200c4043c1d807007900384508103100072081c0c1003e20076181403000c00000705e5a00341c4284046076460001d014208202d59491411000170094010b80030850b88480c0c0c03509 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 851373992 1250 851372742 851372771
    0x18120203130f06140a0c050312040201020c0109081c1106010f150815060c0a120807090905040b0601180f0308070c09050f0406050c0702040504080903071a0a122409 72
    0x10400d440c4035035115034441c131405512001c1503212012200500c00c1c2c415100c400241d0070001003010001843c00c05e5141d090074400a8600300b644000581401a03d0009100d80800003948004c42103c000d40c60310000c004660645905d5143e424080c614020000003041a420b00200d900807078841024101c524505000111142c10007a0750101803006001d03055107251a0000c064807c105103071050b01c101504903034607050410954101302c404148100104060103401841007001001c0c4000284980c0c83d06945040d0744610050030f0a06010440c1d0f445150003202514840c0607224070111080c01685070308240390b0036081f942d421039681300403100114208803035004844c09a8075011615015444a540740c00150078000d1000b180340b04103009100150740e50b0701405004038041d00b00155a44c0d07101040c03506018240e0840c40b078400d42e641045854401034021561260100c1c982540405010b15503100a04031850312503845070b82954440e01e503480c8016040d030444205140c108551510300222 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 851375242 1250 851373992 851374019
    0x130b15030601080f0d050a03020d021215030a03020a060f150806010f150f0f231206061e16081b1c050f160b01080601090b090c07061812020313 63
    0x802d0345070b0441d417902c140a6020f08081c100c21050f03030801500308041d4001410490304400c11824081c50701b0014010040c0c007105000c580800c003a801350049920310344010350b42e024010300c01040190340360f00d0000d0001c2d2a0384180000312410840303040d070f941c0d10020382d40d45003002c0c080c0c540404020403000408042e1130344d46022888076916045c079a0740c107610f0256200e21408407503006200222460000c0c40102c5811400c00c103c084081c5a11a5440b4401c803940240040065010b08401c100107540c1c1c008040008540c0c13458845d6090b80c3c0c0c0304886100319a0f042012000b00b5940000c1048811920b01d044100e291300400030840d0103141081508607545c044034001c94020420810489030032035481c1d40140b00c101c0d2a00181b030603007071055941c0c1c072030480240e1203604103411182c010700c0028010300810515440417282007140b405c1c4800402030902c12410700820fa00d50310340d242543c014100e10b20b01304064101480c000c42924558000e91070794003810b017100f0000e040c25000b00b03160031341410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 851376492 1250 851375242 851375263
    0x50d0503270717071809081204050c09040f03030c02010902060426240702011e0f0b0301050a0c0306080703080d0522080d060b030f0c03130b1503060108 67
    0x2030310304008180d1050098540340758054106a00582c6004111042030420303843c03440e4404401031407514640700c030b44403410026602d82c0010b142802504408118144117441d1112002e1220341c086482d5498107030f00c3c02c1455844140c000810400304014080480007400e003d80c0a902c1c1440f0004861f0412030884400f02402035001c1810f000030b01050841042018109040fa00c1b444202810307034204074642216004036004141010403c5840c10f107c1d030080c1904800c460000344540406604500154101d005800045c941e660400c0d4800780c2190300070490301c4802034020002e80c04c104c6c8a000190140810b0040403c6c07d0060000343c00500040d40c1c0101c81e041040c0354106550070900c000a1b01004c4c0200d081c0c2d484000100603070340c0880003102039540c458000b69503502c510603015000c3e078609070f0000300e070b8000030320400521030206407629511180b040f40d22643d03566013030501010b10084801c0a856108980c0070004580c0f00f40d0360f5211407800c110100c81c03140eaa1030707040c0c82ea113010980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 851377742 1250 851376492 851376511
    0xb0409020907030b04091e060c0f0504150302070f0606051f0c0b070e10051206060a1d060d0e030d0e0a051e10050c030a06050f2805040606020a050d0503 67
    0x400081101d40f10360701410316150002c0020a0035021601d8020112903000c16002011650160301010006c06103d4200015a103081c642c801d20304450b400fa00380e00903403003040b501c004203100d030a001c3ca00c6641240c200b07a500c022140c40c201000e007001c04c001c1c8a140a401d0103840740b807461080454440e40240315109040c0c0d01c803200442e01c0d607645001103030040e01950a00402d040a003025a0351502e231106500d1040c3e60b40780e2290950384040c1d04842c005000c150060404000c0403c010340c1c000c01c0203a400c11030b80340580303000d034103400491a81e1044484d6048801e150602c14600d03218040002d013813a400551041c003041d1000c2e8030158235141034040040465109401c84031003004001c4103c46007211800648440b10760006900c01030354400c0f2012160316000204102d40908070344100805000b040d2070004050000740b004c5200d000c8912400814502480d80e09001120540164009080082c00030700441740d0f40e09003e951003070082401c43d00c0c2d0040110f5070080d14420410f403842044200d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 851378992 1250 851377742 851377759
    0x10905060708090d0f050a0510151e08030a05130e010b070b0c04120303090204051f060e030f0102044208150d03081801050c04091503060e030703030b040902 69
    0xb540d420226621910300701c1d03000407012910402040040ca207003c119401000038014514681c5070140c100004511501c0701e480ca40080742d0b0f41c1e0056220120f0956142000f4002c9a010000c00c00f240a0007031340c00351480d40300000b030300c0d50b2040d440009400f09412241c1c061080b02c6e104c411440e11044240551008650240107040214031404140d40d00a40280c09452610f51503440d0311450803240c0b80c0075408607440d40cae064021810a032041740c0d400144079401140140c00c83d801d8454032078141c446c0000b001070404450f00780d5517050011442005401000f1555595603038403110f200d546440c030002026400242c00c2500e54212a940b1064403401000b064403007020f2a000d070760521000d0301d01200c0c05000c0c004651540c4860707000030900b81c0240c840c0d60441c907084000c48d0700c03242848003d02d201d0341020244821541c0a138241d80c01d03909142c802281d0071500c40c403030078030700c4075554805041c00b410030340f201d0424070000c40101101c901940e03080c400c14498000f40010780f046800001d40000301c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 851380242 1250 851378992 851379007
    0x12030c03030c070f0b010603150b09010807032012010632160f1b060e09061e0604180b01110307030c060e0f0c0f0d020901181104090207030e01090506 66
    0x31203009241d218455480c000024007140c41721903968100b40c0161012036920442040c04600c1c90b00f031480200a00000c00e80341084c990f0000b050010f0151400041c1511030707401008071316000000d804d24440120445071203064201c03104111903000e200ea1f002240c101000504454081c42c05110010741c0b10401d02c4401000c0107404a10b640500351611100b4080e4051900280a03000714511080c0076110b040041252200001d415030030726406041800030070014501c036601d41c3d101495000c04101e03403041c1030f00a01a8801950010700d09030982c0660001000f00354030134804449900342815200401500c8801c10065407032078010701260800d60300501680d00024031aa6010410b035200301c3d800704400c070b01e640811740340041e442400461500b004104400030f060401400181100440d00c23040e00c0c256035008110b000380180180b6029260313003000b0103000c03030176500410845607440d21902d503140c0d51005950000e4001e00c04c11000100d0390143d98020798854059076064440040500746040c14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 851381492 1250 851380242 851380261
    0xa06050102150f0916091e06050a0b030408090402071a1018051819110f09160e181510080a0902130603030e0112021e07020d0b1512030c0303 62
    0x1820000c0c07601c03e400d0301802c407030174103100280103052004001c9085a0761042c40b800d240b0046100e102101d103820390402c83c5a0302e04040e03000711240901c4580e501d0700c0305d09104a41d442440711068005000040c010b04100444c6540795400000c061480010340721001400c0c481c1c0514814101c14658001041241c42401e03070219400c142c29681c070000710800318010710b05142c410954801005c551070704036000d10a82000d10100134204507901d01c00c103940760000913084c1c4005000c0404654807440004102c07805580188800b02d0010038801140215065000076081d044a00030102d03124099610510304000380040a48805526201410350fa0440344000809002000782e030320050000c091125040c140c800c2c00040c500030354500c001075040c01c001401824800c102c014a40340b041210011100e0295004100c4007200079240c2da0b500ca81d40001815070b1551309029007140b40301000d0004c00341070503201001410b41070f01c0c5200344810381031865441e401118014a13803a001040001d90703818 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 851382742 1250 851381492 851381521
    0x1b01020f071416030c090f02040f0b0c0304030c0e06010e030f0c011b0b1906080d0203091011010e0604021f0917010e0f0105060406140d11031011030a0605010215 71
    0x1910882101d12082405001c049541002d50050b42c245405c0081408203240074041c01145411001d415480c041c5842082c480d208250700c80c4500000d00422044d140d82003d01c226001140c010b034405018a4540142c0306807124295000740c086011260b070350b000360401050301600c8480000140000012440054484000d0700000403180c9100b425041c0004a81d1111300340900e411404170414201d03d08503102c11100d994100d1043d60307102a010480269000044400d094000d0710000b0514445000650741500026038901c115400e100060421190005d64503100d14002c40d020625403d0850040210149186191001480b22078041c000050141c0c80ca440c1d400900c0000540d4081d1588102d060091207641c00c180d50351218107120961905000e200c024000040d06001340c0388681c00010503144503800000d2081205107024401941d00344840369441400500c140440e11321004c443c2d4072503004442c083d01c121324020020803e540300141d210a02c840c403810401e9243c442d0b82d08444104e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 851383992 1250 851382742 851382773
    0x10621020d050708030f1905030112060f09141f0e0c040504080903070e041205031501030c1808070608090708070314070302040606051902011e09050c06030403051b01020f07 76
    0x140724180c40000c200c84204010301b801980500d00985443e2400030b00d40c440040c4403044420440207100500c0340301d0010495101040e8468800240e00703541200b601b01600340003e02601b03c4002c1c13800c20310101404580745130841003c450b07501051164001d000704541c03030b0004001055001103d4044103080c2075010b03e0b005801428803500b002003c900081c5004520740001412100e00303070a0008104041154148210b024142030f801e51030140301c1808a40503d41c00f039810980c844d01c3c200c99407802401071200d410080540358100b907444800c100d0341c03500e06210704c4001604040005100d501b011500c402510922009003800c2403031500d4000c0007615440c218903581c050800000010f90780c61240500428041d2142a21420038060181c4810900000794003903904003c1208466214842c4c09074204881c1400082d0b402d120b801c00c00d24203040318003039a0b0031000001c00d0005040d0000042d01d030091400e103038415071022400c0345500f030303018072400300300c07101801e100020001e503d102004045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 851385242 1250 851383992 851384003
    0x70b1f14011d060f040329070815090a0b120102040e0c07150504032a050703030813050304090501051c0c2907060b040b12070504020307030608060a0e010621020d 71
    0x903281000001c455030302141000184003400503041082003244a0314801f41080540050990348110a42c410b021800500000401242c5030002d01c4003021118000c44010313000c0d040030315614000d09018020080765507002c0c401d0070280da0001000b0414001c031819a08a02d181c0c40807070b260b07400284802d03008084100d9410a42c1c00840c40d0010382c81c40386520441c02039540004030003140e03003c4020082d1804101c0d0108201c4196800800c030b000810900300c1c0e52516042c4400e0b0b0302d200b540c48180b02c0f080c4005100d400009400680000590807850683e9011a034140c4001c41588400490040003d4010161600c2d140c00b00f01c4103110103503017603d80504900118039a102c0345003286c010780c810b181c201c5125946109501240c101031003854031a444c143c9402a03000050342c0340075074501c80c0f845210310550b00000001c031028403980044004104027412101241881000c40d0060100c0c1809055150703c1c0c91342c00600284003183e03011010271208005903100c0b00300d0b0240f010030540340c00d080c5c44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 851386492 1250 851385242 851385287
    0x8070807030c1707120501060504201b030c010f150617070c0206090a030f230c0409022b031707050403060c020114180705060702010e1212070b1f1401 66
    0x96400340c400d6074034041e51281b80002015400d10007040216400ca1f107050f1518004c01040741058101c1004490f410386007400301010100061298134950f00c14401d0340c41c1c00d5402d06101cbc1d03d2088040c2c00c07100c8045041c070400588070342c40304030803508004581886101c10f00d52901040b4080d000c1c00710120001c0c000742000d0303d00411130020814201003903200300c0c0d800112940c41c2061000c80c01d980301118400004071015400d10503200c0741c2e20404042264440e940d01c01c018411503581ca155146081d04108140c1110030050031606e80400c90002e0a8000c50138106000009200002c0e080d0300c034946c0f544034141040d066032505401041c511416078195961598001c003044081d92856214000301014401000341c6e0444260500c003507035221600540c070610403036005030780011103402e503500c2c1900e01c250803014200c40d40e460094850303004039080c0800124903041c06800080e180c40303a041662440d044001c4080c055502c802d43d842000c00060041601243d6903100750100c0d13034881380b51a11802d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 851387742 1250 851386492 851386499
    0x6060904151b021e0705101205040b16092106020c1c14040b0d0519110909010e040308040201050a03020f030c0a0e0303070305070f0f0b07080108070807030c1707 71
    0x40c202d0b00d6400300c03840001401d00790391254590403c4541320344000d0701d042e00316000f00e68030380d9580d904041c05140d110710901c00015603c01d208145a5144508640741440700f03007401c2c00c01d0b04244006548492110b07800740780c0d01c404180103003903900031980c1c13100b100382c2c02010600d00d01003034035850b4000b161415003c000a1182c1c0b50100301c000855000001c0c0001e5021440a01624150440d035001412130801d1000b00480c280b0794096a8000625040c04109a0355041822204248070a4800c0382249052214418900c459000d030030743d81825200f4001c07d0f43c90700b00b90b0300d0380d150440c0c00400054800b0002001540302e030002d00761100503802c026091003881000704265800c1180d20203806100460030340400350303200c561600c5510303054000e5883c08403217490040081c400c181001d0f140c14010900032081005100b0605d080b6600001d84990505108600406081007882688030f00d02c11407101084100d03022426a017100d6105001441251510321110b00099070f2060361000c1d030107040ea000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 851388992 1250 851387742 851387783
    0x170705010f05090c031506100e060c07091d0c0d110409080309060c030c0a142517190e0406030f030206090f0c010507030c051e0c0310090506060904 65
    0x209001000d8040341c0d516190003c20725025454003030321310981c00035914011a940102e00203400072000c2d1155001c1c0c1c84408026200d99403018102a000f100001d80250700540200c0c64a003500e41d0588288280903943c8805000d607901040c0d00784954100c0c00b02d2a903140b5014000d03101131407040c40002e6041c0c41080000b030071540c6aa50a6501394800803c006540500748141c0e5440071440c10b4080c154104599002860302400d07070200e041c0452110364015145140050b54200700c7c01c4c041900b85000f48059000c0003281c0c1000840710741d1221070344503044a0703004098a803004000c0384611090280710004070340101a03014450b4000769600c0001c008078a40141441880c2d019030000c0c483c0703080554491b8900084070311041031030703044040c20503081d1381d1000c02c464981e601454100c4400e8803a060031400c000e54a00440e002e105500e5612088400100d040c0c48155811001d440c0164560f01c60341d0f041d039960309001042600014001421440d200000d160810b00883c601203600400c082754 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 851390242 1250 851388992 851389001
    0x30c051c061503050609060108070312030e0313061101050c090f12010f020a02100c0519110d021f0902060712050715020d240306020c1f06150503090a17070501 70
    0x8802c6440003501d0034000c3c01310400c603190700412042c0c01400d036036161882d0981c5a08140c00020b09091011060a4001d8441d0300187c0038551385c407080d01e40e03440ca200c411180c140d40703138401c500100e036005080c040f0324001031107810710503207100e054285484455006c00480703038500740c002e070b0f1700c420651a0210020001d200f06007104120820040c0d4641400f6006032400502c0c500d0408418104012501c20580c0b040a0380c0103410307a0108000c0b201002a4141ca41c040084050341c0f207072083c0d040c0070b21900d80c001803040d071240d0311120b41241c2e1100b201d030f01400d440840d00301035000382d003c01ca0707840051441d003106031410445c0d20f805410700d0000e542c0c214007404402c0d80c0380385598001c01d010720741000360322036001003005665101c828144200c402c2c2d500c2141a00c000741902e0b90200390540c0440040c05090341c545102203040064100e0404d040004161502903101042000000014494000c100b00c070b009a00d50030050603114034560f54910307901c070b400064a00e5a4030502000001500074040d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851391492 1250 851390242 851390261
    0x30c2003070606120804060309081603360b0c0a0804140a06030e0c040f150303110c032116021e030606031b121905060f10030c051c06 59
    0x1455071240542051402d03184280c00c00a15210078070203100c006010300c8211000c560f2541030218202d03046007400074582c040d50f040039012400b0f02103110301305644840c98a13500185a00c1d02e41c0e810804441480d5010304e8494084401c20b0525024404104d452000c0c200e00b0190308111103181000755075107031641c0c0250340711140b0810202c0c3d5001080ca00402254090702c9140790402844110003561643d9442e624040c3d1f001e0350f03503007040070948000e6400c28000207020307003c002c48195603850700903d030071580348030345030305003da90303000750aa02c0d001c14810311303000704240305545c3d80301f0412000740141e000f0035a00c1081c3c42100032030700c016180c0300c81c5002c012070788082e900b054060600a0505000c00100a41d21a4200c003490a190844145c00004641780c2515000b0302c82e84100101413420b048444038120900030130040b102003000004903940f00301641ca406580799100c0b026400200c0300b03a400b009180411106d014080c03400e01c8080b90407900c50b050720165011941d43c03101e0013191000300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 851392742 1250 851391492 851391557
    0x40e010602010b01022a0f060a050c0708060f0126070906060323010b0f0d050906041712041401090c0f08210403061d030a020c010806030105041101030c 67
    0x4004102040e0280f10b400b10380342c800c0c000303421440d07001c60f5112401e551b8408004400d0070074403200d042c65160380707442c0348a01c40f0190625503280d90310f10002d0502c0d000000f0489d810b1043c0352001c507500d00013103685401940c101503e80d00c207074200089484064414801c410700420034550356058803504002c004014209454000380207414090004c007510010001c001c45070780c00f01460342000c184031180300e0440302988903079600d500d00c44052801621500c03e10035102810301c07082c03103150301001c50100e004900c260745144804503840d260144501a00b42c1ca0b0b20022215400180881c1401514000101c1003000001c6d4040c407a07034641e03060040075040300c050280c4041062209410410004208002030800403514400107050b4114a00c0b0394003008141e10745540c0c0b2a00500403810f00211500420415a900e5a25580d0000c1d40c62010366030460008404001007146402c0601c9214010b5400611204440b81400b0040d000303403002d00740324010440c6151400d010345142d400150303c1504604e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 851393992 1250 851392742 851392769
    0x40201170f16050a02105114101b031106090f0a0818060d0c020d050306030d080417180901060e10180506030a2406020a0f060f0204 58
    0x8015080c14082c2a101d64024480104003454450b40c000403008000040700c040811080d44010410f02c81c1030b000045000c1802c0c244c003810306080d542040d400c0b021648401d4200d0019018040620070812512800944000c442d2221900381460811919500c100742000c2d0000f4007030040340c040b031400042d810703000030b00400160b07042418280310558004080c030004141c4114807030031194880168002c0240b071034800045030504d4001c01c4590303c0c5130810040020340c0b101d0404040001400c0c1d1541c4020040c0182c440f103150060061050300c4c0034200140050800300c00700308040d202c190014000b0f40300c1c14141c0c441034401034500300050140e007240444401400200c01c040c800210010f0300302c1014011032540200803600d44666802c0c00c40c80d07034503100c00804035001c0d0710800c1e40110b801641d00a1000020048110b4039030b0004100105407803030250300c2100102c0d0b100b17280b4605002d03190050304132450071404240c0c4c0e000640390701070061000042c0b070f004413801541280d10070ba0000c0580007c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 851395242 1250 851393992 851394001
    0x1e0f15020f0601050307180f050c0d0c0305150909011409100e03070314160804030308160306080c04022101030506070f02060103080f07150c080a061d04030503040201170f 75
    0x188680c50303400d06564000d0000f94105400a502c8134040c0c09103c032600301b507403603510a486940e0401c0c0c580403400582005242880561201310b6400600107181c41810301c10320f04001c038072030306c42d9620030b90300ba040c0780c0b89180100003000700c134000c00b0f0208201503480c0c0350a110074226400b81d441c040c1084c000201703d1050354940c50010385024041c0549030750014014400400d40224030301d030104601c01541541e4240c051101d4030030702003440303010b8640301c4013040100405810008450041c0745130840b0035442d10214000724241d9019009501c50307034000110341c0340310b8181900134045102034190305018284002d0b92146404200368001c1e00d83d988401e05125406400140076000034546201a048560540e2a810758a116565a580c044000000c028080c4080c4030600102c140d80c1c03500501c240441c292000780800e4040d1074070840c640ca0b081c000510303061884414104403080809007120f42e80c55031415070340c0380c100900603414001c00d0840a0388001c82030550501c58880059032031041d051 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 851396492 1250 851395242 851395247
    0x10e180f010807061e080403230403141c050306041d1612080415050706090c050a06030c0206041b0512010c020d09050f0f04021306230406091e0f15 65
    0xb0a43c4038800784410076403103602c141030040d40012120314071b0a00001a884a00e01206c0b00e4100c080e0038000145c15039a140e94000c2a00000d0040302d001d0f000c00318242c80300440084c0c1f140701007a04030071030041c5203186852050007000510741c004402440054514480303802250307865201c46044496402c841b80d00347da2000c41c83e0303283c0090b01400d213408283e03855695400d00380344030b140182d010600039071041c0159a80b01c4c0048804050b4420420b00c00400c5a00d0300015042181c0107003446411480304c00f0071503074403a10803075160f40041d50040c00e081d12140c541101442c2a0b004100120b803843c0008201610b46c0e540d4410a4030707000300005040150510001d080c011007070816010040c150a08012139a10341400200514040394102a10040345000138000d20400105501407031401100040458022041c918260905042042000200340d8240600c0c400d601030317040800d040e49000e202c3d4030840c1c0100d6860301c20f00e050b00d54240303031520315038036030a1039685c05070341485900c80f10f1526166 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 851397742 1250 851396492 851396503
    0x6050d03020c0a0920030c040b1206090f10090b0d0203010e03040608150f0418051e1203010308041e0b03131406011809020604150206010509090c0105040302010e180f0108 75
    0x201c4d1001040001c606400c4880300000c0d400480040060201c081107010b1742d01b40440d00203100060343e0654500c01824039920340d41044407550b10030128040068100014021941d12561011648001d03082c01c10060368000c101c0d8034002500506040204001030f20300740b0441d03841c08118001551140c0c9401001001490010700e0340019482c564600821900c45a45425a03c00103c1e0701240c0c82c03042e118900000a40510041d00e20711034080c041c450450801d2000d01c038440c040c4c06403190700071a0150080741d88002c0c800101040c2c8200020440101400c940c684240c03019400c0c03e000540c1c0382106291900140c0380c8150241c10003804e101000510040110b8410b1030300c01a012940c540800d10301d18001660200c507150307464a04000440d0b139000100c4018041070044011f1014002070020759848090040354001e140242c0030071805200011040d0803c80141e650510301806c0d0b80c01140c800c040c2c5480d040d040001405c80115405101028610503038003103000c001c8a62403c4407051512 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 851398992 1250 851397742 851397749
    0x80406020a1b14120114010f050a0e04080307080606120a0506100c020d03050a0905060d0b01080c0325030e011d16050102060105150f0a0f090f0e1906050d03020c0a 72
    0x202e6080400050228450041e1a02e4003114900d455100d000144da0140c600542100074965421307001082c0c0c0020000320009580003a00d02800c8642ca4040303140c51414242c80241103a1018000554581d1040c2c080d0b950140b0085e1055080030b03002c07a010407101e0301c2039818204041e1038204000942c10000079031400348440340782c500b0340b105041d004913040304001103024041180000b01c41000390f003e01c0040700200400303000300381e441600901d0400203105821000f0700241c601404a5420310700d503001e403070003010090f0807a0302c4000c41c02c407000c03000310310100380b14249502d0b00c640b808002c1081c0305943e0302d844408401081c800c901e81850b0308125880d0440400703451091030038409139a0000d80315054460503240e2407a15044440c86030514007d07410300750505040003030015a03c4c1c1d400704101030b01140940340d41108030344900481103040c080d40240108811203100169028000340004021214102c20005020303840c6c0001c50403a0700c5504c2d042d000750f4403034110341040307052449005005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 851400242 1250 851398992 851399033
    0x506010c030f080c16030809010b04022a0c040501120201350a020c0d12060b03070509101e05070b180703031d0d0b15011106070c050703080406020a 65
    0x840d1460390003400301600685004204444800002c0c01c200702c9100b154400380c070001d044900c480d00c518004108034421200d8090340d500304101224182014003d44503503001c3d80f0303140b0b50421070440d40440444c00d1440d00c050b281c407811040d00b0180e00c0b244200d40c040e0446a19080c040d01140c00007602101c024803201c0c1c03910040d40c2038a11804d241c07128041707020100c1c0c2c49000e055151505400d0190241c101c2086e060300410040d62011070304420b068041d11442e84080c0b20040d914620b410300c40c0000c17115070000c1501000710101d03500d05444480c03550005410801d02c54081c84000401c0c141c103110761040031800024182c001c1c0705030681e01d80e5114240084a81c608400303103610315296809840000e06000c80c0d45041c000d51000c040d0f0306d002101c0003400f110516500740c1480703a25904107482d40d0b10700500258480900754031804202c4c481110050090a407504c50b03650440b8001c0584809880b2030007488030100c006408480108014400c55008108000c01c0c0c1c10aa034035041c0000c0c0e090705 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 851401492 1250 851400242 851400257
    0x41203020c0f0303190c0503040f0f06020a0519080c060a0203061504300b090703030e0d0b071d1503041a1510030e0616020f03040f0306270f06050601 66
    0x2510f81e40001207030452103030400d955642654508040e6a603c00451008000e40030100c1c010a8002c89500c070441254000303842800643c3d42d404003607031290500e140261240c0c12010000b03407010500184030074040d114650342403814010102150030300d0f4050303440f1480c1c95000018800381d480c2c00810400f0700c4401c0c400007403a292401c40d00350040070a90440c00c50300d041241e501e403400c01c03124501003aaa50030804001035842c04c601c0460311010740380000c90100f50303500c907550f54500f404006c600720702e54001006081d0ba26200381c2030701c8810704d0560a0040120441581501d0b0301c2e600d04a0580f252240362458507400c0502d4100d90040c4040e90301c2503043d02407400c01ca403061000180b1103500d02e041d21064180030a00c00700310301501c072102c02034030b1f5403041205000d551040d031520001420101d500755440000040d20380c907280e1149100740b1680c060b024005102242c8194021880309500303080d03014001707111000c0060441d0641105407190300c1c14910b403106209103400342590101c0b09182001e07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 851402742 1250 851401492 851401519
    0x105071a0403141215181f0b1c0b030102041701050618040308010e0901020d060602060a0c0e130e0a0c180e0309090705070c081e010b0607080f030c0d02041203020c 72
    0x111850001401c1351011120b2100b2188a51929008940702501b0503071107000300c0c60041200d03c1c20702541a1f0328008070001c14000102980071400340c40120a50005815003801150400000f801c55840c9131903155508010015030040b100c2d06060710303105110004500d42c6030a004201030036017412205401c10140348100300000390701c404400c1c151070a89201e002591a21107659009000c1d0103e00c1015a00c0d0850104441d5000141d4900c200c1c4440300c1840400070800e0103d0302c001a245456404c40b07955040c0e00305888403600200300d4951f6400403120421b61640b9201600c1609500500c0902821880c6c0c00001c01c0318010707061400c0c0c982d0011864041c0c00004035001c403070000d00a8042040200c1c4140c00c02941c0b4407070b00004c01da04000c803181c0c1c028031000342d17000841071030815080f90311b01003501d011403c0c181d007900c81c2c40b50407403030180c00c04140d601e190403581c0c4000d080f000342010400c40f5408400661000d44050005181805212045071034041e14001d40708201c2c602c9055000000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 851403992 1250 851402742 851402767
    0xb040501140d021603031e0b030c010c02060c061003050f0a020102030703080406020d0903020313050a05090a0c14030c0403031412041709060c0609071a0a0503060105071a040314 78
    0x240740d01e4640005560b5808481880e4002e0040550507104000015410304c103142d07140d00706800d0040002c04052071a41180d03c0c900480704d068150a8040c2c001c004081210340c024601c628000380040c0c0040c1c0307801d000c5081c0070b0400c070044684082007104407800f407090010401c44040c010840b1401085004003a40010f56a4080c441c00107003045036130030000f41040003503010380d0507810944000f400040311038076002e034030b94011004c200003042c1718040004082c60081120350440b140a0140822511400a1800a406150000414001c00c0b1220001a244010041d4820203d0600803502d4a045242c02440d02c0e8040119010100003031004000404030011001c2d001070b40b0038118900c1d034070340d00311080840c025504059071141010401304180354021581500c603c0100c001d64040c4c0352188440081c6c11100c42d0b81c0805c04005104da5052180035400941d0020b0050502604084c110b940b0325100c0354040104204100c0c6080500003016001900602d50040e170141060416403019a01e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 851405242 1250 851403992 851404007
    0x1208010e01030b0a0c030902090420040204031a04050a02030d020d09090b06180301111303020406090207080726030c0d05010905070210110904050903030708010929010207090501090f060b040501 85
    0x300da04145d51200001c082900960000d180c055007e0042200c03444e050924096002490802c2e10095816140031a5245070030b10854003982e50100c400d40021400c540004c90740702c4005c2c401c90300e178440c4042182c0980c0d4100030720002c0080d03507401040011a2060300078102c03106503109444107410071981085507a6544140e56204010380c5500c03808420f0341d0300083c090070100c0d01d003000700040001c0e00e5244007082521501682d009880034001a503070f540b1781034101d11452101520601c01803003030340000342e24050560002c3c0649070751160560380318050001e0652060310701168200340000c4945044203107028a6004200c195000c00c2146086040a0b480d00c1c441040509030582d100300104280340080c0688003901c2c3c018004000070b241100340c0c00c0da80c0d03009171240e001040900000140d500068041c000c05401c03091445a6903141c1c0c50100c3c80c6680d100d800490541c0600040401d030000103205040c001e00400001048014030345980e03801700e036000d400801003a00100b00a0096036002940c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 851406492 1250 851405242 851405251
    0xe0703080c0d1e27090b01140a17040f0204050106050322032f19051006060c080304031e030516080603060403050901020a050f0c04050f06030a0206090316031208010e01030b 76
    0x4010f0511510010100341841880c596646441d11101000c1000c481c291b000c031180c3d503401c0c2c0320210502450020545640590141c041c001905044c08108401c514182d030380e0840c2c440c4072aa2048031203580050259402600203200247d40441084107102c1c96403642042160f110559402c1c10500352801410b0209003035035901c1d440d54103503452440380b10602c001d20030048400c00b0b407103d030300b0321803d0320340840c482c0307007055825120701c510341540940c40d446003034200c410503211031018212564440d151504014415414099502d11003990980049483d05214145035000500c6203802c1445010a82c1c040c0650780810900c04200705840c0c0740025001d41150709800e1941d100c074180c400403890481c908400030321900404020b00420f4100052400544404a4090003160b4610080b101d06807400c4404907816030080c503000300582001c40040072544005030030749568032040c040c50700d0cc3c5003031a88120350b140490a01802c138140e100038a1800343c28000d007511040e515689401919000162 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 851407742 1250 851406492 851406497
    0xa02120601030b0f0409050309030609120a0e0609031b1e130f06030215071a04050d0e15041805070c02010f0807020a0c0602030901020606031204030b0a0e0703080c0d1e 74
    0x10300c0351125649130618030840c0c280c014020b02c444102d1b458034030741b2908402449030184c4503440c003044080c500800c0e184603150b03032a403202e800e009201008880400d0800901ca0b000320341040443c600b501c0078080e0299040f8402080600022701100b4065140150301090140110b10003148605950703c0e000e010543e41804408205410b418400c0f500030000d61303000941c4054140c00e11040f2000b004090b010041c01001501c140c1c82c0d010b14155402d50b0100e0f00103200e83c000610102c0c81502442e0311801c407500181002c00740706080080710850b980a500310b40040b10034112201030700d42d01401807680c030043d03900d8101030182c841d50018266a900100050600800e18000b440040c401c0040070070b00da800c0744100c10701d5551600041d440740d000d40c18040c018054400000c5050400103000c40c01d4107a48084245450700e035494840110314054844c481240d110314000780983d01c00c001c42d4025600a2000c0c9503a20b8001440c2454040340104c060309110300c0c4a11a6803840d0142805014580c0700d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 851408992 1250 851407742 851407751
    0xa021c1e180809030f0708160806010b0919050301240b072f04090308091603080a11010e150105010906030b0a05010c05010209040609150503060c03061918140a0212060103 75
    0x1000000d05000c0840140461482031846c002541c1a00107140c81c0088803c04a0340c140503250298252106402d028012542c6c50130010b050740c604040143c01d04240c2e485503031301c80840e240c0c0000382c05d5560034601c1c00f4544150181401d0b41d9660100c204008040a554040c9054829907902d044e408803140c070104101d80c00207206c01c100400780c04200f40f201c4010000c0108044615016208000642e070800d1203204480304898a604640c07070b40b900340c9410098050500d020000d044030b13000b5160300e961840d55214551064002d104000e00d1800380544804940c080d810b04000601d4510a0390003a0105424145007900c1c40d25101444001e641081c44c00200c588814100940607201c1e1982031604240380003070001c0c0400003a8010540503d150307443c012400d0b5541e040503607880094910306c0742c285080010645500c0c0080310060070320900588410a1799656200103040c06a1030040b0ac12070352a40030311402103c40808a40d403140300c0079021400e02401ea09e0340d07103150100406680c103040e0f55 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 851410242 1250 851408992 851409007
    0x4111201090b0102100c031a01111c171003060c0518010309020a0b1201080c0d02060301090b01020f060103030e030c101b021212120a0b090f0a021c1e1808 68
    0x740044005221a00814010f113003c3c168000c0c0104091f48ca004120303031008091180940c480c0d1012107200360b0300d200404002020700060a8082400fa1224042c00304045070303440107400c0001d0040c416148a106601550b02d94100807041d52800c8a040007000004c02c084000885102205020701c0d000703190005072201c091000c5032800c80e080e000411608c101281c6000b0303503104070310010f05031b0b103186043c0c2d5000b40c52134051011000130081d00039442075046c0300600c01132403c0d0744021810281481244d0701c0b00c520210a6050190a0304143c0029008841801079810b0030401400c444500790341141d00060140c1000300208140740b0120a0980c6000b820b0303042d980e0b031041d04100400480c00b51203900840d4660100641d0280ca451660642a940041d020b41d015105440c000403001d80205d20903a20b0760b820052040d001400034900c10f5090081c44007070030300001e145114002d102d2000603d1002281076011944009886180c01800c2c00000040b05100e400c000c01519481002103840c1e210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 851411492 1250 851410242 851410247
    0x19021c090b060909070e04300f0201110706180f0f0c050105040e01060315050604090b0103061a0a050309030d020310181122380703021e10050103030e04111201090b01 73
    0x10a0494100d0060002e48064884002303070242e6030740510f504c401070b02c1c0c0e85410b001e03400c1e20a0441d02c69064070040c02000c01003a03040e04002000300542c0382c01090f00c1c505e07507030305801040d014a0982d90348031200074800c10420100610700150100f420518101403901c80005041c5030140140d0082503250440302c0001e1012541d1039000e4080186003030b45954503058041300520400d403110303000900b842c1c00081c0e10035185100e540c1098604101c00e2400c000602e05642690000e031112602d0300c8104030713101800d915480070798060000b04401c8071b16507207403202a1441c51803143e01c9004841c58400e5861480070900225494041150f0406080150040300035041c5102c0d940080c030402107000c2103855808407542006800c039001201064214001c102e83c440c2401442c500802503030042c000710a0301040d0f0b000000303201e00200120369440030b04544c00c005940080c0d00440225502425245036440d09000c0c030881c0101050740603043c6440c540040103910010f20910100d00c1e85c0d180502d25991 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 851412742 1250 851411492 851411513
    0x230405090f01081c170405030a140f0f1c0207051006140d061104080105041b440118050105070203161106070503040b072919021c090b060909070e04 65
    0x5d03000c0c078660880e40340c00d06166072681d100d04040340000c0c0e00c88841c4103035551207a080c0d88081c1c500300801810107071200180d9025500c4002540c10240240603000e139000024002068014443c10203018001c00e000b900e40c0503984c4030303009103456447d03500c80c4800c0c41d1031b100e01c030071582c94201c0004a10410034891040c0244100d400000c00d42d420f0000300010302c110b14402600020b450500725503191344c0c0b540c1e0204606a07a00c081d20905034510010090506031210241c0b01c030124244540c0b05116010085003110b0a581c9001040d8015014a0f03007405000c1c4281c0c0c1d880602400550700d41940c41c0b07100c900e11524410010000758080c3c006207141d88504e03084d903107100d0b4402d04582ea80c0351102001112074000381c034219044541860044e14070300384400c0204904074440010100740d251072101140b041d03003800c1407c00c1c550b4280a0007007011480d0010150903d002c8800180400300c03402d194022560051030640501442d40c280b001c10800010b00e04103c6400890030b42c604e454900e004001203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 851413992 1250 851412742 851412767
    0xb04020d09030e0f0906010801090f0624022b05030915250c0c050925180816030210121b0f090e0c0901230405090f01081c 54
    0xc0d45001c114400b0943c0003d0010200300c03080390390038440c000550030046081c100302e503030724000340380b190040000036220340000c1c0c0c0076504000702248158a400c052802c00c1814078105403011030216102910513014415440d8044401d0700341110f0320200d401084007104040100300800c58000001034054009200840b078144440061341810b0600f4100403c0d0141040c0540041010000d52486840e0146030181840303680244101c54040c6041c00f0440180ca0080400702070356442141280300f5541c011006120000c1038454a8a18114070064150300020b9004042c00354070100d41d82010f00404400041240c1c5d04030b404603145d051610084420701e03054920761006608040240d0880e0110000c0726000c50002e035601020b6014110044544545510408030200355a101241e81543c84a0090449406c10304100300c0c00100318502d0200707000c50b07000100809102043c103100318a8080742c041d801c00a007207044080e650401d500c4079214072402c0011402504159500400c25010300b0910048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 851415242 1250 851413992 851414017
    0x70e100f020309120a05061f05040504030e1206090d090e1f09020304080d1b0903120903080c0106090b0607050705041d060a0f0c18151407081909180b0402 68
    0x3d458412000c0f07603684501c1001206c0718003c001c0041d2035400c01030012500454403020805520b841c05041c000100300c081d0081e0704102420044980303644903442c0740303003400312240c1c000c02c114541461540e003404414840c4908110614000300700c5c021980740502d0b04440d41e580308060100c0044070b03c00301d00b105684086411030000c81040244400c06014101007140040b06216640040d0300c0070908100111401c0049181d04400b40041002d494034000c194601c0c1c00d000030003c0c1c8a868003240d60b04418000842c6a4441d00c0503c0400c2c25402605950303041030f035810342041c060b5a600c0d030320303000e40d8095207004d55900d11401400d4400041c0840c074044803502941c03510300304641144064014076407150340150814078102d100511582c0e929180300d1810302c8c058041d40c00c049030520100c0350114102d04022070701e490010714110110042590383d10803e48943c1d11006980300c2903c0401c000c400005200703041c0303000c00018191200071000b422611900084031800003002030002e01403041c1002d02c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 851416492 1250 851415242 851415259
    0xa0302030304120c1a0403180e0912040b03150a05040e01020d0608030a231b06011e0b1b0106150504050922122303010e070e100f020309 60
    0x1415008001940614040c40480840c07401d51038080d40c209081c52402001c034582c0c251020702062160341c515400c54480d183c00102e00b4640341c2d2002d080e4059420460b20749000500b4040c01540401020209881d40d2309281c0c1020f1070801017660500000702809848200790340e1201040d0340c0c64446101500c00108100618803800c003041c1c3c001d4200100c03540d1981d20380940454410303000002d8400002c240c0e542c40c03203a45d80f10303000d11072405e05828485201003014001c2c040d0f0030342c1441f00e00281f0030201000b00541d40c50b050360030340e920000742203131250008020700070310580b00080d08440c08209802d000c0c0c41c461000b070b100d0320300400c600d60101421664126101d4101980f00b4000c0084030021039140c00540c80309900ca0741c0c030031500e0440c00701520080b02044006801018201000d070410f040c19403001d10740a8071460500180040e00600301c8000005000e080d80368406070b5008841440d0001740c45118202041d80100300d100c01400b845498451151040e100f08100c03607000c0700203000002c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 851417742 1250 851416492 851416513
    0x614101107090c120b120d031d0a050a0515100e130512042c150604031e0303141e0c0904021308070b0a051801050c011b020601050d03080a0c030e 64
    0x600100c034a00704400040c0c100484910b5034900302c6c20b07803038418142e24007900040886a4043e4000c102d81038650014458a100c540380404003032150045140c06400070b80384c0440245041e604002417003002940b440540414089054183c418a10030754142010100c41526002070f528038005045a004140d481009501c0d032294110344040c1046a5101c038052990b9485002c840300f64200e1204500120540350b0002800340700e500d2650100e02d10058409480d00e902c0b611101e607100c000d445400d10322095280d00c0030806d645403190480300d80500070070b82c02c17a09103000c1c5501405030801e0030400e00c0d222000807407900300512049480420004200710340d69014090034008031440e0748207044040c0200900054046450022201603200550f00d151a07c0b65184c1d0401400c041003030f1b56410400c0501084103030120134842c9181d1390003508680071021100090007468114160499030040110b4504180001d401201603074002c0107450000c00c4003140188200c0040c08007030110102031180a4000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 851418992 1250 851417742 851417747
    0x30c0b0a14090a0b06150f0310030c050a0308092101180606060201020c0a060f0b10030917040b12251701050607022206030b150102010614101107090c 66
    0x184580a0842150799142e540e000701940b18070001001070842001c01000803d24908106400c3e5600314045003503050840040b45401140c0017210426001c0754510002c1c02400354070b14482000300300440e2010f44907411030f41e40e00c030747d1301a284006010300b100820048500d9441c2143d5080c84403948000c1058030f045414141b031403c0c0c02d48040d5901c2e46000c2c03020590314410300840c2c20071032000c0700800f1003a145545090080130511908005650341d11051111036440468400e00c1c880c19680201e500c216600b4009980340304045640d92141c41008204029030541041c0e4a61030151240040203540b01c40d03901c0100c911241000c4052a44075400c05015034001c0703c06002450f0411079060b00c0d070380f47d00500030706201701034000c0d61115039014218940142c01c0f20118a1140c28100420301c41d0b504d0391214141c8006a402c444d0300d42455240303075259682417003040010031200000035036694960020401d5400800803075020000c0c0009034400400040005200400c400102002030b0080c82400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 851420242 1250 851418992 851419001
    0x10614060d09151e060503060105010809070312050304021e1018080d0201051e070504260a03200703110d1a07031a060a02121e190801050a0e13030c0b0a 67
    0x81155070013150000c948807120f14424201a5407016006040036400c010064950110081c901022071151032004030002d441a095821700356026100d0300e0b103030309240c810460400304070424000a034080c1e610840c0c0d1507403840708515500710b0b40e00b070a03101e014030003400c00d41c03205d025000352660f48a41a1503803101c0398150301051040031254195039026001122044001c0c0f02a00c03c44009602400305112505440140c00545121440551300c201d101840da6410200da41d002500403031480d49142004064221074605038010050240860a04540d1854a651000389510f030140c00c1d43c880000c01c110300512020030006d8100c544221524169100801910032040301600da078550250744240c03401d2072016903c11039030f0740c0c001e0802002e140c030350600140c0001c40d1801c0c01c9042c0d03418200e12042400f0080001100400d0b8016120411400c003802095041c6d00041c02403440c001d0422401096560054000800740840e4805401d203040841d42005103003409050f030a4400284180140c40c0d520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 851421492 1250 851420242 851420261
    0x2a01290909070b1218010c23040503120c0c03150a0f02090d0b0709150207080106120f060903090f0e1501141204020a091e0e010614060d0915 62
    0x2030400d05559507290040e2215a544503420445405100c403150311038840300403e522441d80c010481041c25031034031150946900d410003401003540b4940074010b14403242002c452640c01c01d0700b501c3c900340c035240209070358441140c2524200640440c1a601030b200a00402a041c40b006088944080003462018031500301a5021603881d460f12013292204030140c001c1e1000440014014521222036480d000c4010600a140d00e0803c0034448011581400100b160806030200c0e41c001c041c0c940c10b0111685c2105c046802074456107082c01003290020f80a000111882507008002089012151800355800103180e00101100f8120386000304100b03482e1240e09110792000b000b8440307520346010065840d004600c0111040590412518181c0003850101582052010382405455541c0d4680c000448031442d43c0340407485a01e008221054000c2e01581003151880d100800060745041020140d541c1400aa1805140702082444400c8580d42c490340a0301d80001038012400900d08500008000401c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 851422742 1250 851421492 851421499
    0xe030c060f0f190f02280203070e090a060b0a080703022e030c030c0311250501020c010c02060906250219060605270a051312081b2a0129 60
    0x40c0348a0038a840001e030854210315180000010341c044045500c446c00000c141a41c15118507100005c104a411800c0c0e07104c0c3d40c0101c0505040b9420340740000a8510365640188606034900061080e04d6001c03c0490849504890866860443c042c810048070301c0440c488800d030b003010000440864041d001280c0500440d03404000300fa0070007030203500300c50010b4100401ca0205009580d00a0310081810700c5103044043d2500d0b071a4a10303940d55007641d2000a50308016511640401d4034a601003045030b41040d41c09020384141d00c0d041259102c02200010154101d110400a6401c102c2c000d001040d501080510480240d010358200321002d031150327115aa02401c0744104009c088811281043c1c00c0201001a09441303403034034440d28010300b134041d0500d541016a8940070740041d44074180c0c0c403074108a541302c1c05c08600d040901c1814009510001e41c2d128a41003100407203d00001407000d00700718403009800c004102c2000c00351b004080f100c00c0b41c1000421a800000101041d140540341000c085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 851423992 1250 851422742 851422757
    0xa0e040c09090f03120c0c030e040f05010b09030d1b0b0a1805070e0106090807151709010f140708131b062307021f031b030905010c0e030c060f0f19 65
    0x2061000d044a1185201c100050a07e544000020f03110322004410800d0050021840c09410130042e000c031002a403141c0c1c413100f400142211681828410084502c54a00704452486c2ca804030445164140c103c0040a803040c21000800f210800c0d0f01c40b4841580303a1175810462041d610704a0707071352103990083e0042a60380b00c000140007403042c4007150684418201030010320b03241040c80e00c5400d65100806041c00310903402c149442d464060745070f200315012000420f005100440120864900404c0c0807125010142044101c40d0440c041940011000010380d2a00065082403641000e072421120700440514000049032a80054103e400001d100f120210100c40c20b000b041c004d100c0c1e410025003020303030340020b240c80d80d13007100002c2840810740c01d01040d0303c003540d00c420301c02c1d00741074800ea030200360f484201405204091048240031501030034005403e029400000b6500c0a1600319a40318210014404000b8a02e07a4282c5480c5161850075503180c0d041c8a421501d902c0c0103014000025010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 851425242 1250 851423992 851424017
    0xf060a0321110c010c080309120313140105060a150e10050408010501081903050c010b0a030602070506060411040b0a0309020303070f030f0327020f090c09010e0402090a0e040c09090f03 81
    0x4105490b00c10f4050b10b89601d00710482d43d8040300e40d0402416180c660040f03a01d540b525000b0300e40110700c654083c1e80d00d5a0360200307606e0100802560080c1205603a03160008201040c1c450041c2c0380d003941c66546000701c040e440c01c48100c800103205162107810500c541d06a10100750070002500030342d007040c03000780a20303030700d031108150f40c0e81600381a43c800c11804100040401d008038010001c0666a400100f0200440740101e04001c0c030360703801200c0d040c0e40081c1000c240300090248903040503003200c1c00d03c04045040a4150f2501a902580302403040001e481d100b003d000b5800014031a40c05015a900c80c0e80c5410a421070003c41c210641c00f0800598030b01ca01e0318170901c14101d40541049607030074480b483c03080e6040b9104c20810101d82004561180da01e542c1c1c2c6050300d0520a80c0028081541c81170746070001405040f083e8082e500580c01070102c3c201c583e54400c00710081c0d500615041403291384500f450040d00b00036502c0401c0c00ca00d4680018103100c001156141d41c0e600a40300c100c00601c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 851426492 1250 851425242 851425277
    0x21c15021921020318070303090e250318140a0624090902010e03030309011505040c081303230901020c01090e0601080702030408010c020c0f090f0f060a0321 69
    0x3402c21902c50500d02c442011001d6607541d0245803c070f810650000b64410780c040507949400d0b0150001c2e8045048400100182140c080441da840183c00902028a0141545014803624541d2103a028152030f603180c0a407001040309030ad1851030300248864200c1d00001c50081d2903c4030004107482c02d50509170b1440010100c4800724110082d140d14102646207030038100c000800c4088400ca0400104000d40d01e000d0b94104099030043d05d25000001d46c840d45016140c000c003100380e0046000c0c1d0f0811010385800d03a04284242e500005141600cc0300e801a460100ea818180090065031b009250311009181c05070743c0050300c280340c000c2e021156500b4425006490300e9038280f040100d803904c40d4000a600f5486560b0780c0e03410003003600499051503251781d456825036007626080001030b40002e110300364614000381e840e4000e40c4103807031440841c00d020f5580320712030704014203000b81c204441c80070031000e4694452050080d50820700c0310608110840d04115440b092074001e1000402e15001d5419014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 851427742 1250 851426492 851426507
    0xc181d130803010b0d1d010b040e0f070e06120313030309050a0e0406020703020c060c0a020310060308091c0c152303070c060612050a05070e090604021c150219 70
    0x5030440c44403410350b0b04e400451643d5031300007079403004c6041d15840d4003d403201c5551900078070755040c3e00011950410600901c0210303600380c803813102e0755032280e21212000c01c40403d450040d81e480429020707a03640c400000c2080c0780300c2c07140f50340310901c4002050209a1001841203040d40d12036a80e02c5110f40da00d80130400124800e00034010315202c02400325000070015401894114842e0042e56542204800021b41a070481c40984440d90890315039101145400e1140c043d01120002e0100015411503d66160760b000e06012180a000880c501c060055031090380001c20545c0102c401003291b46a02015850072101c15000b00861500c0d4500e56102d0400d200350907944012218107425a82c8440b011039002820714000c0c3c40c05940d8000c0441d41c3c0482d01c3e200810702e4022401041103000c60301e45149840500e910a1700005094824826400c07401300307002e0742282d0102c40c445101003010540e00f0000c04560317401400394403001c000d040505441d801401b0405c20034000740a001e540c00105440300c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 851428992 1250 851427742 851427781
    0x70302130e06060a1d1207080c03060f011a0c071806090209010c02040b0a05060d051602030c0c060f1b01061e060e090a0209030a03030506092203030c181d 68
    0x3c20900801009601c194442c111803041e20295844007010207003c6901816801c00344803181c2c00880301071201040410690089007001d50041080d4034190380781400110041c050000d031400c1c00407400c14040c00780000e6030309040b0780b02d050b1412103a9444030385010410941c50591400d0508900041144481c400c1d94420001a100d00e50780303501581c00c100007802e440789a650312104880303010405448030710141460401031400000e540c02d01c91001c400050f00c0100b0700c800c40d8410892080400404180031010a80581c3d4183e10740061502c0b10f2168000c4184008140c0140521800d15440c150440030460b122551003041c5400c07040b004003c083c10314007130b00010a501504440d46810801a03080d8850079100c4014101401400021700380782c01c5034416000683c0303c505100207450b016102a0300700d0701910300079060b80300d2a040000e55000b230101c05000d2560320019900443e0140c4842c09134112020780d0f0300c0403030703442d0684008034007081d40c43e0700405042c07040021700205103056154040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 851430242 1250 851428992 851428999
    0x16050301030b040b0c041a041409060307060516080a0f0e01030203070f08040203010902030102220906120609050a0c0b070b0903090105031b0c01020a05041d15100e0306070302130e06 80
    0x40303036030390344034a0098130000d807020401040400c8005a1805a03110180071400340703513012952a850306544540e845040140e262152502505000d4203580c00a8014201e6450b410880d03113462107001250340c94011321901400312000001c0c0707810f103191f000380c8407403602031741c0c0d2241152440190011000c9001c111100c10209100c940024103d41c000c1d100309510600c020004146640030390b0110b070130780c1c00241e12030709100b242e0f948400071518008142006000019070400c5014070700b0100090540e9445400f030702c8103a485926000b4000248451004541c001071075591096888404004d20750041320199440903080e070105104c41400310449a10500581d61a420341d101e030141c40503014001c1d00403102c2d0780c41c1046000120002070000d0031814038103817910f5884602d4940c0c124031040603403481c41c80241d2540e0070031200c0403040008403030184c005e41e07d200c0c0e88000d41000b81c03641ba0003101801d42c1481410100911241d25400400c2044601850303520241e6840c808803500202c207641c050791 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 851431492 1250 851430242 851430263
    0x30c0503010911090d03030b150a0e2701061d06070c03141f27020310020f1b012c0a0b0a06051002070503061b180a031a1605030103 58
    0x20358403141e048032203403088070604640707048030800000e0005e1400d0b990803008292030300409605484c290f0302e442c02ca0019158101d15000c10314a00509140f40c12140c14400c2d0b9004030307102c6071400341d2000d01600314000d1030303504600d584840c805410b10401c580c512049000203810106a4142403040d24085a4032141c0b40f03281600750351720141c840c24014000e40b201d00c1040414426461898400c03501c003442e100e4001600c1d140b10300e00002501c1c3d4040541031b428104000400180c8000030110100e510301f800068407220343c042e2400c3c10b403088800b40e801c42028443d215528040c198004441c0c0d400450503c440e5440000322a0034010a54401c0d100e19040052082e002c10071a5020719031180e2032080028000f5244c0c000114101202c0b108040160300036141440682010400d01d900010070010b000d28208405140c400795100320031300b00b041d0f80b55031007902610b41c641d256100c003c3c542c010946080c00008240c0c02400080c01c55070b070301c00700c4080705600401e00e00941c00c807410f0380e07080000342c0c0d0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 851432742 1250 851431492 851431499
    0xb041815020f190e030d03110a1d06040915080105060112020d0f05040b060301060b0f0d020906130b0c071d0c21010801150b04060c1502160c06030c030c050301 70
    0x34000d41040807403803415141000895140462410301d01c52407001030716801650540d42090501c3d0049a10991043c0b5203000c441c070031140c90304001e072800d40141e842c0242c400d0118844064008031200c402a801031000b207030104d483c1c402a0080c104130036a62040f90035055640d102e09090796810780b602404504604002c00c1000c4640d00280b840c04a4050003088c0c10340c0e401c03c814125681106c0548030fa042e00c5003030040c00c3c5002c0c080d840082c680c2e02c44840c00c10502410121291207203074a203081c042c2d80060126200c1d100c40080d102d103040c2d0907401c0941e0b10b03a01c1c03000811582c00090321004901132000c0100d500c0a40c1e0200c02020307001c2e000c0c21401c0e6907510116140030760184404200143c200c04403103042d00640030303105000e002c480c0000701d03040502c42c140008641c50350300a400420828001401003170340c80409400025080248840480c003041100070080c4039600e4940303854860241801c00740486000d400003200c0039550104034a00c04c15400714200c902080d11600041d00800042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 851433992 1250 851432742 851432783
    0xe010501120b030304090c020d0315050d020a03060e01020309070605040803030703020304140703080d06090501030b06040203270706110c0f1e031509061b0a08070c050a060b0418 78
    0x20041c00100000c0024441c059000191458105500c61416940c5440c1c6d41e9404a07814811401210f52506050040c01da041d0100041411207020b681e000d801c0c2591188155511840d00030015074004100f04a200c0159a44902070741c070845062035188a101d50010f03849105030201d40403030301200d0140d0704544500100320003030f6002400c1640c03002036100903010b00440a0002d44002c1d17118469150f501c03050f2242e110140c0301310354072250ba00c9240c140100081500148450350041d4102c0300141c0d243d03680c0c604031800e024070080052880c0c50b60030304440c9040c0e00149001c140c441c107407960343c86015141115541e410350f50030390341d4208501034050115801c20441681c0c0800201c11a84410302c0f15038041307460120501204926403881005100324643c5c1442003e4208410340c0d50200d1100351a0841600d510030b035031150082203040800a241c40d8803560982c0c103215031040a0310440b100364200395010b000c103010031921440c03038400c1e030200b69501c1c80010200198040c1070010f0b0101c480070031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 851435242 1250 851433992 851434007
    0x10b0f1810020d12021204080c1c0c30110705040c0c020906121e010612241503030e0415081005071b061a060f041e0e010501 55
    0x280c040c420030400e0840d07a40c401c12240300d0a45560300070280d840564400400c000241ca40802c242407040041d210b400b103400341141e5200f82c1001c80140c0d03820340003c1013454480c04100381c88411032144c210300401544001c5051280380141c0003003000401401e412440d5100c1002c04c99440c002c2164a940280c1c01380e811102c2034064402503400745542c48006c10141c0d090054602d0018940c1e00c1013008501c1c0c066203042d0032079015100030741c00c00700800080b540c075040b18100d0055071110070b8107254800000d4008030040e040600900030341c00c18070b140c00d40c4403c18040411044e07030745412200781846450311500368050041100d040807a45107450598154150b03000440e001600c076440d4802c0c4c0084502800c008255020007070035484520f0310400201e400c040c01c10800c10040e4100c42c00340900440c10310000c03541202000030503100d00c0010001c01003844641350303000500410100303441840314020380119600c40803180342550300101c010225000c540aa2888000c3e01001441554443c045 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 851436492 1250 851435242 851435257
    0x2c0a05010c02150a0309020103292103041409160f0324080c030f030906040504020d0b090c03070f0903080a111e01020a0e0910090b040209090a05040218010b0f 70
    0x3c00b030550315695249a00700c0d030001289402003611041100c08550341840350012401243c0d91b01469005290541e024030541d0b0a4420721803039000301031400300b24030300800c0f20240c101c4100b201d5903550780c0ea050441c14009107088500c98400000000d0801007000007001820701c1640e14005142c811000940007040d401921220701c10300080700440580c00a24040040d12039140103000a00f154000c05280100139043e040d20f0f40c00c240304910071070300c0e09415a001d88604480150300d0300354022a0b10010300c01507002035403041c0c068083c00040e0000000442c0103414540d078140c0407644111050356207007281c0c0710080185004009005d1030337a2003400280d80e8480d42c04c00b515800e1034030074084100c0341001d041c020441d95000a8100149e50400c88a13646014240d5203095030345860060318150303210b9071191f07401c0c4940790303003849826640b250b0441c1c00c410303801025010b09090100740c150040204407022030007051041c07032988185aa0401260480765021403c901c0d2200341041e00f18250001c12 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 851437742 1250 851436492 851436499
    0x507020a061d073002011209030c020a05030c09060f0409080a0f031802130c02010b0607080306040506040920130912140c070521010c2c0a05010c02 65
    0xa100304002034840c060007040520030381a0248110b240906541800000e9204140e507205030300300c800c401406403a401c3c00304c8a80320410342000c0320300d0006031403415010f1806c6004600e010002400c260b000762040ca6801c0c0282c1300d40e40425104d00c03d0580d910382500625a10031408400511a440c24ac0200003031503c0240002c900000c1c40e585424580d00140c4042000c50120800c440795194507201c0e414007805140b070000424105500810000040e25005010968440c200680214002d40201c2140c00c6c0c05007030139036a0a4141048141c90b00306079540b0b84513504100105030f00e0b28250003038004540d00712910808200c4180e42100c1c2002550b45c03215084a031034541c01d480e490861140790b0301c190051003201c00c2000d00d154000d05100340c03c04540c0705040103001081189000150a87c00e0700d0056440c8040c0307100b000c84041c5110010230346a502c40d03007402e0384800382035809072071403440c4107000840c02094030404046050101400c21981e4000610907402c0001d9032003048503c0034540044c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 851438848 1106 851437742 851437753
    0x912040b30070302031b13030506100b03180c1e040c090605042102130603031d0d02010e1917070503070f12050709020406020709060e060f04050702 65
    0x80c20782d100f05540480015400c2c00c805018650a000004486840c1e03c0307204829103003800a40411681c40c018480450b0045c000d54003000151002c1d8000e442c115607402030f07050041000109003d80c607129030792000300151203034030481030780341c01c0b03000401e0350780d4071a00c103200c19282c0f140d00600400c0004c40c0104076003503000054600b900c1c90316031615241c244185402d6032007201e814010703600c0195036044407000070159100c0d8003140c1c801d403540e00b50454a0700c0411500210050815000f807640444a4010b603c19102010710304001455040ea0050b02a400c2c110700d502d80d00f0140c6100030621005080d86002c01600300104070440050812034213090498042560750b1160080320302090a1007010494144004000f410301300004544950350b0383e0000b50b5030503280c0301ba100310f64980003010881140035081c090bca40c801a201e440200410000d0000400000701820b0460182c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 851258992 851438848 := by
  have h0 := BRFrame.cov_init 851258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 851258992 ≤ n) (h2 : n < 851438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
