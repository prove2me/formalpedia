-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4629
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:13:43.87037+00:00
-- url     : https://prove2.me/submissions/0343d0b6-9710-4c03-b911-f3bd4968929d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 832374100 ≤ n < 832553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 832375350 1250 832374100 832374113
    0x10c0c0303050601020a02010c020405041109070309150209011209050309030a080909090a080706050601052a06240f130507080103050c041415011106010803120906010605070b071803 80
    0x104000e11070344080c0015907800d00126542c0b0814040a40010224561240941403507406281c0041c098180c09010801c40f9000c14600341c0127444600000743d54113540000c2c400d25072500c091616040e07200b545003540000008081c1d030b45100c42091020b0307a501203081006000c000b107a500b0480502916202c0301c09060002d0140c1110003118040c0d908200080e80a21002c642c0041140d401104281000425201c0c94018440100101d0500004000703850186400000003c21104600c2489540c0128a900581060350140c801c0103844900c030910f401c02d00d0b50036102055039000b41c0c1c628902001c03034400074640c2c0c500034040680c62890b1600307100107258441c40040c1664000c2c0c0446582e00340020510049482a4100400a813074a00c003064007102c80c811031022440051400e0504003400413006270400302d080e0300c259011b03400020b0500d02a800d0029465100c604c02019040e19850004007501c607104020006150348100c07000921024068440c0c88400c00302880182c00180d00c905c1c002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 832376600 1250 832375350 832375367
    0x9190b13080303010e073207031b15093009061701050418021519090f0905101d15100c080c152d04080403020d14010c 52
    0x140d6204030004046070724800001100c1c101c0d17000041c110f07001e54541030100d0700341d011000880c0b03a00c10140b2940341410110303150250390000f0100c1300340e80c4101600d80905110640d9041840110b101e10060000c9041e0014608155601c048085201d014510705241c03a0b02021140e0500b4004501100c6414201c2c10200328a405d0651200c0b070813261a11130648804010650301c4000000000040c4194105a007020081e514900c2d000310b0600c040c5e84c00900300c034190403001d82c4001c0d4049030b010f2100d03581c40144402d02841e401c1042c41c05050842206401590f4040c84c0c0b1515240c83c04224540c4030704c01444010030310f0101d80b10407400907000420b400780064900700d120707509058544846280c004100f0309a03038041d885000100a81d540e801000b90403468141995000b01095101c08514140080b8440d840d42d1130040c030300c00c0a20710520402500307a203010180d0710040c820040021f5a460449007540d40480d03d160f410102c03450038030b050901090954070300f9403e0103190702c80c00b0b0300032550 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 832377850 1250 832376600 832376617
    0x21020409020c070501080f01120206070210031505060a0206160207051f081e0f0613020a1106010806040305031f091b1419080a0b0913120e01050a0509190b 68
    0x2502d0303d0701c0d6220011a4004000c0e9901c0c44070981c003400400512130b00c41000540c043c4058151800c118498002441040601c050400404e1303e60200712801d0855140c000b000e4801202c00d50308014807940020b40e80e84008100e4603098000b01c980c0001107000b001b0650080000414400c69492a0304181e007400440c107074110b000c1007003100490b602980c0100c100c0040d01200c0660040d1b552000300800904070007401554010b158004c0304c80210a083c00101210003140d151914903000c2d42c101546030800580c0b01d101f180d002801400000b80d8880100da8102400c600e07044094500c00c40c0d0700102d8440c603404941541c0c1303005032556000c1d0410a070030503805015128085024001d5a01648078420561951120f0080f00b00c19040039006298003078110141d1080040c001c185000401ea80d80001e4a5003200904e12034902d908102c3d24041c03030140c80000b450410041100c51002804038003600c0c0751402848008a40c0d095103880d041000d0421000b200c8091002980c0c404400b446940b00510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 832379100 1250 832377850 832377853
    0x60603270c090106051213020114070c0509010b04031403120106081f0e09010b040902060a0c0305071a090d03060e040215120a0209030c09011a0c0304091a13090308010621020409020c 80
    0x40040240380c00402d03010b50181c44000900340740b095100384030340c4214bc0880300341d14100320100721501c0e80304000c0e01a07e8017180316980c07603040d801c100d41c444400f0146417205a004004d06e000781039600490030304448032420702e1100f9032114802c069000c800e5145548000001c400002003510707900d48660700a04d00c22000b00204d007020300602050b5044000041e40126003042889205c0f84a420140c0c40700c0e0280c9045800c008007551032030465261901004d001074140403e00042c00d50a0182e81200e43d51807d08000c002d14000c442880101c1c0200060301c00d41d0350060440d454121002101c000343c038081c0c0040d42c680307002c2e1314402c02500107240d02c82c068881c4000f4400b4600f4140b6205068070a0a50080d190360700100b0304c2c98072036100c0c106400740381c002404006070082081c000c90480c0d02c030b8548078261042100040c0318410f034101c54040403143c2030050281c04aa0010000e0b419560540b40603000d180c06000002003110b4001c0030302480310302c00180021604a913a02130b202c811100380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 832380350 1250 832379100 832379137
    0xd080a05070507052a04060803090a0f0312120e1c0e03011a0d0c1502060601030f050f070810080708030903061810020c0a15090b060603270c09010605 66
    0x4070b485010300034000704541c1c0041aa03c202c60407000e40c0940100081010b021031010050118090740c6099004080310341c000304441e8491718094207050701a0040d01c80c80c032109461030700c1c0c0459254210070b0600034001340105008070641b00e50042000030300f4681c100c2e040034140c0d4024599019401a4034070005910b0030b0044058681030013080d1034212510282414100c0c2c0c10100314040d41c0d520411501c0c2005e4090000e910041c90030b003a00300001c20f8000d4071103884e00d02d001506503090359011070381c9a840c0c04100001d04080e04001900215a4509107503140c0d900710078800c03050502d400c6013501c0d116410b000a0041030001c000c000700041030303041d944142c980c086e8041d200b100c00c4803001780580041e40c050000c03010683c050721002c9214811a11003055644880b03078564030030710881c0340240d1104120300c1031113000201b0f240c102070f080e14118950310b04165044824038000703018180c0052011001c0045060400c00010400d00084c1460100e594440300682240d014140d130407003060307062 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 832381600 1250 832380350 832380361
    0x702030f0c0604031415040309060206070c1a0a14090a060b040603021503041b0609090e0d08071d0901060507030f0e011407080c0a061e02040b19110d080a05 69
    0x2140086100314040c1029040c50709645d0342800d00ca810380d9106100344a00200c800000084080c400e02442c00380d1503000c0c5c51414010001c3c00c0c00c0d4002c120f91b060140d088021400591810000c8070140810f00c1d4000d55610b8840c0e020340500601d180b00d400c108803ca0601880a602080f09246d4a22580003089a00e954600340401d0341c0c02071002962026201514541450700e460065520511913561440d4a9901254074070b1440116041a00015a074080502c80401107129961070079000341c0042c650b0510407080204070802c000d15140c10840301e201007004828904004181c01c00f4020042d00c7c4030b60315424002d00303641203110140c0000350860b0031042801c7c000e011010743c1e04070694a42e034a071501000a2000c41d03000d030904540000080080240007001408042d1505220306000300b4501408442115402e0070102d035400c1d00c61040008100740d010190031603412000c0d4044200002c940c590040c2c030300c0d5880c94a902618002e5036004428260301c80151442100416000c1003142c451 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 832382850 1250 832381600 832381603
    0x606020c090c0d0905150708010303090e160e0f040e010507092408040212010c020f100213090e012c010f0608060423070326090d150204050a0305030702030f 69
    0xa54038864085020030014421001c44d400c810051030150045a40120307501c40e102c07800210441b284000200c01000501c1050f9001601c40d00405480000c01000e04182200380d03030700d801070441501403240751100e103903840d00d5038007800006075030080c4108566011281090b0203408220f0744c0b0b1f0002070031240081454040c811101c3c610b82141d42e0301401215101000b0394105501510503030b8001d4451900140342c09090040d0003890780075601600b58100e02c1c102c15861f00010b00c2c4010031060040c4030048101d40d2070b0400c3c904070b4603181d6001c102605a0700c000c500502054042071100510032480c290b000b400e2140e58030050301080d008000c0701d840e52203c48210791650081505640103000400c021034101128030b04181490722142a040124207051403821009030b05c1110a040341064081038100910008445202c610b2151454104444000340040e00752580c0145514080c65041d41d2007081641034070060000504040309003603c0b8200640c2e2a000204124403e1080352026851444c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 832384100 1250 832382850 832382869
    0x90512100e071a030a14190b010e1e19120c060306030b01050f130c020a11030c01020606190801050a02040311031513150f02220f0b03150a0303030606020c 68
    0x42400080711450415800d501540060400c5c1096500d81426030200600c42440d00d000b481040d01c01c00b0240a0480f11000b42c0e09005440307418420b8042c0c10300740c140c41c0d4540f4452403083c45400c0c0c0414503200741c005001302c040072800c192181d0b204503000ca06240b0700d075044107000c0e00410040302c41070703a101c40840c00ea448600000340b00f01555001040039050844d052041c0e100010444102801800e07009011102d00c1c002480040e803114281d8004c1c03105621810841c610300381c01901c1617464000c000f0350f5800010304003d0090440071540d1380607a00310100340c0082c081640003402107080003c420006508a4041680e50340000c1c0c488000d1450000754011503c030300c40340052629612401d112900f010001816607500d4015070001d19100640e10400c030700079003800c2c0c1c01a01c0d8540640710450008000d1740b1485082d404e40002c0c040c511210003181c00f2a035927500415640e5642c03011402c00100c8903114960440f5041101001305609504a039068a84079800c0350068032055040254148 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 832385350 1250 832384100 832384109
    0x3060a09111314101424090a03050d050a1119110a05060310030b1605071b050909060702060a06050109031101230a0e180f040201090512100e07 63
    0xa20301032224641007001010090302c240090024000c9000384000d046140102c801c224880c02008043c03141c0d07109074408088046081d10021240c4d181010b02040340700c8420824081500e0100d080b00c59a9911802c2c2e0b009141d001041c6c803210100204003800300d03005a803041c40800d9000031502130200000510f401c0140800c40715500e990811780741c5406c007550705229641c1081142c640840c464441c1c00080d07010300c40c10f01085c0c21b0645541005540c5c40c10143c6004400d079180c241d5240851350040903030f41c1c015040181d400c14000c0c480281c0110540ba80d2103540c020b1401002c000500c400802c96910034441c075001d070b400325941c0e20020b0044078098010103001c15841941031002c10850207119000301c4042c1840f10302e502d10050094421103400c01c6401d25031100140c45184c1e5a48400c030743c41190401e0314003030001041e0101200244500030100d440300d083c220009029a8441c0040600400c3e020349050b295581c1079a86685171489509551460390030800612407503800020b40380110b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 832386600 1250 832385350 832385363
    0x3150b030d0f1412150102010903050a08090106150c0209070e0325050a03200105070209010b031308030a020703080c040308043b270613020d0501090308040203060a09 73
    0x2030106440403510007002c44200228101902c102c0030040e801000361150300a207140442c542408a1882203038000516411641454403440000750400150307506a42281480900da5650b0102a401040503078070204000001103030708980303242c008180001e03c900a858541190740c03540c100383d420469890b030300303901a84001d000e04561442210640358080302c034020018200d0b60b64000034800c000540058910200101d04231160441618078851544000c0c00d15508103089500001d410085c1441140c005500000c0080d0b00d0f03013400b105400741103901601007038032820300700c0301c040c0203403c4050120042104407003c50309800d507183c251012603078048141e915240c144060080b1409010140c5038924404600200110344071040311101d0714903aa900c090329103403c520051304585042c0880d8a01400c00d42d49880045001c2006503103c0e00c1e4441c4040300305602e1002c241c0b003207100c54024001e5403801640808140d84640d500b4003a034000c038101d411039200d0700b416800703c91040070010700d0b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 832387850 1250 832386600 832386613
    0x5060312030c090604260f06060a0b07060b040920010c080702010c1703092b020703030e0613080a06050c0f0304061505060a0807020f1b090606040b040b0403150b03 72
    0x42c010001c1c0142a0700c01d02408150400f039482098480c0340c07203001c00c1d050307921030b801c00205104942002600e02c0405c507080184070609200c00803980c2d48101e40580311069100080034400c1c40341980241c0310115000c0c02c00c00c00d860380c9090cd003808a2100c01d0b9000b4040100051915a40c46140f03000d040c2c6410132500c1c1d261124650054554060040d002c98001d40c01050540365844c0f1000518415580c45016202405020400d80036020014806281c01001d603682003084903400078503042940c0e07040c188003103d006154001003181c0590b071804508184140c2c004158040d0224604150300d100e004103000e5a154040402d602e4040c5948101000c4818030000c0c011038150717000900d1888404800c1c51045803034070007041c202d81c0620724003008180c4480500040700e90402c041582c070300c803080141c00c007440520724140440e1410059144100f030510003107461551400c08450041405101503070741d880d5900b0302049079400074841902e81d124148190207181c003060003132040e4510024042d02e00b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 832389100 1250 832387850 832387861
    0xd020d02030d02070f050a03020d080601090602060730090b07020d2304030b040b071706060f0903070b21060105071728021e0d050405010c110607150506031203 70
    0x1d40113004c0603118111003c0d0442c01007602444080456400380e8040c2c81072880490f009002168050000c03410000007000c20003000340c0c00300b007041c2c0295191030b1010707c504005520103403026205401003080814003048400c4200c1c168003808109200c2c0c12000019901c218040e0303114004924000007040708100c2c2c150701e142d5800000440700500c081d0305030415440391920a44984100e13000c0700da00035210103101c030b116000030010f041d00921032501d00c942d141c02c40203d59540120300104880240c04a03500c00b8507902402102c01401241408503112659a03600300d141d101c80c1400c01e0360118551001c00d03220f51080d0119030b00c05030819681440c021507180040340c00d900c03250412080300320303452110759a800e404000e2010000035a0081950320f070300c0344046040040f02501c40045a01551a0b2208140c0260070348003159424280281005054105540c14110b41601940d02040006d101002c1000c5040940c0c80d0540b503600c20031103660340e003040c1552140545100e10076410140002030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 832390350 1250 832389100 832389127
    0x30203060903032a07170c0f070503031b0106051309031b080a080406020919090606020c03330906071e020a240504060b03061003111c05160302030d020d0203 69
    0x49002000c0004d40381c06041d48429061103191001054408400503039101404030810108008290340809403281d907150a002076664491100d082030700d0802d0329003400f41c2c00820b502c0f410060001504540c07060000805840090200300001c030b02103503044c4001d404c0c800402e100c0c209541d50016141d45801034104041d0b07112900100120b90480d001c101601e1280c031071160000d8180c241000d400001400c1c8200f400541321150811011076000e515405090380d00040c400a0b1032050700382072031004c0b05900a51145104480607858900c0b00d040600200c00c0000541c1441081169207480041910b00c0034030f00f250b4031481d174800041e4014031009000c038602104070070f201280005000c0c00c0030075207680201034802c21501600e600e59070304500729103404c051105542c0707c4c0150300034000381c0341195180300940d203034000c0e140c2c0a071400d0b0590350030b54039218410229403038100c4226060000c004507460400034a600080b0701901401d030f141c000c0d0500005503100c444002c2d0b00614104001da4480d034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 832391600 1250 832390350 832390411
    0x60907060c1707060b03030d0e060106020c2805060a0903110109030305030703050901020d0c0203040f140607080f1303060b010e03011a01120b06040803070614010b16050a061503020306090303 84
    0x196000703170380e40c404004960f604000402108041d580c0120343d00003041e86280c200f080580c494802d5401800e40d01d0f10b259070700d01c80100c4a00210000c00d141600240c0640d034040c00ca80c110726000000090000d03802c030b400000160440380700b40b00781821604018011a030752241440010045030052002c201c60500981002da401159480018200452540301c07005896040d9180009a00001018840580c0669032040a030443c0d241410044a6100c0490075a105448026040c00380210310381c6c4111110700100c481c5c11070520700410100c0e4480c14220000c10820254078082050114103458604041c0541e080b26508d8101030400440345c1801034804468060300d10340842d544000c0d21266544050140002e00051342c025034451141e8034050044807812000d00c0020104640100404503482007102c1d00345c81c982d1202c5013100341c18035106141c00809400100742c181450000b0704209080000c00c4201c0340210f08032141525007954240e201d10065519801107554203c9500b180b08811101c4c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 832392850 1250 832391600 832391603
    0xb0402010c0503040612050c13061103070f080c1b0310230a0b090a1a040209011803032106050306070507020a0305010f060302040b01030b13051008070305060907060c1707 75
    0x106110100d1903072024251392080d004078010502c8182050300c6590036208181d07200c400080303010304e400c041c9403020a408440344030352000c0111500d640f132501c2e4014010346858590002d0091406801131030900da01d42c000382e201d08228270561030b1070165400d54054030718818a018014065481c014240c51018100000c512070003600f0325118503900010b40451244105850040060520306840030041c1c64640130708170b000800d0800c20403120000200c001c50b01c0c0d40c01c0442d001030b075403a51a00103981048602503c80c50031034000300000705040d000740100c2100c03401c0da01c50a0400b03c02504a03811600316014454041d400b800010307440e81c1c001c0d002030846034001004510b0055407965600e0a664907002c04061198441908108505050240d0401c1e03d4090a060050070020342c0420680e600009440072482c0e200c1c4045004030340600c0404020701482e1050f0f40311562031382000707031361007205030b410100d1445207201c002505031203103000018541c0d01201614540c0716000e5482c00c00e820200f070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 832394100 1250 832392850 832392857
    0xc03090c151b0c03060b0a080645070501091d07140403050c0f090c0d0510051008060a1205100504061503050c21070302040917040f17010603020d0b040201 68
    0x8020540704507058407001080c2c0f141c07035545800f07800c6241a45c1a600e08880b01030180070035031428000f41e00003284035039004002100104043c0c451002c1a4105140c0031444504086400c021000e842c604500d903010100d061401c03141c501c0c0e030b22001102e1881d194440e0302016200d5410580c41e4041041110b904034240c1d2078036445882c00c08040c03041c15030003580100c84651100245140383d04000c0c10413003070360004540000c40391420303000c1c40101d4855918125102c0d96100700090600d0720640505024050143c42201801c614a101814401041d00c0207889030504980000c0c4990f88400ea445005030300102401d841a050550b100c080c05004d00115031480e101d00000503c3c16000700d0103001107010701c009010007000c10003803002c011701c400b000d10364800c48418810078641c00000c041080341e0741035400042485150402500c01c82103003048040c841e40c0091300082c4008030583e0b1105490381c04a070f1b00515042c0310415400c0300c1c55440025000203101c282030010a01d202d45243d03000b0300605 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 832395350 1250 832394100 832394117
    0x60c080f09120304080d081e04050f0d050d06140d0b040c031203020403020118030b071808030c0f1005130f0602090405160e01020f071a0c030c0106090c03090c15 71
    0x41c001501c9000120a041503940301240800c03220104010a003010000c50034841c0d000d08084aa0545440c821750025003c0340411011600b002010000880c44000349800d40d1605a0b010f00010440da00007a42c6841c0384d41840c0c3c021039000902102e404951303400805003110b4102036901d030310100e0760050090713600320b60a040000c08221031030f45c0007040200c1a6401a130340c3d803c1d880050581c0e50840b80b4050607078855031040c0002113803002c03031075040301aa081c14050821b1040050742d8106040d080200d9600001ca04000349607030004090040b84401010f4810a0070200207920450b4000c50b41c800b50356540c000b00e14041201254040207103805803101628060f14036000c40d040e2181a41c010420031060040840b4696008464411000007440030303004030420219142d5a40b519070140a03092290b41801600c1c0c04588421140002c90400540352070300d003ca00b5250003822184941070740f40d4107103011042141c1c400d20820300b51550210010b0300090500c2c480c500400c1c100720000c0c06020400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 832396600 1250 832395350 832395367
    0xe090a1116030831080d0b0a0e040b010e2208090418022706040b0a050a030b041203060e070e01030f06030b1828020d08121e01060c080f 60
    0xd041c40000c460190300c0b03038032907418610410b410081003003031915403c0d0f016403891080c029608111a1800ba001200c1c10717155840c4005800041160f100c405510580900000800c3c0160342655071140e0301820745012241e0f62012022a80f610032654100701c140685914802084d10111100300306001d241f600307003410120000708003220000c80ca54098100458103040031454201d05061b0b607090040707845029200d0180d0300708184040035007414030981d212051400c09440d0120f14030004c000080032010101e5407414030884444c1c040d6015110000c0c0303100200c0c186070190285c941190340c5015800150740d140a400c035500c00000ca5046d04042c0c03203030740d403800c00c800340c1c000d00014501942e8104001d060502c0c5840c090b50403a100c000c8560003416442c503e00c2c08110b181d40e24001c0f00c2d40051204c031594400209000f09807500200002c0c1c01041400301c114200700000d205074a40d84080b2010740500c00030150442e0248034220019a540360700c80000790078030000d0b04481100d204a02c0c10503200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 832397850 1250 832396600 832396627
    0x9110d020603010618090501090509010605031603030e060c0a0c06030f0612030f0c0605070e130b03030a050d0e0712120201110316030f110c0601060f1d01020c130c030b010e090a11 79
    0x4c9e8804002562100140809003900303104a000402c000c5006040c41000d01c1d440c1102c2c41c14034400a000e12903003400120107920780c5811203017080620003d9500c2e68100340b07015402e125142c000c45000914216a1074542c071103a00c01c142c15901c1090341002209040d6400310b0326102c0000e0b00004000711060540c0002d03503117009007030255502c1e844400e80140c50905010000c0f0382e0f180da903250702d4146012408240c038003004440016002d407a1140d038030007010706010050000c10140341c0c40c510402200181d58184008041e017040e210301c026135298a01c0e44012801c0c1e0311a00d411400c406020004600014291800d050b0500641d050104002000c0720041c4212850b840c082060f06038002043c01400d941809103e015101b5418011003602c05090020300e907290060315140c03504644945a101c0368000c010501c08104010043c000e02d2103010b0740034015009500725a00404d00346019507002e5805815101904d503000f4102101540c2e910459502a00040c02078138030001d4208440c8047d501c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 832399100 1250 832397850 832397861
    0x90402060d09060b0f01140301050603070c0b0a020301061d1503060307050306090d2a022b060605030c04092117040b1005010302040501051b031c09110d02060301061809 74
    0xa10f02c0094035040800611107038a800e60001410003031044151110b02c05100203503415110140e4040b626551210000d407042c202904000c0d04140b0a0020403140c0d801c150002c44c161a005e47e111803105d0b410248042c0d0404424181c154402c01d503249501c02c03001c20307101845c0d21403401000c4074202543c44000c64180300c02902c03103c101d50042c01c0708038a800d41094102d044c42611091005407070000d01c5481d01c02000c1c50b040280b00b0309414940c00d180e01e50800102130f14104200d82201c1d440040c0c603194008241604c01c4030302a001e442e00e042c2e00b03850310b441494030310341d0000b41420038240c4041c800ca40d4401c20101c41030030b2088083e52600c1a110301210544681e1048075032900c5801d14281600080703007113a200e00d041500400003801281d9200040e50101d00902258260607262a540c0500f10300412904107043c40500900420303807100303a006100721a000302c020021005060f414407061001400d00a50050001c00040114510a1542100344544605003234a900d8445400034240c0340c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 832400350 1250 832399100 832399103
    0x9030e061305030d020604020d0809011206140a1a04051302041205060405253303090213050c030c0309070510030b011107030302060c28052a030702090402060d09 71
    0x1d1141c2424011070804102948118450340010400ba00c1e2560000345510400c1000070556400802d254182e64010940c0d080c0b1005100000d004080d254030080b240112003464540c458902c0f102c0c006520710382071660020441c0c8113050245014100b805010030300c0280d140604c0d00c40e40c00c12000030a0301094041c0380b4200e105802520403400c1906109280050005032082459142c10460540d20740c0d000c624000c030343d900c1d110351041c3c04484080c6000c088400781103d00a003410000300815650650101020720b1088450080c55001d8600110403200c046a00058903207080001c40c03090701c1140c015503445080d140444a240c1d071140081030900046602440101ea15600703507000541c0c221081d060320080b800002c080c51450341e04c00a40d69680030f016891814000903250800c20b440501c524101d0220100340c1a44903c01c000050482e8441c561004080340500002405100320701c4015910b520318130010750030807201d07408100c0040000382080b0f84c480d804211407901034040f40100b90405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 832401600 1250 832400350 832400377
    0xd0e03030f0c0604020a090c0804030f032a03060b0909070c050f01020a0e09060301020702031f0b0a03081909061202090d0b10030512121b09150405010e0f1309030e06 73
    0x9003000d2060000701b03000f03a0003440c41942440c3e03501c0c6c24160721502e100c0d4015050700d04a0203059003002c0640041c1000000c03625142154092110300d41c4d2441010041040303540e4042120030750ba03100d10042400784481c80d6500c51084004201703024404ca20303c40c085e5015109484421810308056422070b481030710050082000405000400d160102144d50700c02410380c02545400e0312607000907204c4222000c1800c07549908200e440d0b8001007540b00d042d000d44081c21740600a80c5a050000c00c54203c5410014858800c1d85114801481160303410b080316416116400e4180000102801031740100040c035400c5003100c010003021403e0f03c40d0305030003251407048030080c0e1429414002c1c24078080703015403c0c60140410060002002e41a001c9500c04048850441400c26401e612281341c881c154489910800f08134501c004410500010000c0b80d800740c03200e1480d49015002c0c84514400f850340c0d02c0c0d0094800807003425244058101d020814828030340700d01c10001c940000740d4103402040c20510718 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 832402850 1250 832401600 832401613
    0x5120d06080313181b140903070801151d0c0307021023240904061404081201060c0f060b040608030c0c030c09040b18100203072607020d0e03030f0c 65
    0x501c00181c038040751034850880912440380c0150045d80b03104094050502007056104076003104440380d105980c03400d00000c003030391a080d075181041030180c02414481810050000700006000380044680c14036040092802c100b80d41c4d4401095126401c0105241d0640c082c50000060008480c4940d0084110041d076800d481c5500c0c0c40000740317207040100322150940b45d0034596991030304015032280030804200d440250540c0d862801d0710262000c000c101548070304c00414002004110390280c03002c007011030524080350380e0311503048400048295010f40070401d080748000204945402c5100c50700806000494415035420469140d5444114007095940000f40489030500e400d1040482d800c0303044a4070300242c00d040d110186070001c047c1c021210080c5c0c1540d001c0309030a083c4150304000c2c001a004545078900410040e09620803d5038014030304900482014810303980d0700c0c000780585905e1b80101081c1280f00e5042d110300c042c2112059040c4018004a081440000c0c01840c403108020043c041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 832404100 1250 832402850 832402859
    0x60d08070512030925090e070806130203190b060d0515010801020a09050603011a0304170f040303120219030509150405031b0d0e0f0d060f060302011b05120d06080313 73
    0x91900e034112403549100c1170030b114481e13034032501e0218060754805003000400503150486545401040d070f00c507540c980180c0040101000b941034035000b04500940941e41501a481c112900c00782814900401401421020824905000b18170895052140c070448080009040b940030111000764000e402d1690005030082d140355003c5000001800c003920801d082d03504000245482c1c00c0c4001c90200e03e000040f0000e41407200c15544e940307845640c05060fa0fa00c6100c41c490300303901d43c400c0c003055010440d5400030b07466041c064803c84901b510f29140200e201c891a003411009081c001c4d02601c030904c64081c40703005841030148403d010303c0c4244000c1d0f503a1000c0098034814100444242c840581046500446040d0810301030194810201d07410110140c03a0000900c0c00c0104150203002945020300d06042176100b544400185d9000741c0b60b843c028403040390b40c2c402486000c00c0c0186150003410103140b05480501c0501042011200c0124416480c0c60081c2d1468001034014484004000c00411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 832405350 1250 832404100 832404103
    0x60f140319140603101806051f0b09010e180402040c050c1501080106080708060117030d11180906150705030d0c0f0e032a0a0f09090303060e0f060d080705120309 71
    0x4801a00e0a01171100b100011000e46d809910208080d20280d04c6400050310403105864281c84080404c44000e4499203800301e0352041d0f0000d40056000c02e809548030242464000c42c0748a40b010789040c2c1200c2d13942d0725404d00c4043c0140702059828440c0a015014030010284464941c494918401640b1589888100c5007954851350100c00150402601400340c0d0390041041c905440950204165551103041c0c0c03c2d180d889203048a40300b0f2071910740d841c500402c510004000702081c0114805c01d8004800420451103401e131070341584601031290101413000399202404a00380968240c0303043c286a500341100b51107984402c000003a04100b00100b180c5d42003035103021440419001410000d051444040150034050166028803a14100f51015581c89409040c06000c0003000348050580d1440858090501c3e5041107004c00e00304400828610400d00c90144038110000c0001015152a010b2141400b0140000d40350040204045d1020640070000b580800750107581ca40d5483c9400f9000340e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 832406600 1250 832405350 832405363
    0xd0204061e0f080307120c0b0a050118151503090c080604020a1a040e060d1b1701020f07080304031101141b070b0f13060609050709060f140319140603 66
    0x81502d0510b9070041c0000744000043d101c0181e480b007003841c0c00c0380350503034241d6203400c2c0f4a00c02000b6240c1031742080800b81c996007156040301c203907114140c00f80d004005844144c2d40d0303050285040c1c0700035040030030400e0b144c8444000b0812007130500040c88036054480e03100c91402600414010b07409007050200f1420300301c0c2e0308401000395128501c92017081140c1c525140c071a030700ca07501201c0105c4001c1422651041c0c51403032020b510401c402d90321203040480200c0300003a0b1164070123003240302203201230a01c2c041c02110f4250003201c164929128175503031100004d820162058042056003214801d510310248910384480c0104058001ca92802c69117840c0448503030084070780390020030f01400000584034030160303030441d100000e07802c01c075a190300d11011081d4410601414090805100060b041895030186000d41f00a0f03440403003282c4c0719031082e1042a41e9240300000134045440c825a06810400030303582210285407a05607400ea000ca8142c103aa21440800e2410700902c01404030b07525040106 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 832407850 1250 832406600 832406609
    0x531030507051009360b040513030c0b070509060a080411180a091403070c08070e010324150b03060118080c0405130c06020a0302010e070b07030302090d0204061e 71
    0x41c3c02c0c0c400c1c5401480c0361024820344005440c100c4080e00b00344000381c813501d40501130308120465041c4402ca420007405081305805d010b185082c01040307850f014041126403440d095160362040c0305540c0d41d00055920002c0203003080203001d0003034048a80e0340c800105481c07a407980c5c0d070029608183c144810041c10008010341b0800d10303e891200b05503154040d19034040c803010700000d0303101d1540c107108a004804c06c0c086a400d000014101c000c11650f44100401d944500c01107030b00c0b0b0b03900d81c020031140c1d12082c0405824000b00c403814100d043c5540ca090340c4440101c00011414215465081d1962200ea800140c42d6040100400005581c0002c43c40c0e40104402c45103042d091810030390588036428410017501440d00d03031000410f54071010703580c000720950254441c0040d5585500c0207403103241c0480d0403030055080c00b0480a0952000a104003920050980c0328a0624541c4d010703030080d402998885d4100010707035403400c0540d541d4454400102490709204842c080101060040c03204039810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 832409100 1250 832407850 832407859
    0x1309051e01111e0a0306030611040f0803071e0f050106030c050f010e0105030a0207030507080d05071103070209060111101b020c0301090f030c0c090603060c031416053103050705 78
    0x31042d050300c0710000d155084140c250b0f00542d10506090120060300c801d0f0800340582d42440090426080000024400ca0304030000d000c5e011616400410744a00ca002d801900d80c1070202002004040c854590140040c032230aa0b00380030700d0642d55243c1c2542e240390310503540c804a840007000b40303080c81d000302d0340041c01c24a08107074032449c408000303801d9000c003401c001001070380070419004040c00303441201c08a6400a01480d146c140740c200034005094200d40140019058150600a184e40007041d900c4075a8001c0c810039072640c41d10f004441d01c03003201400758080d101d03d00302c0c40c0d4065614462204400542c507200001c0c40f0940601078903001c0d42c0031885019a14080091002c5a01281c60400e070a0b81454540001511810070340c40060440d00520b0265141860010400100340d000c1c1016941b00c4d1010301c07111040244051041004131a8123004c254581c4da602c8600340f10b900181880403c1082d510f0000e6025250203504003103410075540000c4c00b01c0d40134000e216003040410000c06003101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 832410350 1250 832409100 832409107
    0xc050304030f051309020f07020f0a081b060f07030f081b09060c030f030901021809061e062a07150c0f050114040614150f1309051e0111 60
    0x580082c074410082440c442009030200d80c816191042c070709107900510f003900007035446041c0311017580c3e0b0b03e42c803001e4124440c0354983c20808040c01c01c0e10324030003251a0340020782015181501e00c20285080051001c0d40400c08100001d6450011406008640d00969400c0b8000c42c084501030000c1d1005801c1c07100c180a100c2c0e202c0c2e106158a81101e1000d40195142070321005c2c0a0141403660090b03d41810030360101000f000074602d03055010300707203203038044140007000040c00b414401d091400750395040e002841c1c070051500089a4500034030341c40d54042c104629005030000700984d000030600e0320b088a2680040700d81c514050070003000e40580300e9009035030b441c0c1480d42e001801000c0c680c0d2006050107521605d04040c08020742c00300071881540140f0701410700e0b292500000401c5d611211024600301d400105107a100010021001d800300540314440d51180c5404010910010341e5000300d4090f125a1103200040043c00202400c40e0f41c6503030180100c0122185d2420748800c004030100d160b0062 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 832411600 1250 832410350 832410353
    0x90b0a0e011a100c050c0a060f121b030207021201050705040521070e04031413150206060306130f020a030308071d1305040327050406060c0b1b16080d0c050304 70
    0x442d08110404a14101381d030202d001072901a05098400d4040d6034010080417001840f503030044070001801d403103680e65106e00e042c132005039001c6881b810300d08508851025119440700c4e00a80c002d0800ea40000c0c0308420070080004001d0940c0c1c0100c2e101c4000400c00328042280d42011501918545e01021102c00c20811808190740c4d03800d03251046080700700e0860042424980107030080305010050b40700e11a51003101c011001450500d52046407102c0b50301d02402b51003240301140c158000c10b8020301802042e11000704540113031100c10015901c9803141c4d0b011100581d01c120070407000318441d4403a40410b1400000240ca8052040701c00030b180000c10301d5200e4159201843d2255036244000e0010302600c4034101200c1c44102c2660140d00c901c1c00c8120b02c40001c1160072058121030b41128148405625544120368120740007a004010501074004903900300354450350002100d0185850904226409440000c00240c0300b0081d5511400090f4203000c140c000d014017201020107041103403031030510303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 832412850 1250 832411600 832411609
    0x50a0306140904060c0c050d0306170607021c11031c0b03030f091504050d050715050903030708070812011e060816030507030b0d2123070501090b0a0e011a 68
    0x280b00800485d550343d00c4038a0b8a0080a800b00c0d41900102140d400d11003018000d0010131850090600340022030101d0745012500150f4075101d404c0303a9010f491300400601c10f070f16447d5070f44c1441a003400811424880e00910070800340402c64007131070b140414802d00000c1c1c0c02c00ca50042115a0007500208030702017001c1400c84c01c40341103a005a030201701801803c42c0410f0180034a0b0410390740a040d46403103405000b40015200140c2c0c030f1170b880c2c0c0c0d10110f41d407140960341c0f44501ca0400750590001d00101010070f8035080038084150064240314a0306840f012803490b189000d8202d91080341180e81504900318903140c0084c064940c904101c2810b0078400c0e80001032400c03546d4000700f055110360006051034800e800c81c45495401501070b5400001910b0400400440712040070f40045180348030092440c49120000e1012220301d0381d1142c900341d0003031980c481d42d00481080d5040c0d07480e140301800141c080031040d4459182c0d100001200c0816070006825070307152154030300d01090350640c011020b503917 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 832414100 1250 832412850 832412869
    0x10c021c11151e1c0f09030201150602120903150112110a0b0f1b030a020a140111030601110f1002070605060a05130b0d12080610020f03032403010c050a030614 70
    0xc604901034941c00d8082c081c4500f00e980000800c0064146400c19500580503003007110400d207e40c00912800e45007116606c803c464074424400142e2140720f01c0d07541c00e40484001e05103001c0182c00e83e0721a8030160709c4a980c4400c203034440b9540c542481490390500a00c2c90300803521100417103851114515281820384207004050300084088000550342c40c01d03203120031024600b201e944c02a6600c650102c0d00103511111004410348600390101e800380c41c0e0000c10701c40c001c0da500d00300103494110385031403004444c40110266091400c0c0b00d4952002000d40c0200b04484080305160350250795241c041c505403003910f07005000c02e4010304c4075034000e00c0305585a8040c0f40c200d00e040c2c9800140580a000080d0012030720480c09401111200c51904655500060b4140300340e07015104418040d80401c130490355a80318070902e0700c0b10382090020070440061120940c1c001c1003001e61040750350207100300007030031035001141100c042140015200d82c00c0c1d8260203400014014000c1c2c80203903a05032400f10380b5401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 832415350 1250 832414100 832414147
    0x5070909110f030f0a050304050103110408330405061008010203060306010512030919050307060c0f02010509040e10050720120306060f160201031415010c021c1115 72
    0x3641454514070030f4030200f140300800d4500c07404070b80c082042828030b20746940c0b042c05280d00083c14141b0000388400b8140448048862942c010020031203810401c08a0141300307504941200c1511503658800d0720803002290203a40900080d04907414200fa118503124015803050416034010320030400700d0303078001c0380d42c0341105d2040d91035224410204042c503065101d181d40c41d561000c0b0300072031301d40c500e5181140701c1e00740e400c08d0307088510046d00d030141900e541d083c0d200024216004a5045401544110050b06090401500104500f130404d00044d080401080b580040240d0720010415000c2e40403080d082c1c03034403500d110583c010b103002c201191281416048032070f24090010114805031544800c903410003002420094031904000d00044544440541c10b0303000a0403d01121203683c99581c1e1103000b594402e1540c01c1a9203120015a0400d020040c01d9034400c1920300003032080441125800c0700b1340e205400070007454040300104034000c404400902c050395020f00c0000030101c404a600325004d0f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 832416600 1250 832415350 832415359
    0x10f1e03123203041b0f12110a151e23090406030c031a1909020307050405130201080108070828061b122a1e0207030507090911 56
    0x346041240c071034848540ca04200c0105a040c1e8060224000d1030243d4011071162010b5001c4012240c2c0059403102c0d240142d180b008030101d4200601180b55400c41c025a2142c51b9106803080c01c000010380542c066030018400c0c031a50408031483c1540031000e01a04203403d003025140e0309124070001d22459814010b5882a0300c040d24003d5950070744401d443c0100d00080061102585901d0584034a000b02e12088030b5044c0301c0c8480400070810400740f60b00c01c0641040404c003a1401140c0312000e003994020a98050064403000b0801d510340b4001c89115240c851000d13401c20b0a1807000405044059109070351940103014180a882c9012074210648117008803400001c1424090089522001c141c00809291800f8600c1011440074224200b651680e0b031a4840707440d00901d80c1100355040700c1c1004031400301e1200c070358410070841c20341c101010001d45407a03240f94552004107184240c0500709900503a0025208200304181004184041c01311003200b8048080d0507600e01d414803802e02c0e00948503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 832417850 1250 832416600 832416617
    0x20f190504020f040824010605040e54010203010b0306090615030403080703061413240b040f17150c0904020a080f0a090c0e06040b030303010f1e0312 66
    0x1010010f40c1901d01030440d070b10903200544020800f011034059070b41090358001031304400000f0501e0081080c1c034121500701100c0245595006481d03143e041a841460700b52080c404181c02540201800d0000c13480030f0420841d2800711004d04074806540a0840e9100e10303801040148481d05003881904d070400c01c2500c4020154580400050204484048800b00c1c0b403004010041410b910400860107050b41d40c80402c4001d40390302d1f0010888203540902034002c07060390068005910303130383d200e0f5138400710a2450b4110142d00d6450718082e400360780d000c140b210310041000d220f031348108880b07080101500c54a02031101c0000080c01e8650340c0d81c10001c48ca40010100084590318400e04450074a68002c100315a1101c0340d060103003507801d050b02d03d50341a020140c0040c9481c803041c0f0803402c0383c0b90020010300c0da45180ca0b55207003600600030b00141c0c01c9503c41004c03903240d4804001460107040390072004c090043c149241c44140c0301c54404484002c440d0940e04101003150340200c186419041d2500c81003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 832419100 1250 832417850 832417867
    0x2010c02090a020f0d0f05011424041a0c010b0301060e040f03051c0e0c0f031f0f06030c14010c08040b070525030b0609090705060a0c0618020f19050402 67
    0x9014100c041242c0200002d1112030b224955402884d0043c000142040350b0390300d034200e149d1200e81d0885066041144e0f00c0b0040424540d841945200c02c1407585414981500c44001c0c150102566004144e41c00010038402c0351190207005801500c4801e4000700140352801038600d920301030283c00608181c0700b03040c0440900d88600129080c041000c0300303580c203150003002454020700000d000c0d07101d00d02890881100c2858204110b45030301c0340050081c40f5a1810301c50140000c041c8624408006680700813019500085000300b2004500403840303c0901c074585007003640134a8001c009030741080b446461007000203003800b0964003590308070026145c58044c103160551810b8250b4405442003541c403111490f1080002d0140d4041e82e01c04c005490060310f0700d00c1400000001034030458005e07000800b0900141c10490080e0601c40074034500703154054075985801d000c4402544000d130030031148050840a50401500442003a80282c4054802207000c00d4070a8144403180905882030f5000a001d08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 832420350 1250 832419100 832419121
    0x30f030609020a080109180b060f0a0510050c070807050d2d051c050f1209030d060b091516080307030207080c010c080f0103050a080d090b091e0a02010c0209 69
    0x401034211024110741ea2030064901600c4c2040900c44d048555041c038030040741c0480c45000301e0b441954172840c2c05241c1d03207036102040150002401d445070800041c00001465584c4c407020050340105c03d403140d658071205400010704001c10742e00f04d603880703071701c808401c201da902c031510400c0072241c1000c0e040345018050507e00e4106520807481050550501c648041444004140d1060b0312345a041000541031001d4001e5801d0b0045100d07800040b58244a203044151961003420ba0008012040d60304d0403249031f905001300c1740d0b40c0c1c2060117680d00110340c20155082050700c0301302040d64206900c0c10a100b0000540d00140480001400780c0300100118006a0090301680c040550003041d083e103584c0c4046400c1d00900d041c1940c040010614808182030600d074961441c1a41d8101d0044c2c0302c45141901c0d100c10551001500d0304105a540c04402d02203803407510b00d50301622045026000940e401c05046a903241540d000d0241d503003040040d400141e801c80c0c900c242d2a0740c140c5031010550b407181000c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 832421600 1250 832420350 832420361
    0xf06020d090309080705030c0a0b030703181103151314031b0307120504050918120a110708070f061b050616120506010503040f11040e100f020a080103030f03 69
    0x18181030381000450400c060300324503840d0540d0740c0202210101caaa500803d607484e03100780b602c50742004000c201031011140e04070045038800c100c0d00f008560000d00300c40303043c0054024601501c0c1000104844009450f090000542101c03510b580340b01c603420001000c0d02c07190300e0800010400200d0b041580940d000900c25a4010111002c01c3c0101d29280d102107a180c3d80041c600715520500481501041c3e80201e00340d40642d58003a20050050b521100009201c19409a503401a8803c58002d08844100b0300004c01c4040029500c0700000e00c2074001507131500d4880e40111041c3d8010010920075100318003840c0303040722038524194101347e980c4281c2828602e00c048000d0550702600c004c10050329041424520904826a02d83c1c0742e0380c1411582004889054400740c2c000303003003000400c010410318030b455070000340520b0740586092407a40c001030071644030a10346005038000000d07402c1140000c2c42070280e5408440c2003585401c4008000030b007441c1c01400000e051101c1000c80f1140340d8441d0b0b005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 832422850 1250 832421600 832421617
    0x31e0e1003090302010f050c1909051f11010b0616020604170309011101112a0f07380a1809061a07030c1103010e0a08030406051807030f0602 62
    0x15411103260008000303024014042042c1c001d5030070050031507400c40f01072040341e104400602c0e0782820201c0380145144500d182c1c0da005030400488030340200d51640c6a0240030004402c074603040c140460140300140564024104400540e407500310f45010a03255403045410315080f0a0403601042c11910000f180340c0981d8010082980042c4d190801c40040000108045802600d5001802c0396510616081c3d66403565001ea00a10034084030303022410803210105118112401c0f1410383c140c04401501c0c280a2541c0070540d58091070b0701300000c44070040c040120749640c800e4010880403105d9040c02400e04103000d000519400204169802d108031206401c46410041c00b82c0c005035204000009841c45005001c80760102c99400034004206000715110980c1c5501c0381110031515840d46101c402084420907055503ca440703800503040c0500605000703611a4584c591070742018100002151310003041d11108060450002007807240009220044960007190f00390300c0c0d10f851034002c0103130284000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 832424100 1250 832422850 832422859
    0x60509071d31060306050c030108030a050901110102191b050712050a0b0901050f010b031e1801091b090510090203041a01080f0f060c1c15030b0a050603010504031e0e 73
    0x401241c0c101e54022030701300c034040e560074042500c40402c006858071080c4550b214a43c01005803a002502500150041c0e41c41410010006a001b00d1440d09990090b40d0710418294070020006441d900225211804400310b44030070300f642c40da6a00c00703545400320b020b0140780d070841402c079004000b0104013402c0f1072a48086650401d040003403901d40601001d94510003650b100000204401c2020016a4414042d100040c4031054440d10206c0220307101400e40c6d08059408410448929424081d1380900c0d032084102c8451300c0402400c440c04141c0755000941d41d982044244440d0401d120340340810784840074001603032034840d8a801c0f200011102c038007500c0f85c417805000054a080114480c0410b41c0b0072010389250205c0b80301c00c142c6440003291049c0204600740950820b02c0311285a08501100c42000001d104082411103454240f041e4401c07a04092440304200090480d40502604140c054009005a04066a0103455124034003000703146900250850016284aa94a1020004041c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 832425350 1250 832424100 832424179
    0x2131d07080f0609070c150c110c060a08010b0a0504030c0e06040b010c0b07181d0610020102030130060e0d030b0d0c15140409060509071d 61
    0x1610080400ca800c400410800800a0340190b200d0700003d1044070300500300d000b2a600e500d829210003907041c1003500e0150b02101070340e903005400c0c49001e202c0785468660301105028040300510782001d0000503401000c06018120030550844072550565020000c1203446c2c1828200c00c80d5a405298400b40503104c00103800500b01d40c00c40005401901c0c02d0b038041c003003c076858005460422030034100400c2440f00380b00081c002031140c2c8540c2032440100d4003401c2440da540c214841d0480c1d07100094002c0400f0790b0144607045c0b0304002441d9403c02240020750540d80740000ba6941c1c008481480410345074049180c07180f01001080000030f460740500100030200203001c2c0e1a035500055003146001c20b1406410440c1e0b49030001543d06080c1d0b100716801000390a0940000000204444081c10301c0340c81e4243e07109403584100075001070800784900152051512081000c0000042c0c5004140245030040c0095081501c60a40d40004181c0f06001315003110b0180d00e10001d5104403a400c02e81042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 832426600 1250 832425350 832425389
    0x1101020415030533040b120d201902130905010603110303131e030b090a05060c0a051b0c0303040e040605071e0e012a03120b01050d0213 60
    0xd5090710741d4030050355010020b41e9103810501c0b02c2566090040100780e108140200356202600010351109500603101180702c82d04803020410303500090200e0a029000b000207081c80907444103030340041500440300620b01d101607000150701c030a2410b10001c2170704101150302040d912454403040104150050030040b090b15030415500030f0080c1d01003100d038009925008803442c40c0000503521400c242c05840c0340c00614140c102c0240807030400744d00b0f400d00c9800600001040f51001010311852542c07014000a4000d0300e0541d0500c000289118619141441401c0849600c0400e03203ca8280411541e0b40f02c07500d8036041480d0000070702a1a40c180320004000c140d0501910b465401688034032070a02854455401c103039200c14160381031104000c0441100202c0c039102c0c4841c540411018102170410040c2ea40e00140c1c24007680100352403030b045403602201095403103403140e803001d20100c4d030070440b00142e000020484e02c280241c20307581c5074010801e90801e55551481c7d10092541640303c640d8400c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 832427850 1250 832426600 832426619
    0x801060e0a0e091b01090b09040f0b040c02030c1203040c0308220f0501090b0c0307020108100308030c0912010e0727060602011b0212030604020c0f120904112811010204 74
    0x41310a001011040080100410350050070540300341d44200540c1c5061000e0081404000c2249012210000d91100d20840007030302d03944102900342c00c2a60245a595001c41705540c6085c1c2e03041c030065a1f40c10308001700710205928480d40c6083d207610100035545e8100b074001d0307000d40c181c110181040b01a10180000351000c080e400010072140283c0350402e03901d545100b008035501448071441e00a8008203c2880158400c13a4070913030054068480c11030241c1c03651030340180764208030380c10304000c0d4000640140514089804003c1d03004070030001d2095540d1082c142d901ca42d45e034864440c075108811039a0540112807914060600c042050420401d0360340c000c024041e02c144d00c01c1c03103050820340c601310210038400f0411512204000c9980d07495a00c84d0b1041c000254010300c0708041c6802020200300840e0014031100d1103e01c1c0204800c0c2e1030b1032100c020482140c244064600303042c034081112050070350300e02d400302d55000104805125450340a55045d60480c13241c0b0500300580d480094089024540d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 832429100 1250 832427850 832427863
    0x3030f09010c050d0f0e27060112020a0203040608010509091e0f1204090e371e020f0a030b061009051903050105480706020d18030801060e0a0e09 64
    0x121b540d1010341042d1002484040314520b0186604041844015540c0040c100d1145030003203810724000100301355001190049070040c0c1b804000503000040c0420120340e01c81401405400110b0300f5905c9811300c4808941d442011003281e5207000d4140c0c9014440f080144094114001e580b0240c0701c21980b401148919030748079000b4014241e2600050307411400d000280400c81c07400c095150140190920001004441c244107242c804030307007100450300020065001800c1d42d403141d650f00003900583d481000343c0075016100103801844070001c20070109000c07140702038001304251420000030360980000c403008101600403031380000f00000c0c1c840c800d1440750440b10480340a00001c0215032150406407102140d605214800c1c50306001c0e804181440351103100e400e6030800c11545080c551900030060654100240503a50180e000c503408038148035178007a10281c0765007909200301016040d81e02410780c00041c0035810400c02d9800c107a000c030780c984419240c040c24058441000c03618061030b0581e42d440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 832430350 1250 832429100 832429127
    0x6030e10111e160807020312040e0f0a092f0906010c060f020f0c1507090308090415080d050408010b03030306151c021c0c4d01050601170603030f09010c050d 69
    0x4600d881041c8c080b05020150b4056405100b0010283d407070b4500c55491448016202d0100140d8500d05000020f202c041d007107075410846c015141d003a222501c0d00306410307000e225129004d07408031010000c01d0381c0d0000359144101d90006002500045200f5a01d00a000303140316017054900018075941c0d020000100c0000703c10411854104c2da80c0e400008407044078041c400240b0a0906109401641c5055003011004607031054a03880b03030944c0c1e030020f02d16080090000074007040c400101031015070801e0140c43c0160906400031461030030b01e400402c1442c4a0a1880ca00005002c515100215104080327036005a6003100299100c00900d88072041888404026070707203c600c1d00d445c0322a4940140d103441900d60b0b4107040b40c94070b0304203131030701d03c1541401e01621940d00c6420795184056035200640703446880a41c8000040074941100098281d041c3d040180c19091040e10421516540010484d46510020f0070001d4540c400180181c8503001c08250080660007882c4041c41c10542c4034081c0381080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 832431600 1250 832430350 832430353
    0x705130230012c0702160f0602070603060e0a090c0f03061505180a0e0c06040807150504030807031b0f110a0b09090a0c05040e0106030e10111e1608070203 68
    0x141da031104080c20303e0400d01d89900d86041c07041c9650301c40c540320740c60040d4010f4240c01660003d0f08244042c01d000021900115080d282556050120350b40c10400c05020b000603007010407a490409480842d1020000c0070280744070703110402e0034100410070015134010b09800c0c0b1400c44103912480d10038081e00018100d8816107445000010b894a001d0542d00c410042c1002c3c8a05036480e03c00440000d08100b0400c004a4414170f0355101854481400900080c0500000f42035070ba030800b803411110401c014051720410209000c1400440c00d148102c6108030fa02d418020b1092030580142000941c9401002d0480c04406002c0d0086c40b0387c6007030800e01d0100485250600c1503ca002e02c0790540204c1215035000b480d50310005809425030f81c405403020b1441c1c200123043c56a114001e641c40343c42608030900190701c0390070982d4143d80400040c500764000031018014104920245615802140081c01c07018040901d1003510b000c00e1811503000e8402c800b042e140d8650b05003040c0f10755910101d01240203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 832432850 1250 832431600 832431697
    0x270709170c03100203041509111e0301150812030907090c020d11061311120f280f080a0c021903230c010804030203130f05010210090507051302 63
    0x103d980e10880348140c2d031241c0c3d42c0042d042c010b40300c1c03402440c12403c100c0e017000c500504024075a5402c2c01490303a08941e99030105600d80d00d0014107003500c180d21070030642c0c0ca042c02014400600041000e02c075032400100316944a03a41c80400c10316007161980500491032400c5000311056a011038148000c40540d2a18201d402840450a83d907620880ea4000000d198950360f42c0068861b8400b400c258900501400c100c4030f4121000b4202070a2800a010790340c050400c603214105100c10900040c00d0244d50010906540e44a003401071502401c01420b9002c001100943c031801a0b1410401d01d402a00b00306901118001c0c3d0944045940400c1e2001c1030782c02a121030ba40c8258a200b280d007003213640548146075010005640005011b0400c9040d408103104481c0519400b410403402061052a50032191b0301c1c1500290618103085134848210b82402000c60101e400080d03040102c8a0941d80f560710281810241e000a0045582c2c80d04000c4110301da2400921103c105140340d8960020038260b0b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 832434100 1250 832432850 832432873
    0x803090115060f11010e03041d15030604020105071b0f06110609070501030b0a090f09060b040203070f0f090b030a140c0c1b010522080606270709170c03 67
    0x4658a2003650002210f86070321000c8103116100c800c0f40208000d00104001d2000080941150480d4000c0c5018441416450b004a000030702342541002d03030009060404285030340030a4469000601c042d06004000482e0700400071020070500082ca40c41503506911503c6001c40c1c0381a1181c1c3c8100720000c0d0315202d04011010b400702d0054003030300462004000c00c92070000150701605018000b107a02c59001c000000c1c1a030310074080d0200360002c0c2c800c001041034091030b004040311100000d4900443c4144100210250469480d20b18296642003003015410b15180444540c41e50340c1107030301036040110074041c0c90010390b0040311100301c900c02c1d41d1f115941c81c00c000c400c0d00d00894007080074991082c400082030351803421100b1804103040c5496443c2510400c00c98068a08601c00c1d21401e9102400c01c0003015801d120494002c2c0f42201d2072040350f402c0e0100a0072030707054004002040c100d003002003504640039801c40f44c018186000f480d98442d11508000352540450840d0f035020740502100c201 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 832435350 1250 832434100 832434131
    0x90605090c0f01020604150209090703090302061605070212011b02070f0503150c030a09080705150601110a060b0609040c090602070f151d060f070c090513020d0f06060308030901 78
    0x21148040e40103040a1b52107884103d41600481801071549500708003080098490395801c920030419900c01240009042ca0000d02d0000c00602f9500c904441c184004007040e0700008544d81140c0480d601540700700001c10950061000b00b41108051000740d0740c092000d900421041e040325042c402c0c0c1c1540c40c0c0e440b82410384499092039641070318410500040d05482c1781c04055608040840c03000215803000c1d58480c0c0c1682d2000009466650103441c04402140400e04180e9200c4402e00e480e1000c04908504141e440741024401800291130b400e049659803103850035a4800c00c0d00074400d00c10490410809003141c980b40c05100014018203001254104d41c0c0c0380340c00102d40008401d081e4500285500b06ca103150201000c155004031048441201d640317000141130266807003400d0650354040740c9454041c8a106070b000148460921003080000030410500043e96601950343c00400c030308170f1901c440307100d010981c01080350b071400b4004030910800c1d0004e1881801948020010b40e03003948540d6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 832436600 1250 832435350 832435369
    0xc0e090108121204050a0f0b041e1212140a020a02060a1e050423010b1e10050703140f0a110a0c050f0102031e07020a0b070b0406050c0d090605090c 65
    0x80c075002c1802c1280b02c40301402e00301c4080e070190007042610a9200310380c0d6880200d201b00e0300b09858413111034042c007042c4009440c01440308403071100c4a24000e0703c40e50320012200c40c55800c0601788003c0a1000480c40040e4000ca60a04800c03d00c00700c081c503102a6200080d044041000c005110781000030352080003621a00d00781e401441038002101c4004011a006044014000c840100c07030000302201c02c0c2c5801041c558035400010000c20340c80001c40910940381241000c0c040d0180b0b42d171f012010252a09201800c191070546086559050f480c1000e4861083c1a0342c5101054400a0786d50041d0b04428046e0500042d07a64a143c8400a55406183d403442001c0000c1c20103100d8440c200031624045a08200380380040c019242000b071007107020f1484444030b5050a03d85600050074004601d02201c2440c0541614102c45083c100301d501c4200c1c100b00c004000900c1d1307d07551004500300c8112203081d6502c12480003400e0000d0716071850a0406000140d075405801e100e854030758485840d00c1c0822 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 832437850 1250 832436600 832436623
    0xa0303140721020c0f1c020a03080a0c090305150103020307061e0c241505220c03060923010906080312250504150801050904020d03030b040c0e090108 66
    0x100060280b07207803840c090300101020340d40d00c0c4550801010207107500074002c02441030001c201401510b1068411a02e9244408a0b10011900100d42900c006900f003c0c010350494400302001541915024003a01c60200783d0300058540d100e80750003220012288201c1c64140e910903002d031a0565504c14080c1d80d2401450400300654440104000c00707148581d101264880c002c06400d00c0d10100c810822407104d4802010000007512207040728034641d10141d081004140680d0741c010311140c0021071094030300100c20b4480310700e03484a1160751518400d0704480090411341900f000751060184642c050400c0517401d007400f1165080001801000c01c0c4550b10880f15080050340c42e004041c02a030f100b10700002e110050300451020520155000c2c03a0030a490038031b840e15055903450400441c1c03c1c0f14200d01ca0f414042110b007000601040d200c03200c2d0f56410940c1611403030042d1103146800d80c064400c0c0b421040e00f20740303007101c141580c99001c050030503000821b40f42c11481d41d8882103840d8031141201034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 832439100 1250 832437850 832437857
    0x1060c03030b0d021905010305090c0102030403140c06030109061511060a1e02040905041a010602120a0c140102090f060c03090f03030c030a1e08070905010f02010e010203090a03031407 81
    0x60040480d000c0e4216214000d00249a030f1107000ca20760000d000c1d140c901a01c15071500207158140203a5070548030355a041a081d000500e01d5013603640000395680710310b0000a0103502c404041d0000660100700318020344400030900c80c0c03a50384a0600f40000c049034810200700b50040485500303964012035102203072844040c007070001c40e43e0700300307519018003020004c2001004580c00c0404806820348050409032034140c10100d0541041d0900c640304120100071a40384208220042094540024181d002c1c0c2d12100c401c47d40b942078113001030300e1070041d00101800b0450b101706240750694040d80104030243c021a50034003803400030401d108040c041c082ca1380e5525482006200c600b4036003a0740041c2105002004c0302d140513101144181150402d05130100803030005505079071101207103c1d080b02400760b1440c09a5a42c6800440100039280c4e80c4a03490603c08140701c40c84616100303400c40d8000c07085840003556030382040d600650307851400302000d4002a01d000d000710015080b8001540c004c415a59 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 832440350 1250 832439100 832439117
    0x5060d0203120a140c010e060c031905040f02180105090a0c020303010b030c0c03040e040c1a09040f0f06030317070824010e1003050f0a0506060706050604110408030403050c04050106 80
    0x41c140109540003c1e05007044c465454941e440420008004100003c2d11030004145c02076299926841c0002c0a400e18089030070a03c01c219045191302e5011003d00311400000c00e894469007442c608410010001070340008264540b4106034400842880c103c0308161754802e881d58402990004882850000d000140c0041004003c0c00244101440d0000e43c4400072b58070b0445604881c82c034541c0950b100c4d05181d42e40100708414801010040300c01401c10041c0301401c420040386005003440742c64442c500c075507980c4400c0a05111035610561000818107400c0107990303182d0601a1048100382c0100d459543d034280040c00161240000c140200072000c01070f4902030540169424880a040d0780d14108450115204032079552800709004002c072913100020f17503003044c588031080c036000140030100b00741c04c0c64144106611013404940b10650001c400082e5921a040040d006c3c080b58043c0c0d04080d940400c01084440000c40103104886c0b04104551840354442d0070311055840034030410b400300d151038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 832441600 1250 832440350 832440373
    0x2030403020904021801030b1603021602040c0908060a20040510050d0e01020f07110d0203030f130518061801060207030201030914060c0406020c0603240a030506040b04030305060d0203 81
    0x24407450f070802e10040c0200707400543ca511000c80d0b035900b40d1003514000d008500f800703000c002600440502650306e19040d450410034400862444182850090040395181e04209502d0710903101503000d42480c009407640fa0a08169041c050500c105646000f4404840e160021542c032404890032100058010010f90554901c2a640c982000d5400810981c6601c000d880b04982031005010f070910007946183c45291609120185032020f007605406003810b40d14841c0583e600200340d42401c0400004559103141000340e121100f01184c1c003540c0c111005210301102c080c0d49900561043c0c0003a2403c50810781089071224a40c6002e100307180241c0c1101e101400075510940101141501490b0300050101054640c1403401500300e4121b1105180410b0a000881c0d05202030400c1d020219102030940c100346100303414400006120b11402e00c1c0745040300100d9100c0640c0e4000450300001075601d03074507190401c801c4038401101c080300040d04d08000903c1920300b1410102ca01c54015004160720b5064 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 832442850 1250 832441600 832441609
    0x210c0414060f1f0813080d09031b05070b0f0904050a1a0319080322150608010c1e2c030705010c120e01020f0f2433060d051b09010203040302 62
    0xd416901210078045e40a030214015400404140452480c0003c8441d40e5041c02000da1554601130400c2c0110107041c5c0c03002c14400206401070325018101d00340c2c1c070900c004e084401c0d445044080c1d030300242003004006031000d444c1e00641000078410048861802140101502d07000100c480c202c0722300100e09004049043c40e4003665000304001d00042d05c0b60701c0d144240030380a0152404588440e4120581c101c42010b50081100a10040e4024446111003080140c50841d000200700e51200020340000001403080340c00c804d800b100020450024481b5802e204030f048a9074035414041d02c108140003038194401c4150b561690707044a4040102500c02e0811a00b9200c3d21507150b04511904140b0500b042d070510821204045243c01041e512040044007800480075142d610301c40e2030b00e07400300180d4185050447d1000486001c52403400035000314080941502c01e1501500800301141c4801c010f0069840345000703400710203420070b82600010b25400302e0311440000c05c1c0180c10030700040006041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 832444100 1250 832442850 832442867
    0xc1603080604020405040f051603150b0903030d021b0f03041512270309091104060c1506120209090706051b010204050405070302090915210c0414060f1f 67
    0x80081026213003698600028056030080740c0280701031503445040c042d0070780440300c3d4140101d41740e060034090360400e0205c071001d5090360b2083c00c0c44844000780c5420305036001d1089881d0000b462400f1500d6a50307040403031900340c02d0306900070f01720304c902d0000442d0a200081550300b20f80004014041a0450800c00c8461481581c0d2800701d05880d078001c032110b49624006d0480391a0205168030078040e803400d00501d182d025a00c4000300e20700d0114000c5200d4500c00032101500d8250a00385030f65076107890007590039071541c80c00c07030042498080c000c0751141000103c03440d424002c03541c10030581c40d10742c10280c030390f421882140c0c0401e0081081e40c12031203c403000c40700f01c080d0910005081961350800702c0c080d540e0441e04800000d038002018403075440c1140c1d0403034028104400c2161030707a101d039000c070303c000c0014400400352590b150040801e041080014805152001c1c10500c4000b448411514054070300f43d804510813070710505214210f0034906c4403207100c2c0b040c1d080c0307541902e0b030414016101c094 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 832445350 1250 832444100 832444111
    0x7090509071211040c080714090607030537110105090c04110904060e0105120706120f0e1507020105010801020c19050a021210050c0703020a03201609050c160308 71
    0xd1038810007510300da445203d1005d80000944130002c01c2d00d00601c00034140381c900030240c0003074142030180a90036103c2c0c400356002c4650501307120b031380c6114042070882ca03400f0120185c0d250100107800103c514418801902e8107030501d403145018607940009080c00e994003114152007170307802804d0b60026480c160b041003004041e6020b072146040c20100c003103029500c141c1c1141c03c4e00c0c0c0c80600100418140030103080e03000006000600441400c00380014020f00009d404010400d4644000c00c1002e83c1c640d11009074600000200d807140181c0b46000a001c1c1800c840400c0554a80000001c5904040c0203c566015907140580204d00740d580c42c2e01462120f00c00161228031503031004c2d00050321040301c44c1074440103c0c401007c4840d4016001d000341c40d0700130300c65600310700103200c058000b079000502c6242c031b03a90508180d040310703501801c82c03107071800b440c01a41c0440c410181146864103010300c40300192100d001003070000780d031030740b03090a15486910704074030100300c02d207403404040b910400030340340c200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 832446600 1250 832445350 832445363
    0x50918040303020c01020a0201060f090c050a051c09061401081c08041110050d0b0a0f031509020402031305061b07030f1211041d04080306011d03070e0603070905090712 74
    0x144c1c0203a03071030b08a030018a81500540e550b40d8040c04804a400d2042008040b00382041c042da0110309001882030007144101c03400d100000ca0f19424400d00b0070300301c0030345403012030341007220030314505000010740300012032028160803200001c40c03500300c0402c0003405d260114514801d2110348050840d65034000810036a48039201d84a0980303c0d5a8071501540c0d06034040d034440303495098058043c42140c9402540381d201c0c40d0301d0300b803c2064000f0098010200d940001303105c480c42c40d4410202c009400000402580310784000200901e0308031002c0485a454020400c40c0e165a4808032000308034001808507c20b802e000340100c10000b0b02c0790110004000052030725066008004c0d0804058460a4208080194000c241401200c502c00c0d015031103d0300c010107100c90340c01c1544801c4403a01c406070180b41006032803512040b08040e206010700640c0c00c05000c54201300c3d600c1d60341c004440c40544d52300d486405002070020b141e1040d40510f03400f8035064400741168500d454149583d007815000d0031602c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 832447850 1250 832446600 832446607
    0xa0c020301150e01300807062901050f090f1c0c030b3603070c031109010509040b06100c0807150c020109030207092a09090b0105091804030302 63
    0x1a1401c0c0102006a80b51101c403215030360401510345007202058100d0140541d4800c12002d4844000b440300800702110f4094500c1d410309030904942078400c40202400c040c4c00c008880d81e4140b001c0c036894108010320b2114213680c80503400111401d1040700600901e80409000400030ba25142d0305070034403420014880e80102d022545441c250b4280f070341d002c2d1000c1104141c10802c0c800002d0f1003030383c4218410300500d441c3c0e43d801c0c0f1803c002101782080c002da24200610710708040108108840c151500090829a81075903480d2030000c203140c1f4001140580e42c408e00000302800e05c00140c500940d03000c280d20009549032424405244606600c00082011248900000c00d0f1064024100a40151000e1340454040d0b84854242d403c1c0225010440e8503000052000c84d0b40807550303005450301c50130301060360b80c030900f020744680054a425032240d10031b5140c81810150000044011140e05000a010f5203c0400c01074a90380101c10590b80c00280103043c0004400806415544c8240b10781001400d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 832449100 1250 832447850 832447853
    0x908030406023006031501290c0102072904031e0903170a020706021f052505070c0b120106030e10180b010909051c030b060304060903110d140a0c 64
    0x65412550141c040441610140b0016050500902100d810390720022004c0c1c2d4940908c980e4042042c50b609904140d01140f4031886680d84000c0b2040c441001c0000d42d02c0394100c2c01c01c3c0b8540e82c0703902411034290902160709903803814441800e603ca00e030141c8424a146607100700341e030070764104000c07418100045180d010001400000c90401d0b0781c01c80040e51a110300404c10041d29040454000c0310541d4440000400e64041d0f05443e0400a54041c8c80801d41c1d884942150f0305d8000f0210211414154880781000394a41c0032020f40021030203136071000d420560350307110510340384180e611125070103051100511038140203400c50030020130310000300c0d0340030703040040000e0032140c0c074095462118016124400500c020400d0b4a80034000190341004a041a55695a907031b62180d2203110f4100030f01c02c9401e00320f034040e500c24486900c002d801c0701d540b4901450004001c1403134803400c03800301e500008060008100083c0c00c3e1124611900c50000c1003140d0060300c40150084440481041000c1c4000720 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 832450350 1250 832449100 832449157
    0x1218030a0f0e0405042306150d170a02010e3003072c01021e0304060e01090909030504090c050a141303080706022a0d2d080106020709090803040602 65
    0x1441030703001e00c40101e8400c940d20740c112403101b4540340c001c41551100c414051400c0c0c06424114041d44215100c080200651501c109400c5d2502081d4014010104208444c0c54064120002e10010182900c9449401640030301c00d40402042e0788a098103604011903440092070001e5400c2005400c01504c001c80e000c030a1f50107644505004d468613460324002c1001d80d40c04110f20204400035008038151301050415050f500c0c01184261420015912911001c69001d80500b901501d003140e8144002041420701034090703400391148036042442d020b4120007887c40381d015100c1903d0160b0300d41e00e0481c46024a0460b070380010441d0380c807200c4066000000980b14030010032040c1d114030005030b190101003410b00c1900d5500700414562140c0d190040d00c660b03030041504081d00096040c0030703074401d0031409460040c2001c40303180300a84d002c0c00c3c403003071807285c111074800c0c101d40680d801c03129003945480300d43c1c0c20340300c44d000d000341543c4051000c00c1c0018190740140c00666411100180f00000c44107200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 832451600 1250 832450350 832450361
    0x30b030a11120d05090d0807120809060f010308030f0c1b0c03010510030503070308070203160501152c04141609050903031302011d03060c1218030a0f0e04 68
    0x11181040007164100c21820800c0b2010142d64118019007141c120303200028019116820200784902c050b84c1c0c20004010052081d1040c454200712840c1c80303008541000390096030283c4402000303104080000e08042e20311a9003906880d81302c6580b6081d40c44200358400750701d00c050078201c4101010b10489601c03180c03004a5605e20300b090300c0106a022a20300c03e06007120800740510200c91150038003840400c800008517043e0590525240c101070b6503809040f4158000c02d01c0105070700300c0004400c0144001500003600b950244074814890545d580c00c1c0144450701c500034228469040d8141075100c021038421107502500503190660030030449500036081038090351030f403000481122418000000c16100b02c1d40d0068840c4020b502e1818031244030001c200f18240e00904220703510780c00b17601409810a410015200203000c664203410301254101d0240c2004c040c401a8445c54000601c01115071402d40408003907441c051071a00d103140b00101c6590344a40c40f0181071140100480042d500d5621a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 832452850 1250 832451600 832451603
    0xf0901021e032e170a170d020906040b04050301050609060109060e060708030c041a0c0703230607050307020d180b1b0607121b090504150302120c041b050307030c030b030a 75
    0x16040c0d541c1c10000360000480f803100404c0ca0b117510001880000624241a80c00c09070001c030a52501d03961224410f901a01c29181d02507040400070400082c46090500a0401c0d510308500a0000b80c1d00d030b0017408207154049a0143c0050703608041000058014446419810400391070145800410f44811040794025100d1500a84000501300711404560f0f1060284a050071103640c50031680c00042031b0340b9412404040c21480c42820090428002682110015410034003541d4240c540444040d08036001200c41401500030840c2c00903140748160454502d506802485d600c0042c1020050342e20f40e003248508006802c1c50300c0520042c0b40c802c01031148200c06540e01c01c200d01c0310341a03a0000b40d540c3c604031021050601082c3c44005078000380400e065450644d800200f031042910540c0c503540d0103910194101d0203100e80201c810300003150b102c00c4014242c4040c02a00c901d0841030380071a4602800d00c001401c10310104207040d1007500071445511281c03a022a544640e900000d0600f81c84010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 832454100 1250 832452850 832452931
    0x204110301150207060507030336020f010504180e0a0503070b0103030216061704020102120414040b0a0807060e130c050d1b020709020f04030b010303080f0901021e03 73
    0x104012841030500c0b00020b4424800b41031503901c0c0c028080c1090244401c0141816102d105a183c4e413000c5092040c04000c111400e01510303050b43c844000044148002a40136502e61480710341d180d401101140c0c226040c00c21480400305014108400800c10000c02d4102070003110084004144100003900c03041e8001c0d4400346440d4074514001e072074503168030307a11400d86a18034010082d050f0022201e00c2002c1c500307501404e241d52580300403403c0070401601064031b09004140810b4003c10050502ca8007403040c0d40c20840c408904040064442d594880c01d003040d8000c02d028450340344960004140c4003c0175144c06001c48007502240b050301d00d0054500e00280000c030b40494880c98601600080308030080d107940c98010f030203000a49030040ba01601d15403d400082160044055404903001140c000b81e02400b9035840f89001000604140c0e81090a0302d0840046000380c030040c800c0714020101030b0744a804d0080260383c82d15040c2c0006206279114040b401d80c0804080c68043d40003c299040c18 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 832455350 1250 832454100 832454107
    0x50c0a18260601080c0607030804020f060c01020915092202190c06150501020601050d08040b1812010501080c0409050a2307060e1503100b2106032a0607020411 70
    0x1c0150300c0c0400591220889501a075005420384e02c6000884100076010b107013a880c195280d0012505e080d44a51545410120008554010f080198064150600700715000b901d50384404081c0e41c0385010703800d24141e22821300240c0100120b84418004501c41c0f003c03401504018200042c9584010046030040124624061100401c40c02d4030804540f4100880f441d03c3c070f1410600000d545000c14040d180c016070501c060701050041c00c405407801003049001480d5510320b601d11031050300800a10040c042e4100c0081840034035018014107060760b20820003024400914004c01c4041c1c480c004040c2c03541d0181e13400150118047c2c41e505c10b10303281103041c00a8203407003441019150200f5903000804100c6000d1b174900303403030b40c6058114500a050245440d141d49500c0001c2100c0d81d429400070007405c40c000380d200b034210000d03844505801c10703c0c1440300741c0366149d00c14141c583c820003100240d01107285000c01d540f01c041e20a010807084002c1c12003400d00c82c0a5022604451003c0300f00380340d854020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 832456600 1250 832455350 832455419
    0x91906090309060c0f03030c02030c160e090a2423221e02210f060709081c02010e1e0609030f0d050403031509150801050c0a18 56
    0x4038040700144510300e13041c18110801d49800c10044490f82e002420551110003408103039208005403440201c0e070100350340c00907550720f000d407205503024441c3c1d40720751661b100060300019011400f80900741e042850185240f0060100c010f1000c0101c0701c1030111a0755000440350080f046104004850212003005028101266440982540000c117540340040310982c000008600d4007007125003062450388821101210701c00561219201d08005040d40051410324050b400d000075542d0319145280280d5941d91030f8800c1c00c403142d00650180d503805a2001c04c013000314001a07c41161007014901c00080c01e040404c85050070712500705c0082d40608400005926501018000d490b000702041009609d800400d5040c41414009d908a0700c003402c0d0355000080915000e5048007103c0b401f40030482c20741035140d50020303005010344000c10300e0b40841ba45011800e814144113282c001d1041002290901c08026021210301484400c9544040c0c0d0907000081c40c644910221080000518850950701160 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 832457850 1250 832456600 832456607
    0x703120819020a050f0319020a09060e011b020d0c09020c07050a050609090103020904050a020303030c0c25050d050304080f0c190303090909110d260913050919060903 73
    0xd00400c07940c2881002200007007500b00c1e0450320700c2220709005540b01d80d80c030601e1648810140300d00203640b038000901c0c9132031198460103100a44619881c0e5815506803c0e004403111841902c450813080c219140550162814460b600d200c288034030603135000107494400e89001d80c2c004204480040c3e2000c4000e000b5890102c4055000e080156000f50030a110130002400f120301c1840083d024604210100f001c1c0716052090143c010f8015003125560300f0101840e032119440745600241c180a280010b00b1070a016500c485240c110548a80034502c0c01c203403c0080310082d807901141c0c5032004010010724450140f0403d041008a00060300c0c81c16000e405001030302140230909200c80781800c0040c000207402100c9101030350000c100000f001011490800821042d10703e58990000c1e00480a4040140300c0b40700d50711411040c551502d51200c0f19103190000d0003100c00541d8402c0c6550640f150405031584030760390105080080319402070388107170a803250002240c2c059a136144c8910000c0d00b032640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 832459100 1250 832457850 832457881
    0xe070807050a09110409090503070b100608060906010f050a200d030c05120a02090a0e1003060606170402040506030a020d0804031b0b0a18050402041d0a02090604060e010207031208 79
    0x9083c0e0148a0389403c50072400399881341d805500c90640d0b4461500007481070802c142c643d190340c0b04814005500340700e441900d00204911611001600300000244a4209a90894052103060b1900012200c82070020f540e560040c4280404100800071080b0681c8014150341c14030601e5070001d4002100020401410396042124070700c1844801c01408401c180c2c021006603201704103060050303c4006020028581c040035600080740c50032000e060000d90380c01520000c003140e03c1402c04115940c2d0300d00c802d0320707021605010140c2524455000a0140c2403070340240398002c00c014156010344041d0360016800002d6030700191440400031800784100150100818004010051a44412407401c410a069407141031a120104a5400c040c9001003811000c0c08c000790800078401d54590f038035001d0f088401c0e1408800071242240b05404a2024020342c821607070400d0004d0302a61a050402006503440c03000314640768110701c2120000404207400142c1403075203a2007692231200505048196540b400d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 832460350 1250 832459100 832459109
    0x18060309050f1501120c0b030a1b0e010c1707080301060c03090603050402060405060c011d1f02121b0d0504060f14250224040c0e0603030d0f0e070807050a 68
    0x14410340f840303044908401180c904440e451406024103c2d040e1902800700384183d070201f101102c001c001d00c0061481a000700321401d1381100c80084500051070308851031400c42c091140440e940c0d002c4400814140c2600b113056a80843c45146004810b5950130510750007640080e002031500c41001d030800d0360280303201005090500c1e09001070f0605030001001842248150380c0b007140f00040d01c0c050004290402ca01400c0840c000c1309519684541071038076080c04400017284010743e5200601124114802e50703c000004200940d0340d55190030b2003c0c81034000151003120b22030301744a40e4032940701a004462045100d800c3c0070489440c620700c04c2c801d43d0b021507409503110321000c0400090058410031042d0140c40c4500b0003807460707141c01059081c0740861300141c0031000d00f0003540300016071143c00507008502c240021016950b441000c0e818580081c0c03074895060b00104101d20f03030264030b80c0001004040c00c810000d410440f8030952850030500f81d12040d1280c02100e0700704a0340c0380c0b00c0c11100080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 832461600 1250 832460350 832460353
    0x7020d03270810020901201609020f090f0102070b0319141315110301030f030e060301080a02090613020d14090a150c110d0509100507150b0118060309050f 68
    0x560520000645403400c4941c078264882d404200700403180e228a401e16100d81f0081054801c2d02040c80c40030762108004030001039400e040540000f801d070054400c0b03e840c4042601880e0812846000300324100764207035916811440791610120b0041a00350040d4001e001c0240c281c1c20f140c01c14003680f0141e4160120f075040e65461802040301c2b5606e18089070100c998028005280031112128040050020740032010400754040004000c00080140c05d01c10035001c0c0e280c0b00c4034034580d02c00f001000d1000340100c0c046a0000c450060050408985454000c3c000a160010304900145490220b03005407000d030342e4040d10f410200c0060012004601c2d000f007019806000c08081c10b0b00e4901017100c540c0501c000056031409450101c078070a080f039a03000107914064034100308003004000d03c1600681c50b002d00c10703181d142e20341c40c0103405802220061941b107014030940c1c0382178001003401800b20403562414086811b0b490141c00c4a28103580000e4141510001031040d02420481c0c6811440485185603 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 832462850 1250 832461600 832461677
    0x1b0f150103111f05030615120621100b040e0a080f0a090b030c090a0834271b080403110a08040b0d06050f0a2102030a0605010e090109080d09030507020d03 68
    0x81580001c00700b0350040e01920840d1000c0300d000c0d4180d05010072b04c00c8020460150040820319002c1980000000410440f818002400c1c100c03196619008601001090581c0410440c2400e41d1110050400080d40e81010108947d4590041354103510441d100c850024000850510320f20701582c13001d02420415005240740300f9015810060380c0d503558800b1003601c0b900c0b80c10305074800c60b0103a5180a030403807429002c0078001c4100580c400e0b000c08041c0ba0a01c50508060750070110404118840c0800c00c1e580b100155203654a040e510901001c240b11028055005c21801080c1d1a00062001b0074541081c950784000207652070301101d01d5a0041803045100ca41c21600c107035581d6146105480ca4010070a4100400c008814010078500800a40500032003904009000311540032a04039000312140c21406d540700741c0304d5801c94003400401811007509000c080c04150255224900840c82402d103c0d10b4181241c0001da041502e25101310000b4000540020a0341c0c800c000300700b20003a1101d0390140c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 832464100 1250 832462850 832462867
    0x80a050903030a111608040e160e0103020c240a06050d0c050919050103080306090106020c1f021009051c18091a04021b0f150103111f05030615 63
    0x2140e01c00039222151194540c80c1010b22000040c045a00c3d031180c01108600030345c85407600c91a0358000388100c504407401003002a44180d10501103020900c49562580403072002c0a00560094015076518200c1d0320494412802aa8040b41056141c90f07040001c0341444c5040310b15442502e201e0342210b03004030010394031100051700c10380d07085040e01e0741150380e01000d64170030910040900c040c20140807080c0c02c0c41c00001c28405404001c40c06030310150b56a820036030300c0d90001c1e1381d50b134901c1102c2c1307402c504125001c091130090075203584103a0406205481405091401a60556180c3d42c0c0c1a6140c5c2c0041954030020070b6160420756109e06542040880901d64220101c446140c0d485a4107142d51aa1180c21340038601d00c50044055100a0003192a4501c0740749045429a44401d198614491a00700080e03014000030b81d101d10100c0d58140341111b0f82103a42e045540d00800414942109000c1101710161018524102c0b10610982d5110307280d24000c0200078000856506003922031100300503001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 832465350 1250 832464100 832464103
    0x1020c0a150b0d0b0405120706060603060603060b07060b0301021b1c02160e15150a080f160c1b240503010f33021506060306060304020d0302010204080715080a0509 72
    0x10840f81e00f0100780c120700ea07a181007590410050480e00314086100254160803c50702e58042d20581d4041d603020003d140d00d402041d01110303080d0280c4130246a05014441c00907203030744c104202a80d8050005401d0840c90020b0080081000c001904d0340d0300050006107031b03100120401541c140c140e100400090865150304100e00360f0a000382d00440c4010320000720500c006150032165144080d01e210724280c40d01c90090201d81068100b440012038103808142d55428181c5628022500c283c0800e408a650400641d01038001c02000c5507400b1500c3c0080c4a01003000d84071000800882c41c050924103000c80d52154050040c0e550074040c0030b41070005001054480e42c1c10300030b49440e1019044e403c07452928440c0354110507840600c040d2601e03a0340750035103640864501681c00a00082c0f8a05449400030405903000c111407054001905000090140c9007842c06001818080e000062031305441d105510704180540e041027191600000d03030341d0403e42e406080319510003c019010800d5003440320380103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 832466600 1250 832465350 832465369
    0x90a050103021008090106150f0806101b060908040f15080f0115020309030610080f0a02181806010305011a040b010801061808010e0601091515080a090501020c0a150b 73
    0xe0f0100089100084c495038401d601c204041c00344c040340a20681d02c2031100420f600d6400b001003002403100e501054880c100401d20b02c0e4414140d4aa55840030440c1c244001880410401911480e4031031088801060082004101074050105440d08540c282ba00030b1505180c0b8a200c0000c01881504100042410000481c1035403054880b038459903c002100700d18500444680d59818000c94060003000f503032207115441100c2c001015a000000c401000ca03031590003400010390041e0f0b1812002280f080d5482041d83c5c0100d07040c122400e08180002d101d03140035001d0304100c070b45a64900c945c0c2c2000c41c400880c0030780c0b0101141c0034440362441100091140c9011300c594003c2c007440c0034180045682c00c805003009041d07584005c00c10fa030651484140c0e41e03003081c49038282e103030300d04001102a1900e80d14404107490200302c0220b142c001140c800c48800178000e0054a1250b900d103050300000350280001c010305c8c08c40000404404a090500c01840305041c2c811600c5189040c001148940b1082c0d00e9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 832467850 1250 832466600 832466629
    0x1080d0c020d0602040b0c010507111212090304032f0409080909061314040c06170c0c0102040e090a0209010f060905010e0414040312052a160b15090a05010302 70
    0x240003150740c0920f4010302a000f0b54011015006000c030708101c0240e0150f120034407804a41e5607840117844802d0400703440c0d0346c400d5221f0b05107110811070885510311070748100390040340c3c0700c0460b80703855606d4907401002640742c150210164820720003090320007843c0c2d140c00e1421741e00320703420407003d0b265547e451201d01c0b400c01c01e903001d090f2031b038002141c1c1d03a509040a0360392554008140618410011905044901164100c8401e14080c40c0031444610502070321240c03140c6009503102c85e03150038142d100260044442003d4540d000c02002c2084400040140c0c01010130800814039802144100319000c0c2c0d0582054503070901e4424204021580203c01030304854007170811707150421492000c103024101e0480f4401d0820001001c0c80201a40030b5417100500f407040c1402c0166440300c46854928030001028039800d442c0550343c92190903d40f40c000e101403500201458111710702642e5601c82c3c4442111b241601c2644000c4901e2641400c40601d03a000800040c1082158103607400a07400d0a59900c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 832469100 1250 832467850 832467859
    0x70e010c060609020f250b012303160e1623041d06120a031e182304050907091d06011221120218150403030801080d0c02 53
    0x10800c0c24040700d6032000707026060403d4190759808220f4400c400300e03400045035115001c503007004043c100c000ca180f42a060743c0c1c000721520301646082e51a81041f41c150741d03001c0000151205156496034104115a003410b41512550715181c80d0984003040000000e0683c1c2c0d05000121042d00c034240d110b011301c90302840c0500304502941d01c0994518403401503030011241a4181380d16003c042c006d0950480c801c1300100d4022261004054005441d0642c08800074040359001c40a070484248004600300384a0b402c2c90280c1c0c3c2412020040611090f00e64001900f1500000c0e8481c081c801139561400040c10035a01800a410000d580035039a40881c800e20150564442c4490804c20080002d61030408000048500310b50b1103c0e0a0058619a024111284841210904e440e0703540c1034502c1000600e42c0e11f42c0316076840740440a0000e94848480a1807044130001900d040d6a1540440341d40f00325598255a150740c218900a40045c01c103800c04111070f1302405807115a10303800519990f1141d410345 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 832470350 1250 832469100 832469117
    0x72714060102120307030908070b010e070507050d08060d0b13110102030a14090402070f110112060b1c0e010606020303010e250c03020c060d0203100b09060d0b24030108010c08070e01 80
    0x12045006111f1094010440040024003000b88115460018166021007904401c5521040025103981c89603010041c41500607120408040b4000e510080e0300640c0a010600201c846036171711200e4a504983c107414292944002d241403010707140e0114030119081c00210b20708840c200000d40900d20040415888500c000341c04140c0c0d481d6501581d8070b042c0c1c01016900d00700b50303074030700682c000030100c202d140040c10044a40c40012250b0045c1c0c4211185070001c0c5151180d40c4801e55580000000c0c0401099100c500d0010120b009110310301c0201001d60145450354145402d1034451039001d8a0000c0d1581c0140c56104401e1101c0c0b9648600846814a03501001146ca0300380e05042c1070f0486250b100c403000c9080c0c1150410b0f5001148a8951362b41041d40c0c4940740c0c00d0b0b10074140200100650080003c0c810784142003000d40c4810030905e801400c849400108055a5280071030f070000412103001c0210040041c9002406200381000c41030400611a01e020b020061482c038100c4800c80c10440071a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 832471600 1250 832470350 832470361
    0x5010b03033f040b0906090c0607120c29060607030e0d0f151a01020a0302100e030910031b02120a0324030c050310051b0a020727140601021203 63
    0x2c007011821036141001c09a852400f030800054582048594285601a44000a40650b4081100d885820008041c01d042c0f420a4540c480ca20540a05480a200303d50043d8400300d94009004503010414031000f0040203213030084c072690402d02070803184c02031609211a00000342c200841081c46441a55211000411418000d072406441d21010703201d030140ca000c5040e042c3e1107402040d1290100604141010000001240d0b0b41c0f454a1007d4010703002400180404601a04103098820a40301103074204054440064180c0d1030081100c0f01180e9201107060b1030b41e030001542070150b43ca40c0094000159850100c2c59103205e4103206008060b1f50700800110502c0c40c401075130b801100f4010b014419a00c81c40c0040b610306090003030f41d109100312040003800c0d024a000f050700c05c4034054440701c01c42071f903210210440d0300302004070341c01d6004294001c206074110640040600f80000c070b175520000d180d661000e003102c56200960a000004504001da0b0341d0700000c030204a05500700070241e4a039100e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 832472850 1250 832471600 832471687
    0x103080a050721080106050711010e0a030203030f03041119030807021309050f011109011e170403080604060b030915100b040605120903130b0c01200705010b0303 71
    0x244000107000c0469521442c1c50410003e003c034003190040d0710b86103a1a601d80704155100d000e03a032030080004248803811030295100e0300e01e0707080410010b84004501612a8006800c6030000038200450400120130441031044088907440300d148140c510721000c0094005400b00c4024900010b40501800180071085460311391181550807014142040510b0b01450f025443d01404400342c4601d41c03c00000d0f00b41c0c040600201d400c40107050f140d40340318180c3c0da40e50719800046212f90005226005070109140103d90f14030311b01c9103100350744c2e180c11803500c18100b000b1a00710b2380081541082c00e0042006802c0006881065816601203000040d584c05d0f103601d203640c015400c81000400080f40000b240d40d005006080524900c09034401203a985800031580d81c0240d440740034011071a10010411050020300900c00c2e070064100200e50308404a1251351410700c903d00c1c2c142d031b10000103000340c280710084c810f412400804074040e51414807a21010f0110b0000c807940800144820112401d91a05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 832474100 1250 832472850 832472857
    0x601120f1707170307020705010834031a1c0f2108090a030c1704050312070515400f020108010b040506070b060d0614070f0c02090103080a05 62
    0x501003060700800400d00112502500084022600e50201625503000241d01c1c2c81503901c582c42d2540140b012615043c01183c2c1030740e0141c108449542c120f00556646c1124030440e0107801e1801040c4681e0303000104d0300408035240490707500c003103a186c910000c01c0c9a07140c00d036103440c0850001002001c80c2060601c50030500d034008000782407020121800c2c003004060010070740003040a469000d19543d036544d4940d01c840c004440200040e13840a404000180c218031241c00e28008101018101074841e80401e1030924100418030000030080340140800c10204100300d01e81b9015064501107080c034415400c0d21198840c444043d81c1d80049440f2200380c1750348401d0340c08502d4103500caa00071123141060700991403905c20030b900003051003001213004108282110704403400540500d190283d80d03250310072804005410594000006400c0d42c1c08100b85015068106480c15007003410380c10074080240110009407684005d00a540d41040003682d10498118112604190300750740e11105030301c08450301d10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 832475350 1250 832474100 832474103
    0x10609060f1d040e0c010e0603011a160f111314010501111002070602090a0501080705030c0a110a0606080c030a08314110050d1a031c020601120f 64
    0x246401300203060752200241881d40c00c034003078031000041d90703000050203542c1c802405800c40010100030a00614035400c001800c04514107100721111880940e180b800b03074450f0344000c0e00c1c165040031401c000391421b4125055912194017082100e029800c2c40c0c0d44540b41c0510407241030102c80070110b269a40e06220b18954000ba0140442d40c42c1038a180c150000d4000c0034420740604100301c00411319500608406015111544449041d965080c0d50003110f0740c080010242000501d03440e89080307080070050103495900c5024041505400d040219207005000c0700042e21980c883c4a058001c5580314089804d8444180c4418004008480000d9420050f261220b078000000301800294441c9240401c1d083e0f40c0394404151100390107004440d00c0e0424120700d00c200d04002941502e1601e0314200c400000130300360620505041d0034510110450b143c003500c0703a80d51200c034100d09507949003c0c070581c0c0101440d40c040c40581d1001ba03000a50301d074414080c0d100381003811851402885808010b00729542d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 832476600 1250 832475350 832475359
    0x6040209060109091e06050a030807060e030702120d020c030c01050a030e01022b0605043305040f060303030e07080a0b09010b030703210e06190c150b09010609060f1d 73
    0x50f10800541112046100317240b0b82481e221020840b450300109103000c60341c02415071403d04000c0c0c1c4a080c004c006142030707041b0030301c030400c00e00d00180c030703640018149035003144054480c080c00403c000e414080382d4118144285c02c5400d02460503a040801d41d405240280790020395014134200003030091082000d098041210003140e42c480d89010365034000c0b40d072481142400681c3c0d950b01403000b41c9200c07210320100b8a00103c00410208050b15441c401005005890107900f591400410708542c01d110f829901c0395282c4c1e10a2040c541c041c0504a0f33040601c40080a00b83d140c450455111100401c000f002d02e500722000c00c2903802d0940040c503501c1402010384002c40da5a01e4518007441c1002400e607441d0300304048401102c2c1c001c0095081c00c81c0060100352034060505424540d0700c0640602c9801d11582c0b0f60300002055210008a804c0c811450b400126650303034004000303960794164020401c001030100d050084c40d600008001e45495682400b040101410300c1d4030301c1d484114a1040c0d0003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 832477850 1250 832476600 832476611
    0x121308010e060402120c0d080a051614160b031303021e01050115030209011d1c050c3109030909050f06040f020702060f0708040503030f0a120e0604020906010909 71
    0x90701c041505800380e4400c4031011000041e18500035100e40c801c0320b0466116078030100d18004100200000c105000369440c0043c9401103c0c0a807071311003403098106581e11041c0c0c603d81c0c041c40504000403a25800542000400c1500c2d00310040a00d100080410510060030080f480c200741c02004000f00c0000c40301002c201d2283c0d80fa51040c001c200911801c1c0002c10390381124101c9034080d20072554004010380d00c031f0b00407503600c080210012060000d41504030210100ca4803100710310450200d840e6100f02c01518010904104100240e0304601d4402c481124030180d4824086248610252081e428078001c500903034207050a44900e80309520601d0303050f08010030024140d03100321000c1d216800c2243c3c2007088440031001203007240540f0800a400200420a80a010400d1006000d404d48144e80d5203240c0754032140801e0554018036280301400d040070950000c01d40d0031078180211001101c0f8204241142000d1a07a80c0341c0c009800a4000d6030402c2c007180300c03030f44943e414202515403200107100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 832479100 1250 832477850 832477871
    0x705070f120302010b0406080c010807180b09090906060d0b13122c0d03030b040605040617101a040504020d02101d060705060c0c10050c0405130e12130801 68
    0x40c10101841c04a005501c0c200391081140740034815081542d507210b008002500700c1000545070401c0142c000c005005420308014022a6500820740250144071680d5848d08646c1e81404014140649900350301d40184041020644035013920001c0c494100200c40a240c4526600e80c10001c061400a0700c3c0d04c000501120590390012510721501811030f2125402c003a0802e01d100c0844e60342500668490141807071807010920980001544840092002610658030000901190125030004103181c0164a00c1e0190600074401e0401110041b01c0c00d00c85160791803501002e0601c1d0b4900e0074810741c0e80d04003160035512020481c01446a01400038280c0b1030f8480000b410305443c1d10b44980c1c0780344032107841a402e81801d40640e68115802002050701d601d800044075525041030090341e00620501c0480c4081042071702540740500e00040d0341d2035a4074141300c02d00c01d810f000c000d000801c42d4100407494a410000141081360441c0c07810684d80c44a400071200e50150040d40d00864047d82811240603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 832480350 1250 832479100 832479119
    0x60b0f1c1805060906090c0f041806060608010b030402011b0303140a02041802160b0612100209090a02070c06080606040302030f010b03010c0906090303050a0c05160510020f030f0705070f 82
    0x140c90501980840d0300b1a900c1c1c0d080103039110340448071940c0c3c40d00b207c142101282000d1404800c1200c0090010a0301007404c0c91343c40007151038403c1030b02c00a85981041001a400140c21380c00f5081c2e00d0f20403441d5117032507000600300c010002c810f010304079407143e43c400034184240d0040c290302c0300d01d40c2006801d0500c0d80a00740650014000e140c40d881c400841044407002c032b8801c032076a611501c0c5101289009988500030b4400d0024280341e0012085c0c44460004002170101c8013144035080c8c0010380340e080001c24049401c000400300701940d841004007101145201384148200e454500e0072180c10750303d07040030807014021a4802905072165410303880c2e1035807040d0040f4640e450284c000b00701d1814207c030203c3d000d4006204250103c4d2268400f840800c0c8104001e04495015003020143c00050382d8030f03207107042c048008520035101105000d00040c40c0007450410b00381103510050501d00072108240d40c482c401c0c4103107080041c3d00012004200a02440302c040107050141014000c075554031100d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 832481600 1250 832480350 832480391
    0x504150806101206020a1e0903030207050111060a0507020f0f03030108102904090b09060f07090b0f031909050312010b120103060207021912020112060b0f1c 69
    0x402190280303100240e07807040140c0480e0100c0310144402d070143c55007a00c6800003036019603400400c00c030452484504440041101c40c0d0000c16070b40d10f80074194a141002414214190062030401100c800904d11810b0300080352a00052490b1000a1540320040183c1c03401d00c58025400b100e008544003412800004000345040703035101800c0e03803101c00c51881c511040781c0100c0300b5003005003450b006949105400320303100321401c500070b48001000b11494a0b150380701c0e0001c86503520b5680c000410040b01607030000b12107801c070301142010038101d07050000390780c024058018000000080880041d1a0052128a0098000400380200f0200a00c0d040c10b135140c1d03012000003251505e407030000049000e0346004076107000a820a22405d503909559030000a580502001d0740d001001d1001c4c1541c41c1040400c840c020303d04015010740e1040248000350a90903440d04e800211858004100a0309126001301e40c20b10594a000603619000c03d85071210007c01000c01091051902c05041200010401c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 832482850 1250 832481600 832481609
    0xf01121d0d0f110f0d050f040b0301030f05010c0816030b061225110a02010305070c0c06020102030613050f0c0921010902150703020705040b030f010f1a030d091e050415 74
    0x30f00030f0428003103403030603582c100d500c1045130030303074000368942c85424440c0c1c1c0a0000221048104c030f16256070b40d108051103402c02c7e001541d10709800700349102000001d1007510f102c807009042c00c41c00340c03804031a1a0721210203800204141502c076000d003503040e520354088034001c8289408000460505182e0109142ca18054203403020580f01500501140030342c00e0b5036612280354000b4140454668011409083d0140c82c4c8000e01010401311000107842d807410201811003076000507140d103010401c00c10f10f4901034880c0610f41d440c3c8001d00118100703000b042c5030b0100c194080b40e40d44e42c0411300460b81641542d008600b508002c9440c19403244410340250b05418001c42e110304807103100000c100d4061051580043c0544d001a0080041c1d0900f81c00018400c030005050f1443c1c1165004010300350b400301c42441119503507448203030b1200401a1352840e201d41d01940200928003100e20080c003106480d02500c00450903002c545010b062151120b80090702010700203008039201042c10b4940344840d03025 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 832484100 1250 832482850 832482857
    0x1b0f0a02030c1504090c030e010207050619060302030a020d020d020a23120d0f030617030310080607170402040b12060f0f090706030b04090602040b04140f01121d0d0f 73
    0x10300c40803915001c8004241c20240701c401d6413030240f07130103400c02c01015045501414951500b240b20700d1020284042c00040d03000d40302610345407802904c0b52500d54480862003a4403483c1010510150300d0000b2010003143e4141ca5072040e903642400005c3c1107010f0088003d521148032440400c80900369420601c44504880b8075004070944403040000340d010360f000da2412030b407100d2480c42c59a4451030034907140d18594280000c2242d02d420803904640007a04002200d503000000b0300070f04040135641c80300240f06600180c4090f00300604010b028024030a40181d4442c0c400c408a02559903541c0004281840103014051080300041c0d0380391264821034020078290041000207060100d4005200d1040007005d003c9c200b00c80c280502030f4000d19a0f601c070700380c05c01d566445042c0064071034030051014010440c030150f10f0f0740c43c025449181d5090825500c2c0a0492030260142c580d0304020041ca0034442e83e074010403a03014610101540500e440300c1100603100c0c00282c0f40609412070b000b03a094948568 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 832485350 1250 832484100 832484113
    0x1c15031101020c0607030e15130609050d020d0318080706080411092203050d0c21090b04020105160c1502072c100905040809010306050906010903081b0f0a0203 70
    0x3401a40c503124071458042c1c21100420405000034840c002a0b01c482c3d000078a40d0442c5507a216240380d241c0c111080c00382400c18880c45c24031038250410100c000030441120b00c6121a0900c2d07010442e2280c407010f0050038080c40315051400310181c0512100946520012160303919600c80d40100400c2d019141555582d000c0c6070318407440d040c030050407441410001d850b030070003501d841c40e15100c2105225096003040420702c00e4074031540d0280260b005d075940c680c0e079541c803000c0c009131760035040c2485902c0d0700f000c00d01d01708040000540103d1840c0e4080d8090800c661100c40d00d0b51500120a0400c6008000e1008040d000c90303101034668105003070250070f03801c40d9409911110f1040500c7d080b150a20702c81e07100901d480190360701d101001c9910010308072a410845035200745140c00d0300c0c019581140d0402021844035043e584c54401c0000030300089507002d403036081400020388541d41c02e0001801c180d100042c002101c01510428440301c5d60150101c1d44d00f02000b84916440c1c4458240c100e10900502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 832486600 1250 832485350 832485383
    0xb0a1110060e0604200a180824040b0c0913090c03030810060c02130b0a0602150c04060c03030c020102090a030c05030609060610030504020103060b0a0309051c02070b1c1503 76
    0x5d00c81c1c402c02031030882c020004d514100d04184281d80001c0070030300030400f80565103c42c840c0940316441c0100342c00c40091404c408101c44840d002202c003105201c025441c0c004100100d00204107150304024480062640c444801300822f1018243d01060110141044428003c009002d00b240302120300aa036040c5503a101d411110710034008a10420001501d0b8185840140c50560068071580301904070003d40c01c1c1030203021805684155002d100940c00c10b134a025100c10001950551101e480c8441924090401201420144034410f0260816684007071407103440c1d00035811565045001418030b003401d0b540340340407400d400d81c0d070041900a001d60800b140c00014005513079400740e28020411051082e05c0c0350100d00030000100300ba41015110301d00021150840c4006092401341c0d541e01144d02c1e0300600341149030041c5910400c1c40c01040c14505100d50764045020740549422401455807030350703c080e41c1c2503150340854171050001d203480c0c4000d0091000d01301000460348610808036921082c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 832487850 1250 832486600 832486609
    0xe0601090807140f0f0904080a110304150c060e06010b090102070b090105090d0609080d05040b100506090d17030a14070804030504051c050d180b0c03040b0a1110060e06 74
    0x40740f040f15541415003100041503e89041805641c02000d01419074920100d4006034618109881c00d4600304400034901d030041c0d5200c50a01201d00790f0740015460076103803d030341e04841055100000e0802840300d02c41c0080000d0f03600081d84403500001202e260b943c5610340f03080356910451030030340944a0750000040d8072000708141e9004800507110305003801c48840a02400c881d40c42c004035000c48d600c04a8030001a0400080c2c40c0c0714684100009080c68945400f4041c1280541250004441000100826540c54045494180c0c00341d03805500e6070521300d8141071606060343c0d0f200040700084100905101c070359201c48480c121101040d60283c581c144242c40540341039801800060041200f4030450601d41011412050740e00719050322151540c44890a1410319200d00c000500c1d60000b04007400e40c85644800944128881e180c03034083e40340000c540c1c0b48a20f105480c0240300c045a04594603001e07884504900e24440c0c01d480284103450f1504009041c036000780b00184000c80e0206119080 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 832489100 1250 832487850 832487863
    0x90510150608040b0105040e070e040b0402010e030f060c0906070606030b060411040e07051e030406050f071b110d05100623060a120609090506090d1403010e060a09060e06010908 78
    0x4000130700c00e8003a420441404080c02c880340e03c41905d03106e40100068401480350505200d14041c140203205810203100050800340403500c060710a90104e55065256600030405540107d020313082c0c41ea44645001c0030495a0190343c1015100301d01d4070b00c0c0041800450400d0501c501d10495080184042102c0c4400c224081ca00a81600d80b40700000a4103841c055001409144441c0704403a0682c400181c0000d025481141c048035169160810b0202004030b070030200350001c03171605100c0a0780e0103054411880c5030a000f400f601403004040c2c07000040c0c4695542080d4660080199040d101160f05100080d1035144034103141c02901e1141090840481280c0350342d901c0004229614003000355404030382d1008486120520940e8461000601065034850948854452405002c00b890140b11031410034501241000500c9084400e6200c06614070045074191340044010403a10703100c0d071001ca521440c550b0445112a0310b03048002c1084000c0301c0180340305203c00d030f075030b03003d0170b40c0301c0805903100e52 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 832490350 1250 832489100 832489103
    0x5130b040f2702031509010e010e0706140304061409060405100506060901030c020f0d0f030b0904170c0312070c110f090114030f011b090b040e07110109051015060804 73
    0x142a1520800303000c02c02d14241c4016000a0844000303c1c880c08041c0c00c00d440648181c0081e030356600307254540317020a004400810408602034410301c1d1400c08058a42205482130101c1950f0000000b800c020580c2c0c404904121060341202d44c0340340510b0080d0b59000c00f518290f410b0321451440e16000105800b601d41b2414010b00314601b07140544005401601e03e502c184010340c02944c80140c01c1031000c1021200031109075072200004400078101804642c0103081c164001c2c1800b50400c0b01140301a0809007022031803050203503403910440303100c0d4294012041e481c03410900e00c41c2441540b030751000c800100c40307004840c621901440c81041085400c46031485039044603402c4010013420004810915400c41c015040d1040203540b540403600b115200900705034045000341e41340391140e901c240000003900714419003500d41404e110303080d2815100201408100400e411048a2002e403e421102c0c06517400011189460b601d0309090010746034500030f49104041d000c1c0c002038000c0c072840260b8040d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 832491600 1250 832490350 832490381
    0x9030301061425030e030a11130b0d29040305041d06101d0307080f0706090b0711060720040b030102090108040204150305060a051b070b060d020a05130b040f 69
    0x4081d0007a242c281503c10510603403d0090080761101c054806120303050100e0b1084c0200c0302c5c5810000204013405103c02c40c000006807515003500ca00ba16032181980f042d1f90008207a188900f034550581d001d000f944402300b0030310078132441031001f05604440500180c515000b4400700000046001d07614914040b529150300c0300d90814016105402141032090108035035034000020032626011a02d40000d65000f400c565000c0700400180781c05c02c2c40b00e070018191510781b8140c203901d02402880741d0b0050340f0024103168060034000020f650340d2070444100c2a40704089004000d40038064106188040501e180650706000d031030a480e140600c01c450b80384c10140c407001160785458080c0070042c40c0c809401c245050046c0004000700d201040701e103204180d40e07400803d1a10300503a07007005400105042c03001005051100c400001c0404031900e900c89400d40c7c00041001c0c0d0783c00051050810355200700d4000f890714038003480c9103145800c40e6036050000e45040c440c0401c0105904122a50003040c200d04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 832492850 1250 832491600 832491637
    0x2f1b1c0305070b100b18040605010318080a1b03031d060105150c0a020910141503191b0e0306010e06030a12141308101a04021e03090303010614 63
    0x1c1c61400f0b01036046009015102c0314103449039075410700d44d40441c0c040700084408440d040044d180502a40c00900002e02e401d100040c0010600c0080158881c002409814040307003040a09200764a40225161a1036011001a1030f90030094014110000e81c000c40190800c0e21800845001070464102c81c0085d081d040344d0300507441b4860150704010818050b074012010040c0260361800c0c01d95003c1c054404103655103038a0100d000c400c0c56200c419241c0600e000200161100c400003054030761100080c04c0e407003040c1241c003000000400390b210300041200d424401980c05c259005403c85010641a41110050390301d5002410010304105c0700d03150300d54014120100000d000e01e8400712040324609141c007200d18141211409500b024030b00c032284540e01c0d030707040044440c100300d03801c01801400410001c4102c00e440c0313440c15001d5a18043d000707035000140700ba500e40f909030303030a80e600f42071102d650f850f81410344441da01c030781c402e00c9a140000c03288102884c1000404c4c0807240c1c84603494010818 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 832494100 1250 832492850 832492853
    0xe0103051c0f0e0102071a03010815060d02061b100e1005010b0a030207020a0b040e040b010b0a0f031e0207060b150c1b0a0509041101030c0f2f1b1c030507 68
    0x2c0c003c526445032030450050241c0003440843d00c4c100c0140030a1148941350316903040c08013992400380c020328281445200340e030134003200e0340b174030320144843c660140c581d2507840307078005207802500341007408045092190081508000c51250700c04070100007030b6026038603c0102082c442048c5d0b50300380901c000c401c108010700000f05000c0e0b0b0040c8080761010b406401020b54513031010149030040d5004a10701500201044204140c0200c0135016001804410381812080040100301d030821a000354285692951210101c07104142d8000030810407140c01d6644001e10301d021030180003020842d0b8040c0c800c0020724920a40c0d0541511021045074004041c401c40501c52418508440360040d600700341078060208094441c0940320784a18001c3c5d400603000301c2c00d1000141210241c28a03402005900d0209100080c2c1c1322210607401c010b4a011003031800804550302c11103c0f050030400c40e45104440d20803007082c403c21040805403c0403210141c588444208580d40000886402000034030104010030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 832495350 1250 832494100 832494107
    0x1e0b0a05010621020d0605030609030913092310090609020a080d1e03022106180912180307120b090105010b0a050c0c1203180f03060414030d060e0103051c0f 69
    0x1200e24945e202c007241d4655190b0200381402c4d13003610020308030307040029405941c9c1068042e41c0e1405030004410841301540380c2310792111141d500d0500d041e00d800b2540c038030148102005035030540610640c0400440825140c14002800711071f00403070190b011658002146007002c20301400c0f00c2c146484071405030220078503010f0000010b4584c4424154240220344407450561340c00d140c403a00f140841c1500d0704165040008007906c080c00310020000c5038082000700c0d2004030b290303003004c844810720301e032912422661102d03407030700d800056034041c8603136440060041440289010103d014402540b0340f91954404a801c1e10424010704207595000c1003242e0480c0e12410041581103017003025114074240c2e030750005064600c180c0da58040342d400450743c00604410b203010360322440303c110703040c64070000301d60b01094890400820141030240550703500d400d41d50060086480b80d41d0b0900341041081d0719102000001d0b0307801e01054405124140500c5102c80345018072948184860f1680360200622003004c0303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 832496600 1250 832495350 832495357
    0xf040f150f08210c1f02041806050114070804031401062c13080c010603150c030e0c0411040e0c040303110a03021c091806031101091404091e0b0a0501062102 69
    0xb1680d8883c013003e17049501581454944500c1469401503500d0f40341c9034248000700c21424103044031034a030100800c09030f070304041c050100718400d030300582d15a402824118840c1c0200c2d440540541d180a4903e80c400074107601c250150f41032100414034101e4003042d15074144650900c4202100c2c03c0c1c10115144100790380c141c0203610310501820746092500031111382901c00c1a8401c0f03803a5940d9203014240c4c0c008600443c00c1e42c02e413a260820440140c50442c0b0359841c84511140d00550b5114100600b00e200c44040303902502510205c0034450500d00780c100001d50091009600041c40c42242400c41c81010580000e07841d0154002c0900c80d6206144940004041429005000322614002036003400044a070113101008000000c2051441c10712089510350004240d040044840c400e010a0280c41c1094228280036030340003c80b40380700d107418101008004112004800f01000c00c104000c1c030034041c5032194072a13400500c9181d0740e030320081d9400072a00030700c0c1d035581c0b40740c0a0121140344c640c0c0c0038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 832497850 1250 832496600 832496617
    0x909010b07030c0818040c09032112150308070c030c0605040518071206121a100e04030905060705010917090604050108100f0303120c050906090f040f150f0821 70
    0x102429200d200c0000ba0884403440152400308004401c09c209001c41d404101d4006060043c14821200c10400018000084000392403041c80e61340b41415542e10235001140080c650001c413055661002d030030880c208040d248811100226202c00c0132951500c9a01510708882e0090001e00345502c40142180020000500c01000c022134006560030200050183d440140b41c03000e10f0a2010001d42804980c0b08034502e0103100c4022410306005002c466100880110307106049096803580f10351500f216940516403110b42c1c890720100b59032050010640c401340c0c0c0184504420085050746601881150148008646e0311031402e0004105550180f403240c3d90005140e803030406020307180d0660ba0709207241703a042078000804014144040c90300074411029180c09904213181840c8103000050600d00c90100740e03501591030224030681c20341b1550000f00f252160301000703001160240035412203283e202d203d031000f4042e165000040e481804241d500c02c0303103045468a92500f0105c4e607911650b40c0150b45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 832499100 1250 832497850 832497877
    0x1030f05250315270209062e0507060203010f062007050d060b0a15120203010806131b09020c1603021513030b040f1a091e011409030909010b07030c08 66
    0x3c2102c400c00400c14040410301e2100340351080702550b0300620a02d43d20041509004001c64808d07803511b000f54400140d00920740e1045080d0341111008100d0741c90040b804005c00b070360f00110021a41c4480c100d041001d4820300d56a50b8000e4802481c070312940b54002d1003c59043e00070000a2003107040410005525a0060401044141400300402c1e41da107045d51040040341d070302c40c00789204643c1c007281e0f040000d030b0701c01c40a5042d5414600c0040e110303c8094447e808050081a00a00b0006044504400e25070b01c0c5114030342c00e6503035120820203075016006104e0980107140f216948805160001004d0340c0d009481c00c86059800444080d050707101c1261a507951010500c000000780c01080b000340300b01e108a0504000e81818500b19a00a022000a1301010003860030028122000507544200307900c040c40e03014651500000180c01000884d11502c642000481000070302c400c000010501101d043e00c440c4001c0c0c0e82c0b849461254010301e500100041c559403050008102c2c80030150a05e62442c05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 832500350 1250 832499100 832499111
    0xd080c0f0307080a02060f090613110402181c08040506130302031213090207030c0615081212100605030a020f13061116060e060c0703080301030f05250315 68
    0x4124500e9030700203400480b202100069440201340d814040d168120382c4082000700c0038203240c04860f4944100829241105c1114007040d07061000352448085002400340c0700719a695a404604607148070342c3c80c0003d000b00381c04406ca0402e1901c1c1c05048090581162289083c58288002c214030380d0f0008136211a42c080381070004c00135a03800e00c182048021141d0740c082d9110741c030b90351107900620544d102c14000c904c1070000001013030b00f12007843c40055100300002060300307070b284000c400c000e020b400c280d01d80d200d10710120403481800c20042c04050442011b00c00310355100e0600c403400342c0850050300c0000da07007400411580244c03900a04035a0702c03807003860b40c1000c00f14203d9080e044032a5020b000000c4101203d4401c1400500c4030040180483c9800c40000d81003080c0508590741103030300c0601441000801080c8101e040c8007140183d640b1141070f950b41d5a49041901c0c075000381e408240e6017030040f40c02101c0e0614000d02e40c4051440914403032401c151079620740082d00c0203030078040500c0c2e68907030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 832501600 1250 832500350 832500373
    0xb091905041407290a0503150409060501080304060e0301020c07121401140106030c08101202030a06020301030f031e02210c0a061e0b0d02090601050d09080d0c0e0d080c 74
    0x2c0c03104030042c1c540342d048035144c0d805144c495000b0141c41c8414911028041001601d995840030440b50f103c001c101801014005c01008280180181c4a000d030049161400108901101000a01c00c0760031560742c54100c04045000c06080348204400b07140c3d0f550101c18100b060707250312070410003464003c03100001d0700c600d141e505a080d81c03008124070340e0010058006002d02c0d505440303240ca03c903081d460b02002914211845200c240418055034100140b20815003007150780410629081c2c9274450025501c80d40d403450003801116520344101d000c141c0112100b25072000200c1114020000350340205102d000101042802041001c5082d00ca90010403040860108c03c00014000e00c1c4900383c0007408505500501a03298a00b000248000d410129820810b0b65016400c42e40b1580454940680c0c1d01c403200140d48510594890302801800d2084000c1404941c0700035100036601c1c29010b10001c80310b00c01c102d4811580024071130344450030801c564080744603c13000d4240421070314200d50107445076 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 832502850 1250 832501600 832501603
    0x20307080310032a06180f0e01030204060519030605040804030b16110706080c1831020301122018090d0207180513140607030b0919050414 61
    0x440c0c0780c048100001004200300604050400301070400034500c0c08510984c11002034262909100b010208600c3c5440b6180c1121600450002402c2c00703461040e00683c1c03000d0b02c1301500b901748001e910461511700001241d0401000f003103c00d00d0300310f4020081609540c0c40d04010803014200303441304030301404040000b0310400490343c000c60100b01550015107107820f0041061604034041909500a1182004541e03000403200d0740288080c00604c2c0c032010384624070070609001c20796017940200b2207120b5000c41c40d0460242d08a0600c0c002d00010b076046583d400c10181d03c000e101d020440501200417001142c1e580000700e80d50031f1201c100c0b00702e40b480c00f000210007110100c1c490b1403070300070714060041c0e0034810084210b1110540c0054030030140f81c5030241d03489001c2402c091102c2d43d105c5001407000408160010304403903005508000100e040c00c081039070307520226441404070745002148041854a40da03084d00c5500380c90714030242ea00c103a50583c00580006042214844500b101c0e0010443c070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 832504100 1250 832502850 832502857
    0x90405070e130e0c061c020a1e0c030e010813080301080c03061e07050711040606170708010e011205070503060702030a02062206020f16050d020c010314040b060102030708 75
    0xd855840081904075081006408803800d4091044a464100c4010380e1040220f02d0780d21150b01101c400740c0301c49101c1e06c0d49009003500790140c0c5800740700041024846400c041e01d4400c1c0d050004616158162258080d111180d0702900034000c00d0790131801810640c441d45407181e20103510302094030741c55040e40e200c41d03481d00281c102690b207411410044802e400c04011a682c03194154002c40c071981a00403032800816409016801001b00000d010010b000ca4010075450b140c0e8090010800690741e980700030550305c1c661100c04813018400011070b03001481248620b05031004107186000903481c041c1654002621000111440e0088441c00181590280010fa2103204a5000303560344501164000342000030003080076050ba4443e228000100315140b1910302c1c442c0d40983d0069172404000a01d204501801c505003180b8039005101a0420201065001041880b40c089460160301c400042d03041d80c0030a0003203200d02e0b4505c030015010800504035542c2041d4103005991402c56591606030740c43d031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 832505350 1250 832504100 832504111
    0x207110306192003040809010c0512190f0e01050c071e030c0828170a020f0c06071a040201170123040c02030d2004030303060f05060f0a0f0302090405 66
    0x205080710081603451680220184030f00c07a00303031019000d2241800b075203150101030b00c0038000305400f09203104580d0058000ca80d02a07040002c40d0086911202e40711080e5101c011070f8141c0d80b0848010380b4210340121a8100b07019101d80f02d5205542c0640011101c0707412080728240f581c41501e6002a0140c0107141402c55022002c016203080c6080d41040d9039015142d5102c4c00c201d40c4403d251204450910081c1c5c400500c0718505924110182c0c02c01262100008014203201140041d004e004240c001071081c1840d102141a40c001d0780e0b98500f00b051078024904042d10b03581c211985682d1005400c00c00990091050405a610009800c1080c524050036001542902445522081c280c0030220151221010844040c84020500f003002074490140e04503401e403080e110038569500010309550903609125488225480c0c40c2d4905005014090303c2c0b0800d04c00841c082d402140a04040f81112044104083d8851401c103006800b01c03100c0c03224003080e0082590070300c1000900c0c1d44501801d070162 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 832506600 1250 832505350 832505371
    0x50604260d051008030910050306130212060f150a14160f05070b07170a110609010209040608190b0901150e07030b1e0d0201051903090c170606040207110306 69
    0x9241154905040c49544e401c440702e60790091040300c4440d40d503c02610040070342882c140c1d40b2925130030040b90810b071406050f010740900125215403845c0b410300c100c5200700d81c112090070340340401406000944842d40131403042e100b001c100d00c12015010700b602454115907480700d40d00d0039641d4690f500035004001c6086580301004d000c20790502c40c0400000000e040355001017450310600d44e41c2c02d889600c154841d00d400140200d106031080b8010111422203080c1c50081c1c0c0c00e0b0b49040080e180c000d40c06031404900c181d291840100c0c180c14002041110340241d03080041034070000d174640c1035071a04010310400c429034071000d001c040c400050507504001e00c1c8010180710f103400c0c4150301030709517503800030414010918000348040c503942ca035101d1407003940291610540b1441030700048555100e1030540c11409a00d0750758001600d98140e01111090707004491445099071910004c10a20b621000c4c80400d591080d0040f401c14607107039005102491180c09402001040180441e060210441c1d9920f442c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 832507850 1250 832506600 832506611
    0xa0b0108070e0105390606030303012105120c0d020309100305180d0807030c0f0903020616061b020c091504110d0e070608011d01030b04030c0b0906010303030b04020304050604260d 79
    0x15660b07203072200c003865240000e04100c1c030300100823070303503c4c0014800c02c54228558001a0303440d0421b0480d240b082c84e0008141d50320406902c1030340030aa401042680410b1040a266601c02440401503503a240002815240080c4c4c62000c120701400025100d100d070b803c046110900d18580400c05c070f034007024450f25000051310700518040c080710b20700b0000340140084e0300180c8096503802a0107400343c5c0c2e4120760302a100c04041d13088072400d2002101c01410b080c1380c0a040d8078409410079407110402d08950807207048113138500078000c3e00b001c02c2d6001e0210030100381a80780c4d0307864642c00c9003c800c04640c04c85410840024441004e480d00b0389050080c0383c102c20f07000d001c600e92082403140500340d10041c81140e564100700c0d2035201c1c541440040c007004030341000b0404043c460031a42c14466040002c40b091814140455510381000703200440211b0710b040102125402c20b802924800c0d60820007819940e03541e82c40d61070304031a407a2885111221120b03074494000114130040e0962912401c4000703003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 832509100 1250 832507850 832507927
    0xa0510081b0a14060a030905100c020a0605060a0501050f2b020a0e0a0f0b09030a0515010f05011713022b02010215010b040513020d060303050904050a0b0108070e0105 73
    0x4180349070700030f1003070101580321103c840d0322140d003202d1149409180c001084800c50504605041020145c0d9550324207201a441081380d000030800e016070f01070582009680c41d4201084500d09840c81002e011507014000e00f811005100040e0480030348501920000031130b02540c8801070b141c40c1841c2070760142d021810005080c0e000c0004401d4410503941906000d00303204000d4824440b520844001c40d4000501848686041c0940c400e00c82e8840102c4540300c2c00309120545050b000d010303001440001c60303c0000c4540c4242d14501d0b00b121080c00140b2151600c1990341b001500011003070342c000101c4921240b40d0110308800784001000c2c5811180075180070710009060100c0a078100780d401200400510110082c03104036800c81e0411030724114104054100c01d000390048662404041e45003035000000d25400000a0104600c200c4003002140c0c4c030300140c80d0854911001840c00102900002100c2602030485d0b806115014102542032082911295198524070580c201000070301010160 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 832510350 1250 832509100 832509109
    0x7080c240f01030302060a090f0c03030f0822020906013c030b06040501030506030708010e1507030212040b0c12250203030103050606010804240e12040e0a0510081b 72
    0xd42200031100c0c4401c080d45140c900070350f1804041c22904440795683c5907031081000f005010201c00d5805000d1703207581596030401070440740410502501040204d80010b80910041d01100213043c60707c4030a0010300a19000d000002200030400c5040c40811580255492801c0c0481c6000c00050100c2e0410a114503d41000244012282005060400300000800c0d030342c8509907001e80c0d0007840d0010707007580d07050000307031801c049a4414102d0794a4441030b0300030340b0b50103c3d541440c0c003008210b1038415280d00034210104e00c20103600740e500c0845400468000740c1600c803180d80001c0d22200c02820030004942c00c0c80e19240c141d400076440303401d00205410003803208400100045842c009141198076548480f515400300600060410410364002001c2140d0a150f800000d600c05032554040c000c84202030000702144041c60101d071086c9a140803000d00250200c0382650350880244c0102d4071030110751800380030f0281180c1c030a0b000024000c42c200804101c3d040c00780041071a0702121a54000500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 832511600 1250 832510350 832510423
    0x23030f31020102010e03090616060615020f07052205180706080105150c0d14122a0a02100b030a140304031b030321060302150714071a07080c 62
    0xa02261b002071107001100d82c1d414064861020000041c0504801103140110003083d0942200d80955140f145016450380d00140d55172110082500712803120b9140d50410013030000185001003003092118002c0c0480230241c1180c0c2c0c020070443c845c0044c03000204c1182e030501c09030303400c04000602540010440f500e441601041040305444034185810100c8481640f100c0706480004d0620030040c1188000c4074800040311079501581c0013041603030510614841102e07a915005042c0d40c0d0031408000d840020200444115014a030000d105908489210034040e00b4141c4d601503060080206c1503001c00c0350485030844e150700b240080c566903401c515000c224040b028400a1106040d2001800065013001c030740348140c00720b80004032641d4500362400014101c65040203411211050442d00c7c48400702c80030307203211481045034204ad00155009503507282124860b400031840c41d54940b14104050b1401460b40b180290007130791804158070012480d000d040c0ca40a07407112401c01c0c07400302c290380caa00301b0b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 832512850 1250 832511600 832511621
    0x11010c050a1205070605061c172b1a130e0c030303010b030f07020106181d0709021e19180902040803070317060f090a27020123030f3102010201 63
    0x168800000d0401c0e111100010600009c1c0020280003104985603112400d6400c0042c0307985c2c003e01c1c002040d0001c00400542d400d0b11800071403c04544541010f9062030340c00c01490064400050298880c8010b070103000416007500031801512400a1b0948003400110302030b004e20b0304180d80c3e030b0804002400495800401c1c400c11640b500500380448540001051020800c0034000b00e4007120301c5200e2103a0f24620b400301c0003244503003000022181001c0e005230840c1d444a041d240020a0511100c44451241e803001c1c81190b811207c40c81d5809010705100340b070301c0c4141246c1e006859280d107904d80c1260f200e90041b54146e071003c120001055400500440281d9941740c81d1b20b402e00b01503022034841c1f40c5207400b00b84601300c45000a5a42610341d4440c0500b0b0f0607082259070000c015800903005e4030030f8040140c3c00034200345804000c1040203c0103280801e404008180381d03603150b280d5000103500140284031520f004140498000e501d05140c000054030084900c0c800004070310019003100c00700f110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 832514100 1250 832512850 832512859
    0x170a0912080a0e012c1309050703140c100201060515180925080f0906070503010b132d0e060a06181d012111010c050a120507060506 58
    0x3a103400a038141c0d040c1c84652545043c905040300e18031005030703480c69a20310107184582c03140302601480c001e2610114103182c0c0c20f6429484e1188205142803e595011502a00030760080030100001245010200341010350f030415102c03003440100014035602c4039990902e0042c0c1d16081d003803180b46032000402200a00150303040b4540999062074568a005007080c0b507115031500c50002d100205100d00c040c1e0b9440c0588519805040c0d00c0300017424010050762051500e07030900b0001414080c0004085001300c0785900c455003160310b46400c0c203810303902006030078211a002c181c0008807a0388101e02d01d03039048920060021041c2c840000c040c0c1c8030348a6400048241028030034004c01c1d8076200c921409807a518a08544072501808025a0010300b540c0720321510080062a058115050641c903410b07180509010b0352081c0c4160804914202d0b0354a0141901070342c0c4042d807010358052a01c0d0841284200d00f0f6800c0c0c00c10700e4659a00c0e007410405100b012600010308038003001810711540742c1c00b107400c84 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 832515350 1250 832514100 832514129
    0x9040b09060c210402030f060a151409010e040602070c1203110606010905100203070515061005040f09091406010b09101803030f051b0709180f06020904020403170a09 73
    0x6003d0504550081c40145600c0c2c0c2101150564034203005010308081e8190480360181400400b23030004040c0d040d00901d004444c0040403a00009111f401420007000030f082590690810702d50041d4414042c10445866508000c41c000040c8800e84290043c501e84981503500042c1d030901410b8441c81c8040c5826075041413040040710b03a0040001c10998506881440c1d50040c6140b0aa10307503c41c6d40c03000340c228481d40901d451f2500302104507034490f02083c4d07683c03030001d004584145e8550045000e03150002030000d8052114950717070340c05184058000d1300c85044480e011a01d990400c203003a001141c803424005900702d5942010612448003000b186401340e8005c4400c170003140c0764540c030300004040211814240307001c54810000c2e103017080e401c0c02d043d00e40c8402d104105507807481703641b1030802071038184203001c828041e2064041c3d400035080700744280b1180c0a0307030780c4a000b540700c04020380c0e00940c03e201c0803001c00e4209604580c421526000380f665100d28000180411003140c1c4010700010405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 832516600 1250 832515350 832515367
    0xd080a0203100b1b100b15030408030a0504031b0605070e0a083c060601031d0a0611040b070f0605010b040302010c0305070c180207121e08090c09040b09060c 69
    0x780105421502810f2000ea29000201c03c030070b04011850461584620a581c1d0f04442c00515503c00c1c50360400403240c010698210044011450000300c5d0f01400761541400014091411500596801031092800c408803200300ba10009030500244070a031a45550b0300700304404141c01101849000d0401c0f00c00d40307515881c2c000c1c026501c0c0c02d00107840c07607500d01c040070101e05809800700880b458050a1001440d21101c105165aa80300484440780020708100000099040c042219014000c0c2500174151000e0b10b5240c56010706a80790407503901803410400040c0a4071600080d081180c070610150488480700c2c204041905c0e0180c0013400c2e0500308000800043c4e0f0024070201c8000c1e81800c0c1603032500701c1403d21884012565000c04601d85d5054881035528115038014111580f05da1070785000012580405caa2504003840802c0c0c01440b2620500440350140240c2c65200d0340c441c0032511130702c90007008036030303580c0b010b0720b01b2110b200b200024450200028001550f0004605400a0a03c00030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 832517850 1250 832516600 832516621
    0xc060c210e040f0b0a0504020d0908040303020d120c080f070c060606030e1209061215042a02010e03030106030f110f0c1504020904020d0807051b04140907030803180109050d080a0203 80
    0x41c410f0074401e90380024049c901e02001d400c4104a20b81241001d6243e41d5603007400b0351580b09100ca03441c00590714401c45000060301d441040b12540e03003546c42e11959030314011501184000174041c0c00a2000820f803003800110107010f103001038a1181c2c0c0109401e10740d605264504026043d000b108046d09101806090301c881c015104820484030a10560740c541180354040c4000c0300c0039540e00b16080c03004e0b0146501084400d103604400c042c840c0200301e406240101d00302c0d144012002d00b02e4004000402109110f42c0002c040c035034445000041d44403000410b10b04c1ca03444515080128600850041190002409100b001c80d040b0010071690f450540d00240d00800b000340024400d90500084006200c0c50b04181c5902d242d02c0b000301c1d141d500c5c401c0c81c55113041d00c290144034460740c10a80c641c114080d4880209008000400c01000800c4c00c40e929101c550700000c008001d040054058100100c1e024021043e80b40c0c01030000d070280e00a00d00c3c00412081d0001c0c02c12004900400900c840e0342c09 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 832519100 1250 832517850 832517869
    0x20708100608150423070f1211150c0601031104060e0702060417040305160302040606170a0e0f120421030509040b0616050303010f060c0c060c210e040f0b 68
    0x407a83c00402440d82c07617150030036034000ca0403a07402c4203988055442c060340100086080030744480034802c0d003042d50b4559003456070080c0200000c0500803408160340305030510a4030240e0401d1000d60690400540c0a6201c0c58144242e0054030101d1130388152089508284c400e0101400480030b4850311744c607100d00040c0d079810300640300920b5000d0984030300791040203001c20355018503880380650340f04244a0b005e40a54008038001a88900e15021000640034090212480244d40c44505560740342d603015410300040240700a03015240c0a0a406843c00c1c103800c0c4002c000c102e45840f0780c0c5881d1401c0618454400304540600c503018040d429482020903008426101448422100803c3e62103010000c01c00d42d01941780340d2401d50304401c140e901005070100103141610717016050301d03940954504c0121100035858001a041040701d070000d0102c2d520400080d6280f40c029038100400080500090408100741260702000a1400c003600405240c0fa00406403840707080740c002d00840d22a117000804d22039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 832520350 1250 832519100 832519123
    0x30f1b060f1a0d08032a0c0106090606020a031112040e0a0b01020105060f0405250207090f020901050316020304030b0c0403120c20010201320703020415050c030903010c020708100608 80
    0x240c00b000040310b141c613800b00314804001901c1e40c6c62105080c406512203035040861403820550034141c000c10315540b24866541203800e642e006200001d99914140d8541d01c920b03502c107a603400307200c80ca020343e4201c480c0140024400a503106000340390101094040329040940941103904010078404a5910300d08020a41c040841f030001d504d844440c0200200182c407413901480c10400302c100c2045c4c540208046003160340c008824064104040c3c01d0100301d100d0030800d10f01152061010032840345c00010580c2090150780100c82c0b6203a103d4959580c40031084494401020001074244100080300c030146501500350705040d203d65001d590f030740040100103002814580d881d800488140d030301c00d4200026941045818402c085c00f04600700c0c0585107900c64071000b0000a201041c14503120b13100300c404442c220a6810044240c100040b120b982c0310a148640c5071105001d440e6071a642842130b5a00201c007078004205452506030480d080c20201415134004501e00312040000210100715040030b030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 832521600 1250 832520350 832520363
    0x2030601090e0c040c121a09041e061406040608010216201201050a050705130501211a0f0f030303012607030b071d0d030f1b060f1a0d 59
    0x1600200c2c51a0240c5441280d078054140311088000c141c019804481076039402e50207200100d205104914000c03604007846070048050800a400310f071040d110030180d5140807003c803450740800d07120340007595061041c1982e842e4264085c0300491800384250390081000800075403c1681d81300d000c3c050404101000740c10100b44034090000d941044c1300d583c01810300240100200030504808078000c2c40200c410b031020520307000104111901960036035141c814203255112a02d41810011a0b03c022841008411512050022101110b141c098032201004c4200300d110a591103104101140d286440d00038040e0300c1c800b00d200515240441181d042d40c40403109106003d000710900a003c12504940d41c0b007a0242d110048200318003400010b0060100d5a90316010490b50601101c4e61804203400540c05101c1c0c001301400a401120720120708002400c0c0000d028204919901c607426204108890595440100c1d11040c54140b04072445080c40000c00d449141c414404201c4a240d00d04000e00007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 832522850 1250 832521600 832521611
    0x60a0c020f03010606170f01180f20090102060f0c0412020a080d09090614010f030e2a03120f270406120b06030f030f0906040b030405150907030203060109 68
    0x155101d0744030800c03a491020703000300501999841c2c010b20031907030090000008640b20010422000001074401c0c140d03032911511184041904031418010560784016100c4c02e43c030f41603442204180c0400582e121030710303050b400784d45400040009040000040c546511044120148120020088107540c2600d0010460352885251800000d0440c6040d600011143c4540d001842106500903800012290800c80c00e000c241e44500045084401c1c51a90500150320b03801003107100c41c80b80c3c112000e12190501a500030703202050b401e441c903049248906030022a9070188104a080410005214508062013a41065458118056035100340301444001c10011f40e0740c10a000800c505a203600700004104000d425a51800600d021241c1c3e40c095400030540700004419040201e1980185900321000e0351a00c8502980030810b80c10103c0c2c0355030400170034800452034806550042d801030740224000c0459500d000c0303c81c00c0e000b02c01450341003290880e460400050703c0c002580d6064400c44080440c2c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 832524100 1250 832522850 832522853
    0x12120510051302130b04151e050a0e0a0e0915102706080a020103051302131116110a230402030a02070515011a070218130c0902041409010302060a0c 65
    0x68002d84013124a040c851081c009040340c1c400d030040c000ca17032000800301c25200811406440440502844c0d40c219070191120802c240d125000030040b03001d10b4181a0b44105000c8040380c40902c0a8000e000400755040501c49481c004200300010b00700242c80c00b8003513103004000d4400c400b00e0780c890404404551110a400c0144030325045e820303000c07001d02c1040803540e01c401140d0345507907a90050340803918080c04140c1d4405055812050b0640141c04c01d01c031040e00c0c0c0340c0c1074020800ca0701d400441800500007044d02d50101c20001d000c1c0c43c010203921800f15940300c200506002c5984c008003052000354405068142d07802c810703100b0340a048800685954a0484240103823280c0078005006000b0350352804081d10300801c840c0d0503540d9000740b00f01ca928404030045068800d0003806540800d00d04130a02407040400c02c413551001c0140007507440b03544266a000313418100d5800911501d60081024441503001000b6408810f0b4100c54410455145402081c0d55120b038981c2c220070003000306201030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 832525350 1250 832524100 832524139
    0xf060504170c0304140604060806090601030f020a0504030b1e040b07090f0b0d050f150f030c030a0b16170109090c0f090b12070f060f1107031212051005 67
    0x1082026103a4042d036555481e44405031a0b034880d02030000384039451180203402d070a00c00255001e03552291110140d58071407004110b1131010080980d81011307103c01d280002c50100303001805259042d80c4400751030308d0451401c800c1c0120002d00c500c1d100908561601a0a8051404103070050f40026000199441d104000c8500c45940d0300718914040c03a00071700141986840c8020540c48010a400708095112840c0f0407404010a1354144440e10850002003058904840c4980c007164004003250081c0c40d0040201c1c0c10204d4003034041d10b0040300c130010009000e03103402c00e8003105c40852038003081018250f0304030b011249041c014008019034078441d000030080c00c64030382005005100e44000d5420f689c4c400800192504c0d49603503004998000c42e011800b0f00c001644000c0c3c40044245076100340c14040101c4103407203a240d4110400c0012034840801e2034040c0810f90166001e03001d8509203445200c00a041107100c112104075062401080207036800900381440155502280e41940d03880ca201502d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 832526600 1250 832525350 832525373
    0x3060806010e01140406080309040b0a03210909090f0b0402011b0b0709050301090b01050d0c0f08030405092a0f0403050f0c01110f100f060e0a0507020f0a0f060504 72
    0x98009100d400e001007502000d031400103040300d00343d28201d0942104034003440140c51861051071280d0f441071054000c1d5103042d4001e16400341010304039140c1c4a640b1f4030341d403000c806e4008608120314076050140040740d40c0b0070402c201404007000244410403090766400c0c5407004c43d1f4030141c070071400d480100c1c00f1684190404a18401038000f0300340b018405041040480c2026a214408100c044a0000c1d0324101805003a5a40da04640d95015580c60201403003035420040c40110b4108100e510086403100300e000302c01c0054003483c0011621a8140700c1030140604002e0125110311442500074400815214900d0742102a600b4002e0307140d018100250b8940e0289810051950089141c003140340707640000d20084d0a40261384035500d9000f10800b007070715440e80002041c0c2c1500202e0030f1219200054000c00d03490880756a0008441ea0b540c0d4041510950940b0040c1100c0c0d100c0f0244505294104020010a0501009444402c00b90303528441f2500407003800601854071680020300b440001d400c103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 832527850 1250 832526600 832526609
    0xc21030c112106090d260c0717090a060905030c221a03190b010b130f0308070c080706050d090f020916032318010f02160213020a020a0b04030306 64
    0x651103010191410782e621500111003d10440c441c82a140700300d248546803d800f150500800d03a00044221180c90300960001400740b00c044108106030390000e00007010691180322500709036504c601c400b000f009400045a4044c4040010140003400241d90104a81d802120101e0303118000c4030945402c150511900380c1204207030303803908400c03e8207080400c1841d4a0010110144c4040307900a021980450380302c1200501026080001409058020130050074169281c6503100f521680d10841c0041e982a281c001300c44d80744000c1100001c015080d00030001401c81840a490b42d141404401000c0b40209507064102d1074852490b24180031220034055041500909601050f1074003102e001454a460384516000070300d4102c170001d10768010820101c03050054a426511a110650100f0303114111800c14501c0d5503840d40d18004205141c80203100300208c00c03181d40716905280c0104080e00760b100c01c41c0b20400e4010043c41c4000c682c0400e02844069002c00c00314016222804c0807030080c42641c21 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 832529100 1250 832527850 832527889
    0x2030702151501080109020a09120302071e0801050711061501030905010204080114130c030f060e010c03050108010c030509030a03021605010e0307060f180303110906070c21030c11 79
    0x1d00061441a6160500041c82a282c50083c1e903030306c203586800c91143d0041400090a05c80d414001d050080c0300500c1218080c1c41103410454854100d4011124501c85440302090b04200c2040780600c203004480d4040310034101202a00c04590103035440d0b10005100c41c4c0c1c0b08401d94486885a030283e0b21203c000c940080007151619142c445007402011030700c0c51441510001d1001950289000d018981c1c416031000190101c0c510350740d00d0170b1008562200440d5281c1d10743e0054000c0035024030501100035030683d000b00d042d524148000f421109004400010107041508002c0b2401002080394004966407500603581c02c280020000030b4041d902c401020f42d4281610400c0b1014004041c14405000d03c1c001c210009000c13030300c60100c480c00c0c0c1489050b05c2d1101c6070000072074020350200301e06d2150700b80c125203401c61082c000340a070391081e4011500e20300750800600c42c14107034500f044032002805600103018200f0381c40160400d0303c040300c01001d65151201a50702c580700c213004080c940203500e2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 832530350 1250 832529100 832529143
    0x61f1103040e0108160308190318060b0108090a030206011206020915120105040501030f061d0f2d1207060902041d0607080717100f080f01060602120d02030702 70
    0x181030300c2d1480c003882038504c18480c4031803205481111181113411690700c0726001d131500d07154410004e840c405004410041c50f540b41c3c10705502d021425100d5952038400c2c180000c80300d030f840f0000360aa40010345516038030340c0703e0790743c5c4000241c0014081d4150b82448602210b4011a0b16100002c0e104100c542c6801100c1200a0b9562a018401034070100100d03400710394641e0b0321070301880308607042484050084002100d80c9004107041c1e0f84a500c0e03040e0040d840c0100e10090070b2010b444d11b01c1c800c41c17000041d4008100c0c0600c00300760140c4e100074005c50274040e20b680c1c0d2915111035650009200c603200403100000c0c0807070030004c8941c030240b200ba9020384107000e00c00810b8002c1d802d05807403107054001c40c040d85001074851783c81900040d104411584400141d8244011030400104000741140c400300200c40006c580310b4ad0100d1401c0080050100030141c4541c2103d0311402d4a4032548003405661222032031207010302014080d00d81c0142c070140c00603100d603900c0034200d26106031141100950341050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 832531600 1250 832530350 832530359
    0x90a2604030b01060912020a05220608240f07050c24190b0108180a0602070813060305163b01090f0506033402070f0509061f110304 58
    0x40c0103a81219001d80301c5d1580307640e44130000b109100c0d00c0e0a009500144221040c03100c0e00e05640b0340000622030703405006100e015044107070f0071102e6541007407405500c90040400018008004480c001c00074182c0c2c03207884d0401820602064001800030400d01c00046480c0c0349000e000c006103908042104001d0310a070241d80b00f154119601170f9102d00706658002d1451808070058041c481083c101039642e0355007507855004484508030000704520f0305009040805000c0381e4140060b01700203009003109560340c1c440500342d003810180d40d80000309050508080002e1918510a800b01d6160141480891340b0103070005440d50825440b007414000c1c0120b03d00e104020110041402062400c0c1c0b1903095598907603003040c108410520455910100030400944121400b00300300c0d07898032401e0344908000d000801c03080140c152050008005030301414013003200c43c20b21a540340c000c100994004840d82000804241c0d810000d800d81d11003240c0b03845d104241035104203001c0c40c620401409403911107849 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 832532850 1250 832531600 832531613
    0x1710020c120723030a021b0103020405060720100c0b0703060e0f0a0617070b0c0307050d12060e070c0f020307050307170705010201151e030606080105160305090a260403 74
    0xf40c2e0241c03c503401d1000303120240448008121050b4480320780050a000c0a114240500c403c0100c415604141c0c003884006400d454107000b030600a44500c146058102c0e0860f40c46100c1c040e0308503c00e100d000d840d1040c0c0c3c1142e41000c1060191a008026864580d40381d00d41503000e4041688032198007150007040240341c0401075034840c0260070a290038800160b9075501002e84414a0308000b00c140c010700010410104401c0081802c5100c04c0300741c90500c01d441d100c00b030510010410420100d100750381c0e8462156841e10401c805804c840e041c612150070031100c0148148291440140480c200c1c0d144e4500b5503404011480082c00002c04440300162114000c0c0b4a008100c0c040440ca4424060081960740c0180101c0100d4241c0d4016800342038a410403a40321944864440701000b103222034003001040450090070060001100081071905000c0c80301a1103504042031402054a8601031080d00030b808600038403200d800076011003108044088024000c20820540c40b4811000140001000034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 832534100 1250 832532850 832532873
    0x180d1e0201030f1506050c0a1410060803041203051602030105090d030b03060105100c030e0319030806010f120f0f0903032f0d1806090c050a1710020c1207 68
    0x402c2c0c1c2d007444043c1505035200c2c29540c035076603035142000400d1000d01220307210320081c00d80d808000b011030b1280820340d2034040301c5809107802c40c3c00c0380e04084c0c100030004c1e400c0e0107000001c0c16980b00a42c5050b00d00b010032501e91810441c0142040000249048000410884c040040390014000c000900307051000c95a038164801000c0e011906240a080d510715010407580d0482c1c6001d0502814099444002c03140d80060316800c80c20f02244105603929920100b1541117003011041058940309070a081c0507002d0740c0300611990400504112a008a070390090304810400030100b404551500e01d04401800b030007004041e9483c0a140c26220b00c01d059158101a030030780c07581d0000b4000450740f141800300783c100105071240c1aa80412080c0041c410319440510b45c04010000040e004009907120130603074405d032605903030040d5650320602403850170100c86c0300100051781c0394104580386021000d441d500005422440c0039404140404040d0b0244000e114501c030440091b40d0f035058a1500548241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 832535350 1250 832534100 832534103
    0x24090e07050a0c0c060e150315010c080d0510240e011107090906021201050d0302030a0c110d051b06042607120602191b1b051002011a15180d1e 63
    0x50800450340b0710007d095049034050b1006079156a00303000b0800c0151400d80080e00121110790040001602040041c411180182444069040701604d0811520703100d501c40c1004504108250f0740700b018150300310f0308a0080f518282000c648401c000e401c0d060526444c2c0c9c1c0402051b9040103044401c10109600800341620b61203484091640c90f01d0500a01c10707182200200036a01c200705a8000a001d091000381c068811241400300e0070590001c507a00348403882c012101030b400700050b046800080840c2c0881c000b42030790403501303042c5804c010440003003400c148000c4082c1c504005907031510b401d20441001d031951400b00200c5081900d4050000d51100b0010540d0740d281c07950141c0e119100340303541061000002420a10b19030a07450f500302c1d00d590848851f40140d03c4250000c4e503904c075805e07a280c0084590b00000350744510f40a00301404009481428441c080702144180f0764801c110580c1c51000103450003a09021100300801c1100c0448100942001c003612401c6d0b4410100c500c0b1510810b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 832536600 1250 832535350 832535359
    0xc120709050f220c0e10050909010b03060402130306050403090e100b0304080d0507091a0306150c010e010c02030c0606031c050318120a0216030c05040c030b060424090e07050a0c0c060e 81
    0x840129512300840011542c4240181c0041000d20306000142d40c100400910044c5014516a0041d000700300c0365004441640d145c03c2000241034200c1e01c80001090f10b02c40c0c202941c07808820001c801412801020803080012000c10305000b0070b41d05070b400d6404039500c10400ba052111000e4428046031088a18500608004450601e80c1e4030070749001d02c41c06485c91a00941c803040d641c41d07e80014040400d290341e5200c1910300e0b908240a10240280590051365690860522107420800d00500d942d0003944003049107651000c0060000120a0580c07400742d49076169030342d01c40c51801c01140400f88a2003240c80303000100451000400c915032454084401e540e6080341c4a4600302c005d40701c054103405102c40c040010341042c1d040b1250310980f619000070481490000540c03103400a4001c45213803400c5107985001107004500000c0301c0702c49820b09403200b80c50310307903a40b00b91040103100ba0204000859003807480ea0003a0059004654450018401c241d140c8000401c942950300c22643308 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 832537850 1250 832536600 832536619
    0x9030a110715171501050d0c0309120905040b01030b091305120301030309140d030e24160c0819021020061504061206090206070b0c120709050f220c0e 66
    0x82004d05251118900f006031911402d010911225400500040c007182d000d2503200d0001100049040801660400c041d80703070805014204007d20040300c440020707103810b00d4507040480c83c0d6591480899503110100148150520142d840c00d0350a280e1440a0000b0680c0080b0001c02019000f14148041d00c109600031903113003440404005001e07609d40c0f000740c0402c1c8480e00c0004142048040050756210041c405003907080d582d40350b800aa400159500108040c00d69a0005c10031000d1280e0002c042d20001000c00f0307084030042c2c8410880d0000003c0c4106480e20220b80c80f54002e211106840a002c242c1c610840c0c0d058550b1612600100c84109400d0031600401c0218034140c81220181e5414601202c1412030554030300c0c006000388001a40d00680a105040001d1103c201161041102039082078446130805000030b41d03904050442c00034003002d00e0043c045500c45406110307202404407001644183c800c9507441e03002c1011400060001d003012240f03290281c000512010030344c410740308443c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 832539100 1250 832537850 832537861
    0x40603020a0f030c171819150501050a090b0d06110d050c04080a140f0d05040303082203120e030301060e1f021906020405090415050f09030a11071517 66
    0x2c9035441015031000c5807042c1d40e440211400312650780c0d44000e51ba544401c00c208400301541c5080d0080c0b00c80000c1c00784000c601000c2205c40d411201224203031040500941d41004001400828103000d4040351030742d180512181559001d14020180350040801c200000107096449100d82c0a2100c100e19a410400402c0040c001201100c0845156402619203100c180d9148404207842d400a8401c034495220310f01c00c820014483c3d5841c1e1421900e40719540c515602d005031841c00700400a4003031100f0380300e0200c0070700d80b5002c84181c0f0031b506140c210041a103010074500203044c0d10841c0720b02880f02200200e072490300440000c441102c1114600c04100d0080c68590f261169811280010b8000d0030362003410454008010342024440e92025080a8442011404102c0b040310140c40b00300003211075150700290351280903000031003c04407480b41c0c9806502696648182c849100c1049404161300d1843c0c20144034050242800580c2119131400040006110741241c1c03041003001d4041c00701049 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 832540350 1250 832539100 832539107
    0x12110f031f0305120702150309010915050606041502150a0f0608060c070f0c15080601030e0a050c010f1202030103050102031b04060f0e04090b090a05070f0f090e030f040603020a0f 79
    0x440c1d0f4400010122030401150300f6455402c0040d0072a000140c16098243c102d00043c09940300f26165400011112400c1c102a00d00600c6941059103803451b00003401050b40f1840d080341c00383d500d80b098010809140c00c800b00e18102010021152003c950710500400005542040c00202151901803001c952140307401c549654040e01c5401202108002d0070001030000f040d41091395000c2d01c10860f616a0722101c8401c18814084110001282d10041010300d41c0c00d40b003580b1051034400d0050602002641c2c0e100e95941080b100a41480b02d404d1520040030b01c5003901c524000840b050070b41d240c0d6507a241c680c1c042d400131745604007030900100e010080b0281003410f440494103d81e485140712480c03c102030b038070b80c1404001c00d90813940f17405800001c1290111800d0180213200000d241901d0f40f400c183d410054036030008071144802c1e01c4104001002010410281e5042800001d0420600c5000782d00e18414001607545202d0082030000b20346030190301900381e203941c0342c90740350b8403d4103403000700d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 832541600 1250 832540350 832540411
    0xe0304122013020d1103092a030d0504080111120c031302091e160f1206030f05060103260712020c0406080d14040806060112110f03 58
    0x88004800303000c00c6000ca000061450030350808203840040c0d0a5509011030040e1000c03801c00d544568000441d061100007030300c1919000100840d4460541c10081c014586402a643c0c20303458000d4010010800b600c8802600c0c0201c800c01030455100b07800d00c41002e442500244075108295103400d4800100c0d0350044c0c2100e884801e02107a068503075448100c0b41080d90009404e0031182040120110016200d4548890003000005031180703040d54842c0c1c10b402c14100041a0002441c050640d0350029600180d0041403258682002c4188000c03140034030006010551014044e81301140e84242442000304009060301c0c026950200c1800190380084609007a45440084540d02081035034041500102c000548061501c140d0303e941c1c410100041c01d032002a002260990803e501a403405c0750840c03000070416801084039404d0901d45003100c1d46410009056a060180e440c2054440252691050a400c5040040300380caa5003050302010071754104807500050b0107224000d9902c0c0155407071a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 832542850 1250 832541600 832541609
    0x1090c0e190e09010207020d0b1602010c05040938030609011406062101090501170a111504170106031202161e05030604080c0c010c0c0306050712020d0e010e0304 71
    0x10a1414030b4800269100c4100403c80302076950709100c841c005a840249076211280a4038114541d41001603828408d094030036608001d583c504101410351503089007d40d001c4070024000000c00c0040009a079031303090120240d9250038460002d41114804184000109200e419811903a281d504d07111200d003200c20000030072a60b602150000781c120704e05031004200042d19200c844a01b8000318000c00e0407100281c100010041e1900010700c650407182c1202c2c0080701d40000180705d0011252991056441964400e41c09203151903001340c0307e126900c080ba0020501041040c0761f0b490020015030007061140000c442d40b82c842c0780b890b1000c82c40000c02030a0204040d10312024507140c44541d0001300681045040c817940c510400250f203542c01c2c00090b102c3d03030050191540d80c0604844150500840120180c18031100c4041c0c0030104600000d0300b010340c3d50006000886444488094603500c20070103540b54000d00019505c1e03480c510a400260342003106200900c041d0b01c2220409440380128080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 832544100 1250 832542850 832542889
    0x30d08011401110d0c020f1503010302040b010e060a11061e0a0b0109080a0506040c12120806030109061127130b1528020a0b15120601090c0e 62
    0x5011020002140d01c6203018141080c00080480740500b50800308911030aa020640c0e541e809030940c181202c20740c618000441d000b4000045440a071030f050701060202078012680c3da0208012a40108001c032121400100641d88600b40107400508100c8540e2500f002400b4400c003040d03103181902c1012841d141d00610b84041661181c0304580100100750365a410072402c0d50700001c207101d0a1000a403214042c00c09001e441c82c00f0300749100710400325400750f0f824100b0140400e000c00c03811400c1900840c0b00c2c0c034100100e0b4865000090142c2207510000c0d08542c5441c8940d03080d411803030001c0124a02040c1203010f4580c4d0740403099440c5002010f03880c0c00c08010b002c0d0704420141340e0f014400c0c1c6e0100805201100d03210180c41c52103a004009222000000810440d003008010aa0b954041149100038a00840d05549800480002070159004c201e04050321960f02d6940002001c880243d4404407512583d50316122000f510043c861b0070049040000c1c008502d042c4a0f80f1800901111903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 832545350 1250 832544100 832544117
    0x4091415010e0a0306150f1508161412070e010809060112060603061104031b0515161208070f090503060f1f091d0118140a0203120408010b030d 63
    0x1075801284007404241c3c00300b461000400050100d10400d6029503043c029400300c182010310b000300601150308891003110603a0301e020451a40a12016031003488c1c0000360301d6a4408100c103603484041c55500c10305401002c500300f010048110001446460b00d03650f1503a00600c42c50055070003280c181c55040c0e2640000006200e00e2100c01a1300350050b00c203e04c001030031b5540e629064102c4154000084510720001400c00602189107201c52068132003500084140e45000d000030056020b000c0c2d06c00c803010b400320b440d8848a58605c4034092030764208003102403502c010040244251811030301c09010a03a9103101c188214031400ca204140c0304003800600303440d111121044000c0301c0003800450b900720b801064a0494060088180091102403404180104006004848203001c0144201c040c0e140404c0d103c03118010540040c2d16580000c505100c041850b15030f40c1c1025a0148040c1d09841120700c50600c49083d80300900440d60f006000b00701c0c032941003003015254900f0b9034540c0c0010b00e100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 832546600 1250 832545350 832545391
    0x40b0103060507111603030e0307140d030e040f06050112230606072301201b011803120513050d03020a18030609110a0803040e0a0f0e03040914 63
    0x15400b650b0007100600348984044c80720310080340b44c8071000b030707261400c04683e020400030580c01941071004114100c001e01640c0b0304010480d11401d04680540b88241207803054882414002c51380380140ea1000743c0306000c1e120302e08180c107024003418424a1300227121942c0c45201248148508403e01044840d03c14408180c10300f6800c0303c910181072503a003c7c1d170401403100082ca603142e8410010740703002044400a082d4100340d908440c4002040c4a5070a094201d19207560317105400c5440d80001c0060b8440003a40c0c242d01c9500403c0f0a1a04c984003036518501d240902d41c004280c0110200c451006008665600c0f0418a040300040d100034000d901c42d51003110054002c0d006007481001c0c6151001c038450050000780401030f410ba2081e0386095484001c00240003c1c840e840c6244202610f03d01601c0d441c007120550340c3c3c801d5200d07004012a00760003080080542d80c00004044042c242d0510184080ca48010f071284d205110f2041a10314040441c0c03150007844055a106040d50100302a0f08600c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 832547850 1250 832546600 832546613
    0xa02131e02030a1a151806040e090715080f0103020907090803130302030f0f0d0c0f020a03060c0e010e13020706020c1c0f08040314090d1b05010908031c0e16080312010e040b0103 78
    0x6d030110b64407031406d01011400e0326281c0b18451041c04000300a0008501d0254200004c44600003e401004441c204000c10101c01908040c1120f9069541842c66521201d040303c40c1051a040008103010004251083d815000603020689000b101274031020203c0d4184640d5aa6885001110a0b0024a116842c050141c1201e85a2500410021841d8243d07580011403074555608101d8442ea9034200c2ea01103158042e406240a00d42820b10070642460400015038140e46105204000358002902e08100120758060f180d010040030115254455148048200070b00201c00070400105500c10407425603102d040ca4600441e010384450342181069540031b03503280d02c600302071500001c98842100000b600030341040e81036205010307402d009500b4100010300401266111141e030754020702824114a601000e8504105500d440001342600341d03254890401c40e25948009035668011000170b24040040020000318450140c1c14003183e0703c40058801d03416058a019100d02188401480082d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 832549100 1250 832547850 832547887
    0x31217090c0910080102070602120c0a1e020f06010e0609160c02240d150b09031504060605130603060c0f120c020c060403050c040e0a02131e02030a1a15 67
    0x1901c030f02c0351102038030740b0344150036640101c070b0807900c06500050050382424030001003604440c2401480317103080032150004080315a8254202d80c05600d0007140120329008000381d203000b24070b4906444840d039407040303174090075a02140d0580c0101e0400000407000079588003851641902622600310300300c02a028030151280256680c2100d411028068150810040180441d09143c60011070310310351100755207000907031a40c0030010452091003501301980c0e0114041d40120314007d8280742a56075030915101414040d4031454002031440040c4000700c203540c11045c00c3d00d004038410f0001c001240030031140d0204c0e1442c2c01000560f40843c90440c04425003000145820034411580c1d110300d02c40004269500c5a4000c6075298042c80200030395080900660807000f2554014000408107034020a545003503440c021030049a56054020311010004c05000050402c0002103450b071800b0503500c002404030207501041c4030816a940b00f01442e15502e80200c401c41c500520b818200140c1d507854215a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 832550350 1250 832549100 832549111
    0x10e120d02131205070e090c0108061801030311010501330e03011802150711060307020f0a0b1e04031202090609061303030f0903020a1815031217090c09 67
    0x25000c015100c1003242c480203603000381800d030044a4065640c1d2a1080c60310000d41e001c804000704010800c1005600800c0c44c4184402c2800c03c45610f95549000546d0030380b000c00c9100e00101c4100003c014140d000a0f450700c40d1010720000c1280e40d8845580685a407503071f400403006a079890451070188507507e1120001c200d0341307041c003d0b442020030300002e086d1003409100480d1540800031440a40c80c0c844041102d01d8070052501e0300c0e0201d5501c8100000c000e8000c0709014a01c0040402c0e1028401c1112036000c0e105401900e081d00403038500344030b0b00e120550b0139060b10000848154101030307c02c00c16a00456154171006102c1c2c1340c8541840280d00001d564980c0040c060010302015101d040007400c01c292040c4c41d00c3c01e118158070340580a207015803807200411001100a00060f2208420700301550501e030390a0001c40c0e0140300c040041d144095049408030440040001041000150301b03c840c8401d4076180000030354445030100c400421100303820f840d4803e4104689500308406a81e4005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 832551600 1250 832550350 832550377
    0x70803040f14060c0d110c030901050708041503090c140d120212070501051006020313140d0f20150711150703020c01030f0c0c0201080a02040f0902040302040b03010e12 74
    0x240c0ba40d03812410824100c5483e0484100050000510b2095100300ca10801d400d100d01c0f0308000d000340c100f03075590003010490b40c1400307800282e07070061115050559004054801c3c0038050244840d60040250910001c00c030380c0102c046901049040440d90041601ea0700649161030102c003945a01d02c00c545082c1100e010340c0110f032140105a20507000418655010318004182030806e0240c040c240c02865004070115001071007400000440080c0300400c0369500c8440482110344071000584028a00a00074521584a211481040030b070801c15108801110f00480c003081c40c483c03e200301e01010380490b2140d02401c000c0800011144590861800d0028148202010802300c41c2c42c4503a00c240d0302680985c0c000e069006403586c0c540265105402d2015040c81010761520340030f08900c0035100001d0502c09010001148821039030306480040c00c200010310103c40d59800c50600075480b60105034003990600e010308415081c140030b0701e034507240c4440080410012550a4000580010f859003500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 832552850 1250 832551600 832551623
    0xa0e1f120822090204030308180703030c12051603180e1506030406020c01051f0b0a0917101802030c0d08090607170a08091c0207050105070303020438070803040f 71
    0x580241340b01401c007440c8a61100b4509050403ca807001010500d040b078003140c0d0002c502800040c0c1d101d0030711464030b07900440c203610501444005440502030348140f652001c80c03480c054400e06070300411000b04118602c00c0c412117280c41e0712030040c0200381140c1022706000300c0f0300b0002030f41c00c2c403000a681c418013840b401418601040034580c259401540c600c41c040c4414081c007420501d00c03540703d10042038401c10940c5000f10625015080c00014411221060244602c4044010080c1305c2c2d0645491100d404005070307809441074003070f0030300c0411049c0d0091260300c15600b2107081a4106000468101c40c10b1820403218008000280d032288004a98035413a103903190313180803035000c0075244600558a84a4442c50a54061840e003011042c1d005403402043c18100d0f1959000706884068920170318007103550700130504040d0040c1c82241d001c050400c40403600407100050b40e8210341d54080c0301d0a54043c0418001c207416a0314010f40d100503002a4080002c100011599180e1805040c45000714610 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 832553956 1106 832552850 832552859
    0x60f06020d170619030311070e01030507030b1e0a050f150109140609030715020d0207030506130f0605070206060f0612010b090a0e1f120822 62
    0x2401d01d0b9200415895200c458100181201014001e6880e07030303032854000d203054400072a110080c02020b402140104551001504990308075005054050842c1ca4503840c00a016010b41747d20711840341b461008591905205102e42c40e220000102441c11110000314100020f00b00d803d43e1341d140c1814003031070b80c000706140160b902c4501085402d8207940301140503407007070984081c4c2c0341c071441400044401400741080390051032076081c1c27440c1d081445c40581e034030305c01404001c0030f58001c04002036010100145940b0010b0140343e80780900080c40d10740d10100c4806a07001d2006800210800c415410280c610002240302540c000e03207461601e000140078030b0750602550001090000700700905a0750381c0842e0003d088404444c00c26814051501841c00112841007000001c818000041d003560200100036001d8120b00c540d480c0030007611146815400081e41c0b250b0361261140040f4 = true := by decide +kernel

theorem cover : BRFrame.Cov 832374100 832553956 := by
  have h0 := BRFrame.cov_init 832374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 832374100 ≤ n) (h2 : n < 832553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
