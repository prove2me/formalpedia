-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3935
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:06:22.608979+00:00
-- url     : https://prove2.me/submissions/77bba99f-4025-4078-b99f-8720d4f8d07d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 707553956 ≤ n < 707733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 707555206 1250 707553956 707553967
    0xc0201020a0c0e1608040c061404090c02071401030e0d0f030204091b0311031b0a090e15010906020c06042c07020606040f0509061303180b070b06040c0c08 68
    0x9108104400100e640702c02c0401d42c90b900e80d24440045101240c81d031400442400107941c180388101c1d422801240d01c00030340304a460400906841444c0c000d004c0c650140000d100005852140d8092103502c404503030064a80e00c0e003446582010300b60b07100c4100741454144440c80d4114840060b0305801c900880c50900003541071250b0031400b0b4480d40c0e01422400b4100008880f4504607403441031900b0b1842e49080144c1e4204148068050008440b001c0c070781041d44000840080b81c16000340103102c82d031b141075125107484186808001c00169014203240768040041982540c204200c100038018170300007010617144143c0000c50b14403444c014040030442400300402c40c04843c510003c203d03904842d4071606031400a10096944504407107440c8110704084513041d00240c607120711400340150742e0140c2219654550103549c0090602d030124100409a041c0e140f0b81c510b8503c1c1d400240044842640d0784c4c0d1041d0601c10721500001e00160b01c03a629046621540c40d40140f21559003590004409442d00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 707556456 1250 707555206 707555209
    0x8031602010e07080312010603090f0602090d0605070c05070f080709090503210717011401261602010e0c1c080409020307050c0f0f03160f0210090314010c0c030c02 72
    0x10710060380800403e01c2182c2c0d0125001c4c0022010b00881000d00d06220450ba90780d060032016a07160200162213003600944820115605030000c21b48e03100064124921001543d0b5030408844040b0788202c0002c070383c1103290b01000b40074803040d80144140c85011075094240b1480e0303900c52005101d18492716680d040302904102c0148141c4265019103070a40ca110451240318080c80c0c40c0444045000804801c842403503d03004085090503034441c00302e0b000b90750201c0801034480c000c1c09054542030f4032010228841c407400003082548a00da0409182c0045903001c08068250350019110100c0c0c2d8028a49000c81c9456844d600700c2d0030401c50300c034003105123507504246071540f10310341081c003850b0300000401035240d400c00001c3c2030030710002040f0f607041c4a08062103512500030503c1a519900100030094030340c0a101404509140a0305400480d50b4541e40003c208035815139000d00413884810003042070019019868200141d400001e012a001c81d9800900d500e0300320070020140070081c0c110700190b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 707557706 1250 707556456 707556461
    0xe0d02040203070806030706050406170705090a03060209011709061501140a090518040c03032a0b040203010e0d0503010506030411130e0c0f060912210c06010b04030803160201 77
    0x5802a10031552814070f10001055400d00b141c0303250283c425040c00040484c0300b002214100c4130241ea4540034004029a880183d83c40030f0401401c1200600c2071444550f82e004450000b58461800140e9449004001601031030095007030810340e040c002d08009000d1004501d9a42c0821003070042c0f50b04201c868016640c620307500c40b1381c4d010603e0204403010900d80000c50310301520811280f282078080c6030380102000c03a4088400038a0710045403000c0000a01680140f00d060f411600c68241072050000b888181c5158050300341c41c0842003505100a5017400e100e115448407844001e002c104079400f002400c1807006104490251500000041c1481112040ba200000e802422424110a1009014040c01c0426200c1045000340b8503821028544001e610007805006080315091100c0b001c200142543c415803000403d00030541035224141c9051030410100c000c1d00e8020780c98115801d07480c1e103404016000850002c07002c04c0140f001c201d029045e241d00c0180030f80606040ca1034408200d01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 707558956 1250 707557706 707557729
    0x405090a051e0c042a110102160b160206010605090406030b0c03190b012a12050c060f130605070207080303090d1706061b01020927070804120e 63
    0xc1802041080180000000c00e4540d0000400342180d2400304141e003008111181c2c0455507902520815400c41701550305891035001c40098102494620102981c42d401d9a1001d260180113022601c044810040e9082c4a83d8000c224604503002200032132201070760740c034018042c0d4014400301081912055655170403c201865005401d9501c1d810880100c07126900705030303450884038181c0039610025981c64070071000c3d00c1c28140d482ca16948400104108102c40381110004004007108260000c201100c02c914403000040d035840d076981d481da840b07031401c0a9001c0d01700390708000d84009022a000e81c40d131a4249050300000000b6030758031880301c1a4a454481c0d80b28071240c0c0008410018000360201c0c0b400114800c64039001c00b901d040e80e03a412071403441202c01580c84031080c00f400e000ca0281d9010342c1c4135014414001843d00c000740002a841c401c0301ea191840744d803401203603d4a0f14100003100c1ea00b0904a04201009060594030122810303910003031041001685030101415588000d581341 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 707560206 1250 707558956 707558963
    0x4080a0f1b09020403051b01081801150e01030c08070513180b04050318011e050a050c072417040b0603190503070b010b0f030c090d1406010f06030e0c0405090a 70
    0x120840d0340c65642c000030350020300c015202801403074000b82c3c1d5041e40e9502c2008030340301655201981e03a0f07026503040291404681e000300c10b42d600d1320704180c1d80001000e107101070a001ea100c0c5080750316500e0020380d49185034010383e0036508408010002500c0e034201000070078031042030110b82c0120800c1200d102070203503103010303000d440614240014010040700900351301411068840d0030384c441c84011b6880404031a4400e84d01b042c1190010645480b44015214503031562074103a14200c14150464a232600d40e8000900001e1054510406001c44107003c640814482c20440403492050700f1964884030001d02c0900001c00b84800a222907500f0f01400302144610816040c0305880c0e82003460340c940007400c4c211180000800007051a500c02c40a49400b0a10180d1440c5140d49505d03041c04035800403c0800c1d0044c90000c941c3e00003c00c0c107004c0022240704040201030941c504503c0c40c44101251b070004040c9450921003000030030003c0b40810005070196800324a54513038580980c5051140034018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 707561456 1250 707560206 707560253
    0x8030a1b0b13020112020f27091602070e0c1602190e0a061202090a0905011805010f0f0c2a06112d030105010806030703020301060617090304080a0f 65
    0x45281e09000d44a05071540c000e071795540865149002010403480703600e00b41410445e01348140881040d200504100a030b414000341e054028450340030441c03007007094403201901c00a06d003110b00041c2e410011a00205025010206241030000c03901c0068800c4200c0d00207041314845440056441e01041400b6030480780064180c51a550341030300100c9401684d02441c00c0e410443c00240c2088614020005190002d10f2003845031901b00c1d0100040c0ba651800b214195240e07400841941d102800000d40d07503016000110f40078801c0c0203c0e004842c08111842d80051a001c0c82c00a130650140c0380c4104a600401c2e45121708010071007926004e042144014186410a0064054a030a60010f40100d1503620f20286880100001c0390719503800b0229501001e8800317000410056201c1c5962580014001d0240e0b00304a4498000c02d081d2000c9402c60360100310009080342e460f6201d103180781c1e40072030318001660a060a000040c0d4981140d0a13018240a40b440e40a800780301c450300144400342c2d03c8101e803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 707562706 1250 707561456 707561461
    0x19060f0b04031106040807060c050c040c1d1020010b060d0c09060c02090415020c01050c04140303030f150a120c051c0203120d020f030103140607020708030a1b0b 71
    0x2862003a5019010840d80812080d9080c00c080c203010342902c003955040800b03014040c2c1081400c842100c45050140c1e66071040034800c0d90309071260300c9407801221103683d4106a4464001201d03203c5048802024054805500c164071495480028802a83c0f01c1540203140200300b8070a66000d05540748120380e10035000181c1c0c1e042c0380d00da0341c0540307007104450b00c0d4181d0841d603d10301030f00e4480c00c210019400c030340054001000120480341c149846450143d005081244814103182141d44c00c8414903241c41d800141401080032412440c452544110000e61540c41c010301520341050015045c4d400142c91400002c25503560b280a0700054990006e075001000324030b0402d03d14031240703480b441d80075802e01c061180d0340310300d5000ca0742e0206402800521280710b030f805843c0095440200c140340c2c000d6090200440ca9941440114001e5000d0302280310703021000311906007042c801400380020355100b0041004103000100540300031001508090b8810300b0010305001506107140001030610900b00c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 707563956 1250 707562706 707562719
    0x11030a05060124140306010c06140f01080613080702040c11150115031107021002250e010915170304050604090509120406090323030703120e0c0919060f 67
    0x394220386012140f000c40395103606180941e41c01c480b01074030407140c00c0100700041d0b555028142c070311606403041000041c2e203444483d9031106008251032810340c0e44c03150307001017054a0f02040708035000164408c41c091508451350300d60380da511070141c0c000d010341d44516006000c41d01482008240a0400c1c0540d40d2501c500341003111110b03803d024814168024030b05a207070862292007004000440b64071040e00d88003094082085100d5184c030b0b168218030a0758645540850f58410101c40748034002c0150795400e04114220144180503041800200c2c07501e00c8510b1200000200001258018000c802d15020140b078540e00318800c0d038218542212002900140c4284c0341d6000a1040c0c8a20003a15038443e0750640451542c480c034840e01002480880e028404968040e562401c09103d0204610311004c031200e070242150020541907010a800300110a40e1004601465078105015409030041104201c00a00c0c45100903182c50b0403480012110345070583c4c19880a006001401400b10040c1d56602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 707565206 1250 707563956 707563979
    0x40801020f0c07080607052d0408150f07050304020d06020c160503160302010f0e04021303030e030712380423012309030403120e010306080d0c11030a050601 69
    0x101d00342030b01c143c01d400200c910020901c3c6003e40c1141e902c03e890b208030348207881c1d58030140c0c440c2e41c0c802c0c212000181c0881c4258100420080c2044809014110342014982d038640030000c2018503e1540f9034200401198070904030b0b0351140c0d04a034040c490300441e0510f84024080c0c42c5003a00b40344551661219a840c83c40184130858404504840b07400701000020f00e880003030780c03000071f020800b551b035110800ca000c1c0001c068100b0340a04010704110710151090700c02e051a034025408034855082c503000700d0800380001c030040c0c0702c020a05c1d5181e035069910005031049040c4445d0342500031000040056400c003842540d40100c8004404580c1400d080ca004000c5028540e0840100341e04034030000d00760306001c1d001c09141100001000b001900411184031740c0300030702d01510341c0404c010100005010b88603420169115603900280181c801d000503041f51180d4106000584c480c103440e5000c25841082c0a00c40d90340810700f42c54041e02000031a00e0320003001c2008003c0c0c007907107001103040400c20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 707566456 1250 707565206 707565217
    0xd02070b04050d0f050f1002071203020c060606090f031905010c091413021209061501020f03031503070305030403050c010815240f0a0809010f090c0e04030915030b1302031317040801020f 82
    0x62081c1a2b05a03424a015000c80c032072113032100304c02d0300a14002492890480050304000801400c02110004ca04001034141310503404101411005c400d0b00d8401e200c2c0c00d00c602c6050703030240e00303002c10a20309200044440001c091710385031041d10600700e810700c48241350b01918840d0002d201d00703008606280d40340d41d403030360700880d100b00c0911420360384144598400545c502d0380c0780600003d50f1035901c56200b00301c41c042c644034400d9058440e91000000040041000380001e5006d0303400b922038400b801000510008000e40104080071102c0d40840c0160780d05a01c40605641c150100180342e41c0342000300000e8003c6090300744400a0110340c44080540028420340b1480c8004020001c845034015480c084911241024028448145003070004000b10185d8035045802030030604051a034804011851207003c10002000a03282c00c0e64071500d0070240c1c1c4944285ca00722400758250300e004d00380c0300710743e0840306c0028140144ca0710300070350103100d144101c5015060500003956140501c290b440c0f0281c1c0b11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 707567706 1250 707566456 707566463
    0x41503020901080a021c020708120c0304060b03070302090a05060310021308101b12182108090d030f0207020406270506010c06110d06080d02070b04050d0f050f100207 73
    0x110303c000341c22036440b031084481c004200c040d0708641961021101009400c0003408903070090003080b814640040401e5007a204882d05001150f4034070b020710f003074426a4400d00c185402070388102d00601c0107030b4603500c8041c0d000400490002e481d50700c250010b45003400b92101204018400903003d9100c0350300c1c038003100564540d4411250b0021416070882d00b15100d15944107940c0400e62114941184034030355440c0418070320400880e03028515880014801c0c0c205004441c48010342496050804009080441d13240041c18040c074549045598107881e040710140b400201551085418011202d40d410741d40020f0f0094002c115080d02c50600c07216409881e00b034128502d10320132005500e481c96028051240006a59141c210101d558489000e0980700c0156080004203004d01000c2082d2445650b008041c0c0c4401400003e1200401074200325258100d081f180004000c180f015440d0b298601c507a181e4440c0304072001c080c09041050500c00602d000441e1409800900c04043e8280e802400c0300a02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 707568956 1250 707567706 707567717
    0x20d12050a0b10021c0810170307151407110d08071107291809180a0c1e060e121e0d1707120908091201140615040306050408041503020901 61
    0x43c001c0181c50018007207c0c0d1000e00314603001d0a02401104001202008400300212402c0210507601c0c030990301c1c058906465015640c0c440c003421490364014254204a85040801d02880b000b290707103860f95540c1a040042c000d811303011075a454494882e4141441c240b000b603665107520b07110801d58024500101e010b4403504a40c8800d40c100c0075008803200d0382e002c084c030f224000e50024180a45810001d0111070194042c02840d000024240404072400e03200300e040b0b9020600380414010140c0018001c0d600e00d2010560038450190000351b00003404501f00c0c0d1159403403191b92006450b1042c44040c5040a0468040240c00b40c0c10001e40c1c00020030458990611100c0c44102d00d108242c1c0c00c0f112a00001c24600030030301074440c0d40c3e020030a850300500c00f17540751410031703808110b8401c09091120404ea41d501d00e103a180d607200102660b080401290801001c0c22184001c41c80d5000f1404040c1c02291744102140400c10414101d400402001c07003004e038030001c0100007500a4200c5003000c1e02251 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 707570206 1250 707568956 707569003
    0x1060806071b0312060b120402040510050f041a060712020d0f0e0607030201270309090b0904230610030201200607050a230c0d020d12050a0b1002 64
    0x2030182420100b810002d4990003280d04190310100e81d01c402400d82d8011450b600c200c0400d1076207404d00100803140030010001002d0400c1d1040c0000c84000400d01e017104d42e0040d105104955030581501c1070b0300001c99003c502400304050941c40604813052040d400100090510f04002003125004200d080f16001c0ea0418414071405448803540c400f0f507100094044c0505809034a40341001d080014000c1c0300010b80340c21002c1c2c3d20b82c020651840000131182e103840d000d2027050340c0812090080c00240d4028800044041c0126194035000392000b0700b003482b9800c41d684900c0014050504010300d003001c65031907080c0b82d422600d5943c19400145e000a030021980b2602841402c1c1c901d5400c8800d2006200c0b80e030340c06108460076005246810108030804000702192106454001c0020355100981c036982e0402040c003c0c900982907007854203641054900c440c440e1f80140303800408524032200400c01e0303078500055400070080444001d07405a03044020341c1d143d41d80050840748510744000d0b6610b005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 707571456 1250 707570206 707570221
    0x6060306060f010507051203010f051c020123130b031909050c010f05070501090c051002030705071415130602010e0f0a150e0303090a05061b030a09050309090a09060b0603010e0609060310090501060806 88
    0x5400e90103001c2d02140440010000f201404561090b000030482e0a050410310b1300c0319101c05684880c0c0c0a442c0400300132061201c100303a244032042284003840014c106003078580c0e480b2616109840318841c10310645a50b140c071964068001c0343c6030903500c03500811007180145800300f07000419004403409044403003420030b40341b8000000c44901e5500107001341500c0313160181000a003a0780c1c10b0400d400000d50b0081e034607212010409440b04200400003440418104030700203084506100c100d40d000e0780300098a01c4140008a0594440c94108807041d207581c880500c8540030700240120140580b00c0081004800707803020035462811072003441912880e448042c1c0b0b128241d051088030000c0e01c481000820f07050b0000b540700c2c03c0101c1c8503406a03420403500d5800620250401c4480c0e41d481c94540e4061010421688030f441d580f000700300c41c00e070305650602c40c101c9200c82c001889280200305000c0400c2c804e9408005c940003c42045005020100300c0d80b400a0203003406102d094090312640010800302d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 707572706 1250 707571456 707571499
    0xb070e030c12030c010c0e030f0a0803010e100b03040f0b15152515060e0f010302042f09090901020a0c0201050a1b060504030206060306060f010507051203010f05 71
    0x1006801401800520114000c102d100d052026140c1540e00c810403021000380000c3c020910f50449540301d040c011104401070608111103100d82581c40e4202c003480c54001a50802901e0549042245060765640d452010b4800300c0740340e8210200240001c010401040900c07030050050520a01a108964607040c004592400102a51541c00161045141d007001c42c2c500103410307400c000c0c8039000148a54122140400c1c02c241c1e200fa6540f503070305007420418407558003e2200400c00004207240a16202c82180a03240c010301001307102d19165030245000701600f5850b660f0a40040c200c051a5400f070500c0040c4691040480c18003812003200080e40704041031092b00c1090744262103005030901145c2c01151142e108840705000c5c0817040b0008030041141c90b10340c80c4e10a1141c0301c0021942803505010740341c201c0c002c001c18842c3d48404200300107511030040108030344000382099510350905c1c0c90114200b02d0760801401d0311046c0031000190301e034034906a030404c0b5030b02a202c1c10303030882040c010045d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 707573956 1250 707572706 707572727
    0xf030114030118021f050403021e01021621020d170d0c03060509040f1b0e0402040f051023041503021014030408070f06090501050a150f1e0305030f070b07 68
    0x40c440d1a850703c0e03400c141c0041c0d45ca8400e0203178600d04185002c0d101d0b80040e11000e20306034200c81e00e18107040030181c1540c0410103003801d403425440300712056140501300c0700300181c1e0190314400e01c11502c103100110b458042d003409034144e001d09000600110b0340200300c400d400c080819a501410f00c1d03191a071060203031051609407140a86550100d80c0d8a88986020383c0075001c0c101c4041c0c03c3c01c1c0c03800d04002b4a0002d00780c090b0802484544087c04c0ca80100820b0f503807005030b800d08091804080c08030803c105082603003110b000310652894011000ca030014800d01c2c0e000341d03582180c1000c2010407021040d9000400b40d9100b203540300e9030069441c6c0c0441d80800c1034034488102c0f4508101240100301d100e0081c046440c442c41d00e00c0440c803c41c1d501c0300c0545424140854480c0e44407001d10000e007070385029203004100440000083c407868001075100d4900c00c0d02ca642c4480c152850402c4008840440740005141c2000850b0b44d00c0c44003103555041c2e5481366105990740100d017400301314954802c080c981d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 707575206 1250 707573956 707573959
    0x1509030519080f0c040e13110310050a1127030c0d0506010905090105010f0b0f041a030f0c030c0f03040215040b0712030605130f27020102060a0902100f050f03011403011802 76
    0x1b07a0340c0d02d070201c1d091012044050b16420031104d505006135a0801242001104808000c112401c010038180151001c03048100351601c820f002d294105940144028203003842114607080d041c80340c1002c030342010304030300c85142c0140c4448000c23802d002c40051043e0480e80116800c0005030780300301859007240c0d028001e407506020f90a034208403003079914020b48560751076141014601343c0e031004503103c03a644120942c50101da011042007510310300c801c1e00700e600004980d03645143d480c1508440790144120300c42c0cac000051010000c01d06548500340072411b51803c14403116039880d216003207039020703811072541182e001800040d40301e15144a0b0203981c04980c005005407032000601a0364101401940110b940900c1c2e076410201d910201107e500b10303105868000c400c0500c2128000241005070080c004410076050800e00700058a44902c280c0c2c03111000d00d1300b403c0c2181c1c0c00c04100e0f2244a0031034403c00b0584088004510525410714804210804130001c12251102c150354500c071900212010707 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 707576456 1250 707575206 707575229
    0xb040f090b0a060e0105060a120606031d0c030c1306121110020a020603010e09030909010308041703032e030f0b07032d0c090b040b0309191509030519080f0c04 70
    0x4000030f05084000e03180d031030400d00303160327065801140040c0d04803151030380f015000a40742c280560390144410000c0c007815210720042c100b00008100820b07542c102480819016001c3d00a141e1a142e2980e0300c000d010306042d02d40000149000c0c20b0032150b101028507810703c145000c800140c0c80030700000d92303130540540c09040346045a00e4a24510800d04000385082e4940c08200910480b0341c1d910340050b8007030361042c4082f80c2c5450500604445003402c03c1040c1100d035000304148104400b80480e9582d854212000303110300450901c1c05102e003c4010b074001403440d040c0e19000000c0010921105201c4c640c07236603081011b0407140d50301081e4888400345126610810759500c00301000c1c59004039040d58020b0510015050750ba8030030740c50540c0030b940402420007002c018031541d60014025000712b1041c00b03035003d210b56565101c0c403520107646d0b011258a55685c00400b020140074609941c00401c104203146840603441c10098448403089500c030400469240004001d01100000e440c01c0c3c485400c000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 707577706 1250 707576456 707576459
    0x13140c1c0c14130e0615180f101d040b0c1e0702180f0901110909060112060f030506040606090504210c0b01150306091e090c030605250e0603070f030b040f090b0a060e01 74
    0x10062314203805040700c4285505458003080404a01415580041103083c0c000d00c0c0d89418142049681405001d843c10840100b20703610760950403540c2c400d004a0074481c0d042d43d0320507074030010355180d107100c5841d0541d0350a003041000100020744001d01c16001c000c024081d00001c8036125400b8030030901d18990045281c404500c030382d407180781400e090341d0a80000042c03850310f40e4035141200149910031621548a08100700402c0300030301850004286040c0144a40d08085d51100745001890009408600010001c0c18940c0d2007040440d41c0c4030380010060942d961a07170480b1042002840f103d0b008039052a0307000405078441e00c02c1418641008034401e500c0070b81015000e000d49a40391065032042000c040110100d0014490385009045518024150880f1848a007092404942c0103400303022502c2070034040d580300c13036084a51021031403030b19265404940c94250000d00c880c41e00f03039800c2840c00b06882045d401a07400f46036004c0c0920801070140e1f880c90010002d0b10058005c001199440200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 707578956 1250 707577706 707577721
    0x80106050418030e2101270b191e020a020c09071409121209030d2c0d0f0308070e060906070b13140c1c0c14130e061518 53
    0x82c3c0c000d049005081c840703103460300c9903001031303071191182d041d01981d41d1290b2401e5a100400447d11754a035202c03c4c0014080e01f01c0c1c480d050366000c000d0040e0300c191040c140400422031582c4c81041a04070460104544008c3d0f4404000250400c08461014ac881c5a908034120316103207004c948121091340d5024400ca80c480030300034054115400e25504022082e001c02e60f004020300c510098010903490080e16215500d040610342205510a142880340c00110b0302d031104c03040035880d000ca18250f00c50112001a400114080c0c0b17040c444040e207800c2c40e584d614400c250303100320602d02032a0103643c1c20007960825403c0002c10f204881001d035205808100d04400190420320302607000c030a03034000c42404101d40e11100624100001010900c0c0c01c0900d0360600c40c9010002d040c44d000040c403180080141a5903002c401000c14001c20030890001c500b03911a55603403100c0b00c84800c00c080c40c24081c82d5481100c5540e50340f0207983c944110340580300000503a05001c003a80e003c0780c2500f034400d02641c40341e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 707580206 1250 707578956 707578967
    0x10e010f0801020910120e01050c09040b1f0e010c081225050d0509010207080d0e100912030504021315081018030c02040207020603070c0201020c0105160201120609050106080108010605041803 84
    0x1d200c0c0f0b03002c54a881080c2040b500038810b841c4100d5900908035954002f0741c040008070b0b44500368180c820840b40210961001400311101c1e00740505040200110140d0001a40c2500340104000c280d014005845090340014a210500400d40e10100e807414070f00005940314151f22140c10f11000034402d008110b405849900300765040380526000500e4030760729031a054a1035029501a14402ea10340445035100340042141c000e903034003540002c1249003480d0760381c000c80350001c64050042588410128055548450410101581100e405c2110458000f8040410441d5204440e5940500440707040d920045000e540507c0700700b184d024a01071400e58055840311414501a82c00c10790910014005844410040d8007a103501e4543c110341000a00c002481d100244100c18108002400040d00008034644512501c5909080c81140a020000408010545a40300c12100c0d030509000180540e00007103010706a42200c0003c0c01100d4848082c042543c0021411001917151040c884010078400ea = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 707581456 1250 707580206 707580227
    0x60501091d1f0b0406020601210221060a14064006060302030603061b030c07030e040615090b04061d0607021005090a050405190e0312010e010f0801020910 68
    0x140c2c1e41d20310b850b0002c8414032545640741c12a608400300000d00b0701c00590104007107030040c89031107000031071280070b001c191800b0003800310008e0003400e01c1c10318014429066083d420104851030110713031136850650b814038042d00c6154203003000b030b03403421010407558204030516045a502c0d1200a807241c001144100c695032034111450b141801060006000d508142d009150041c690b9540140e2130f800c1042c10981007442c054451003804c2e400e1640c064400500b4420b491b8041045403a1030340740e01c1c0380e09064403403c1050024640c040d141040200d810214440c203038950b440325654060206486550500c0644614040c0f04041015045034461032072010007111200d40340031f080581440c070710751701040002202c0101c1c080820008101d50605060030103004004000840d024071250402d5021342151031204040c170011551135040c003c0c002c440801c112482e9400c3c0e660200400c4d030752420741c800b00c00002e020300c0124140304140054490014000e42d90360040045c04101d891841c244142c0d11118907 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 707582706 1250 707581456 707581471
    0x50f1c030f140f0315090403020d0311130e01060306052d0f0402130501021b01170a0621030f050423010216300c0b030a1506050a03060501091d 63
    0x58400c200010b5108020f015103403c42d0083c1ea80384d05160004000103070040c1000350207004284100004264000f42050211340c031810006000c1c024071001000303508c148148400505020500040c42e42802d540721812540996008c00c28603403074404015502c2c560758115000704403a030031250445061402201c0582800602718000080280c000c941a038004000d0903a006a83c0503041019580510455030070807002021180080d500c0340001c0e11024085001c103000b82c580c0c400281d41210f090f4400c901408032030410001101d40048038910410200f5011000a8544540d0512490142c01903a050300e03000c0010040303c419250981c22484003802c1c9090461042c1e0001e125500144003844000c0c2151401070640c0300490b0800e00c5140c0307001f0240d4010107a64469034008591528041800d50f905509030b142e5035183d9220500c080d058914494240c1000306030700054441c1c0007001001d40040320784040c000b00d503640d00151074a580c1032003608081c030001d040700c0c00203039080045540d1101e103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 707583956 1250 707582706 707582717
    0x906060843180b120303070801050909250803040b040f0f0308032d090703210807120f18060b0d330c262703070b070801050f1c030f 58
    0x203101d0002103800280c00c80c94945174000105100c101c6500c00c0c43d19000d0720f410b81c6c1c884d0782420807019030384e40d582d0060041c1c4800c4602a40b01c0041e1b041400383c0c1402480d0b882c0441781c946489880c5040700360320a10a400e0404001040051042900c0c024401160b42100c1c1d82070450703481c2c5c82d4204140340076900240c14030b11241c00202d480c12441041c18001c08100d0014100d180c05c6241c03070108135464420780d1500c540020200200d0700c0e805503c1e1503010b4a00d14280011741c80d10a01c032009002403400a00940341042801031003d06100118151540118010700601fa00802030100c400c6400c040504488400005003410400071800c0c8000110002a8008099603d45408084501c40c202342c0c800258110074440a9441070048450642c070a5080d0301c8085c188902d0b142d036581c06030650145070701d010070b06e80420b191051041c2c50f6100c0e00814031080c3c0b813030440c5c00140035500c24020b00b44600c8602c0f03060025420318410b0600f001c0820030390b190310b05c845a102034803940105042c1c90300300007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 707585206 1250 707583956 707583971
    0x3011e030c05011101020d150609080102092404090501030602091c02180c0f03010b0403060c0f020d0f0c053004052209050a0b060a05090606030406090606084318 71
    0x100b188079420341001d0508d007030364202e07040540080088400358004800c503030050001c202c2965407010004c21654030411041480005520301c4159401690b0140c800180303000000801d1002c180c00802209034100e40d075502d00040b4a8510499074080440079400c61024a05881000d5481000c643c218441c103001390309200007000a030840e03600c240c2180580300030101e0100200030580c003d0785408140c6041501e03000004200007540d5007800c015a0040028540310007043c2801031092100280d000000c0c1d90600315510200009110041261100340400c4a90840100700c1c06040d00d0641e03030001d0034140401c090700d00100e04100d0303d841620200750f4a000034000070703008010148680d0702c598034101d030601c1c0000400403080020b0340854001d2022008201751940d40000f1690311a0b80802c00188940e080d0034448000c10880d003003a209072052884407507000313030542c0c0821551090300f4241c50089228003e00c402e990150345070303400c082c44103440900c0385581d28084000d000b00f80b01c2000a004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 707586456 1250 707585206 707585227
    0x7030506190609080714060a0807030b060a030903021c050406030b151c0e030a0c021e030d27060807050a050904020d050114010201060e150307050d0803011e030c0501110102 76
    0x85101e64001000309880900803c110b10043c0180c1c0c0007800c5ca009002240460100811141d02c9046640c00800c442c010008406c0d0740650321810840c0e40c041c000513182d025146014004142e001002c2c1c02612407428018554043e040e00521034202c2c80d643c2c06d0a1601d042ca003580a400c902e82c1c090340c45910713201c4003900502c0c96030280000c60700360442c4101c105075810000044595401190f44a500200b0800c205180c2010036a041c8039030640301c0101c000c40c888100b5a03460307000900c20758940600420000c002d40e00c03400c101c0d40318821442035051030031a241000c404c1c0c00b803446040e0206801100044041e4060400381810b254079040180c54040d9001c005002c0b17901040b61144950741d00d200510003401c0c0b40d2484a461202030000f0080030b820202c10340b05c040c1c401403101060f4100b0f440030148645040c00404c009190203000030b400e18200d854220100d4200340106105a0f02c2210449003650f110303070002040725046000421410700b4a4011a10300510f10007021056401300039000c80c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 707587706 1250 707586456 707586499
    0x1c0e090406020928052e0e01180e0f0601021f0504030306050d111903020303030108060411091003020907090b0a031b020102120a090609020303031617090607030506 72
    0x80d034490800140ea5243c0c240800182002035107140b040080988901c0083d420f0200c031850035107004031745483c61200662200414850002003e15042180c680744144560700303c440c581e541c0e5030903210308218a003106215290071406100d0303180c03840c4a10b400300b90b08401c11114150071030380c184103450700d510b0708008041800e80250b800480c003a581c4d80401051603450f1080d2400b0b014201c51240c94000192a48200c20f10390211031071003564200e1060038090180d000150082d54080c0c1500e440b5a5541000c64489000301c609407076410110400c1031892510b020481c0c410322842c0403450f0f402e400e42d001d0000a0134014003440902001035000b00301c14240300050a04a0002d54005c100e407002001001c441c1110000981c00396070041c080c00e00707050740765100a58030212180f0001400c00080c28884094822007801941602000050280e01c09011060165502060f2a0704220032170380001072901c110304071965801c40e0003079404511654407a07080290401c0000b0564072a415112019158 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 707588956 1250 707587706 707587711
    0x90206070210020601031a041a0939060406020709020a05070b090a1a0115030b03070902120405060f0f0f0a0912170c030106050405090429190504051c0e09 68
    0x1507481800104200000d01800f017a5030b580300a660841f6082c140e07141c0b02c6203054040401c54480d612400034203420030800c0001080d0a416612042c4954900e041818100c0e000d4022540c1c0304c0c1d011141030b40d60070680c0403981142c00d01e50060103980d1510301102e0094004010341b0040000030420381c4041a05100c1140c081c07a03099001e00580c2080389015035100c201c02010350440d4200d20010021120000001820050a41404100c1d00d200384002418000c8940200d54001e1000c60f41102c102c155040e05442907104601300c0b045030310382e00080c0c2c0000d441103a4110804028100288070604070040072070700300030b0042001c5031000c025610707404003500103405030300040e42241c104003603524020281038001d144410502d10399410480003c06070f11450241a000728101c2c0c001c9030810100610408003070250072061a41103c1942c03040800e21419200407032a01041088001054018411907000381d030300200808000900c0d00e061180b046141d001c0005001504a030f521080e15840c640c2c62 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 707590206 1250 707588956 707588989
    0xe0105090a0902060d06060f03051b07051c020c240403020d1b0e0604060e01030c060302030903040902040303030207060b101205070c05060c0a09120b010b182701060c0c05040902060702 81
    0x6046c03410624002c0a002007000040304160404040c01101c001c5000315140a809046d003107643d9440070b0a00c18600980c211341150341c25410360b5203e41580c1c0c0400c1050304080f0071079156a12001003602010000b002c8402001024020841040103107020701c040388107a842120b40005109500103000018002d80e8030080c00380110b84104900d514281c03003004007600c00003170161610350440e02c4403c003030302260060a0070b1660000110341c080c1020000e8600401e201e8109660399601e07881c0c0240690040304003283c103d8100000000b5500d071032101c44200703008540c0c407454074407604d0030f41c04040c000140103041401000460540801c00a100c424402c031302360300e1002d940b251350200040c03070510107620600e50341c26040174500000ea0710320320303032411070700c0740e0041700d0f20b41c04d070f41000446200d07035003c020740d020000c40e07541c16031640c882c02d0f01000054a1111a8100d81e1b0f9204107860040500308024401443c01500348038601d8241c1c460312159002034207083c00e200959010641d800e004101c3c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 707591456 1250 707590206 707590211
    0x40509010c0e030f030f03040f170405040f0c0f0c061b1d040e15070327140708031605121308010b0303090a1215020307090602010f02040e0105090a0902060d 69
    0x8680307058000e0b010b6018000b081c2d0080c51000310016500c2e803240038800300f03e003601d5000004a014840524285c0c440703a03800500e651074004525580301e40643c8641300740c1780240d0400402c0c039920079052150014980303564540c00d0720620000d0b42200e909210203802c40324031341e403030300700d4000071130705151941180e0007544800c3c4c404082d1004035081c46100074100e900c11410610440201280401c840c0841d00301455203111f1a03d800000350060528501c402a1a10b6000305101032201c000000302a407602076070002d0074103c5000e01003501c9024a014030410341d4810803050001282d4581d0900000d80541c09884403428100c06a20aa0340180644102c81c82004018820f03881d081c49a042450030403001145484103801c00703d0f000c0038a900c10900f040c403004000d0340512001201108510982c624119502c1c64609070141520303615004140c0158070340380301003443c04242c1c805c45095445c040100180f41e0b10701800c01c183c4000c02410320400d55280d0307040c100140c030f07103801820456072401c001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 707592706 1250 707591456 707591471
    0x60801090201090b210907180203060f0109030308010b0d0b0d05030406090f0e0c2512020c0306040521160c03020f04050402151e040905060108130b010e1504050901 72
    0x14500001078210a035a07036000c122100a10742803045000b07a175850505003101d103a844d07111190070180c5a9000003204e55103404015641d08081e170003075110340c004581c3e280003041441e0045500c00d4403804000c02042c4460018030403481400058403080725070b030901042480b001e030b000ca25000401c2004580740c1d400400c0c103000d46500054480c0180c412440e00fa800d062902c0c001030b02562019040c0c8101900014180ca119208003004001200c1221105080d2a1603460031120401c980d00102005000e11403100220349808070341c19001d2074010000f0300803c0301c2ea1250131021054007040d905040e0042117883c041802200180c00c4180c02143c020407da441c5006100304442c3e511041449145498200001665104c07250029100d00c41402da8988046082030120a00041200c41d1142c0011600048840880c2c100b644551002e90701c0b0070050300e42c1c081c3c901d104a500000101081070004c010300c081c2c0f0340301058070380c002c10b251003011004140c0d0f03020a0880304242c4407045141d46407483c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 707593956 1250 707592706 707592709
    0xa17030705120f0d110c0109030e03010b24090d0507090504050607030506330d0b0301200d09020f04060e090f1b060f120705040303020105150a0308030a0f0608010902 73
    0x4105104140b1280d414078043c001400f4018074030820950390501c07543c8030388041a442d1500c05641c40060000000c028070398080c20068144900d2540c403d12940c204000200c0301e0900706200e045a003901c403080212000740144000240e00000b0343c0caa08410120200408120100003603802006102c1000910f803e04d81007041c10210f00626040605060a050002684844404041d4135a41550104062500300e00b000312041e07804e545038042030001300b04086c6444d80340d4820030090400320003c1205894400c0c2d4107483c0c2d4840c0c1d0380c1c030a284005000c2ca1401441d190000d81d0814030051010380c100114400240032a0003541046168828039000c01201941c00c02c0000e02e8130344001c000b064914001c90b420010b009415012a0243c500032030801011000b04003903c00307118440301c081d07900740340120004141c1d801c0de101c00d40c010340c2003101180b44404c80444000502c400030380350110b001c0c00c0d91503100d65588003408440e403840d55410000e6410003d44610800b6043c00d50000c07546500600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 707595206 1250 707593956 707593963
    0xd060915020a1223010506031005040c020c0f0d0317070903150c0f020c03060a18021507120c08030402060702211c210b010215092b090303030b0a17030705 68
    0xc1000302145818040900c1310070710340450742c1140c01c2258559a41d6540050302206100760342d108940107070a000200901c59000b24004607a840203544600c1442440c100708042d220007608040c010a000b070040c003180b07018464850758071054034103000c4c00306607a07030ba11222030311580716001d04525650500c00a18541c0201404421040c5100420102140500094607100040c1c0700080e0241e0b00c44001000358800d8032001a1540c000304174240040561503d1161a80b000c0c00440d42815002c221111031800703408020404d542142d00381c1c1c2507035030b9942480f460703500c009401d0340c0c0b20030b00700400d5040c2072050200b030142648c02c00c05460031114200a501d14010b01030f41501c01d0142100000ca250b0101802e4007501d0448880c01003410480341d03005074100b51680d1000c1245081d04800c204221200081070040503040f42c1c0441102d45400700f0015850005012403000141c0c1c80c101000030910036000140360b00c80080c06110500e940d8404564000b0001500072001d4002140300c10030b0001c2070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 707596456 1250 707595206 707595221
    0x51f0c122606010f0315030218070f0503070905040b062b05150d0204091106040305060f0705070f0b100f140f010c0c171f0b0a060e0d060915020a12 65
    0x8805011814558000b07031584c0800e040440c00c15513140103181ca0604000202401150040d1502402d04010440410070110484041000c1043c80d00044d031035500c1803013101d2080c1031580d0344c108503a043c5004c10000d80680342140768808410f2124500300c909030000c604080382540c0350322407981c05c4410300700d069450060441440010211600b9866120b0100f900400742d4101c0c0d0000710045645014002c1c82003401d03030306070050000700d00481084400200e05016041c00e408000c070b0f950302d07800115071314403440d80002d03c0e2500c000c0241c0000f40944d404c00780c01250000701c180d5043e469aa0303240000400e640101c0311031409c12000e5600e0b040c1413550100c102c0302842d00602001d1180c9032941014060303c10442c180b56622006030712800d05000c044080800d4070030a48074501c031201c0c00c6000d080107482d040e10548034140b0018250307010b04d5211031401c1e006070000000a4103a1a20780041600750016211748042c80525803402c6203e200602a480b488e40710078050245a040c0401114450b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 707597706 1250 707596456 707596517
    0x51308011a010305270709051e0c071220010c0203070c090506220b061216021c0309030c0203010c030507110102041211030f010501030c1e051f0c12 65
    0x1c00050100e09107215040882d91502e01400401756410000240d151801e141c1c041c4a255160406002d5803528883c400c042103c00d86d402d45000b51111074220042e84260740c1d00509840f07042e20440c000500a1011488200c03503803100003144821324141c079084d078011090110050b04002056001c0010548421f00034143e541e4040100745001300120301c1c204c041c01c92010304051400e003000003e02c1d0716040740d080384801601242e10f400300e91100d100b020500b55048900d06041d130010042d21072000a0801009440164150541c2c0008006030700504100c6419401c20801c0c00003000507844c03d0040c80108c1d00303513980015103858440d000030409041e10700103d50a0f40100800c2111441403d40d003514581c201500a18a24040000030324000b06001024441e50030840000305114100b440c03e403c03680904150141d00034211001450055180a0790b0fa11030103454510a0051060180c0a43c00b8214145a0b18506403a01e070320001808041c428000202d030700759111510781790400c040c40003901 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 707598956 1250 707597706 707597711
    0x602060f16030b18011a03060d11030a24050a09320f150106020f070b03060a030b090c03010b0406051c06140c0406020d08070206040b04050712110a0e0403080a0c051308011a0103 78
    0x14041d0008000c00c9149d0009040100a048140aa940d060001718981540040a1000c0e02111030514501d00ca40203c0201e40b1407600d00015080c0d0224011110150742c007418203030384160b002c0030500340c50030100c06000709540d00303041421a9820400480144600701d10040030031001c031002d680c041c4134058000d0300c110740108a841694004c001440e02c19607021031481500d9544490106540f24090303803014200c004c2e402c061010b100c1c03000c42c503841c58104c01e400030302481d00e0510a00041e902144100754101e8111842c01c07035501d04805414280d039109410110f42c03261400c1681e40740180c181c48012000d24001010000d1503010440500003505504180b01e203444c00c40780180d240c040082c000341814542d0030000f81080300a04c0041c1c045e049103080f20030022750300d09000450b1a50b83c002c903401611020b0000c02c04040c4070070124492581035440070240c0d9228001d0390068200900410244241440710b48803624803c4071b404e014252420000404501c40201c40551035400001c1606051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 707600206 1250 707598956 707598961
    0xb01300b060d0b0a0803040303120203330301290120010204030b0709050409120c330b040506220b04060e070315060f0e0303070807030903020a0602060f16030b18011a03 74
    0x940224031414400c018540042e01c2e0b66446052040190dd01a1340e141c0310140c080c00100071000102c030b5000710190541c000c0107680e2401106400d4589016402a200020381600d510251300c2008030300041d81222800700c80a01001e00701a003a42c01076001102d5009003c0108480194880200001414101c41c144062059600c8090b081d910070b07c0010700304a4042c08007400d1000c1c0101c0d0a100c44d40444900c14a107617622519011f030440140500c60f05800c3c06404101840c090150740d01030302c8c0081c4490307090a10002c0b2100701100c4400c213802034a07190004840c507541e03140710303c00052903412641d00b000d00d03181c5801070440e000c0c141603400d40c030000c5000b4010158004000d800034042da0030030080004a0500091540c015010020a08440081c901d03042590004048080368800d580404101ea1140320503070700e400c011119207041540440010b451a81c4070900300440c0d44080c200014600130943c0440c101d071703444e01050000a0751000042014500b081102118110100b82c05401d50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 707601456 1250 707600206 707600213
    0x2150304020105250506090610051f030b0a0b030c0405010e06070c050613030510090606081c03020904060e0412020c030a1a1503060109090302010b01300b060d0b0a08030403 76
    0x2e0180035030721a8644140b0040300400074071007000d002500c1d00401141c20907d008001d0079a1800210352a404030240c0600008032414044c09035074420403c604880d2141c140b242c02207008106880c00142c2c0410082400521020782600460041143c0c14a4a81d29810103002421a09084006600078007042002c000440c2982803400140c80048501964030701d41c001608111507242d8001500c00d01544641c2c00303440d09075038441d50846124000c14807202d56180c001a844800e19069284404030034400389a0300e074401d030700500c1041c400900001e0007544920107940072440881c0e049850049070654642603503010480d50580079401c80c000c0c07000d0051742c2d032100740f040d60a003c13401001c240c440105c0c10030010102960340404d4040c1c101d6541e5039581807503002400c0d84034410f03009540382002201855101d0f00554070b03551031640224056100c0c020b00071148100c44200d2080c0070356120401e004569403000105000444460b0100355095100c041240c403d60300d070b0000340d06900400041002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 707602706 1250 707601456 707601467
    0x1508040515040809040902040e012f040b160f0b0a0506040f020306031f0906111309050c0711040e03040609030c0902073f050408060703060303120b041e09021503040201 74
    0x4c001d0240e0340030032099168400715010707003c004d00e44840d6500f8415050740d011241c0000c000301900d008142c0484030150203030403515200301c0c0645aa00c4900300201d1865000c03c5102d821424802c0c102d21078405081c0d01c0340400e00200341d602410f4030340ca80c0d082c002d9602e8107018400c1681c0c0180d40c11840d50809800082d990b00034050b5920210118115101030742880b0b078404a03009800460a01040203550314040c8103a01426072141100e04440012520040724880d10f48100e80d1112210300e014041e1301d88540764a84400520743c46601c420303081a02000a102600050055442d0081114158604902401d045401c2503a42078070622049010075040f07404000340d034154035010307040800215011f60840f500c00c2d134101700c0c0e6034001d0080000e50382e102c0020400c507096507080c0c41060b156180102c2c20303580765200140000c1c54844204181211560209210007401403000031041e10003540c25a49109403450000007650300c017501001e606080c0c108000c0301c81070083d01480c600c1e090780040c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 707603956 1250 707602706 707602717
    0xc0102030a0e010302090306090606150306010906080925050a080c0f0405040f05120901031b0e0111030d0501030609050f240a110c0105010302150c15090715080405150408 75
    0x2c000d10400b00c016039074025412075462030b04c0a02070760207526148000c10b5561a00740c030014024075120500d20030200e411400c1d01e0190070140d40b1540d116150400032100d1751009095078207140500d009a64140390005140913161011340e622010151900082001c2d0044d550b01201d81608135085d0100f0aa807a15006070074113608a8000070740c0e0705d443c01c000c00f5050750010020200c2c031400b00501e02910841010382a4100240d90500054900050920310503140c41202c0000c101420003488256001c3c516046442000030204c07800c0c068203103076070b00c166a0207920580e1207640e14140308040c40828802d00842035154001001c080001c8400780340041307850f808100e1442030100209031104019005018011b513024100c1c1c0c0c4400b082d24015000b40790030702c001c900c2618102074031014030010106580c840c0c8880000781581c2c4814049860344918020f100300103900818102003070004010140d8125840250f442c4140b0f40351602d80980b4240c441044412044240720401000a2080003101d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 707605206 1250 707603956 707603977
    0x1401020a050d0207170f0418090305072a0b040e010902340629010e18060f1c030305060f061804060b1b060a05040c0e04081905090f030c010203 63
    0x582d00c0d03466041060040014070706580b18032000107406e03402c618415018000341c1c0d003900e841d00711401810060030704461000d039008010800038004000420709190b00032041c4031405140c000f600d00039200015104480c1d1304891000074000c40c0501c0031052441c1014054005100c0031850080801c152a034a402810200c079411030f91604100d45140002d01c20b0100e565100109000e00450070141c0200d1070309014641081040444a015240d0300c903003042001b0010240044a0320020389003864840480200010b8101034450340f183d007540c441c0030f610348140240e0300070469040324616000342911400741c1800e01ca6107810f12111200d6031000102c94240e80462901204401c8020214010303000550103058000d10102c0c05070300301b4981034070201c54101080d040d2840b0755528602842128000e4034003410035292603500344605038185c1203050f0490b01400a4030f00340440520f04a10100c0031221507000100040f840700900d00b00900f14240341ca03001c4014059020019000070354901650b4000c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 707606456 1250 707605206 707605211
    0xd0c05041d0c0f24190e01022b03020d06030b04140607090e180f0a030f020106080105040803040206030709170309090c0c2a130615170c07080c0f0a1401020a050d 71
    0x5021000100100e6042c0284400a42c611001c008000342040080d4141b00703000d40610440207100c02641c608240c80c001c0702440500101c059440102d0094004078480f088140d510310700407000c14020600d4503c9244111a9400f04280241074541090700180071141444003c0d001444414604c07194164014014003c2d1600a030308490101d192441c800441c003518080c2c1d07141a8281540540d5400034180650020300049540f40010b0303003240d900729009081c05030b00380049001458510002c5070001483c0c80c01118480d195103410b030b0744003000c032000c0c9a103500000f05442c0c6401d040e4112a4417048240c9013030b00b0100288800741d20b400c01403034001043c2c2040420a0280f005202101c40c1d44100540107400354401c0c3c6190a00520042c083c6820103845021440b682d10f10034403035000c0d00e802c14140b40030551254011018160400b660885500d0f8050211848049081041c4491480d40b00c00130081c0359920304000e182c0c10465580c50700c1c0c41e4010000c25060756084000c44900020350b9600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 707607706 1250 707606456 707606509
    0x30405040908160f1709030a140f060c03041b0302011220040b0d060f0b1803010906180c050102030a052b0912020f0a0308060d0c05041d0c0f 62
    0x50219407084026581005403c05036480c01c0c0502801922405841800c01490800d08038209031500c0c00359652241d8950b00084070080040e0000001208503d4110112030900310303802c10351800e00e18201c0305110211004000c020621202d85019200600b4101c400c940c42421078000820041005d071074440180d41320a425031040340b240003402c0410346000e0070141c9035500e4580980d10b0b03a000314015070b0414100709010a01c0740b40040b440048905000300a444d203205000004c9100d503030740c80300581c59582d681550300841c45901a81c20071202d5941c00c0341c0c44c4251440d0031300640819400c16030441d8000d0014144250300601220002c01181210002c800c1d8030403d0086d502401840b0401d05508280700102000704801c041e01c0342c101a0340a6801050442032929614120544050000f40c048000305034142010900c200006005025200f0819150408074090b03c50b0441a0600742100c00c0442d102c428050040d210b94001c01ca41c091585171180700010740003d090070000c0c0f50040c04940 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 707608956 1250 707607706 707607713
    0x60a090216020405070f1d030a020d0501020409020d0605011101060605040909020301060302031002190c02130e010e120309100902030706200703060b0f04140703050901090f0c0f080a050304050409 86
    0x70500d045075004005010514018200030700d050a2080041c011400281020071408000303054482c84131000350061407611460f40070440d40c800c10400684040d5805c201c085000b04a50006000c0c0305201000855492302d000001050701c2007000d95480b00e0707498444140132440d4401d0403142100c814900100c1c0802440c00001e005250f25400250300d44078000c500f01100049401074282c0100c19032440e80c10b4541c1c2503055a034030b40c0a200003580308005062504c085c40c0564085450040e504000090300c54200100c21f2410072000c88803400080040b0070020000d208001071001c1c1003088505104804055000c6a5104054042e000900c0072214450101c140d030078007214414228541101c00480d074a0a20300010261288607901901040000d2040f90409000300111440704a4494050341d480c11001c40080c00c0c090039040965480d1503c1c980805d07c01c000034203102d405043e54a0301c5030302e0b2201c05482059558403020241d0080080c0b28049138002c001d48084410035240807420000070725 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 707610206 1250 707608956 707608987
    0x16050a020a02120c041406240d0c0333080c0d020f1507290f0402280603021909080d0503100e0a09060e160b30071403060a0902 56
    0x1a0480d041842c6c03990307070b1800c410b0300d0088a0041038160352070160701c4640b1a420070003408440440001506c00c100825014610f0340c00564104514500041e0429030707426111b034025681e0001d01154611690484044603a8824001c0100b000400601101c014100400c0c51000e00341006846003440300444001b035111100440b0840c0d600b0b400c100d40d01c5000749090603510300d081c011034005071078090307255a10846c100780c031703030302807024010300355901c1d5626420407050203000307100d0f08545810740c204140e0342508200200c1c007034141918096129a407001000b02d8206050800200308600c200080100c040c0100e06460208081d10742141c0e00d90b070300c2800c0c3c00d9140d11984602901045141000f121081a6009080345840350006209094070701042c0341c3e40700c03000040808048907408040000c80045030042c02d2000b0b8580340100c0b1781000e0060300404007004602c248120700701f042002000380e4050b145800d40d0810321442c03070442c10880c0c0414011072050180c03248082d800071f41d0000f0220003c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 707611456 1250 707610206 707610223
    0x6090d081512070806010e04030c081606020d0b0306060306070507030f030b06040605520b09060f09030403030509040507120e240103080316090e090616050a020a0212 73
    0x1a1030030420b40210300302c0a64034881803090030424080e40001046216503c031000c0e0065405950740a01200e5a444802981c1e000501d004000c0394040c12601c005015400a0704c0d5200d031440e0009400e013030b1142498106040282600c2c843d802078410090750941003802d659410b900340ca1310000710500c4035000c0c1c1c014552400441c2c0e1210003c100051038540c44001011410480c00d8a050324170402c42c7c0c0c0340207489980c07180446a500b16000e0f04040050310b42810100d088007001e541180341c0320303104c40140071b80645841646070003000800600b61191701d882c98214040c07000440c6440d1650310010218050a80054840e80e11000800c4807035118440303100d48038616200c100180e119034901c440e80c942c5204000840340b80702d41c4400c20080071915401d8100c0303400c9807800c0d165540d052003054200c1d8002442500303004e204603010400d111900b909910551254004180c2c5041c005d805071400306140305c00b0020401c08001c0e05008560110b114860998103903602d060f601c80170300c0c220b400c09140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 707612706 1250 707611456 707611459
    0x31a10080a0b01030c271a090c12061822061407080903040305031c150801020a0810080d140d140402040c02120406081b0c150906090d0815 61
    0x504122200384540c00a0043c101d82c4500030034981941d40d00c070300c003807031082d6034544200103440309680d03043d8040260800c0600c1c0b1100015200c8907100c020018040704020b0b100d02c026800c011900c0e5030f040780c12070300c0c2c241c000c68101d844850720720301e00d804075a5010b4002c0c2005107026041c080c131032480e00030a24401c0c0c0b082d0300940920200401c8102040d2b91a400c40c4c1960020b0281004200c280e2070110440c0c00792030b0020050b5140070948103180707205054250014404d5a0390784070140c401544a5140c1c0c002d411030100143c0e1313980c1800b000410500c80a0800000340b11240b0042002120004407a818102181422001c8505207070301b2030410b024000c1e108460303908080b005040400190420b91080b80b0803281000103142030360ac01c0703a65255030010240b00c201c0400041c4491801120300d20303817003029107000e080303900c2100c5015050b94005244502d402e620050903c040412031500c46684200550018421440c1c1005a150340f0041daa02d00d0f814844c904001c607409080801d109070710300d0310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 707613956 1250 707612706 707612713
    0x1b050a031707020604030b07020f010c08240a0b04031a0601051c0e10061401091706071b0c0303120b0405070504051012050702070e0717060f010c12080603010e0106031a1008 76
    0x6107400040e480c0d4041300302b4001c8a500c5c2c5041140f00d240140f210601410b480b0000c1e40b80320810039585080000803030b0fa240da221810100003e0700c060180000c002071845811032240200e01001c18880800015003401d05014081c041c030213254007080e114009640840380045251000b01a04030b0030100d061421018403030400d00003140800200032407901c0141c0a0741c0f4680000d42ea42c0300a1a402600d1140d000c160300000040750316584034541010121907401640c03072610032141c0d144c00c910391190303000721b02055030300d81603195070b4a20341325010701001c00351000d00080c50103090017030941c0308601406108030015500c1401640c03080140841c425aa40b000b0040ca007455071029595102314401d540042640900180325180705450510078030b581c3c030000d40043e032107120070012070350040c13400d1504100b021b412400c0410010001500900340c0d0ba1503214481c1426030a1500351612003840b00d05980c142001080087c403805001c265801c009524850161540103498441c3c044a900003a480d22 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 707615206 1250 707613956 707613961
    0xe060708220308090a051903120212030f010e01060e0d1218090902031c02070302150f1215010f0210050903090a03050102180f10030c030b06071b050a031707020604030b 74
    0xf51500814040e5000c9030066245950f0310300700303d006c2968040e58103100d4182c0300100005040c040c0c2c203201c0c0c0c0e8810f0041c0c40c6110381c1550501426001280e1441040c44031200422210000c005000d0242407079140a402c460b07c03c130f01180071100400c00040c07140da0640309100c4200c0c8161007414009162000504506550b0900341c000707099810810313071081c02841d901a07038010041d40004030b9030000707030040c11100d80f42d03800700010000010004048264100005580d4440c0d000c02003582039162101400c9908011071100c0700c00781d6161256040c030080324a104c0541d500060f48006009070300501041035079035148100c0c20b500610440c0e0380c2110184801108004064020700100b003084002140741c3d0482c2c0301004204a80b0702035054000e2000d1841c8442e02d44a41c1240d0001001410701050f50090b110103e030a5034004c04058900da500103d58011024144941c04020401200d459591504580f50205c1d01b944000880f150b0440020381c180464580384103032401180c02609904051 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 707616456 1250 707615206 707615213
    0x6030f0a0506091203040b0a050a0902060304030c0c0e151e0d030c141209010c02010216120201090b0f032208210702060c03190b03060a02190e0607082203 68
    0x100b000b52402c901a005000718242e2061100b0700341c900c516040b0000003060b40b68004d801000b002c0141c151000c0d1500d6502040261b180c0381d00030f41c043c41c82569000300030310036400c00e05001840d139000b80f90b42e241c5144c140301c00c04281d002d41614020040f40c0d803500b0110400401003d12400454194004451032612070602d0340040300e200c1102d00610040c4003103450164813540300c0c656601a81035801c014044664154480c0d05001c4015106004031f42a82c090804101c0d914002039000f42070004481c0e82e15003c41d42c0c0300a00a0080c00e4904046d8140428042208074a000c000c001d082c1c05040c4c0d00c0200886418440394600e0382d034110314515070303600c000464403015050b041c40107910500701da00482c05107803001800612654001c0c07401421920b8103036150340f0903441c1c01400804292203090030320745d40c2c1d014088075019412200006a0b2024103640401300d0b01c00d0545088180601d00a03840303090744401040354040303640f20201940d80e40c601d47c0207403d03901d0910b110030520550b0780c0011040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 707617706 1250 707616456 707616463
    0x71b0801231f1a0901090609181806050103150b040509070308280201020a09050d020901052101050a141807060c0327050301050a09030e130e060405010c14091806030f0a05 75
    0x4c0b99007a030322404a40e40310a000e50b598001d42c4142d6420000800380000ba6004592141c0d80740701d0750f010349002010480e11110140d4000b80c1055a51706100084000391441500c01c0c0c400c603c1d0700359004c0c03020746005001503890341811f2101801c000030005103030f84001060700e083c4442711002e003200610803d4a41d4028005d401c41c21000d030200d05c01107c00f28003032a0040c2581e401c1580201408200e82c01d00092040703450044400d074540301140c00501c1441c49003030007944c2c4580c20716440007031181d402d402e07207403042100600813032745a8070304840d4202c42c2c10011a407031080e14040d04110624580c20310381103a41142140030b684011030040c80ba484250b024078124011148114001d00040d2035482d040c00031641e0040004010075030080002d44241415840e4102e1180460350000d9410703022203400e400d1204c01c4404503a1655500c2c00c102e825500140c50344d500714810402c0304c2c2014040e80c04201d0801110305204a180d01002c00910340c3c1d074081100e03082610801c829103029200d80d2810556 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 707618956 1250 707617706 707617717
    0x2303030307020a0b060405190b031c02011a1012050405070e04030816020303060a03150f140a060f150302070c1e0306061e05060c0102071b0801231f1a 66
    0x2ea9404c10340c04100d0504c2c0500900740210b029032040030802c0700a91200d00140208865036030140514240c661b03802c3c81d200ca882a5000140d0004140180c01c0072580c00340c415000302d802c0c401c103840ca242d00155603104592881c07840342c81c85e0014254940e41015850620182e1180e040180840204800c0560111320a401000c8444071003407118140c0400383e1700d03030104881260700084a1401007021654a02403841404040840010f1540c1d144a03d04103503007032030310340b40d070420001800d10005540e1403180700020085d24201c0102d581c1080d450b00c81e00c0500c11070140070103801055600900a5a9441e9002800400d8811005405c014502c110300c1105110170b490040c50900002124958039500d480743c0214080d00040f21824901040400d40200042c0b448541d401d001400000e10003034001c0c10b401c404018584003043c941307024542035a0100c0052900c4070454020106030300c1e058295181c0000e050001540c02108410341010081ca0075401703140c0b030b03000d9a090b0100340c20501d0010078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 707620206 1250 707618956 707618963
    0x100503030a0e120a110121020a050c0706141204020609030106080d1215060c03050f07031e02012a0c08031302100c050307060209040b0613090f0e0303012303030307020a 74
    0x6850001c03021002d034603800d0700040a042c4003000c5e032000c241c0390b20400c8061040305030f15982c00301c900c0d4a290b07030b00c040340c0001110030003240300000d64418903402000004024251407030450500b60280c45156110f000d210151001c1c0034003540401c013150b0f14032081e200c495401070001c009269540180743d03030741d0443d0400003021504044040c0d81403c2c3d50301502e08180c0400710b00b010301034075103030b4110341d84481140b085c3d040041c20300010107010340c04030007808207070300940d00d80b03880440310920222481d50344034200041d0785c5070685039511441c81500d05402c80c012950850788641c9840342c10340c0d0300b40c0142c20080a8905c000104038036610042c000080b140d000755050343c02d6142650041e100c00a0b44040a40b06600a01810780083c5d01900244002000900041103e060000110740075420404d02d40f107504009000c103120040b018410b529545003050000d0210110005401d03440344018083c40200c0602c0003400003004040a08d055500312024044030341d0780c03500041c003d4440c45995003c0f03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 707621456 1250 707620206 707620219
    0x303020702060a0f110d140702030319020c04150608241003061703030c030a0b0a030c06020f16050a09020306150f0705061f0501081003020310020d060f060e0108100503030a0e 77
    0x1034881802c0010746d8800b4804d83e40b20417448021071100c030003c681020004aa0502c41007001d1140d01070309401a01011015800421800103004104020380d00c2e074888243c40008141020019241e008015a41060451100111030106007104001050540303920720f03004050600ca0f103005a925071b0000f011110305111884266458114143c0c40380b006481040a0302e10038408108134800c5a400000451002402200321665940d26018601d0890340000c0250300460011805547d050106500500b06a819203800b1810000010440881405010301080e408400074000e9100d40610032100b4040a18250b10742035201500d020941c00303aa0101c0d1035010310300c040b40c070000b0380f00c80411001085c440c40643c01c9003410011605100c008100b030043c400f4401000002d80c0301480001540c040114015907604d0306458041c2c2038a40c10350040d105210070800030840343e03600100b492412034007403038800b01b5510703000103521202c0aa40c000780d900d400001400210305400170070b40704d0302e40c000b903508 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 707622706 1250 707621456 707621477
    0x7020d1403010302012003070203010906020a08070206010b0409020a120216030f0e060d0504050123010819080a051303080a050a0f03150308030a0e0312060102060603061005010c0303020702060a0f 86
    0x1038056020038440240480c0080c2c0c0c4080c080d5800c2da85840c40c008580d0101e81c14022650000707400c0d616078900035120072344e0020b071042003607130310400c01640803000e40003c24495150402240242c481c5100d8074680503408200c140300740c2c2c0305855007202c0d40121031095440b81a0425201c88021040c4021030220312401c4011451078000d00342140c260380010403890034803d0034980d034000b401c4024011513146d50b880b81454414090482d15aa0034503005c6440e00944d8101445546090080303031607808032180c100344210002c3c8141e82103035407406c560b140840e241e442c504411085006541c10080241c2c402150b101d0740294007101030b118034038a50744c81c0b242c102e0300d900040c2d0894402d00014841840003000510219040034002e54000d4201c80f00041d4640c0110720f02030942d008031881d02d810000c0202800b21647c1c0c10440c0030f800080450241949007400002903c0c032598500c209418003500c020907906250113503040d140e500c1d40281003265110712851005068546249914000c40d996940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 707623956 1250 707622706 707622737
    0x1061a0d050f07320a03051f03080304080a0c0f060207060b060c0c0d0228030c09050601081816080c010909180f06090204060305030414010f0c02210607020d 69
    0x1c050b001e010703503456212403040c080013030311040c2c05501c2d02c01c1c12040c000540c400300070790058020f00300b1003115900000c0f03a040640510100d14080b1400c3c056010503d54148040f560714401c0300d8009a010949035600c50210302c0a86071840741d00005020004035140050a000f040c0d0001c0002c2c9200d01c50030407041e869441000b0007402170320906280c03a80400c0d103400d03941c2400207421042c0e0740001c014005252000221328404448040c9011100c5001441002084008046031014082d0480e05101c6464031000082100c1070080540c020321012f105a05081441800031421140ba0500c90040b00c0d515803034589e944454120119000401054001071401c1c032500c5071030341001c040003070004508020303101d11000314100d0f4000c0c0e5040c1d942d040c6180c0107075aa03228020085205102550700c99203011181c5030010405400541405a5642454040d41e4401d500040d050b904403011341c29600b88880b400d0441400011036071103807064409000f00d25030001005480a80d66030703948101940b1a10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 707625206 1250 707623956 707623981
    0x906010f030308070f110f070612020708030c0706020c0a1a10060504140f0a030c0305160b040905152112070b0f0c1c23100308030901061a0d05 63
    0x1002400007142035000c03941c034610030780c4080d0840c82945450358840d00c00c1b030034490070008145907928a41e4001001003015035000003000100e150010301c01c5042035425261038070148801048035180b07400006181c010000a54117840103c0313400f808852410f213a5152412546465540355881d5040c000006140c007101c441003007040c6c44407a0b9480d41000c0c43c202030b00602c0545080c81c035600090300424a151611642c40000c002c501868220303281070b2035410450304060861044204c65515254248003508003401103404599445000003056904c142400200304800d07200f26501c001c5030000450304000440b01c080009000c10141e5020082c880b455450f180302e01007004146215400000708569201c4024030791249030300385524541408003501d481c2d400200203c01160300d9441c2d40c5850b000d0103151004030008183c141510003801c02d080e24845a083c40d1200800175000040002c400d25400e4008200504042001d071071104030301030820081e47c01007949070315414034220004801c02d1000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 707626456 1250 707625206 707625209
    0x1101020f1f1a010c14010608030c03431a090105010e0105010c0c05090402060c0a20010e0102300a0e04050c0a17040303061511010b090903040e04021302030c030906010f 74
    0x58603035001240041d40c400c00c1004580c0c100f540756541c2c035840016001c00901c0107210080c11300012f0740e91000301041e4049102d00c01c030405002c0f40d01d4145200c0003081c03d041a0041d007800c20741d09940380415031030108000510440c45440c0c6a96920621400c1d1105401480c180c41c42509003000ca6071b25500112100548090050030b44100b015041045080031406503410038001f46c50123107401540e25805d0314241040800b124001e00f40705c607511100c40380d20910b140e60300c0f00740f8040b0408040c41c1d00003503980701341942d00040c0c40103400b1000031701e842c01d4000100ba010310350003013500c0350038228028080201c01c1c0181070042d41880c0002c1e48040508048079000d13829905e9040300e40b01881032400b42d50034020022000d0551b40d0002203040d0b142200e0480c5071011a03940ca9404045451002d4251200114403a018030010342c18411503c0000c4282c4044c1c4042070807460003603413240000765515014150750700c045031000052125111422004511541500d4100c3c0d11607603a818203900440b240c2d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 707627706 1250 707626456 707626459
    0x7030801050f0a0302040e070806040803090105010b0909070503090c0a060203040f0f050306220206030109050402010e0111071401030906060f0f0b030c0405062101140301271101020f1f1a 82
    0xf03014001458954800c006d086600ca08603102c0c59200c4900703a280000a40d030a4ae0b100c4408420441201d1090040c9400b405800f469141041440740118407aa40050007002c01e2010103c00100c016a0410140d810301d070004220303901e181e03601c3c2c002a4580e44a4025120040548180426090414210001250005002000a6501c3c0002c007003010542515503074851003400c501d8805a50340102442c06400e01c00d40001e481c1c201031001624012036038003101e050003468114080b0748032000c038500c402c43d1040310b94544035003080c2c2e004130b001b0306d81d076140117060030325010007c14008203e04080c02a51403518814180980314200d250742400200d4034201210001c100a005504080006c0d1075180086000030f44000b0001d606800620307c240c220350f4840c42c40010004041c81d090003110487c09480307114031090022041040c032003904600000d0310100180a5101c0640d100f0406ea40080140c00103440c0d001d09031410050255181c0502203100750b0408000a900c0424040005180d440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 707628956 1250 707627706 707627719
    0xe0102190e06040b180103060e0403081b0f040306020406031119030902010905030a380615070c092405030a0f0206090a030f06050a093309030507030801050f 69
    0x40ea20803928041c000a11542100050100281528640d40078240c4400d5080c0240190326501c00014104d804a9000071101910b400501000c0b0b41c00141e003a401045c48040884504001640350160707100725200b4110304080000c000052005c141d02a00035070380560f80038061518141d00d2074500d4001c0e50f10344040c50100c800c10581072030080d481445406d00c1814004085a901e900090500300d0500c02958000b40501515580c011449130500b4903400c4048251500030440d5050542000006c102c03e02030b8012021020007110080700780c0702c10a501c00503680300307291214018001b40100084030400380d40898941c2022003441d4100d10b09031000a001414605039986030001e041002c004181c0e007102d4100300c00304103500e800346944095402110360044501e2a0301d000d00840300c0c01401d440c0e600e841c014640c1d001903001b40141a8070ba03101e1202d40d0740858a55542c051800184219601300c3d4542440001015000005032124601a03112010aa80d0b144280421008402c40950340b089 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 707630206 1250 707628956 707628997
    0x306060d02030907170c180115030b040f0216031b11090a06030204111c18030f030e0601240906020706110c0621090102070201020606062215030e0102 66
    0x1526901035540409110f049031a5640e035030360302e017645020920114205401001e4800040c1c00c040308000f07030112840e0b00500a07585000501c84800200500c004101a00ca40c5505e80b5540ca5412100300701c005018110342c1c84c072440d0307003603513241804103011800b254404c0b1100c020515140c01e00351a07a82c0018051440000d040c08020500c04020072079021281d5071070020006da1118800d0318040c01c0842c03c0c2581d0b8030120800030103941e04195181c0300d001d052283c0240508014402c0090860341802c101c0d04030400000700b500039141400100e940d41c070904000044c01ca610052400340070540314080f41c500901c1c3d02045070144018002c0c0700159024400c200580b0b031084010b00c00040d40c0780280c0d0b0f205464100051040e903c401c51440d109240304400941151201d01101d8000c0c101c1d20003145880c0c66540082d4507108001c014520030783c404203580225600541c49114115000d044000501d13403180c03100302d03808844660020004c0d02e000031404d00f81c01c051007161520b18264107142c2218 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 707631456 1250 707630206 707630227
    0x9100e011a030115020f06090304080c040e030d051b12150402120403140403050102041410080103030c0b190f1a0409030503060405071106180d051218070506180a0605030606 76
    0x500da11300102d0218070a404c020034081100b40105400360700044055550f0b1890015480d18006010166520492902e0190f00342240c0000c1110b00400c1c03e840045060b0351080038010b528202d280301c25000040c000f4020f00d41c0d80702112160311444201c901401c0408800d000e0000b2070180c20310080150f80d0742c001043c0401d005240d00c1c2a0b294210720502d02d42038881d521142642c00c95400803450303030541c131164111840c00d08080248110039103080081e42d0725540300108401020a030290520320a80c000c100e4040000d5203401c1580e511031818400100c1010503407000744000c00b01000c980340313081c00c80015441d150088500b4aa0035941c0c507400c50300c07070030100402401d000c0d103610240090307005441c40000d07050208901c1131b03041d5207100c0080782d40300c04003030305000a10619504004c1c00f04103208030220801c0e0030540105812100500070128002110b01d002d50f55008168014004542031b6130302204c042c500004140d0a0320000145580d81c142511039010645417141e01c00703010f00507030401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 707632706 1250 707631456 707631479
    0x210d0b030f01060906080c030d1403090102190c0c051023090405010609080610050603011806090216020301140f04030c030215040327030320010b09100e011a0301 71
    0x8500003420703100505a1180c080382100c42e03c0d071040180ea0b4840c1010040d5940501944411074001c0e40641098501070500400d460719031242107600780c0010000c0b03107181c1c00942c1501c240c2c400344250400038504d0f280b009004000080030454410300303108000304841c105400081c1c400c103c5502d07014401414400d203240d40c0d51002d10f911f04051024000521280c0c0c51380542402440c0c991151044a42030011550400000800c12070812245031403c016079120b5004881c111581d08810404104c0c0c10f1100c04050419540800e02960000c00d2410b000c144202030444280c0c4218020040b1410324007845400302e400721408400b0900c03107400034020900440710480340510a2064520b035080d00408401041c0c019901276000400c010040bd001450903c020980004045410382081c0c0c6141d80080c07840b81108421295000141c03000c03102400250001a06080300810300650b91401d1440000040103912070800e01c918400c00008040b010b01000b580d14201c5040a6440c1d42e00f4203004190 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 707633956 1250 707632706 707632721
    0xc1503060d0305070c030c08100204030b130302010921030b031605010302070510110324240d02070f06050f0c030411120f0f0d0212071203180605040203210d 69
    0x1c0c8982013150030300013035035111404059441141d0340005c84d42440001c2c5d240003807045134454a50f1042000340041102904d0303240c0d2045c84980c3c843d499101c2460300b01e01601403000010841e0382c8104800d481000300ca0007500c61860207941c1007180b5000b000c2056950b50030b4400342004c54140c0a801e01140d482900103121550289003165420040240100c0485001e41120814a41d000c001e0003012140f900801c0801c4801207800c4103102000c00c00502d00001e015075a5a40043c10701c200142c0403002c4043d07a210000180b000c5407220306a062801c1c041da18203804a40c07041c81d10000856405982100d540107480100c450350440d501c0750340b6544da002c03850341c0007684107054842c8901c0c100000c104c02051040f00b000501120015182d501d8680740107102181e066400c46409201d0308130b840c50a50703440ca43c03c009003807142c211030007040e002041e085d40c11601000740170702400140441a004640039901c26000c40300e20400d1058400300404d00340040c00c0c89080700f04030b20042443c0541142e40c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 707635206 1250 707633956 707633963
    0xf0a030b0a090f121d0409121206090e06091501060f030c03020904021c110301140618060304081b0c0a0302010c0218090c12010b030a0f0f0614090c1503060d 69
    0x40c002c0350b140c40d8019075112203100c00000075104003080303054068450b001c114242098400740a450310548d030791480c000a42090508000c2d0811a42e84005410b400c50001410ba9040c1003203444121148035403101011070350892a0702c600c0821040c2541010125812201a80e40f800c2a1500495086015011403858002019020301c114011aa524802030a1070a00c010110920b0404a101c1d8810b55040c0100b58607680010f000401c1104800713841100703024000c82e603242d5100017020800003200004102950428008401c010821501c40300074588140402e81e24086c0d600505a400d035900344150010350010103000c42040103500810304130000a01c000c25804540300344005046107410211140d110341d52010000710303818146240111200f1802c2d000a01055040c00080f0303658100381440103024480300b485450500031030880c0303100c00c150f001109002c20076044101408400b010f950b044007074020800001e095180c259140b5000c014042d200c0342c15070342c0e0308080044031407d540b01075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 707636456 1250 707635206 707635223
    0x15061412030a140a090e25020606060901030b120d170108010b01020a030305180109080406030c090e01030b13050111091c0b0c0d1104090501060822020607111009050f0a030b0a09 78
    0x7203070703010f04580300c241f00320b458030f02c0c09020400910703986504a064400e81c03404e40d0004000d001594940c00201ca04078082805d02280c1c040c10000460b26800190580030300034022954000c551710361180810100384a410a00c81e01030362107500c0c4070300722032450507440d0150b0f0010b91004006402500415404400352810f0300081d0040f000c1c242c25903102020482d20706800280501c055905841594002c0c0c07094a0200011402c26035807101100040c040581113100c80400900f6602d007e922258080340d00200070300080081d8401942c50380c100c084050710904022100b26609440c80c0b03008065140c00c00311841a41e190101004041e0b80701c244034051840d1103407501c2900806410007000144190b00002030b00707600d4440018944031024002c41c0f141100c0c0719140841580c0504a00400e0b81c040766030f90340d141c09501e02004a5211050241d41008854280304c200a0708109a030048800580e150310302400b00f241002400141404010144200305001c14460002030b405206c0591040500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 707637706 1250 707636456 707636459
    0x14073b04021603020627070504090606120807060f0504050a14121c05090c0d080c010f050108010e12090105071e02030303090d0f0e090402040915061412030a140a09 72
    0x50300c6280b901c0a055001d0390000c0f051005204102420003211281c4042500046298114403074444407039204a900c903a03228812501404080da00610040c01c0801121010805a1826102c0f5821414040d20070602d05081550410414010300b84a607602402520302e16034241d1303a01d0150f02c003955108050344241c1300e90181e2407003d030009241ca01c2007120032046103c0f4000000041d103100038142000c3c4e82080d952410281c84e0405450641030340034603640d0301e8044d000680b1740181707552450071620034100000010304003410b51280c0b101021500035030713445211007110020319210f0905c005001400030040340c0082288a20300c810b1180707000400c0140751942e6000a4510b4000352859903254215842d144800c0340c01186554010419003401c0080e14030110005400c00ba004201a000347d845201c00d40400011304c0500007180c40507501041207507116582c02646003001050540a0580781342c8a0308900400010744d500001d290342c40c1c81100304501044078080e045141c0321820311a06100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 707638956 1250 707637706 707637727
    0x41e0b0a0207050f013c02031008010c090e0a1508030a03051e040203030301170a020a1e0512032a0303041a01120b0c0c070914073b0402 60
    0x2401405034880a00c09a142c5403141412424882030354003006180e898090500312801c1001084d0144840c8044000d200c1030350000c440d0240c0b40e408005840191000081000c08010b008900b030645810000810804c0d02c0003206540e0641d0364010030304021818400a402503d82d600a044003505940040c80001d55a8090078555004200d42c0c0010030380315420026410b0100c0b1401c0345680b00060002c80f64105a0042501da200c18020a051120301031200081c1010402c41040b0842d40504a01002c9503182c01188172142c000e920543c2c7c120000000150314034003502c3c1051040b00204c040d41ca024134081040d00313440c3d01100c10250710100c0300340c030241c600d02c144003962003680243d14010100d40e591aa074040c1140503040380032001610110032010588890003558001810042175594040103c40c492a10b0256404500400c0c1804546501101ca030f86c1194091002500c81c58424200c0d030b0212425240b50100e40740070b940007810030041101c2d04c14811040301030080c00040c640503000301c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 707640206 1250 707638956 707638973
    0x15050702040f1a0a1d15101e032304020411030114040507110c041d03040f05030c01020703020d2004060e15040501050f090c04170d090f0e041e 63
    0x300440300c2c580c0e1007003040e042c60410710a01d4011981210003507003031400d2410550f242001c1070603a4804540160028540d040c0e96074000040050003070421001e445003d0b40103058445441c801303412041d0800c0741211050003400b9440b142001e00c580301005802c0301c48540c80502000b40141da0094855888100105900b8006c0d8083d0020303000d0078440078003171014841600c0001e05514108810207040e03c050550200320044560000c40340803903582c41728404801080a48600200d0350b00001400040d0039070300001040850380c0a41c02d403034041e01071400698075009036100194200e40c070356000f000025901074802c0d120808268940211040380800700341255000c0d0818003e00d1000401e00c481040141000a01c035501140c0500a560500000c100c10780000c50035140503c0407140450103654000050318003a2042c00c65101c4400d1004e0171b80d135561280142c0c0100402c196001c0400c82e01a900e560708251040c04030901c4040d12143d94000242080304904071580f16054070300000545c140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 707641456 1250 707640206 707640221
    0x6090308071b1e05100801090504030e03061306180210051b120901081305100b010e040e0610060201090804050609030c041b030e160501030504050f0616090905101505070204 76
    0x43d290240654141d40c41c1e2083c5402c0c0c1d4016600c511103200141c83c62175804884141541c1b02c101c2c0200301500d8601d01a203047c3c50b840445a4580160410003140c0d407000c680f0110680d0058400340f1000c40c3c13101608104d9017000601175000f840741d021101c1d80c03d0041c8003d281c0030f070010840c0c145105101300410b00300a804a0302628001c00000c2003e40340d80e1040f06541c0041540302200c2241c46140d07104e42c3c0c1c0340d0300c84a40714042c944078910b034070702680182014040404054000d0104a0f2040d05490701c54030100d075a144503220700302c0042955481485101856580720442c50325041c00c002c20003600d45c20100c040c03903052142854640154956000c0c500d0b04d030211403640300051589840c05000da0781ca00c50707003170460f5200c030404507003005000e0506401c4803000e0070009030302e8980342010350808d0781d0484000441d1086a050081003a109031405070303e1a0580c1d140200700d6203511151040d0764080c1c440310041c850300f90080c050f4055050840a4842c5caa0070528a0b10b02039a01040035200d16 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 707642706 1250 707641456 707641469
    0xf01020a1b030b0c0324010203090409050d0212030705040e060d080a030506010906031103150d05060709051c02010f080603161e05060a080a050406020403060f021b010606090308071b 80
    0x4500c002c00c1080810341400e03420603118a021411071800b40300001c0210041916500028801100410141d0090040701c03401c44015100b072082c5191030034420303540c02c0e064080e04d00504ca6600c516840d0341c9420144ca01801d20780e40d48925251502d1144161184051300c910791000d000d2240c3c01c0081c0c034040007000c2e43c01d50b60f01d02080c41d203030080005d801e0912550081e0305060410301011000405207044a83c002d8080201c0344181e5406030201c0c005006180300103115209407821b2005880d0442d0080045a10455031180b440d07941418141a01e0313242d60000340400d1040c0012076100d80a80302c500d521450103401c03605803510780c41c201601e420b0075601c4062104500c1c0306281543e010300c085500a000d0588050380f0b000c0140400a01d0103100503c6041c49aa0345c07000f003020031083c0d0f0100d50003181c20010500035241100030000096101064160440345410020b20031410103002c2c0000300c3e02c013503c44811070381ca161140e801544c8040e0084444c0750540c0c11285510140c0c8207820f004d00320 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 707643956 1250 707642706 707642753
    0xd030309020f09280e0304032103020906030f07020a050d03090c1a03011802070206040b09040e01050402010219020103240305060106020f0601060c020d1709031018020f01020a 77
    0x255030051140b1285520756035805a0540810401e8100e060340070242010410300641d02c0300c0000200c6000204040502d55825010014000060000c658005c2c031101400340c16a0009044c102801ea040f40f049845054120030140001501c002d030011010340d00500d6401660026035442d035031b6508003000c0b81030903c082035480c42c9203c00d2080000501c07002d0881c0740c0010820f00103103283c2c828540014451a180444800c00c48203551103141c058030b43d80c50740680100c0d2140d80b640d161003995040a403849000760b180c100d0042c901f000501600d40543d40607000b0b0a00b80e02040070540c03a5a42a46059041c10744503840c1820104c5014203c481c18034011114215490462404a0034440107901c05403c550284100500b1524045000d0b41112018146002c64408903c0820046003c0d41c01c0504084400240702840341c040200400e0410411420345030b0742120715441d90115144503030f00300c064190500d420401420100c40007043e10321305004a40450005507601054640c07222800780e100e45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 707645206 1250 707643956 707643971
    0xe0105031207030210091407080115171606080f150a0306022b0203041406070207120c0e130c0902040305060c0705031204120f082208040b0a020708060f24030c0d0303 73
    0x40c02344a4040a01411002030140402c0b0f01a0442c04070758501406040844581001c40d0780081044041c803070461650004014580e101009050303090119031300004034405000180000c1003070b01c0314401c8840001e1852242600350748540000350000260105408500c14401c200c0e2060350f00e00290b240700c030120150713807460a454113000c0b8640c01030600c20341e0303803090044c40511384e004a14403003501d007903210408018219050100d51254103620500094a101042c0710207034586143e01701c002d900443c9081c88599a8400200803885107120181071504501c010804514100c4010003070903006201b201d042c8064883c1e101d480100982d4120b0307000b003a00030b0511403950400300040f040340c281d00b030120003031400e07080203245455444142c40010550509420400c180c040599000e015030704c038a551a0314541c2d402950300c0409000740b00d203510440c1c002506001086d440e0605c9207009060280c110184044043c8440c0d1981140941c91701034412003000607102c05103000c030168082c2d90301040c0c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 707646456 1250 707645206 707645243
    0x51825050d0e01050109150f0308030421030b03070503030f1b1e0303070311040302060a030e01060e09030a0801090c200336010306080d0c02011e0809070e010503120703021009 77
    0x8407a451543ca051b2800e1f00400c01092400b0a200d0003240c1e04a040e0650341c0c1e50710f182c1088039000b0f40c808040c506058030500488640d140c3e00c00300c0ca058040c0e0440c0d41d0140c651007015a2800744004180f80c0320410042c00100c1d043c6104040400a80401121442c4ac0040854007444640b074001c000140d002200300804030391f060150244880340149543e15003421900840c4080c4562200a070a040c1c80d0303ca00c1b0030340282540132500800811035103c02d01c1c209174010b0b90f02e80e80020200400601083c0011071300c0034191164501a082c070307171145040e20703070349648020701c455100d00301c039695010a1040203080d4200031048420666a4a004904034440241c1045140c81070800e4604040c80c10006000400000a115030a00300900740000701803454401204c154192500315419441c0519a541245130000c440a021300d4034070042e00c4000ba05c80031011821142403003000c0e410703070000e8a210000364140b001040082c0c000d2060340d243d01150070525081d40c00c4028102c66140f2008114005d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 707647706 1250 707646456 707646461
    0x60901020a140703020a200d0303020415091d0405030403050601062d02060f150607120806030d050a050f040e07110c0d0c140307051306051825050d0e01050109 70
    0x1800301c001e841030a04803d03450095540e0009074005102d0111403041a41e081c0c04140c140e9281c0300003d12000075640ca6150080294015100340003661400144022000340201ea81f0f6090720030742108414243ca1006000e4590b050103071056071580001c20000c008520140f10307a601801c1c540e280c040c50943c01e1105200000d6051a08100c0c070704c0c550404048080d40880c0d41c07500010700080e01c401c1b0742c55494180074510b9080304255030004c80010100304200015007458204403460303c4090b103503980c0006050b02c4030000c1d100817001450402c24950203c0c001d44c0030700022842c0101c69401d207601c0ea00082580503080c0d41c81c40c003003050b1361408000307100200040b1a145500b40c444881030807070796840c102c0c41c46140c02a207003010500c20754902d140d1030400901d00101001040445219400200480102014003806014905120555040032101d010060040c030505e5855888842e808014466900c101e612100400c0f9040120380d40b40e101502a00d4090200c50000256175403410004104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 707648956 1250 707647706 707647727
    0x410307091a06030f07080c040503160e010e1e0403020c090103080318070807140607050d1206050d030e10090f1502150402030a2a030c090f1b140c060901020a 69
    0x801c0b48100200074420a01c940e031180c101900c0e050030130b543d0b140d824181c8114040c5800644c2c0600c2151051707451254800c2e090002c43d41c000d04c0c0112242d884811104c2e03002d1049800e0101002d280e112950880320b405040780d401402071040d203101c1500400000d1000401703074416a500b0b8808021b000d03400b242c1003403060b2821114402004001d20302000180c503903031107100d42d50b00214096003d03031054036802c08440105900000743e40409208000190580c101040c0f254003883c03030600081050306000001c00402d64040c2c44100749072500d14104040b0079414400381d0200714280800159464102c50410058079041003214020b0024102c0246400d04814a0a000707032401814440542c401144610b18660480c8860711310010300c42004c0000d141202008803110501c0d440002446030392046103003959042d41080c05005004c110140c1982d0280c1c0100e8801c0395141c10108000d0300921151000100010f50507040c02403d802c1c590a05004880303040450f50002803d02100da8401310014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 707650206 1250 707648956 707648959
    0x1202120105030d1e0509040906020c031e0a12050402130608240f011205030c0f030d0506061215042003100b04060f03110708180a410307091a 62
    0xc0000302040d40481101c204c00418103109002921600c6500c2d41d1f0059114140c02078425580c40201c2260b0329500c0d8002240d4034103101100c40d180b100342c015407080303501c132140e26610883c150301010100b03401420f004e0812644104450b01c505015140c07400307072000500c00040549898444003020610354901d800d20607c031061300c03004100410f940c000c1c03220b05462480b2645504002d030ba141141c03031485100c050100903c1036402c3d41c00d00c258004004c0030240705c80c000600081d01c0e90814044940035810608a80e940000e00003802c1407806c1d0703a110f2203420014004940142c0c11401040030482a4a0701d180d031032000400c04c01750981100b03032030b0003d000403007460b860107140c103a0013400b4481c00f0040344100f68540650f500680c00d00c0060b101389582141041c2e0781d941d4000700d070400c0321880c8501c4500520315043c0000b01c0c050b0700a80d00d6078080d0450030341440608110342c0c400c4980c0c100e030316214100310840c2030741480f034804004100280800c4440010300ea52003ca00f00818144500e205 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 707651456 1250 707650206 707650217
    0xc1c09050a03080f221721090d05100c0c020f030703050307030c060603081b0f010b24130f0303080a0218040b130c0f09050607020f09071202120105030d 67
    0x1c00000740303060304655030100c0b4035150f241c917021702a041542c00c507280a407540e07100c84140808140d0110104800d040e44040c0c808451380845c00303100e119016001e44103411a201814440000d03581071841d020050a4802c80c2a00c45115001805070100c528043c000400520032070340000840c00c0c40f680c074665040d000c500800041e480c540e245603032441040e100604003c10141160104a4640c0140c07000c1d40d405012a504c4103043c3c03030707415007602414040159520412100003070705181840b0b06031030080d0117010380001d01410070802d03152800481c003030003526070101b10b80b04010b540240b6040c003a021170356520181d1459400e00800e442005401c10526034070400c1035803800880400310300010402580c0200c0d40395141e40004221b4000300442c420300340d0520980300c950540c028243d9913520703055164400810b0712007060100302c0c082c03110006d401c88420940b80341145015244039900c048285400049012103911010a0f0f810541d249550922024014402403400384640360740c5181501e0503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 707652706 1250 707651456 707651459
    0x61e0a03090c140a03021509040204090509011d030406050f0d05040303141e0f07170412090e06090a0518010e010b130902030c040f0b040213050f0919110c1c09050a 72
    0x640c902c3c0d405d21000f445000c0131941c08840c030b5803d80c2581c11400c030080045407100d58800d4964050b12048411034280d505c2e0a0001c0b03107035840711a00c0c01e05041071100544c14107080c2031013a515917001c20440c03584250240420141c3da0850301a0501ca03600c6550041503039807083c0200c208004000d41444101c0001204582100c1c014180140d404101c9286590079522801411b48000c0040c400014a00f4010420003080c0464606070800480f05a946c94442e160748400f81c910807541a40c1c070030750000307400c0702081e0640a0342e0801900416404092207004400d12002400c4071404503400d521a5181d1502c218241740c002d05c1c0743d084e141207450078000e2000035400a0307101d03900b5580d00d510481c0d59150092104145034001100050007034030440d41c1f1007001c10500215017162041e28801c01151030301c54050304061203201c0c020356504c492451851400952040603000c03036440140222002d10100a01c440308124081a0125000350b4005403803615400a29049094203e1801644481c40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 707653956 1250 707652706 707652709
    0xf1a070518191e17030403030c080c120a11060112110114040f0b030901180c2706060305090606060a020304061206270e0109030e061e0a03090c14 64
    0x41d55825048216848070204080d07080328406800c0d035410942561150201c200c4400e44011854000d844459500c9078a11400c07840840d40c030312982c00018002104841c0450014038079001811070301101d10240c2b480c01d081c401c03084440340c000d00308200010b54048039019615400f4014980580307034508801303c9a001c0c3d510340040a1105220590401088014056078020380c403050314040d101320102882c0c0140d403486002c0c2c8540081d90510030b02e510f40070840790045040c042d80300000d6400001d800000b844c10300d04250f8180c0a01860305035462982c2030550103403a512600c000342065850010310360412038009880e140005107898050b000030071a032102c454000003030710304907140c5161102802001d00da90401404855024544802c3c0c03413500c1008944084210310495069420108100c810041400342620b12105001c0d0209010005d10b004e50b0031712100030000a003d00304020100700d403260364100c00d0340c010950b28001a946090510802201904020080c2500030200c0d001b00c07990030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 707655206 1250 707653956 707653987
    0x12060414062707090e010605190e060d0c09020d050f070824120307050105060316120b0703020c1006080f060c0301150c0b091b03061e130f1a0705 64
    0x40d440782c90b011100035814002c102000100081d00324040c080c00428848144e0b203010f04014001c0f18030034440c070b02018185884401d8100201d40c0441441c0d821a11883c0078400c03a2403c01d50180e03000800c209010420700014001000701c0d081640c40041c151800000c1c03000003083c0540900d081100b0082070003108003100e0f009070340301e07042441505111655403000500d488840100e0090901010400d41305110042d4411441454144d06031400c030030b24402c98605a2103035008201c18410350070001d9012030450103401d54030030b0560a005203003040100c00325250180e0307000b03808003d90b1030310814000d0302404d222000455004100502140c02c00320130000e030a0105020700a030f8548210042c0202c0e5120740c520040c1503401000a00150409109807130300d400000c0c03c0b0001050400f407150301c903818002015440b52040443e1344120954007441d00c0340020000c1d048450001e1004454004540990030702c406240c400d01c02c515131000700c0c0c0d00848003c80014510818803605222a80c00018041d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 707656456 1250 707655206 707655241
    0x405010b0909060405062407050d0c08040915030b09010b0307051905090c040302060301150315060518040b060c0a06050a06062a1a070e04020c0c04020c0c1206041406 73
    0x8807004545a0340c0d48020509411a0483ca0382ea0502c0c18a051070703050319184e000304412030140065503110064800c0640b90000bc014004182034800c000410140199034080c1c8500d0b0000c1c44d54040140d601c5c3c951040ba03001c00d41d0a1031050755031b0289141b0b00d24080062400600c0107880344d0038000035820603024140311920555000d40200c0b0000f507045450039084601440d8010a044d40701e5840d64008030300326840e45102c0012910306440c1150150840ca55a02210300301c0d40e0791f5113028020008c0090003030140c45040e4015072581105800e9564801c0039180580140005003000015800e11400f6600d0180c03907802c0203460b00c10180710581c0e11030440d074001d01c8a02040d0094801d418110900030810032000380c0f2182d8030300c6c40c220a01c165036440a000c0c50441d0790700a4190000d00400040f0310400761032045030380c8800342d808001c0c01c11781c020b0144400c0c3c1303078199070854040388040360a012011044605a0708843c04010410006a621500e064003040040441c2d1400714803c00b2a2003c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 707657706 1250 707656456 707656459
    0x40b0309150108060c070b22031e0203280207081905060609010f0b031e0f0403080a060f140a0503030706050609161704141b040c02010e060a0908270405010b090906 72
    0x1140e00051450328031005115800304c0f030980c2348505c1e40e80ca04000b0645248590134203144001d00c0361001c1410b1002003501c08001729100031112040c2005d207880c0410340c41d05491000e6000e00d9400061412050089100c2d02c02e009650401111052034200d0800d44010503a0303100d91312410050003440f40740d015240aa80c03003030340060341e29180c00704540003c10142c200b0882411591007008200c109041a2a00851003511440c8041c1c0741c410784101619014001c0056070491040e00308030036130380040312288508003e024486242e840700003007420340d403001d031042d43d2140c3c641382809118100340307460541c4094101021002e680d070021004101349900c600a400c1c0700080b801003000d00c4001c0707904005800350f0f1411500210a840030b00c030404101032071340f1071049243c40900e07405507006015118201c08100701906d840c2d52920840401485400300548400d00c2c148800842e421501c0d50011003103040324074103610400c0c150100005e0300c205030402188810306001004c2c00b1780b24980402d411040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 707658956 1250 707657706 707657723
    0x3070c060507080d110711040c120b0f0406091a0a060c0f020a151e17190617010506150f0901080402030c15070c14060a03050a02040b0309150108060c07 67
    0x4003802e001c011401144c6014080e60319003100051600e8060f00285003003407040801d01106008003040100f02c50380c580b1084007150315031081c2e400c11665035000c0848000010641c082c80c40003500411300302c446c00c1d0480080d0503501c000c8083c039031030749011500c0080d8044031450203590408800605503070042200400503190241c8540855a03500f030020041c0c80ca40941024581a0620040940400508000c0c0da0501c2d04032224010f40f08181d20301c100d2085541c40841515205460504000036566240c8942d5503070101240203041107c03205503051481002140c6410014104020f2a00103508104003c40800c40500244450380a45081d0402401c2021259480740040303800c041001285652102d003004280c405001230602502d001e6028400541c28552200705000000c0008400f5651010381030103d10295032094010f240c1c843d61444c1c0c0075007032660b20310221609810070b50740d565158000d222510124540c1c5803155006154076001401c03039040a001118151055640c050615007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 707660206 1250 707658956 707658967
    0x4030803060a09020a021b06040b0f090d1e030224060d0204140106090e010f050d021c0b0106050901031514060d0608100b130606050d051e0f07030e03070c0605 70
    0xb580e1030480d0006094540003036546054211009441e039a00600801403030181e01601a0386041404c2608d00703035004c000f0740c3c1d4a040441c0364541540e400c0b9040d01035100318005882c00c00500c19031096111460482080d800ca01091f04d00a400c017103e8001d038160b0500310340e5000580c40d104000882d0007240559005068036101e00100c3e001c2c00c403143c254030035000c0c2c0313800004520f50f212083d80203d070303903c40c4040c0803a6280c0c0b003004150f100e07610540303074851803103140b0501514065a91a45201a1048040f152000350740d5410840c1c2c003d80c000000b180011440c0003180d42c141c000d0100800d244210a60000e04101c1c0c00500d1014070219980124408602c00d00420082c1d440540500710f044201c40e028030f049400704c2c01800681703120501410b081403560201a80c0b6016150580c2c01a0b01c80d035040821502c0b6000003041c0090a0810040b4401c0c402c0380b000d2409a00e07a402012400358482c418a40740401905907494041c0c070b02c0e401c2d17108020312804a00c1c945e0100c400c1d01c642d850301f1513940c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 707661456 1250 707660206 707660209
    0x3090a0605070c0209040b0108190f1b0906030b010608090105040c14060c100203010503011103040512030a020d020706090302010501080a0206091e030f0a0606060302211909030c05160303050403080306 88
    0x202030f1440300941100c40241400203204000038918101c41d03907c02100c4014540c05c00c111102d00103400c00905801c090003000c80011401c80c140021000d900b180e0344c04907a600d50100003a141c0796841600c80d1449000140320040d4040009a401503501c8001d02060800780e40d0030840400310301c2044002c46c03800850030641da0700c0a0403680180c2070b1034122070000030403981c035800035402031052511961070080c09540e402041c40559108641101c09001c3c04d20640c403244820340c2c0003c00c042186c1e542005070140c016404e1010344005030064800080106075803602a007107407410b8211800c2603016452000c0140d4804088400320070003a14143c5900c0590349025091400034104503901d4041d16941710326800c070010700c401c69130340200e005100341d5a072280d00781c00b00d205607120350702518649030303d8442c482141c5040703c0c0c01034042c1e4140c4c01c280e8100e0074200b048610b1400304400140001c0c0e0300d10113001e41041440c19018141300c003030b11800d15603540600355104511009141c42404030000e44103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 707662706 1250 707661456 707661467
    0x3091506040e0a0c180c020712030903020907021518100f0b150307030f0c0c0f14011508060a02030601050304151b05031603060f270e0c010f030203090a060507 70
    0x4a0142c1c08840301c250091503e800d4508550184074102c5141d2558855501040e003e00c003642045070700501840350034581c4640550900d12400d9050003c2c0c400c2c008010303140ca0008034822801a8003819012003d02c00c3c00c3c0c4400f401030701c0844081c602511040741d403240480d0010000000200000742110a5406500a00000d03001c06910909151003d02000120b000442c03160082d941c04002c901c1c5044424400c1f24a150282800a0300c0711070b4080020300001c0341000e0a0b4082d068151a048a60b5145825221942c1c2d100300d022406140c00c2209903000c00c195078100d000c52030b0560440c902000024081d00004001816490412180500300310465003c9811100c1401d00b03001c1c1d40a8001010344194002d0324401040984010181c0d02213100e80325403001e9030803096041d081c640c40e00588aa9114801c20a140d40744070b909100c285621480c402c0601d10201d0401420308408607400150402c0c50056110f0306060041040200e202c0000c204100781c07030741c04100010369031a442d004448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 707663956 1250 707662706 707662721
    0x10908090d1110020109140f0606010c260406030b0d17210106020c010914090105060d06170703050d1b080d02070803040317090a200409050d0503061003020309150604 73
    0x20006003408a400b0300f00e5040d0080d6200d0303402032410000403102c940d942d582e03560550304601125080f29001c503d0306e61146141c0880a40598441c5a40c003a403018011070100b030114200b5940740780003508200440c0c140c0103180c04038000302e901070b807607260a841c0d411070080d040c128199241c00024085c0c140c00426490b00f10103002d40b01c8001055a140d2901950b100e291814040c089203610100040c02181c1e07030012050001b001e454001d040e440e050612065811042c600300c0da031b5840350008101d0f80ca400031140c1081c00316900030318406180d402c0a5060000b5000600104955030303140304095200e4074080200c2c1c83d4402c162658414212480710028050003000034404000001840107265201c04038141c2c0e900c0701c0500c4070003901c5003c00580e88103105040241608001c0401c0341003008400c40d90300141101900100e25a00141d44060070100140401d10100d280481800064102510f4103901c1d00340070304045145080581d00d040c2d44a10070b801c007c029114401c00a501625035400030740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 707665206 1250 707663956 707663959
    0x70b121303020f0601080c01080f0123040e0a0c180212040f0206040509040f2001140c12190206091b0d05100e010903170f012303030a170702010908090d11 68
    0xa44d60758450000070b44442c907000c8070b54001041e07880402c5410300d4a043e11412074103140d000085420304c02c8203052833581d030004a50350156a07404c60800b514001e014400240d846414802145414400380c180c0100d040307540844000d105004032071009000f2682940c00641041e1600b000c09e01a20001e4031500c41c80d009140c12900d030006200c10072440d07941c8072580b18030a1205115030000c0c0107075200d034901e80441d290b0000e0441107080a025506000800384604c00606850b020341165603180960707030000640310940c0303411a00d8105001d80c1488002d03041011800a40f20716036070300e080c0028401b10b00b15620301c0b400e01c00c0103540400808000740340519043c00e409000c40d89404002d140204232192094000c40c00f07000c07d59941107207142c8500e2040c10340040010a0340d092848455803240324514004040407051001e02d00ca65040018011541c250340d200c0f40100000c400c1c80141d840041d00c2082507a040c00c2c103000004030681c0c01d0750721158041d03521410005c42c41c140343c0540f1a4986010317 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 707666456 1250 707665206 707665213
    0x50309100c1d150d0207061503320d030c0234120807080c0a0837090317040302041e05010e1311040209190503070b121303020f 56
    0xd4505801680000d0184042c5405403001000401400540503911445a03040d04040119200604a95014121250084a00103903a90801c540c140914655420540f0800c14951101d5081400ca140015282030754a5801542c1e45d4018600b0342e843d480c000c2201e0505449155086005108001c0c050526480c00542c109882001078607450f11138240a8104040341d4290020801400b010070402c5460340c1310b040c0c03038546016500d0310011500310050804190090040c810081400140a444120320010010444070b042c50745042907148660840402a6031107072000c201203030003e40c1c83d03049030707000701828004841c1c1802c42c0c4540e02c524ac000a40c811301d040000700c8001c48101d0740441281001c0001c100e01d9072030398038820340000c0c112410165070040440010000d1000042c11043c09030152002d42032144c002d0002c0d080601c415131201060103801d00c204410714003000128014a41c0301d09032441c0c04052100b06800b031100411200c00354070f0140a0204040c030800800c03581c0004001034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 707667706 1250 707666456 707666471
    0xd1e2706110739080a020d08040503060708090105100503030a0c062004030c0504110f1303080304050f06010608090a03111204030b0f07030b061c09120e1504031205030910 75
    0x26a07040f0340c4001d820864104462050005007064940700c24113640c8040000c282c403034000c0c3e0030065043c14180b800ca0f1000014000050552010854207004074415200c000d00c1c1d140022441d405c40c4c0d03000b402004081000b500070842910044206d43d4020002e242c030f42c010070031070f007481e001408041c42a00403140313854801c82c1c0f0002d5001c02400035a0f01c1005400c200e243d03203008100c00e0301ca03020701c01d1908500801c00300e080319240000800f02c001d4103884080a00d5546d884e102d441e80c100706d509407040d070462910891090780620004e40034120509040c0f0140c03c0103030300b2503a030300c101d448014240400082c040080c00c50802c22460f02a0520840e550b545850303150a0911100544084035192854404a03290900a009a01a150000d44a5428101d170316015402105e181200c503400c49540e0313698800400d07a40c41c0043c1078020030362a12903a40c580700782441049499203000c9843c0e20024042440043d24052031003804c40c0c0203213071141e180d4551030901804d2880d049001c28a06150450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 707668956 1250 707667706 707667743
    0x7140a0612090c0e0705091c0b010608040c0906031101080901200c190c060207080d0807120e0d0f2703020402070812010303080627011701020d1e27061107 68
    0x4003810b9500740c401c01c8023022190503a1940381c41204000b42003d580c00014811288142c10341a48503010395944480d99540d245030070111829600b0550340d401f80c12540000550308004503640002c1c0714002084406030010f00070342d04060801d007544030045e000034009901c01c8100000b55075120450200da41003030403480c0c40218030b0b405c1d10030440940204040041c41c05008914440c1040b03143d15002c00a80c1d80690032540d4044102c0d0701200243c0d640c20074044014204811441403c07251100f01250a042002401e20709203d050b100300d030703641d003981c9050f10031001f42d101c401c07268180c0340562569000d00d800030860060b25100c01c5154611800002803507801940a401801c0c242e6041d1120b1982e44400d41410003100303849840035402c0c034010880e1035008005606180402d80005081c0714403000004c0682d80380c2c0c03c0150040300d0250b0b070410300c0d016603c40e0041418003020546140162030341e01c290000d101040c06410595507400b45115015003508540c10307154020100c0f4045401c03100c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 707670206 1250 707668956 707668967
    0xa150515090a0f060c020603130b07030e070504020c030412080f1606231f080708030904051e0f0411060409021209070501021207020a080f07140a0612090c0e07 70
    0x10703052240e5510400012600300c8486000c082d6110b43c0d42c2d08804c1c00350344c0c0a10189600c05050304d4030501c1035071801004a03900326946c5003d030003503541c0420290528003040340340003102e4010603c500e1041002021602c0000201d40c12501454000c003821000d0381070186403802901c024900c03010001800d94a00030202c1054600940310301c40420410b030048020b023030700050282029810030311090114220081032002c46a120727107403c11581d87e054486807800c1c20841e40f0340c01102150b2000c140c0320307100e03d40f50003010391150300702c4170b060b652000710a00528030390009405000e10440c0b00011a0a001201201c4032008001806030780d6590394840c1140003d40c052489035125000400100c1d00780e00c00400d000c403c03036005074000c0401c4594809001d641340e011381400c036071010724040c00203400d03002885450080800080034181d41440e2010540c05496079180903072141307070050800e01c003064000d0045a0180c601c1d000c001014401840c100d5030342c940507000156018544400c01040c2c1c1d40c00f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 707671456 1250 707670206 707670217
    0xd0f140c03192604141c0e330c100c0c050c0a0803040b0c1906140a0c050f09130f0c0e0901050f010c0812040516060f080a150515 57
    0x1561074604007204640120b452010303d4800501d00d4405101190129036428075a0240c41c050f6000d6801c0c500c152030004c202d61403640c05c40d0000c210380c0c4a0150b07461402069140e042c0c503034490340740702101d603511080103555240081a049143c002c201251600001c00c085c0240c40342c089000c01240340c0159020b86a16a0341c0000c5503a44078070075261720681001c030036810071201400c004509090804c2c2621142d50802105510b01c0d02c140e910350380120031000303030509180b40198000a0040420181c2045440c0d0050854410078100481c4800107039111048488803120030700001e4551031540c0c001045541c07210f00701c07400242080e9002d0352481c3d040d8882d1a074868241c550700ae03103000110a0151488003442042e0707000750246000c41195001d010306851452081804038940307641500c07410b01000342920103844030760100d0400041c009034440070b9000703496681000c42804180041c010a10790000f00200038903600d8601e404098140d20403904003400e40100101d00310300d00b01f55400502c0c4c100d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 707672706 1250 707671456 707671507
    0xc180f030605010b28170c040f0501020a12080402131a091605040e040807020307060c020312070b1306020c3406090e060616050319020d0f140c03 64
    0x10300740000303101d4104000b00c40540501c12403070112091021a81c441460705030440c2400d20605606c440500c0000d0008248078140441440b82c41d81c0c1040c1142d00710010603007001d8150340c48049000c1c0401e04601e01082c410a06140c004003075502c80c40880c00496928504406c50390429004c030612090010000058610a441d00c5101d80c4ea140c01c01c8008070700364103c03a00460000c1109010009039085082d0380075010322401c81c544902640030030302c1c003041e03580071000050840c000601113140c00c5c010030200040451b40e15080150645070000082d40251110307120300c018203010b0041045680544919507801420354040c411120b010a1482d00e005c00509090362142121f186207040f82c8072880c1c03c1e01e01c55650900310608100c0d40000c014400340c007503540901e0030310540c641e00b1041d1000b0600303240b06002464444084400201e03004102c80310940641d04801e484d0b0282d654000d08038503140e01540f610300d80300c50f14005003812501c5410300c0407480d40400100c00e880000c01c0c06132540b50210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 707673956 1250 707672706 707672711
    0x20315060415121508030c06070c2102010905072303032b0902090a09020f10050d0c09030611040305060c030705030a0f02221508090607030c180f0306 66
    0x108002000914403960242e100181494012018018481c2c00d60700d142902d00080051201c00b000d8240c0c14000190b44048032981c00000c10402202040c04459049503150425050441d03055031018945654100802030000c0300140d80c0302014801d402c0101e44036084401e840c0300a48411250513401e590141c0704040141c0c000100125040000485079942506949840781e0001e40034103102c0702200795032900340300341c130346a40d24050307030f680c00040f8010300e40508000751000351841406401d902c130040f1184a40b044a803e40d1025820004460361000401c0d0001041145400161072000303503170300040c100c170b4a0200d00c4075482000e413008005403030055007103c15903038450222152500c4204c541c01c0c001601400485d0650b9900d41100315180c500348405403c00101486140c50003e0741c0440411070140140200441c2c041a1190000319901e803074040d540e131620301d207215036814002c0c014030105961404460301461203040001c04110300342000c7c0f2841e582c0c81304000c7c0102030500050300d5151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 707675206 1250 707673956 707673991
    0x2090a08070f120f020103180803010608060f1009141908071703030403021209060c010e060402040c02010b0d0807020d0f03020105090606010e0d030f02070801090302071508060109030b0601030b1002010203 90
    0x8041c031007402c984d001e603080542c880305900441c050860003e640160681e900003000c0010404d40207580600f174156165170391451300310100504041c0018205010b592000d1032480200ea000c00c03250103a030081c0c0602c41000b9200c4010800e10300e002001302000380b2102d600420505004074011049441640030701d143e08055074443e0b5100e1005560042c0580d0149409070b01c1c511005010300b91110005140300e06221544102070300391074110707a14074442d0b00110204411841c05110b11a000c4049200070000826103001080701008603940103494403001150003400c5554900e180d0f41c40b03640c4102c08140c501c00c02d14019020700002d40e0b00440034011140025202c0d44115104406120001c04c052840c413143c0e202901d81c4401c5001801c00c602030301501082c046802d0242d4840d95219a00426a00d0b141c00807001041c640ca10b401006c00c010501844526a40107061905494002d1050304494560341b0050f0024202c0c1111981c1000325140301e01c0c10180c0650141d8071071901070010030401c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 707676456 1250 707675206 707675219
    0xc04050a09140114060301170c1c0506010602011104140312210a1a060903070306110403020406080f07260d030501050f010e010f0f1107030f031202070812040602090a08070f 76
    0x70340755040c41380c0c00c407009000410808002951501c40c440300602940d0030b2250881c0800e08002c109503040d01e0890182c1885e004025040100c5401040c2600c000c000451607844003080c1031240d80b04a44c0700c80305225064031250380038030080ca20b8400310140d09503680d216036941e4001d840403071040c41c0c1c0001200000b9204a80500603003843d02c0380c009400042d01203400800007160060b484c4150103100b0020040002040c3e0300c2590b0400c070088240301d80351072651040000707550309500030320600d03002121a030254100c0000c2a80995440b170040c040b0401401d009800158005c01c102d403428452103281303c2005406a103d40c0c143c400550303000d101040c410f401540c10f4085000c0361400225110310200d40c0500c111036100c041e00c1e652400492a0b00c0c20418240340c00c8154000f564026181058801019080411030040000000c801e6042641d16210540f150159034045d00f0719280c460006820000c00382e0456807002c00c020301c00410f0948810100c0da58a40d140124044860035840100d400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 707677706 1250 707676456 707676479
    0x120b0f09070b030126161e03020a150512010b03070906030203040210110a020306040605060301060e0c0d110408010903020c01020c030c150f04120b090105100315050c04050a091401 79
    0x140d0300b00604503499039107040c40d03811414491102c0c08400328031760b400c80c502001c01442071000c1209041c2051940c58203054000459510f104c5902c1d110507402e0764100016210300300c980013282c4418610591111074540e080d2110b00ca1700440003d046120000403d2400a02c006140186203917512a007644e91078800c143c040780b10640b0080d41c01110040c82034a814459907840d05000400403c0d103003200d00d241e011a203003440c291011141591a502081000c0c1005d114040c000d02c1000f06003583d5040107400d40c6090300c109210116100d88818810300182100400c40e001405808001c210051441c10025101e441c402030325030050041140c803500c14940010040c208210042210001e520304120701d0034294006900c0d500318140902000600c14070688402805030301940200e400b0b840e16485541c02c603a001002541c82200d004410310200d40c1e1a03080840b0646050030020307164465182680712801541d03c219401405010041840d1a454114440391044012500003598840000754030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 707678956 1250 707677706 707677709
    0x15030b16080106052205040c0c140c130b0315181c050f0c070503031201090b01050403110405070e030f0307050c03061b1e16030e04090b061009120b0f0907 68
    0x800a00c0f0300c10203809500d1410030f200902c80d400410b5151b4a00126007914401e0b40004082800d00d12072200b408140c038002080050403001070226034910000040c880b0303091801d070440d456550100c809868a00b0084913104600e9100320075807501c0c0c0018100f68001c40318200d0f421600614524500312580c01d00c030307000e05040c50b84525050445441c91602c040c2c00800d03800d511481003000020341900c040c0020320700056200c0d20200c1c190306062804042d1a03400b1000b50401400300070400118500da8041180101c0c121000305040d15500411035141d46500580b990500a40301c0301500030b000003008110640c030a00564148010a0f0205502e0383d1003215820b0414a00c0b00c81c0342854041c0c0e60007410807000c0907040320349140c404800801c80e5003080114100810f042c1403500d0074583c1002d040d09210170308071024003ca002c0d5948854422801600441c0a0b00043c0b8400c0d0a203030084228001802003403900a60f0f080503802c102c41c1555090321102080304031070000c10251140464000c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 707680206 1250 707678956 707678969
    0xb090c09010302100c02031f061a0c0c1c05010c020d090807080c040c022b03050c030622090203030c010c080601021c180305190c060c020916020115030b160801 70
    0x403804d03038000151510b0500703900891385400390840103808040c4404040500800c582d0000503024200580d058040d0b060840c840001030042c0040d4810060008841e07541d4001038845241c000d032000d0b4040740341a01c0010080c519400c101401c01f071268002240c070488075241d510880300c2070383d400482da00c401c6240906010340e0001e2060000130304003174200c802c80301c0440c030490301000c9500c1700c040c00c86c0000c1c00c1c01c0151070010411401342d5a501d40170303075500300d040c5801d001c2c518249000050f16140c0d8a00180c0e0a110010941801c014010f5005500300340e006400e0f00d079154450a010303070003401d5154040303001c98000e002003006940b0000d492900c0410113002c1050b24510300743e05582c4034440c0110804003580141000c0000f440c28046c00040141040010f21030601c0c901c0e0030307050001035030400d5082003400c000181c0940e590340481038020440e0013519084190944c0100c5c050010394030281140d400b407a00c00001c0040009101c1e20811000c0e4072803050308102142262203000a00c03502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 707681456 1250 707680206 707680219
    0xb040b01020c1203373b0a090902090a051605070516060809010501060305070905010513170319080f0103111207080c1201020a081b07020901030b090c09010302 70
    0x12240b0b82441d0710110003a0710a40704881c107144004103038000401000040402c0c0076085440201c0c031041c0c0d14982c400000312400c091200e4141c81080d4400394112403000c603035800d041e10308190702803a462080c44005002902c5030800340d4a400d50a0042c2400712000c0f4011001a40012441c00961160900640550f1200200010029000c070b900e60003099003a00d60b4003c0040d0100086007010103a4000d044540341d012061421b10205c608640050b400300c014507090804100340c03142d02c01c50f040191003090a0464550145080c01a0820300799001040c0b480300c40768040c01910400005091a402c0780304101121111082c000c40710548192824402540c1e00001400010340c540b84212200d4000380644501080c0303860400e02c3c18049a02c21111034120003492101c0c0d0070406000010004500002d6103010700011f8020b003011002418994141d50f4064544501d441c0c20b8200c40300c05400611201c09540c6904000640c40010307215401607205140d040b0009050032030199040300e8004108 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 707682706 1250 707681456 707681473
    0xc040b1518060406030c0305061002030a0c030e0d0614013201030e100b03121c051008030f0a1b0c090c180e01030308070809100906022b0b040b0102 65
    0x41040360440c450701c9030307036900012502000d9190b120142004066960b07020034002c0d00740501600b00c0d14090200c03401810340314118104260008211440c0c4070481c0f40c00320303d0340c0441c10111a24400860040e61103541d5172140402d0043e140c00c0200c928001c41c40350352269a03034145401c49420841d40d500601c18030750741719485060460304c440e50848010304002c200b10254680301e50910401c07030031074071000355030b81c00c0a001400c003000075041c8a1010607009140c4407035a101c000380c800e0384a00c0100c0d0191130b403000540032050b40035180e000f000c1842c110703174071540501c9141485030498108034000802d40b00e0300164258001c501408000d03042041d0301062410070ba1390750090058409403a062101400c4101080594401400300800e108400403a2030350440c540141441c4010f841c10042000c40d5050011f00c81d4040394407408040a0280000e125081d446c1c448041d0258800044401270f20044140c28000c5464201840800076142000354414080410040b00c4130100004d00682c8078440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 707683956 1250 707682706 707682739
    0xe07030c08152a04030b100305070b040501050304020d170c0a0b061507120905060d05220503030f040302150f190e0a020d08040306060303020706021002030112121701170c040b 77
    0xf0039040340a507000900c0c1a40b00d07240c2c01c014181c00c0d01c0344d6400c4c01d00301804005100050000e000605019010f40b0316052800380020325a0001400c068400c4207201c3c1128100490341035a02450b0007080801c94944010094071510b41c0741012060700e4035a0008005086450060180c0f02d1500340110024103044081d110041000840c2c03034040706005940c00046030781e507601b10140c403000019440124403881c0ca60450000510420354103000501c84d0365000380024404020750341d000e201d100e90300c40d6981e04c1d410202c4c41c0c8003a491200000d20003040c24441d4040640350316600c5404031000c4240420076000004040750366690759414181c06c41d101400042c0751128510402c14060b402031801e09469032906000c60349a070b8000c5016034000c0c0c004103c01d603018400071001854001c07045046d50326200d0107103d21017043c84000d0091103000d2042a000d400361f55440e5405002c0702c0801419a101d644100c403500c0c510241c00482e00c40c1c0a80ba0002e464640505a130501b009000d012441034003c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 707685206 1250 707683956 707684011
    0x2d030305121905010b0702130b060714011107060204080d0c0305040b1c020a050306091506030a0b03011d0601170304150e0d1707170a080103150e07030c0815 69
    0x1481d1824142d084203404180400c2c6000d03d83c041d29120380c50903a626010310410600c00000c003694001c2c02d05040e450f03099540c8110555100940198540d16022100c1c3c240c00d0040050741d0080380d607a440030400c1000d008882d07015100360350400d01103c40070345440c0001d40c0d01650341d040090018404010074041c02c281e40f405030004007040c0900c0881460340d144000140e811400400300014004010070035207250000c01503030006100c00b0703002018400b903404144544030041c04600e149031038800c9004152030940c440549440c000910610040410146540b600002c0c46203122190300381c42c0c0e4142201d004411142100c3d81c01d000e524210a81c2d010503500115008030381d59020a041880d400450b0203450840c6e01c1c81a035410f10396441c0118941004482e440007400c2e4007210050003c24013240e003200605064030b070045c801d941c01612030f02c0707080003501c1c2c075801c18211402800b500208016a010050702070300e880000780d034482c01045002c48402c500c100e40030b845e0140180315240d21200c10380d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 707686456 1250 707685206 707685211
    0x303090312090307080a0f110607030f030209060904020318010b301203071206060e0d0201080619030f02040b030c0a0e0a06091d0d022113030506012d03030512 70
    0xa0141c40489a907212180c0c1001d46440c019550310400712140030408c220201c030003018040c1190311500306900d5440c014010458046a502030540c00501c04801d541e0f41010769002d003200420941d0759140214640d8284111207464140c207600380300c0d40c032001d840c003900d402e101c0c540313a1082c10340307081c890780e10107080f20202c0e842c5040d1034001c2d0700e036112054125900462040700301e0f072641c544548181c5456000c81d07031140d22200410010542e09040c654a80e140d00c45038680900e441c04294a89000180d10104440c00d6840c00440d01c0078000700b0005d6030005503440500845080200740c0d80c1600381074844812820656200b2409201401401d08401816820100450000500b56254103008d0125540142d4512880c000440d80c00c3c440c003010004012903500c00e20190083c0004090101c0629249500031008041c020921044410007003005000441d000f100301d450075650342044c14022a4604040c2000d1000101d0030340c28801c001880804481c0c6c5980c6180ca8610389409003481050007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 707687706 1250 707686456 707686459
    0x24051302090c09040504081e191d1f030501050406030b0417090310060311010903050c0f040f050c1e030108070501110102070609080d0c1e0f09081605040b030309031209 74
    0x180b105806581303403440b9081c407840c410840140d03114000c4880d480743c4100044004108202048407241c140d5442e4124520700c9003a0414510300440300101a02c4407401100c13460f00101d480601e0b408116121946c8000e402c0d09440410440e43c850061006440c4c590001030851010003022a001031b010603004010840548510307404c14515500103414180d0400241400d00c2c0c0f1840140300b4001c034034000d4612030078242000002141b442d80c83d940c80f007200003d02031168280510903002510b0719041048542c68414041108d407500e51703540a02c0c0d07008084100d00445440103d084c0c202d0944080728142ca128a009240301840c00004582c5007851a400d981c407035409120200010700385000301c02155200c0c420355521000c451022208417011010741800700007149607036100084040070701c1d180055451801c1245041c9412050b04c081084da4050a0780384221841c1c0001c0c00741c41240c9009994085409010506074502055540d005103048075515030060b807803200007010b0754001400c3c101070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 707688956 1250 707687706 707687731
    0x90d02131a040b010203070c21060e0709051b0409050a090501090b0f0a0c0e0f0a0e091605040501030201120902031c1808070815091204032405130209 66
    0x9196a405585031115000010305a14100440701c1c0740602500120710701c20310065044c4002901d03000032502c054482c940618020314070103480648252180214680c0100e018004846044180b5544032041d00c20240580d1a00c004140300101c000043d2a86404030504107051600b4503001c3c10080801512045040f5600c01c200c1000070400c0c082c00001b0360040c03035078000614100c41103403007440700140003408075441d000c01141007541105092000c1c41c1c0c00e4a001341c54503010004200113034880d40281e11103008020800070240400a485800c0f008501951400c1c65950b90030300c0195a401c0c04024042a0103c5181a101001ea8000305903617000800300c03081c000504888200c40218000d004000480d1015060910b000c1080003034004d00507a0000c0420030700d0041015140c1c601045210314007200d51020500980301002092000c1d050300800d00e50f5103a0701d00d411404084070b81415103c48040c200300c151510020f200e1740c0e00c41d0725107140c402141c5010358200100c408005000000c00344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 707690206 1250 707688956 707688979
    0x5030a152d0209010e010306050a0603020702032d0d05071e1505010620071a0c0c033405030606011b05060a0e0f0102030402100807020c030d0f170903090d02 69
    0x542900070240c464003014001a43d0b19a0350300010440103044080314149410050104403680703401c01e50300701b218014500140c850b40d0740e10003e400c10705a0a2402180d0340d40311110040c036a1803c030511111038107903040302c98140c10b40009035428029040c0240c100015159421010345020310b03c00d5040d4458454004019a0350079040304503142a00079000240354015028000c641040440c040c5010900c014518a45800d03801c89065900a000b18101103000ca035220940700b0402c001c5c149041d00030191a04c00c00c80b0031800c0908507010f444802840142e58400e0400c00c41c0c558941d0a03902c01401404a55035080c0040da502d140004407401c448440103149008103000340802c601070001440003180e9452030004203860524205040b411591040050000507500c40502c2d00520046042400895440300403e90074112031519179a05401403c18207810f681e840791030840d88003016106c845914045a14001c41d5007021a0711200d10380c4100100301483c44c2c050314000700944001d045100304c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 707691456 1250 707690206 707690261
    0x10f1827030e0909010b03070803070b0c090105040905070305070f170f0c0403060608030c0c1206042d050c09010f0503070306151701060e06090403080f1005100203031005030a15 78
    0x41c3e20840d01841d181e5940c2d9540c0c1c0f110b00d0b00f8496900103200e10320095060059a0321030f8566840080c0140100070000100c000c0f07a070340100300792801845480c0342044a8944010098064081102c210340001c2c8141440040a0f00400b282280ca400404134140a40e8805015181d402005000b41c0392443d0180070000000d07080c0c1c0507100160810701c020b5512484900b0300549080c550220b101e114408030081170815000019800b58000c1d04030388203031030020040c5654003400180004000c0310079807214207035040c444000f400e000d40c49019a0348007000d030380c2ea980c103412240381e60054bd0361503008107030104040350180d00440030304001050302c0c1607035540c0d400100c582004009580443c994448204101c0b034103100d00015840f507400c2d5400040f40c94540d0f801440e01e0340040180f01141c0d0074a01141400c07006030b4098018240240800314a4124401c01079607907041103c040c41c01850441000c1041d04000c00c201c1e8040e60700440c0542e00c98407108840000c1c10340401c14000015040848a018 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 707692706 1250 707691456 707691469
    0x60f032a0c0f060108010c140304020112050f071202190809070f030f03020d0f0c080a0306151d1203070807060e06010b07050d030605031f14010f1827030e 68
    0x141407400004060b041d549203881801c00c40143d11507605640b506030308002540c0c10010720f003202004410800d039a0b955a00c0140d0340071440c60880341074a0724010800c003094100480c15800303080c8035143d94500501070000c0f6401e9205071b00d2020b1010301740071400f0007d42d029210407900034850768260350416407145100340214440c0c1d4400e403205855013104000307040e01403001c0904c40c0c0b00352a08882c485c0d030546000d00781c25000750300102080800111040460701c01e600060142c0a121250503140c0d1806600900346031440b810012102210654200c16151010441003051400c0c0051801c040c001e85580c140c3d40c225031015144543c40780300403100c1c012305100f0f03039020301841031542d505e17900c00e42032050ae08240082d801d8185031038241c090099940000d8030300c05021745008147c00c000301110503880074140c40340309101d80d10608000800ccd80c60900d81c3e0384040e40e00c11003000c010b0305ca601c0d00003015550108407440000e01c2502c032499201d1007284140001c180241084400d0b036400c000803480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 707693956 1250 707692706 707692717
    0x705130f090521032703270f0a0513090203030705070312080105010c020906100e030318190605072319020a0f03022116060309060605060f032a 63
    0x10541c11509032420381c042c004030703000f070540c26446085056140c003070245202c1d1300c050110030140d0041c484001802e108200b00321901c0640300d00700340c403084806080b00e240c003011128040d4452003103039101c5141030429101d03070000c1314001040e17207884200061000c001081644000d90700b5000410949000c02c90800881005610580f40344441c6008400014405901038010718100b108481140c00541c0c0c0d01030200da0130200131112041c84200580d015140c25240480b00f9801d0b010100b81940a416139400c40207035420181c0b04500980c403160811161000540035a0b800b165080c050300011402159030014a070f034884a00c0740c2d8903003400d4981803600b0301c09017043c2100d20a1b00760510031424110300d070000918000c4100c0070342d103082da40001c141003c41c60000802c2030070401130140c034050810500c504141e00e001c0000400c0c0d1500c3e001400781608141c10350700c260a0920003d45400c0c14030494007a481c80354669400d45d254810421031000401043d0002070909562600d407a40d088001842c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 707695206 1250 707693956 707693963
    0x30604150e2202030a030807120c02060a051b04180f050a0203040c1a0a0809150702210406050a080a140a2901020c12030d0c030204170106080705130f09 67
    0x7919141405820358508070140110825846040915006031800108102a1039040c10242983d40d0b036841d040711020000165084c2e000d0802c041d0320801500815510700072610040144050b907990385151810f000f49429800b200b041c20003040200ea10903003405131200c100c0200110300400c00040c401c051340c42c184c4480c9901603002041c04204820f000d0510010300902168000c4450581c818890034001d510b11030091200c4440007454001c030500a072a600390b04900341c07050074105440d00954030051000240c10907002c2d0000070f60118510302c1a83c7c2152582e544e030a1800090382421204a130002c3c008590107038a4401d802c005548030211a1301c1940c040c05c5c0000d461030f07103a02c0c1c80b8414690a00c40815555500c1d05030480340d034040341c070030101c1d80280d44103528240c42e032008a1075840b81c0c0e003140e0502c500d40302030100f42960680040080f01e91103d04444040e0b175007005a403c0f02e00f5840390076100c0d801140c1c100428203140c2980c003e1f0fa6100c8500140c064030140c4200300759404280c044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 707696456 1250 707695206 707695229
    0x13080c01050a1d1f02091309060e07091b0c1401050106030b10081e100b030a060302040e0c010f03180507031b0e0c03010302011b140f0c06120c03060415 67
    0x150810f0300307100f0803042c42c0c00303d00004054550303003a00c0b82c203544520010344160322900040c16004c01c0d00d80a40030800042ea04100304803100440c00c0150061040b0030f4242d581e402100800030340f800090042582186c4000c4107000c24652440c01034440070030388082143ea581652050b01c5001000b03108850080c10b168402084071003421003007048080701d42170084244007000301400f8031910010310703a10405100f0080c41c070352901d42081003001403079560b04c0f221080303000004000d07040a0a41040040703134401d58003808095040c200300c42c0c503415040744c0140060041440412498829041490100201121354400d004c003500d545091400d15041aa0211070180040352110051107604d00108030a58584c1d50354200b0500b03802c42d40c401032101070704001d200341661480400000e00358400701c0e88001250b1800d030308074902d261508428401012a0301400a85070301506040049482d100006542000603680b826140d11050308041c1246402954401d00800507507500c1c181c42c0c1c040c1070381043e031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 707697706 1250 707696456 707696471
    0x108010b0a09440706020d05040302130e0a0602040801060b031603090204150308040320010518061c05040302010506040e070302010c051005010303051222300c02090c1213080c01050a 80
    0x203e0b45004070079401a03007190303c8172085000c6c1030b40c0070b070a480560394100da16054030500180340002a140b101c1c0d030021103019100310f000402c0320302e82c014000c55a046000f0b215055988900d40c001c0d0000700d601c2098170207a030010b40c000f01e12981c4030740840c1d40b00070070000e0b02e52003000d0880900c003100e0304129541d440004051040c490f841ca009000c418010b03841c0c08442000d0f6000801a000c0c20304171070ba00d142050f40811565803480c0c207980c00c100d141c04140c0f40c00c083d000c00401c00f9107025241036000d0351070300c0e01041c56400e00e13000360312244440e00001c1803980d01d5a030044441040040e800c2e07555000d2010300c01021580350107070321300031030103940ca054841940711051006448007030008030340d40c5503020410300c4205050b51541403180c0c01c001680c14440101000b45204c15080c9200d9800c200c4aa101c60107103600281e010180300d00a0320450026030752143c031000e013482810002c40454000c440000d0074010030f045030000755031042c0f4a40d800c007081048290309440d03098501b0761040380c94209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 707698956 1250 707697706 707697839
    0xc0423091c051c05090c120708060c1902070302011d0406030f0f0b0f0601090308031504090b0a1d0c060a11191103150a2304050303060108010b0a09 65
    0x1422030030808120410413081c180b4114840c2c0d940c003100000c6e401118150719010a003101402a000209070110a50b12545000d00f181c04840d440300f071088800d56681c002d81d0f2142480001e0b10010b490341a1a1409258000100c00080c0412400b245074010b44400c0040006032640c0c1c8040003942c401d0720000e038584140e03e0840f49042000b8903441c070340c010301c1d800c0100503a84180340d817040b01e80040307000d83c1d2522000d030002080c1100604003500541802d034078400700003032080310510a01c0101000c100401d0f540e40b40c8190210500792010141d40184030001d4030340342c08001405094103d06100a00900c14500350307060240081080100c85c458400103414800340e003a20408448044005e0030b0f40300561441180382c1030f8050003964034156502042c000b401e10310004e00c000c034004124402d90702e00d05450400d6499004030f44003400628824000640040c000c4160b808a0031192680325a960a0002e0011104103044441107040300055440f0841d04000000003a00186081040d611703009020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 707700206 1250 707698956 707698987
    0xb13061805132304031407031407241a19030c03050c010201052d07180801051906030510020f0708040326040f05010503090109080313050c0423091c05 66
    0x20342064003603c540100400294003420204840141c07174005600d0341d925080c100d4480c3d200c2030348200c90140c006035590a01650071118104005103400344e910f40010040500e090ba40540d604c1500002c1d2107180645500d4200031100d01070b0950005134021590740d0315210b01644283c2d209a403a0741014411980950782800b9081d441504a41e09a00200901c3c410004a12013426289180c0f610345000c0ba641d40c4c807480f13410301d407010380701410ba80d900d031100c00840c0240001c2d908010980c5c00d032084103185018901038107080307903000000b800c02142c500301104041c1d030003181480043d4034100005000580b1a0010f48007071801079000104504003046015501344003004400050102804200500b80c210316200054810030b19145403079449402a003805003200c06801080442c0100802007041504400594060300500c02c4410041c01c00e418481114051071090b03600c0401810303031103203482051802c03913044416041220f01640e41c400b01c1640030320328640b4260024500040303c0b11000c41c0c1c031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 707701456 1250 707700206 707700251
    0xe0102072003030304020f0d0c0b0d1a0a05010f21020a0c060513050601061202121305060a020f030c210103060f0608030f0703030b010909090b100b1306180513 70
    0x141c1c020f41c610700b8503130000740d840c41c0060301651003081450315800401c4131000e0500000d01500390781c130761603100505243e0060910001c0e580000032070141040a00d10f4425a82c0e07007201d5060b1200c80b8460990003044880100f080103a400c480042c3c0040700b480c249034402800c400c00c0d01e13074031105054158903012060720009841d160280d00000c505401084010554604507201030400040d07a088200904004e8080e20344c0592600b0391030b20402120f02054018a08101d2081c8140e54030b903610302d6910000c0703004c0c2d041d40006920080c000034038854080d8004101d020b004d2800380c54192214601412124030036001210080d85501e032413044000f440c01802c000d411140c0c0950305000c8265141045400b03401c2002c3e003010380782c1c0505001640a006040301814200c00c6c10702903820303903041000100c001a0746101540c41e043c0b00010f124111038041ea03064001038110900c0441c0f810348100c0c0d020034894407071324181d6405c810000381655044018545040071710000318800c02501c03d140103013040c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 707702706 1250 707701456 707701459
    0x10e07030c140c1e060405060c03040c050d030c06020d06080105130305030f07030b0a230f310e0601090b06070803190906020a020313050a12060207060e01020720 71
    0x280415603003165040524580080000a505620750316001038803403501d500880134080c12640c44004907800f907800300e80300344541c0c000d40848245841e0150310485620003160050701a654010051165262410029592501900e0150b524011503122503040fa4044000142c0a40d5910400c10110000b801280c0d0301c680c2c003c40103e202e100d551030150191100402141c104001c440c0046e0080d0301070380c0310403c803040260110785400c0d21003040485a007042003806001c04c1e0642140842803a0240342c00c03480304805461607100b030207500a003450350861114540610080740c1c0542c0b02808541c8194110021100000c2c201075141c85a440211815203074083d0081c82e0030040c45001c500342c1c40c00c0720703045511003000381c4074624403140030750003400c649000410042c000984c1c00c0405a000024158020301a440c4c40c54542d03032032007080042c60381403203101c1e52621204034090200e04598060b010340d90107003201260321003003919100c2c01c99006e404200c592281452901207040454800303000300100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 707703956 1250 707702706 707702711
    0x601020c01050f120c0c011b02120315040b0f040203090a0308010b04030c05010f0e271e070e0316060f0f02070b1c1404062004120305090a0e010905010e0703 69
    0xc0390200030a9902c50804c82c0742e00c24805030041141441c00e28126422856141d001b000108600c09185484594907800c40c40144209120b44020f00402021203015560f0848800401c6c07600700d09102c09080380d0444654403500803440040d168a0314001144502031034005000c1c0481249005841e40704180c00540c4006402e000c14800119843d1585040d50400d0904c1c0341c0c24400003604459486440e003070b0640060f2174414115104400c030038031700500003252080b2803480c0e94100403000c81c01411000310041e500c246e00411a8540180c40514039084080c068482100c4084001511050385510400c00210702549001502e80d0001608044c030410380f001d0422149894a41c030500c0c000d180c041c42440c60301070b05440804003580e0054100c9002032079127020360325250030500c0003060141030801c43e035051514111901e10b0780d0f00c00c54040d02e0b2000d45004180c1460b0704c085902e500044541034004205120128040b94442d00301c81c0201030026001c103080d8100350f100f1920b00e4010300404103060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 707705206 1250 707703956 707703967
    0xa020114040503030f19110a120b030703020f01050d050117011407090302010f03021b06060a0621020702040b061621120c0e101706010c0b040b070306090c080601020c0105 75
    0x10030200803030707030002c0e9110745401d41c2e501d07412000d903603030fa505800e1343d964185030224407914248250042c0400c0c40041e00c40400400d2209e40d10001e807421280601d6043d0403108007440186041c01d800e200c4144180340182c1000101d47c07840c1700f1500c01b038120801c82c0804481d0f4070400c8400740a01c17590322404001c1200242000d502c0a0702a4809010007030504c041744a0964125102e94142d0301c0311207864541c400c1d40700d1540500303900c44000f551000c5c0620b40c80c0c5030119a150042c080d4200a40da11000107180701e8821b8441802034015980407030740552101c0b100d0850b9070310780024204944030701c031402c0e003013100c14a0070001061282c200c420800c110baaa0dc01c0042d5042242d18010113a000c102040380410221708468505d0004074160703000b20100d03d40d10160340c0c0100025900480c40540001903101d43c001511f200403903010086c0405014400540056400c00c1c0181e00104c5600780030039400e071240481000d40e00e0000080c400606003904004043d81d0400410b01c03100001e08110b440c09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 707706456 1250 707705206 707705213
    0x2d0c05041512170708040e0708090706050909100305030a051309150306050a0905060702150a020f070212150f09010506090606030c2203052103191802090c0a02011404 73
    0x6068185000e05402d490300c6904110f0120001103400041d84079035003030740d01c07130305c86518100c04103050b5512000580c0041c00104114000180b8900780d8520b0703100c41c0d080a410104110101e04002c00c101d01d150b9415500200081d02000600346070442911000c0d12041e09a818075440b8207075074015080d140c03e0002102c0c81c182030803880d50903030b604101e0201f00c543d19100510007410320000700608038405c2034100001c5560105003281c9000743c3d98030080298940481400590290881e0120801c508014000047c940a48900031060044003642e01c065000c596010030302408039880c1041c1c180740e40c10441072481c00e00c030302d82d803144049403191090f050a04c00326031035000c02006412a14000250121400542505021001000c815100f078103502c0f494895150424007403e181c1d15224a60800072901c04030050304c1c4502d43c450040c541c00d601d1140030b08050450440885071006a0000084c0035807038018801e84620403104449640c1c10039064000d0031507000d0540c415103e1390700010700001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 707707706 1250 707706456 707706479
    0x21020d02010c0204090516091409070b220906060f570303061a03040201050d1e090c050409081204050304080a21110a2d0c050415 57
    0x110340a01c2c2610401900748085001050f0381080a0705a201c1c502c000303801580c0100c05001503a08061b014055001c800000c03121444090300c5180107600f0141d410b00600302800050811a0040140003000802218124040401c41d800501241d130701c42e070080c8080c6400c01c1444600c0e000a00c1e08044100d40343c00748003050040004921004001108400303003100e440c06510b5800c4d00c0480e9407040b116a0201042070000c0e15a5086005c00e04000c000100382100c9080c0c400c03c4202c800003645503680f00e0380115841d502580360307121101e40c0c542d190714041002c4d04400e054001c03070a00c000b960900906000c040a8902d60001c0c0c4100c6c2040f40c6040026400c2068900d15003070403091303066a4903145007160542c01150003c141074400c840d015014491559003143c4403545922240c60001500c400842d030a80c0300c0d400b070700740701c2c2d000020350310019241c180b007103030b0b000343c04101400523111006e01868092110801620f6541c442e200500c21440d003445960b25005c4560485a415482c0504d0000c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 707708956 1250 707707706 707707729
    0x10f052d010c080c1203040b0903120c0702040f1e1b05090103180203030f12090304050913030903050d123207051e0721051b07030b0403092102 63
    0x4200340000b100d010819860b050f200c5a24504003999000002907040c001039410849050302c01d0040d1782e0100f84100c001008607810001e901500141c0b56458081030512988105022a00f1503030782c402d808840b280c40e11941d04058241115000c5e000d0705d48510800b42c034121080c0c88030140241c4247c99400c0d4010b421100c01303800a003000f00c0d5048a40034075111210343c11070301a4042c00f0025039801c100c0142002005280050702c44400c494a070201840c0c0d0f00c0c00f460083c1900324002a002c60b26204007820a0510a44245000b08400340c0302e9403410f0400e0b564020344c3c408584507004d0403042c890039000c1c4001c0e01d010981e020490004030003920441e607036124120350b8505501d0000c20082c610900460351403640e01030950407030b0b038180840701405034000241907076145c119210f0356062903052004402140d29507955181030400e145802138408120000c2048948510301c0000005412486610b118031b0180e1a007080292422803404a900502da240c0a0300030402c4c444c03c0c006a982090300304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 707710206 1250 707708956 707708959
    0x1f05060108010e1b070602030106090623040e190c050c0d03090c0b0c070f030f1703190f020417010c0206090601060c11040609090f05120c190218010f052d 68
    0x666142c04c04d4400346007403080e441c0c007900c85400003001040c1d80390002203c0d42181c889549681061030500c07244a00464944a4001c0120003044104401c900340814140c0010044881040c800d020740025411100c0c11412400401c002141c040c40f481820f0011403d421000e003070601c00c843c810343e14002070b0000ca00a200103078001158035080c9903802c02401c0003038515000b44c40703902c0e40c1b6814011005104698102e030301000b060082091092800281d0b80604084030101107000741c1300d00d039a40904005810b110046909100000e468183d00c1038180d808501240000b4054444c180000e082800041050140b58000e400420800754800031002d1826000000220103505000001d0040d08856000f2240b80341442d00e8241484540314411250074030910803030700c2481045190340b4132030249042c528500d411055440032150807400328030300c00b02d20003090001c041e03014204444401070700f0b03000078150b0300110790284400d00b0700b003881c4c1201c00944a580c04c0c1c40c131609442d03200384006104c2c003107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 707711456 1250 707710206 707710231
    0x3060e0304081f0e0a0b090d2d0203130f05030c01020c010219020406050a061205010501021b1e04020c060a05060916180801020a033207050a0504081f05060108010e 72
    0x10f4885200c00d03400744200d01410001d85a1001a0f800c00d01a241429200c895842c000d46400790803990094440060300043c0e0080d50342642ca0221081c140044140e2450713080d40000c00601c4e40405880000401a000c03844448079020305200525242c1420840024190340c40390b0300c110720b240e030001586448080c00d01c3e114001c0d407510b840481c010381980d62003180c0154640201240494002000c401d041e520409d081155a90364001244c0d102371040761218407181081400a8900341080c10300c0d80d03040280c10301800c0c2007003d404141241d010031500c0e90300f9002070050084070f41a40c020950032102c112414040c60806445800400a400d84688103005406a041106184a1000b14020102d12008540f83d044070200900a440f10032201e003880d62900c90310307a01c0680e104502000c09000b00d0041c3c501c0341d40705071003034900d580001a0f52003400000c1c8000103000b003080180e211494490700002218600d002841401d07030350080c051398180022070005100c003191071128180d2160000e07540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 707712706 1250 707711456 707711503
    0x50d0f0b130b0a0207050d020d0806061b03160201090f0501080a09021201050c31090b0607050f01141510141c2418090303141003060e030408 62
    0x100691510790000402c01c1c2040400c205003041d182c2d025082c0765004900ba6844034400440882e220392414140340049111040032034510b080000240012030244540d13032000c00c0e0020611403460704182d10510301240422400011940d00440030b030300805034059070496050502c3d001070011072000301180c0b5059940c5114a0540d074a00c11000c0c130712422040200b104d030601601c000381d99409000000f0801808502600d404c6c80241d0320003000d01381d802c001d04041d0307040c0100380000e458061030a80e8010814807010000c40c106118054501d207501c2d00008140900c80f0310340083d100002c3c24150440c9000313071001480c4e2182c0003102141f100740d140c510304004590030448403902500c040702c05a860b0740c0136001000f50460b800b6032001102100c0c641e6030140e060084421200c0c0d6400303021085210711064070828240d0360840c3c96100e100b0300300031404503202d4001b10380c45401100d400c0741c905049c020070820301050b40300e82250440400065403503c1d0600c10196079540c80ca0301c410404624a0300c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 707713956 1250 707712706 707712721
    0xa0813090c0806030d0918151d1f0308120702030f04091e05040c12050a0f08091306080a030822080a030f09120c03020f1c09050d0f0b 59
    0x140000030304800d400c1004000c920050040c00000210340d0746000c1d20600f4695050103004140d4041110301103455601400e4150070100098111400d04403a6002d1181000c520524070345814944e14110107a04101403600180c103080d448034500799241680710014040c000b01c0c3c8070030100d800700d5000d001c0b0442e090b11119001c91a500c0b4124843c05824030100b130204115886400c911100e01002559203058580107202004a80c81628003c0100c040c026040141d529100040782c002802034017070328103c022640300da142e1780032105800c5a88480000780c0703c0b41071611201c00700c450740101c07904115450406003002c3d90380d40451006401d00c00d05100103050410200075100b581469006505050040d600e030000e2180c100b02403030000f09083c40d0190700348031a20300c2000d00e859000f8108400c02c8041800584110158540c2682140520788440344443c60030811012148100c01c00740d0300b030306140c038001091042c00d90881c501c40c040360380b9141c1c00f0529245a0108650b040740130034216450390700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 707715206 1250 707713956 707713987
    0xe0901120b190c030c020120070b07090b070f060c1404142d03061b09040f0209090106020c010e0d050606040c12090503070c0b0a121a0a030506100807080a08 69
    0x29071215899050583c3e0301060356041d0800c040d105000d400030300100c0902203845074002e44075040307075025110a10500001c504481e8100e500884141088030100b0340351400c1d0b024036030160105445c2c041d01141d01c0020030149106070b00803c800b03450100c082803d02d80341c0c102c2c00c0c400d41c4035041f0003020503100310409035113100c1c0e15001401d51a060007030b0709440c1003494402c0340d120b141e024481e004000c0042ca0003010f40c58000c40b044c0711019854900b83c40c2e403040100a1186402c80005e03254203010000040c1c80f6000030a020708080d070010138000c1a0500010f2610306c01202c00c07402005142c041c0b2000840020740103811420448002c11600300d08001100c2000d2411b800c0002141414104400d1100100041c400f06004420380d0a41d03d07102c0c1b003c00d1061041c0c4898000149152081c0400040960701030800e0700c0302c4250603003410250b4000100340c0c01c8240c000391a660045c20500c0148005104141c000b081d401018181071850140c0d901d07160500710302c004d01f649400103807401c820b4682c107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 707716456 1250 707715206 707715241
    0x120a0311070b10121a040c0302040e06100b070b0a09030c0210180b071a1503010204091b110a29010605030415020906092e0f0e0901120b 60
    0x1a140300e45a400ca41071801044906450368040142c9440c0085501c140d01d103030114a40b50002141d0042d004d1103009110030010040080c1c038191070015002c00181e840d4042c00082c185480018113603814034030507908620b02c40f2351000100c1c4a00b0000400095540c02c40e40fa07100d0700346a000548002e00d810140c40c5940c1300000290b00101c3c1c0c030701540c0c040382c001d228694040810b00700041e5036074845091100758400d03001c000d0141c25a1950500035a0340440090385c0c0207049002060511560720007007800da13001604076003d02a00c80e0b2610202002e0103030311a4240030141340c451a280300070820300c1e4840c00100c0c0050084e20103640041c100e8411400d580c040d5135011080302c035141da55240c1c01011904195400c4403d0400c092101050010a0003618a4607000503c460710b4040d5a504120a418021200381c503800ea11401c02c02c0c03101d1018283c801c840c012500d8202c8040d1103060014420390000c2c412520070380c0c16100600810060340510700b00c0c031380e00414101d030075118504001d0010241303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 707717706 1250 707716456 707716481
    0x5251a040815040b090a0c03081c0e1f090b070c0809060a08070e0d050d200d0917060108100b030c09090f070b0930030703091a0903120a03 61
    0x10224600c2d828101d0b0301c0c8041c4600c0c0600500040c94a560400c252102124030000c0c2c0004071003003040c400b0030a90002000c818a54000307007022081503402403001d03070f1581c20b46080f4540000e1000c0700e010b0b04002905150b2103801c04200403440381555203070040c4002030300000400004140340020020444102c0d030300c041c8010480d5403901581c80d0001c002400c1102e0705000100001040b090a04218081c0c2c4005070384070700507003898402044100c410250440c42c01d130445d00d4405a544030900184080d02561003541d40305e0300c5003400d09403000000301c20004082400e60026004101c42d400100b81e41c4880c0f628400080381803800800001c0c44c017840c00c1c419070741c414001d0f810706c5008203000403500c0301800b480c403d4608031b50780c0d003501c100319028200300c99030052a1814842e05054036000a10b000d04030003482050600c40c004440ca145800141003200843c0d69101d041c009404c01c401814220110301d0501391800020b200440c3c0c40d0b64070110140400303000801c005529501a07005281311040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 707718956 1250 707717706 707717713
    0x91002030a0b0a0b2d090406080312010501110d0305150603100602010b030a110d02010302250c050a181a1008060f030c010c1415070c05251a0408 64
    0x400240c40c00003003145010b040d104255211000600303107a14400d644140c15030407040401407540003400820b00f000510fa04031035120800100c41e541d40c640c4506000b0380440350085480320003545010312911010303003049060001d440510700c9079900002e5034459a521a06e40803640e41c07101d90040854021148000307600ca0004000c2003040b20483e00791000720b88403940203000c5840c8200903d6120440070201400c00d91a45298000c68204141d0710f9486074410f14005142c80026180c07818038011741c0d440e0144540c2a081c1071414042c40741c8111000d800100c0e091f10f1154a810621801410b022040120043d1102ca010460320307291650401d0a60010344510340f9040300c1c105c0201140300407a2074510030014480b020089040004140a1000040e11035080490300c030744400420017202c804641c40c62060003c018071022911607414040c0e14592a41c100301c546501c1d1450906070003220604110712042da04007803000407002e03210100c403850a09140d00d03034211190032515102e6508112020710 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 707720206 1250 707718956 707718961
    0x10c09180b1f02060601081f032d050d110106210c030516210b010608180d210509030a0c08070215070c0608010e0402060a020a0c0e070f110d0809100203 67
    0x141c004c211184030708000d0381c0d09415682c840d00c8903442c0300c1e0103180c006066407811505000007001c4035007c0362106918170780503003103030311401c1010440045240201c0301500241c3e0320080b469000b9101c4596002140c0c001d2102a0801c0d11f0b0144540d104110351550000703103c041020300141c09034140146810205988010104e11001800e400c4039200c0d040751007840002c2c1c0c12490748180452040d981e03001c100010729900e01041141c0940000e042c82e0b2400c032201e00c1c02d1503860000c000124a424080c1c0380c44001d0442020400007294a03c40101c440900b42810080d40c0007020040f200c5000c094102692000414104510300e409540d43c02504080103c181c44a5a141e010141c1100c6216505458103561030301801c44000d0700a1042c2001e01100c200030900514198015100c00d022601c1114000065516802c40c403904546c800740102c6003100c1809032030b0340e00010b035121001c12400e00040300300310410029500e07a8001040400c00038070303202065024001f03202c101d041c190400000d54890 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707721456 1250 707720206 707720269
    0xf060d06030321090c03120909060603062c04081605070b0d1d0705010c06022502040c14040b0d0219020f0d08040209060f0103020d0e0609010c09180b 66
    0x80b20380200e090704202840d595500c00040c602440c61340c0b65200d40c0003407982e491599000e10a441241c1c0c840180184081e0100309a441845214010b001c183c0c2c003ca507951030400c0348403040500340c0000d0040c0c80b00a0481c41c0300c404004001d50011791000b0075075a0381040c00180106c110740e0900c0103003140120700c000100e0a4146026012a28120104125500711441124084400c18206001940040300104050740c010700c2900d2209004000246c44c11840b0f4800c400701c050034101c1c280e90864000410350560509220710300c030140c2541840620300f056040030f0031440c0614803440700d0a0700001380030494102c2c150190703940c0f804441030b4105042c3c0701d420301075180c0e4075401512196124032180e210845108440f0580078507000b80070206507071101c43c14405400003124070907050540070040c88000c5940d52203010102c94140e40507044500700082e0321804d486007005000d0800107034040034480306040302c006800e108080c20b00050b15002e4030f0041440803d81c4041b882c0c11080e4a1083da414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 707722706 1250 707721456 707721467
    0x10f02160c050901060207090c200a110603060607021203040e010b070605070504300816021509010e210604082115060c010204091d15150f060d060303 66
    0x51501c1500c400d01056168800d004055909104840c011b9002440405c800c1099610a280c0c0c9200d078540881301c00c140c0b0030070034070f021119003403d03000b580210b92140501444030440c846405085810758035500b0300b0340000b1894010342401a204000a9240c203909401c01c004607401410004146013041d0780d903142c1d4002d02e0300240c200b55030490078900000c1c8441d202e1030403902a1150b00c03191510903088645a500c1080300d90207042e24090300002c2d5034010403000006010310040c80107604a00451502c1801003450340140f10800d56041480700404580e04104400b6850740c1c1580c0056000703080a400c1c1e200c107032002d00e500c241da00564080c4070a1010340001040d88407420440c9404401c2ca4407025000e00a044600c820210800c50b604422071034508014a241103021001600709621060210100c0358580003401d1084900d0402c1d0801c134070103201c0140140b0040014508610b4000084e040b8107194015003807060002c400060515540c0c2c1d029134550031340c1d00070304000703494032460b0281c80e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 707723956 1250 707722706 707722747
    0x905070e1005010c0803040212100209040f1103041416060503071b170a031103090106080d021b10030e010e0a0311070602280219050a050a0b031503010f02 68
    0x5880310940024034584a41c00498003100d1060399202c094500686845006800240c17041b41d120852034000780c1161b100f000100c05001c03041c40016a02d0301d50304100030848080300b503020031090405031004150040202034030391040d0020034010601d80009102030814614006c0e88032002c1e100503004c08c0360b96108001d54451002c0d900c0309408642e40341c0070304ca80800c2e40d0b0f80c000d000f0702c400c440080e060320480f0080e101c5a040d600307012686682e00c180c4141706801c121201c0d00e030790b0354515003000781c58820040d20403140310a0010b80f901e03188074840649840700b015034a9000b010201c040702c400b588030b0740c04001000703c0000200050044a0101601c601c0c08a2080e00094003803610401b4207800030901000703c405a400a122107110142201c02140d600120000920380100e41a8007589230701c115600c401104108011145017040d08024500381c0ca5000140661500e0006004540f8030710116508055200040c064038031085c00003c7c00b42c5038803144440d8140c000f042009070b40440300107611 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 707725206 1250 707723956 707723969
    0xb0333010318150b0f1005030f0a02040515090a09090b0907060f0e09062e080c03010b120a0f0e030703030b040e03031f03061a030c0301060312050a030b04090507 71
    0x2c0b0010b030b003510301c00c0612a40035001c0c0c8400340320000c1082c280b9441d40240e901c0c3c032014006a241404d094000f03110503086600c21800719500004106481c0500918141c1c809034891046040c1400c000c0410001c0c160b0040462907040b000451817042d9845420722002440d04100900411a035884c08020002c0b05890382c0115100f16607001c10040c3c0521700c00e4040021030342d510300c3c04801e10310400280000103080c05070003040040c10760307280c1551340c1000b101c00680eaa64003641c844d89200c00070700700340b002088000304010510040c0300c411502000ca4100c44040c4c500040591031315a5680010403006004072802c40c5841c00d000c00000e4003202a100d03050013a1001c0261074aa4014001a94000606030005030003c1001540b034001d001900c0c2c40003c058018144555242e6495078120365200d0403950300036810401c0c0490360701d01040251442c0741c06070000d005c11851a541c1400e94a0360780c070150144040803891030000c0348668480150024020001e105462490801c103813602054010762 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 707726456 1250 707725206 707725211
    0xb060d231f061502072702040b1605150405060a09031205041b0602070b04091503060207151112041e05070e01060e01230703050706230711070b03330103 67
    0xd49030002c6085d004031100319981e5010b020280d860b40c1c180c1d80520650060a543c20b02004c01c0500c1404098040d40b140340b0407042c420740c01414054079002e0031048030610341c052182000700264010850341e40000c81984d0104113000d581c6402c1d1903080c0a01301040c17800e4604806c01c030600001d44148101c511002d402602080d44a0308100c0e19481140604109030780c040000b001182d0240c0d1007025a0b450720018403240c1503ca0342d900d0140c1c0d00c141001da401e51075910503030700d980c2c2c000d22807030100300c446c0c0503441d24110100050400c00900140043c0103644180030949148506402c040b070360550010503251200d442d00810106071400380540380010300074251008141d4010f038803d201030030002c400400e11105a440c01241c80d407047d0342c21070400a05000c8400050b5150280d07280d018031790800c042205120f40d061444880c0020401c4040180c0072003850405440844c25000b52814412803a651b681c03035100041101003c0680e45200d40702880e52030a08001b007103801004c8100c00d9a06 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 707727706 1250 707726456 707726489
    0x50403020f1323220f02061e12012403050405160611010c0206040203030f0a030b0405090a060b10120b0f1002031926070e0603070c0b060d231f06 64
    0x4002e01d96130201840a241c464400303800410070300007521851a2009000510300b4004403000318044041184090b40a1008500b01c03084007505000c1c91b005d001607031001c0150440000200200002162a810505d65504049000c0c8041803291a40c1403407400401c0c13803240c1e5110b03401883c0308142c0764610a9546003000005600340702182903801550000c2c011400e111002c040080320303a0141c000b2000703156403034600c00740316182d5003e0584a0a150400f41480d0f115a0915030140d500003040d55100b6101620058103080d080481501081c95800001540014120204480110801130607030300010182d81e03014025030000c010442091b1541c2e84054109640405488042c900313107601d0741d400d4504000b40e948a83d01008158401450300d0440c504880c10b101084140c3e1041d01c0c0300b40028135034014074050100600441d07400c680300346c0e0302180e4031200340c5a04108c0c1d021400d903075032141d401800450948600300001c04402d95007021000c004052245124001c001d03c2c4122a2a15200c004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 707728956 1250 707727706 707727721
    0x5010c0e1c020f0105180a03030507141f0b041404050606010212070206070308070c0609140706090b040e06010c151d01090b0a0e15010b030f090d050403020f1323 71
    0x200702410580c0505903d21030f24000b4010344003600b200d00002e50107440c080519440f5500c0154003030055010740c803030700d5032204103051642e041020407a460350ae0b5803240d080050280700c0c1c8114580c0d8804001e0303000484504000025020700607084907015006689000e11081c444085000b0340114426000c403000c9595511a8000310300500c0c1000c1d41c411030078450100800d000e0000542d011145240c000910181030707489104450103224155144502c207070300140800342c1040090f02604035400c250341c903649802c104403030310b1049010305c40180102c140441c1069000e00054801d0301c1d8026400c20701c008035841284000c0103480304400c0c2031010b004203c0001041803080703001c0c2c2d07904094031301071a0b501d0a2106002d8105100c040030a072003010750000645072f00f2101d0601800d4000070f030564a00b4074aa81e0340c600e40018000c404c05422218244070f8040c2c000702140c003203030740c16a4400410f40c0f11000142c03e41038140d4168880608085800d241009042c10a408408065506074044d840d22074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 707730206 1250 707728956 707728999
    0x120f06010801060c020409060e1005100503010e03091201060b0d09030e090f0f100b0a02060108060109060503150a02070f030f081f1707032f0102061303180305010c0e 73
    0x802c15020444d8602003001500305a00302da4141d6010704808a942602c0c400c4842c5030144106c070700f0101c656030f801801220b0140302103c8005203030450090212134403004040c1c1d00c80c4101d00305079202c0c014010704a200c040080d000080180000310396141c49002704172000003e440300103012400190f422540d03007940d01d020188140101004480c544075962410161040e00c0f1000e0004400001c2d2150002640b1304402c0080005003540e9003d02000c1d4917110113207240140603048004a1401d02005102070703103000894104103903013440c01c0c032001e03150940140000d1050002c06003041500075849000e158110900c00c4000d40c1d00d07030300e20080b9500c0b1080400204148204c42d411002c0d4894104003049600004404c1100d0b4602a81c92259407075842d0003105041000224903070550303c01d403080c0b40d41102d07aa03000800081c00501041d180541c640c83e1023103401c0b28001d05110150007100c101c1c103000100f28016651090007040408107401c400b415040301d04000382c1c0b28400c04401c4184d00119038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 707731456 1250 707730206 707730209
    0x60308120604020f040306050a0608030f0a1106010803190903230d090503060705090118031407080307080306010804031107060302030a110702360124031b050a0504030206120f06010801 81
    0x41104c1418941180e454602810307000e0042801e05440d81804503180d2400d01c000c140c1d00042480e1150b0b07a5039045009003110740c42d0f2460140303980010b4010400c0240201c00c4403240e45924103c000a0880741c00203a60600306c0f6040944460f040c00801e0410344001b10460140454146c01c0383c5000b07440f00d0086a844400f4010203815821140102c0d582c00c1c0030300f019155145050401c01851964848406900c020643c410745d84521080220704403080e0902c1480e02401100380507515140c0c0c552034a0009200c054803190400020400003014103100e04a1400c17600c1c000400d882d41c580c0d44182c000c010750801d0350740c1d101c0300d482c0802801240d51888101c9121603400b4002c00d4107100c95040030504040423002408040c0b074001036006000e249120805d0181218401ca8680c11001c50388102c0385295604021040c58a0800305007000700f10b507048651302000c0b6280041e62030400010440c0c03680100d9000031f4102c080400c0340c0d04c144d48a200358501c203c0c0405403103911955114011145071000703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 707732706 1250 707731456 707731477
    0x14030418051302130f0b0d0b010f0608090307030c111201050601020c0d0c120f050d0f14090108130512121503070b04170c12010b03010c0e031e1006030812060402 71
    0x1060407050104d801604890240f4102c0040012425168008541d00c03c494800441e442c0382d840300107000a03600c0d202c0c3c14018100324949004245040004203a89102e420805400e101c0900311000411030600c9480c000d001018040c0501800d074646041d01a04059039001c0c09401005413007002030411502803c1500d40207186086480e2030004100380d25000500140c1d4502c00c108084d40110380b0402441e984d01400c2e07079400c10414280140107115840c2071107000340ca81070401058205a0303002c491140c100c141c085106070034002038035040d8607114003403501001201000c900c0318007050710b100350b0307602c6014a11003051107005c5200030141c881e00c0e103006078502d0050501c01404548114800700e007802040d1400c4901c0d10815030b0015148150ba643d46001c83e03915110780d20242c0c1001c0c0100901131102c1e0a01100c00005130340000d8484448042c508464a010184d450820301c081000066581c143c040c06c100c119140e051080d240d52041d004440c1d6001b202020826500f001d2007202d0070f2299 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 707733812 1106 707732706 707732719
    0x210f0e0a05060604050c0f030a0e010612030917061920030a150305060a090201020712030503010e28090230071a0a050714030418051302 60
    0x2000700f0013030085040a0601144503003400c10b68189150000e41107803a540e0b01d10214004140d1406007110a41c20102c0c002086140701c1a07066005000369640c9010913107a550144400c0803c03010f84400354004400161903d0700c405082e10510712020000ca096a121066140010450304e90141110800000d22204c0580343c803d00308040f0103a103d110f000f600c2e58444548500008000c1c0c0706d070640f035030000d00c11a031085c42000040c00ea00300d000e5003013207000e042c011700d250001d004010700414050046000b954003500141090446541c442910a0100000d2000f4020109080340c1000c056100c411243e42c07010021074107041e48054105100b0340c40030b101340c40d0440d41d5104074211480251840d042140c030034205c80311403286040c555aa01c1c054681240008094503c80c40203001c0410302152803000c084034100c04480701c5005100e5030701c0d0440349440d41307a20032000950011 = true := by decide +kernel

theorem cover : BRFrame.Cov 707553956 707733812 := by
  have h0 := BRFrame.cov_init 707553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 707553956 ≤ n) (h2 : n < 707733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
