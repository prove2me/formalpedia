-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3235
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:11.417681+00:00
-- url     : https://prove2.me/submissions/6c7d6935-7fce-45b5-8cb8-289dfcf7718d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 581654676 ≤ n < 581834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 581655926 1250 581654676 581654683
    0x1b0706091a071d0a0b0705030405060c03210f040f030c0204050a0b1002030f03040f0f050709020403030e04020309070501110102041a040302240f18040c0c03030e01061d07020f03070302 81
    0xb10b003140030403400d41c503150b68094004000b100320342d0000d14510b041032a241120806500c00c540484090104100c04601d40e039a16020341040480700d0001d60f11170072220b80300e035400b11181920820032480c410030082c00c6c100b54454160301c1680704a0282c44000701d41f0f000e580f1a0250740d40254050700740402c000b080d085075031006821030800c4400700d000d0082c3c0e020a90701d0b44681e0901c0b204200701040024042385c20240214a52031080b4801d00c04000ca54668030704203200b07508518419130b00007800300203043d48019080301c403a008580071071035801e00300c140c15601c2034184909418000c400d01c03244103c0700d00798195001424031040b1400860041c42064034507a01034001203120b010f51960000c4c80650303861101034200e4540c040945002e04048008590750020300840640e041c00c12150880c0e03440310b00030001c450844d42c8540840007864076014094402c50114040d00303a1629404101d00c0c0c40e290f050716042c20110110040c2c546803c0c008074140445440c4000396803000140100c01c15a000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 581657176 1250 581655926 581655931
    0x70309080a0308150a0b070803060303040b040e01080606040e0d11010f0f05090f06100608061504181a0303041202030102072a091b261504050105091b0706091a 70
    0x5a049004c90145041103034014242c000c03005108401e0262400040c0d40300300440d00240c0060489082c07030340d6001c03105c032668000d401ca54054000385004100c800e008100e86500801c0841d824000c101916907006c0d40e8030240141c0c1410082100d44100c0542e0003075001100039001d0f1401070003400c84600e00e0001400c02074800c580c051217610f066403121400894054011982031030042c919524100e400c0f1a4030070060180c640c030481140842108440c450002c10040403a900a42200a12701080740115504584000030541640b0300f03050560740c0c0030048400b92005480c50611070076060020034028082c100e0000c204040340088902c100101c4600000740358624940340440c545c0b100003220903541100c4680c10822040181010768500a5840407010643e0382c010304541d500071255404285800e071034030144d0086501030441d260800d8000c5501600c000d40e88514241400034403c4110099101158904040441c008003008410f802c1030216940140740d83c20911409004000d810009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 581658426 1250 581657176 581657191
    0x90f19060210050907030b07090e0403031407170601050d020408030301260304081f1b03060614120106030509030c01020703050d06050405060108010b0c03090a0f2c040602070309080a0308 82
    0x10255698203103402e0b03001d107030701c02e4100303030080c24103c0c3c42e43c0d0300d040c2040d40140106003400712000f000708080700c12120041c45140281da012030006088a4450402d010207419401045038180181c1054681503c2964003e00b00307103822640c4002080c451802402290400e41490000100000b400d0712020340d10040c429080c00d000d140300158425403942ca200e43e1140040582240345240d80104020580c511008401d18000c5050680d0340d0f4120769144050401304082540e13180305001c4039070702c00c0c00b001c1d42d40300035580d891901c40103203601c020800c01440b80404044c0c481c0b0019198800600a450803040080c00a54456000b4600070381240c03c4a504043d90614282000580e1b24040c042c1601829040e1a154090303403c00c0d06101c603580c40840f400359188410404240c21384c880c059244001d0500040b8150000c4c00c2078500042c4901c8120032449042c58105d0b9000221000550140c02c90b41c088001030381c401a07842c003601d2000c56a07004d44000c0c011040200305254121100500c960340 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 581659676 1250 581658426 581658433
    0x30b1902041e050a0e041716050105160f1218080f0702040b180601030b06040815010510080601120b0307090f050907060306140d0c050d0c08010c0e060708090f190602 73
    0x12141c060103a004030303038410658540d03c00001b20300420b02c04800140070110400410b8034001200403100380d202c01c164001c503010380d074500400c00409540614a8a840f0b203070726144240e40c00b02e4000621050380d441443d4040303556882e01401f40740c4d0890341103500c00e900c20000c2c1e44440703503036030085529000540c1c02c4c0c0c06203083c44003180307035494421504007094803521004500b54486c580110010214881b10380d4000c0c40801c004128444200105280486d000000f00500d47c10030b0280541c103003800400c001802140030520410703a80048901400ca401d410300040e01040c07860000b45072004c07a50040e10054507000c0b80101109254101d01c1c8609105012075840941c3c9580450484403240700e8210b4500da08440312002c1e1400601c48040c1c076003e8142d40e89259190300014407116540c1c0002c139a510040768042055190a005d9001c000c040c1b030a00d401c0c002c000101280d424861800020084400054411444d0f5102455041540170103002443c500c00d100728041d2609105000e098007520 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 581660926 1250 581659676 581659679
    0x303180f0320120a050901180f05040f090c03020904080f0f092121070c080d08011a030703020a03020d0606021b0a1404150308030c040f1707030b1902041e 68
    0x20000a103a921422070142c095140c004c41d0a42144c0680040001d64100a21903c02004000c903860720b51020b0005480c143d03400c00e00d03040402080341d4006000d030500724100000c1070040b81071841d0460841c0d070182c4042c8503d6031245003280c8548541494664031400114412010058240c05404c3c1008180c072410744201f502d000c00c0c0c0340d5421040c0c9807041944044244080500007607004121840c3d011205814041c403a56261004504d80d001031402c0d074030101020040d240e202000394010086c0d00441000e10006a0030340401d84001002e010074035030009030380341081344203030b049600b1008401300c200422526440000e44980318100e101c04544107505c44804145000c0841c001160711001007006559211018040036206c0700304501d2524003080700c00404a120b0200451084c0c500c00c6005039101c3c24101c8010404505400030780d003242d500340302a40f00f50400104601a6a0000c00c540e0036555051015085841103a5900c0122400802c000409500c1c143d00e00b602a02006405640176 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 581662176 1250 581660926 581660987
    0x6010608010e0f071404030510020706110f07030c0309030b041104110909040609080c0303071e03060501051c0615021e0c010f030905010b060708070b061504030303180f03 75
    0x140016145a0014803445000c81c2415004500b0845d4101340101002c0c24039580c0c6c0c4403c1e00300618410b03086405900081c0d10000c000980c45144190044001c11900f000500c840301c00603409078503001814869090100340a040c0592940c100955101c05400307071501c1c052420311000c52117900c846000d1800e020a002409081e107040d108000000350404600d540c039a21028040d001c010020750701c901d000c00c618004158180010740c418820350b02d401c254805440a41040303038408907100c00800d841c090050117641c0c1d0100846401885485100404040300301c89080200420791112400943c0c854060610b160082030a039509107201d0b9030440c40c03400c40d9404640703d415010340d160001e031084460101da03d0003a4000000140150300005000b851080480c80d1b5a01150080d00ca580c008641e10003003045400c01c45600001c203a4161030b01e00c24210320040d0070f00a41c04001d0500d03884040c6003440c1c400d420000d865403900040910030300720090401402d03003031071504e080f045207000c4440034091 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 581663426 1250 581662176 581662199
    0xe030a020c0108040c0b040e0711010506091f090501080c0109120302060714040b070f140114180c040213030c081c110a0212101a09060d031704050601060801 69
    0x52500907003080036044004689038400200121814000c0b0302001c10591007410142010300092682200c0c40d0030040c0e0701402c0318070540c510f44820b038104010030030740c0e869280c08180c000300103075016503214108060b0380004540f01c1c0c00491040d450a00001120300380000d450010032020780b10001244c1c0c5803211a803a4089100000e03025038485e84c040b03078070184101004e01031400503400060078152100d02c0e001840e8000700f010b40b8480c4a0284080a00080184030044030003450001c10046030a1040c0c0040550700501201c5440c0e1078207507e10b0b48a00502c00880c030310740d0042c4119030b5210051410700c810403d5020030741300d5442c080340200d2098000203820035544020b60104034511215942240d03614a40c24421140c0d01644a19000580f910148084845481409000500005020042240c104883c1440101c01030101e80200d0f07110160350b503401c0902030b1500148103400c0c0c203003510f54111030203a04104100d454200014000c0200d0304505036852540d419a003a6070f100d118401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 581664676 1250 581663426 581663437
    0x30d1b1218030503060619050310150c061a04110403050c0604060516020a05121b010306060e04050a02121005100807020c040b030c0a030c05090709120b04060b09190e03 74
    0x103407584124640e40820b014802071940700a004046602d442d0b2401180d01c001c080022000340800d030044180304034060b031070660102801c030a6a140d0168084400700030a8452141c4001d4601c0750350b0105210280c60f407000354403001c100a0710034082c0601107018014194402c0c8001d032005e020321503070741d100b9282400459084842030b54406060914111500866030903a001c1241e01041c0d14000181c0c0380c0310000e10250312104c900c0a011030102c030000801070641c400c50800c0c100b514000050241359004000c455040d03c041d01c00151941d138a2400e00002d00c00c01c103041c00403401043c100010003100c2941c0d041a00d0055030501800702c08460151407120b0142c3c1c0e0840075803c8018241964201035000e40c501100050456a4881c40200829105100c1e6001910a01d2210b2804e1046d81004100360740c01125a00d04849014500031203240d07400300090005098403d0207021a060100603000082c402400401c1543c035820020070003001042c189420140e9030b41440c4092000040c040159030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 581665926 1250 581664676 581664701
    0x6020f12031e0a1b020f0606010927060e18011b0815311103040506010e150301060906031a0103170723010509060c0c100905030d1b12 59
    0x140e0030501d103206491a401c000b00325030714440e696100c58070341d00181c40c8005000c003507940103011b084c0e1900702c1690074008020f0210f810711113150400c01100500404414600c0681e02c1c040700d0310306016581e00b020380510740c03103c200c0803d05020710400f444540c40713a0340002e031110000c002801c2140b18062a906003040c0d0030340460301c000700151240409000c15008201d00421010300340300d0303024500408003c0c4c1c010109104421000100c04881075129001720940c3c4003001904528060f6210b994800e4140142101c416030140841e00803105640001070503a001402841107640354911000182580d00c829601b001148510b26041c0702142081c5040c1e0f50040b01540120880c244851200d502c10300045640b0030802c0400014418038802d040706c01880200040390a00340480200d02e0908003500a42c8403c108200c00844480700181c01d0160140070700c0c002c605d01005017070403030a50060500c4900600d0600c5586061170309401c4080384411629110318010420110807a400c46800e055a003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 581667176 1250 581665926 581665951
    0x315190b1f030b04050f10091803050a021608160603151a040f0f0503013218010c0e1002031c0f151203030b060a0c1103031306020f1203 60
    0xc4000788140207200511034050402165a00504020804581d0101c5006c82c101c46008188014100d84c1c3c040c610040c0b1520000340400d494070586004003411105d40141403020000d00108d80303d00034050761810801003c020b030103880c1d942c03400f82e85070111104c2c1c000007109000c80104d1000d01a105050414140c1542c401060b424030350000200038100407241e4800106200005889203200c2c42c40b001b604259000401162801c406e2500b500c010076103404615840400c00894420340540d41c03a04d10303c04480b50103d42d00e5160168000d01c1110181620550070981450101d03908074240d1852180140c40104d002c070310058080f82c680c080e07807000c0100d090307200000c01e07020070880d0400c00d1540d03009240000e01c514445082071014034035030301240c0748050345a0703c0424560541b02c0c6c00074009040d5019841d00b051003900034031245c04400c00078041c0c00e5106161419440c1042590300d0b0465001a0390031260b11441d000c0e641e1903420850300040d2064401000040054406903405804c01d012031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 581668426 1250 581667176 581667199
    0xa06080411280305070915030213020f04090c08040b09120a0e0a0510090e07030506090703092103090209010506071113020c010204030c03030e03120f180315190b 71
    0x100b00b4020070212030480d4110a80204004500c5003041160041d03104200410700540303001080000c0d43d184041c000025082c4003420005a16603882003050001440001655202111550440e0340502c1e08646031840c43c003c110703124030350400c020901450061090390041e80c3c2e549102c0b5510b203d000c4043d00300c55018071a04010b140118840c5881e41e038000e00315205e00e80c8410108503140d414400d90000285211300030420707034041c42c2ca401d801c0401460248100c1c44c004002c11141c0f00043c0101040556524104c018410f10800a00c5a0540f002ca41c00000b10b035000d00034058030900c9000c0e4410b08040c0e00020f070a1038624100c68040381e0240c000001401c0c010704010720540040007000ea0b05800300181024100700b88010006544074030349d0940410b0850500900c8604603044103400b03517001c0e0300f204070208000301c11795182c0700c080814036a58440d02e0b1010780380543c0000c010b0f034040c4240c14604800f0340541520f18410140300807002541003031082c1d00f60980e02039500e40d81c0c01c0b2205850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 581669676 1250 581668426 581668429
    0x21040e0a0e0d18030b0702061b07050a2d0b010801111c090302071e060818060121051006210c0b0901050f0310090f020f04050d020a050a08010207020a06080411 70
    0x203500886501c0c06603143c01503940d0380ca6031221800d048841300b005030000ba040111035108544031b04400c01c0003201490400c80141e030703640d0b6101d0862002a00001a9203108401401c03424200c0c0225041540c02c00401e07201d0740780c03400b8801800e020f40c00f80365007801d8100c80c2222000003030b03030307008040185220418412441204018071400c03074182c1c11802103c1021030407180d20040105031421300b100001c0700a144c010010102d10303024002d0341850707002e00072039108100c0000e80075065aa01d603a03041c1e80400948504030300f0034040c5074000d00702d0058103404680021103911150171210300f00340b14a8040e103100060304030014408001130100545082c1030000d0501c0e4806801e508406062441ca042d4055903446605d400880e001c07401c540c1e40c480c082c824052280120003030a6100740c0c0550800005400000e0b29001e503003c0d5500542180701d15005560318600e41c0c8000b4280600303c040c205448103550707070107580080d070240d001d047d03001800200c0511555406214a030854031404541d64010b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 581670926 1250 581669676 581669687
    0x1020607260408120403080103020306010e01030f1704051305090d0305010f0611120d0b010e03030c10021602040908040f1d0109021602030601080f16150f0221040e0a0e0d 75
    0x400c25583da81090091078078207010f82e401c0d40e000358003e0b1102012989144109441c00d10144c0080c4240401c03980100000360240d0f0802040550140360601d060a0040e550416802140d002d0369105020b111152484219644254000c200e40030a8038801440c5c0d88050b016a00284a081d91405110740100710440c07055a01d032400c000d0107070036680c1103098041c410b00250420a54803082694490b0b81071200d40e045600040c40f024150069410058603060564036400000b4a812000d0b030000341200c10780c00301c1c145001281d40c0c000c008100d00055400c0c48030003508540114141c0b042100e10204540c0c000384035407204603124400c0c1201d26802e0100c5a40650045840448400750400032600166014840780b80038203018402081e001145058007448c2482c0b202038034542a400aa050000a0300003850701c020f4034090070b20400400114000303e180400044800c0780907000a890214401c201600038000c0780e520b40c190651300d4450314645421100c00d440064059809440805041400703031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 581672176 1250 581670926 581670931
    0xd05070b0a091d07030b0904230c03070305030a08090c06040612092319050a02121f0504110909060f100e01030605040302061e010306150902180102060726 68
    0xe00c0d04445403559903540c10840a0f07002199103c2c03034140390420001d242d05220b0001521400c81e940390660410b926400c00440c2d8850100a15022405d100e00000104218006015a01908480d034090f52410300540302d8100e0441400080c0e040d80c0420b10fa4400013403aa04074001c002c00c03980c0340a02e040003d4482891402c1116182d6480b84424408109140c42032000210103a4034440012041508141001003078282d8040c10301c0508801004100300044218400740e0607071b00440501502d206151030b01c1c969102e10000960903040d00c3c003c80c00241c100901451050880210340d444c26000c000341060221441d02d05640300c0b07070005aa140002d020917402a01e442c076a000b0740c0d5291401d40c40415002d0f0801d81d640780d240c030184000c041c0e0400c5400d07848800c80d0071108510800c485550300500041c07101278a2507031101c0c074548000d0340030700404c0000c2405120071550381480310f14541580d83e07455038542c05400b544001030f070100e0180e01d000345042028030b083e80d400958071b01140c1d84100003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 581673426 1250 581672176 581672197
    0x307080903120f100b12010e0a0204080c0d05010e0304060f0210060605030f04020604121b050406030c09152403110901210204050603040b0a0606021c0302090103090519050c0d05070b 80
    0x1c0260000d0500740c40c600400c801c0484905d26501c1f5814000e2041c284a400740804280d1403042004212003071f030201c0d0440016100300d840c0c1c0022000380c1411030142c00b0b0412241181e000000e4006a141d405c100010740c044410307001da550407004041d00300100c8080f0712402c030200da0304000017602909000e43c5150700c00e1000705070504054442c04411704c031000102d0103c3d00d0030388a42108051040c0320425500801084905000382d0741155240504000c240c49000752203503c2c0c008c206812030364108504c01a0858100040106a4001c001c2070204412040c8202081c40c16414101c130398161012a0944c41c0c0603142c0c0348080d54141c44200102040c08071003071078554244008a100e80d104c1000750300076400b400c45040907080c8808802c0459a030b950049055501500d4100f0007201a404901c0030720704681801030711003c0c2a40141d01900810400402900660b00d5a444030001841d92141503401042240c0481007004103000c1803111a0b0700240503980400402c00a05103414000c0c29450070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 581674676 1250 581673426 581673451
    0x110d0b06012304080f06060a0302060a0503072a06051608060f040905010509010c09120302070b070231060501180306051e040303020405010f171b07080f0307080903120f 74
    0x31402c0b1610201d80241e080300b4030541298510062a0f0010416950840340440d00459181e1550703002a01602c43d078180c0394284440440042d413424001e08000c0c4441203101282000f0392030400e003810003201e007050100c960b1860074001c105402c01c1e49124490036810b58844c8000c0d0f8403a0000c20022074104060a64095244c4803028002042802142e015102070300000c500b20240c0d002c054055a800e801c4980c00005041c01140420b40c002800c208403413070b200e030040c0e9840341da0010407294181c8281140c010304c0c105480c07012000032f0500300695844101001c1000503201e07001111009101a5000002c0144840500c0841c080b584000d41012032422000c403aa0000c40c0c030fa044400c0c0859069010a03404a130400040d42c220424180150261030648030200a010004c82d03010000b0346648400700124510fa010f110702001200d04607900007040c10707103900208501e0303c0694001c0365000300040c142d50114170310b00000829100d07040d45a90010b0a1a90b640d07048440820000700181040710 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 581675926 1250 581674676 581674727
    0x40c05040b0301090f0609110105030903040605031e040c050a080d020604060506040e07080307170306060717040b13090e06130813150309120807020c0603060f120a110d0b0601 77
    0x207071710340088030b500c510445010a602e801c83c184003004405400e20b050500c0b00030001c00c03070005804400c580a40300d0301e0601175240d468604902c101ca01c00000250401102d80741800b041c007000c81c880b00100c80b000c41c1c2846441d51202405925602084010000b590003a00400c00007180c503000b407548050040c100080c4201700c02c5e007407403038007035036900c44055904001004002d10075101002c540f124038450b0510700d5030a02e80b000c680c0b50b200b500e2001c1e02083d0040c19900300403103040e0448008006c0005403688440801003080442d844a100300c82002d0b1520075051100000410814400d00811010362011406600c40d40d849500c20ba009a15441d4460310200f9010030035042403c0302d240b683d03400502005189410010301d403440c0050424407200508000070750381d000402110808080c0d45d5a0345a854041c00b00345e502ca000c10506501c40040c4110001c030b084006811250725005041c1840c0c00c070794020500060003c1000090309400d501c0c80012515401a0302d040d40c0c3c0141c1c040c0303109104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 581677176 1250 581675926 581675933
    0x1f0813060510090e01140c033d0806010302030c01050d0209040c0305040302011a091609090f150e04020f040203090c04090c0f0602030f1822091505040c05040b030109 73
    0x880007158181c2d502d0b059654140301195252041c840390304a03140080201c0c050014500556110040c51120700700c50000009110007003150540c41c24004420240c011145103c0c11030b08006081480d00d0460741d160700d8002684000029014120b0350007030041d0640150001c01194242e008441d24041d141c0c003048980c4103921140701d08042ca44180d5400130303103410140740c001d096a00611046084100e4010300c000255212095a50410b16201d1074510303c58948070150384800065014091042c81c0541941d000300f442c1e085000c04020b901001e91885454582200c24050144c03000b94011143c3c2d480e01030303181000c1d4011900b06507400c085500c04aa0311000906407a03007100202d0300b00030400410862200f60030b4854000d0300f040d0011b036041c40c4203440e601c90b05026001301d2040409180f0407035103142c0c4801031000403018048036090030000c00e86203050003410065800316240c00a44011404540715486043e014982c00081801480c3ca042d0806c0050500184081d515540c2c0300d4418001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 581678426 1250 581677176 581677181
    0x3101505120a0803041211031201060f180308041d010b070602090a03050a03110709060e0604180209160210020a020d0c060f060e0a050f04030c0b04030c060f02090a051f081306 77
    0xa900c103101d4140700c5c04c01b40d0002001c10b07908190f0549694014010700c10004130030322714a81510107524048402507240300c001c841c00740000030180386011120b00040107100002004005841410170000740c03090307051502c06400b031002d20403071250315028056000001c40c55001480c104030020110b004c925160740320242011514102100400d10920008007013400500503000100307030f40c1d0f80070401a031420341c80e203100110040425100d59030b250203082155130740403c40030815401030103440745450800c8080c0c05100c8140303039000146c441c7c5907295889241c00e000316031240340c0780c0e40034040c81644001309683c000840d4604071038054032500400628903591103000014080940e006055040c660310b494110359001d043e410100c0e118000300f0022036042004d2010090b0301540040700ca5403581000c6646c54003001000b4206810f080610000360140e4000d01003060003118084180c0369101c04000f01c1800d4030162502d00601071580c035003414010b04a6651150b0007002410420704285c1e2100304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 581679676 1250 581678426 581678431
    0x191b02010b100e030705040b120312150a06050405060d060e15010e0901030f120e060a120b0a060f030f090f03030507021009050705120a051b03101505120a0803 70
    0x5030355030008040a4680b400a0b01c4003507a040c100702c11a20000400300f034450505000703103401a03844241403086a1901307060000029039450681e51036a403055607191a03c0001e0b641120440d400315014021481d12840c1d10341181c443e921964034040c1b402d42400050340280703284103c40d6035a004002605c5408607401c51003011201810240c030b841c0c0000240910800681c500c0c025100d4000500002d2110941803c40d2a040f180340d803001d030b140840071128a29182992504850082907040c40e840c1c0040090500405640c01407010540110600c104600319229140000b110144d0340000c0d01d01a6101c51240903c1d400c0100c0c8000e42c5881c1d280301c243c60120100d0020381d40d081084040b590504c41c031752413200380c0340d814008079119813a06c0307948076854001e00c0d00c00c9100d1554041c044008000f440c0542d54800300b1713554401401500112610f210400d810f0113801201d03030103070510220f03204070807007081d081d45a10022407e20382401144540d10a07060b18a1080000c80f00c003090440002d5803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 581680926 1250 581679676 581679731
    0x82817131a460306170303131b0e010906050f0f010503130206030f01060807090303140d090204180302060a27030e0d050309150711041a1e100806010819 67
    0x390300c01c5582c0c034010304541e9142d00140115a01c0807202c4002c5c000481100c2d004214540d452144414600b481c40c03400000c0462020000c030081000242c2d25010020a4101ea80540c2c04200071680c0313109002040d00311250243d44440503014004103580504042c58011050000d90703c50440168003040b182e034820b40c1c000d03007002c450800420419610000040e408405454480601d501d507a5000e425070201100c0d821002c0300120f00d0140003401c0740c1c4034105c0175130018014455488040e101c02003181c51007070140c0040c00780b84000b07101d50101e4058000c1c84030903241c603449140040303140c03d47c43d030380414030803400c00850300340c01d0203076940d009883e148250096000e180d482081008104030040005186034110701d050041c400840c2200052022610064401080f00d074144110100100421803c40781e00c442000444020184503030303900030504005580301d884030b40e0508820b403503d200448015000411a0000440203200191071900c08102c0710340200391180d03441c2c10052003042c10754100d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 581682176 1250 581680926 581681047
    0x1b030c120304140706120f1803030b010e31090f0308011d0402010504030b07090312051806030c03011a07060c11100501082817131a 58
    0x244042203c1d14650740b503001004041d003030300e0000e01030101070a03107122080859680c80461743e400c00542100741e210074001140304406005140280080c00100001d500180c40011042e50354149030342c0d24051608013543e2070301810044071640402401c003421206455441d054490001920410f0302d02e1494070030740b9501c1c0150f040c110800507804401c1580c0783c02944a40034000541d80003c00ca50035250040400c940b41da4402e0300654548616510003002c42414541080c030b0503910502400686000503030302e120446155007040300c2c0e404250b80380718a25004100420a00b04029501840c0c044841191401c0001d5900d80034129042c0d290b040011030841018035484940c00d00c850742280360404020050395051110582c1c1d10407030120302c400403000901c040200c10b05030b11907094020342d01c41d111002000900800301d050b070b08081e4070301150707103422400445e000e4203d503d00e410a0384040c0c6540e05062803407081034502c0c0e00c18118640404400d0010440b044403c034100e9821004000c0305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 581683426 1250 581682176 581682181
    0x10303030615020105070f030e0a140706230d020c12120105040501091a041e020705010209010207151409180f0105030c100c02060a03110d0501031106040b1b030c1203 73
    0x1c1d084190b030006012085924110802100541145a11800405506e8001089424109001c1c0b0341200d03c003010b4480030301015850003a06001402100b60742c5541e83d0340b0342820f1142c070907076155604658400c1d010402403200c0e14a4603016406003154078507550441d55010b40e000d00040443c0e01c001042e0808040394001070000d810a4020540105940340013041652203800c00d82c0441800c00750740c18416038581d1040c1c00f50020701030148a0f00e60140f94210741d500048d1074a2030003075110420b405d0150050440c00584000d14805848800c890341c1c90300d40c1c03403503190201021561f01c20309406600030b40610342d4004c40e0b00c05c45011403141102c160000219414a001c0600d08a1204d02039445019508141460154049101802e2641c1039901e281c503400d41c0c031001e8016020003011041c0f6070102180f0184414001d40006040768003d041c0840101880414002d4074492802038218240341080102030410b07020821b00601080c4005403410214940d1500307082400c064121404040003005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 581684676 1250 581683426 581683439
    0xc1e011116050c0915031b1f11011104051207030308010e19020c03090a05040b03101a09090d080105010206161b05070b04030b0a0b0d030c050f010c0c060c022b020a05060103030306 79
    0x2000481e004680b00b41e800c07900c000002d0004d03499071040592300c40c141c07003034403482c40c041c400c040d042d4003c800081c400c549038084a00c100d03800a1103900d00c41c60880e201410080000714a4400352605980d40090b40c1e030070000c02140d88000030307007030a1b81100072080b08040c6043e5480904100c0c01c129014541e00c0741000100a208012500420b11071460403003c5040c070b07a00007401c3d0411134022100883c1900490480d06800320100200c0ca030002e01c1c03601000200d10020a030311402c40010349030b40406903262801242d54002c01c60304646048000004000700c14050120300c07003602c41880c0101d812030380342c0d41d07040c0c04c00e070136988050080080402c00f8410054a6081140e00c00d0284808000c4101e40a00190f00717010405400340c14803440721900c40038420148034006c0031100c04002801526060300c8014420748181e042544d08500d0704850b420402d2020466003d0980c410504080c0d00c0f0b002d4205982400e5544500400d510030074592000048042c4902d40c0210302940300064101d18160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 581685926 1250 581684676 581684683
    0x90c0a0e09010e07060e1909110403120e100305062701082a060f07050a0c060f03090c0303081e0f01090c05030417030c07080c1e011116050c091503 65
    0x101d0300d40740790400038040c45466880f81040030508011913010004e480d0711f108100c02d041240e00801011400c11400706201d1688600810440b4840d45c03080c041141c0d10f0200b1105507c4042006a100368101201e00d0004d100307411607504008001d0803110100c5a402181400d04041703151040058441c2004105015040c06100c104560590f50381036203012001c00140300103d8104840c0c400c080104a00704001c0c0b914050f40d281d194480110386621045041c20340485101d03114060020302801c071412040f81c030a020b4050202e5001500700c0da91400c543d41907031b190100074490030307411480d01c00401760900720070070003030081c880b8800c00c511365410702e800082911104030030b103010301004205202c0021200d0b410030003040300010f4080e4494481a210070307810301c0f0f00400540b205002084105201e640401c80101c1d0084076a407050040b00c40d9401c1c45d0903030341380f013005001c40b00b001d00c00d40d9807000580d500400b031180704d00203441510b000711f0b000420250302900e01c0340100c0c4001c0c0b00e10302903003403c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 581687176 1250 581685926 581685941
    0xc05062206021603150b030f0703150b0907080702160608010f121a090a062d1e02090402040f030b090609070e0406020702010c0213020d1112040308090c0a0e0901 71
    0x91001d800d86003c405064091480c440c0b10040c128200985a00c0420480790b1003c1505280202943c0040c1c0c501c8203450350701d00c0035010a542c0d00f14400d0203401c03140d00b144140f480c501409000001c00e540ea20406403404200180b11400394041c03580362107250304d84001c1c0c8201400d070945681c07200c3d504010ba038001400042d00860744002050350001c0104600d50f0104140c00582214100d1a0f924607011a04180005400405003810b03c507460303500508224002c5204202c1e04150b10a103400c0c20400e00130744134025400c5c02000c0d50b6034103507010070200307400401030300030003030400762905e55a024020802181a4803d49800c0868014040024801c1c0400707070300034403048000c007502d0f030a2040501000101070001080315500295440441e4081c420500045400800e803842240d8001300f40400f135404110070000c9607180000c0d00a1f04140f48080d1074611442c0710700d407250380d9100d03503068500a101502c0d0268500c1144c140584907500c0704030707041c00b5080c030350514412401e100800c2425517404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 581688426 1250 581687176 581687189
    0x1905040213180c0507020d030c08040e0a0b03070302061608070f1103190b0106081e07020304080c01050313030302090a08010203130605010905060123090303030907140121090c050622 80
    0x7003d014490301c952107019038902c2601143d00b0f4091300a2481d00f40d601840302c1030000c205900100300080c02c2408051114800c110340300c0d0500c00c40060b2010181c5440d01404004c0d409201031281443d5558000b500d00d00182c270905c00c0515149940d01c400d040100f08400803035069500c0014035207a0300b4284110110381c480e50340e901c64060348656a4120183c014043c25080021010008078800e94603042a10340d05415641d881c01c034100210002d469038002e0103040e5091081c4900e100595116200b00c030b1181350000e0054a940c0c4441c0d4089010b54050070f085a8001d001039004100c0d54000e10045002e8104480b500f0826909440c1141c191303013050340300c1802e240c1341000b0064071748d130070807050951481440c070b038081152120b00c04100300780520340b00e040d09840301004114a0704000646601078920010100390207560100044034041c0004d16403c04032040100c540a956505402241d81140700307040000e03019444601240490b0481c0000084134450b0480800754020710f0f21804002d00072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 581689676 1250 581688426 581688431
    0x503030406060b040b0304020103050604022511030a0b060f0f0a081f091101032a0503040506090706050409180602071b090e0d05070212060103081323190504021318 72
    0x103171100303010050100400203814103807984000341199503030350304864a00c0c4604d10f035941544500c03180b22541c452005022a0104c165602c0311446207070004107440d0903a4031000c881e860340d4a903c1803000c03000410301c005402c100719048140096072500b0040c0054214803000b881a1030210900c10142003038411099001c92402c02440e021649401d201d0032000301c20308010442d04801742070054210341c14407c4103150444c1418043c001d5a0000056015a028200301c441d42d40301c907150a40c45600e42d114030300104034104010484400542c2190382c84840664028045c4111602c500d000ea0740054802c46085c115038004064502050120601030700300c80e1010481d030244294004c3d40da03d41c1004034410701034007107050b108564a000c0c00783c004003501004d5995039696407410090340d4000d00d07228089803038140000b04001c01c2c50001344070103180c008189002407007030390b0038401c0d01500d00120600c014400c0c070010465407500d0000301501e0a031810701450072454040d008924442030f075440e422050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 581690926 1250 581689676 581689679
    0x618060603060509060d11040216020126010513020c07060e18010f23100c02090a0b0108040201050307120507050d0612081206030708060405031e0c06270a0503030406060b04 76
    0x11100b0313501541c0110140c5107418011000c1c1811803440140746070350365205000045030010481410300c4004024401c1c0c80700c1c40c0c2054011f402c418017100b03844140e01c10081203c010402480c01001c081004800c00e100107140c00109008142441441d410000110744490b2103038065041c003040541c0c401201d2070b4040c0c01941843c2c9410b6a107801841440c0c8145d0769150b1086c0820f94103031030040c812200804a504070f1442600182241c801340805074481d0b0242c100060140003980030782c2c21a00016541e913105503582da8015030f02a04081d1200c1c08010f07d4440c40f0b40021214441c003070180e40b064a03041c1c0c90300302640705802540c0c11034200c0181c00140f030685130006413413617013550340303410307440005030181e43d2504003003440c0203610791190341c0d1071150100b40418050b003c001084015008202070f0040358002d11680181c1c0304540b05419517a10803030000d2400c101100a044081da4001c0c03070032001a03030310100c0924040e413043c01070720660000002d020070043e151103a10014068161660300300b5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 581692176 1250 581690926 581690929
    0x7030c08060907020c280b070b04020616120804020a142b120e03010f0c0e0904050c1207181e050a02130b0306010e01020609030a1b050106180606030605 67
    0x32001415007405202c0e240c011982042c028003070400140e40c040c0032404554441e40711040014030000d148402503469403004101c1d40c2040f401c540d021600490b0304115512141c1c01e114996112004040d078031000f015009000030440600d40704c1d80394050352034130000c2c00c2a0041110f1039031180e010300d41c00c070311700017421000d40c80c3c100101c295240a01415488c101e140c421454004402200040400f0480c100345404160408807103480010280c0c02040f6080b031020244040300c90450340c52011441501548140e8580000401d074024400c0094401140b80344010582a0b0700d1140c035600349810030b0b90107201000c2c00c00e2050000e01039022046c4131010225000301c03034801040b84628410b58076940062104599501101c2200d180e1904003c1031a54600c0c00d403c0a03042a95064002a200f1003051010341c80059002d0243e039007400a140f410a1081e010344245c0f0714025030502070b1501c80e5413403010880030300c00e00b8010000e0382d2608503071402e81201e00044900e260000000d151a00600b070146 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 581693426 1250 581692176 581692187
    0x1d0f0616020a15110a2106060e0405090106271503080717090a09091109010b22120b04120c0b010306110c010603030201020c07060c0f06180f1a07030c 66
    0x4036401818070f221002140000d030700a0080500240e81c460b00010f01180080e40c011184a1090600004455015000c903440c2d8207460b031174400c03000050810b03800740c0c1d124070b0150f00c1650801100c200002d40c403030b81e500c0b0b20384c4200d009952448411000c0344046502c0c50807801044e081c00741d44850144150b080d669034411174002d41c1d44c0542440d0419205051a50001085503480c03200180b07080429070381d5104000207810b4920048030001002002c24001e0309080c01128142e4444901580c2000d00002c0c96654000c4003004141c1400342c05c500000305100c21500003001c550082c481c40308a4582803c048924603005101d0303208100101100c4000701c1d2168520f0350540754842ea010410311512241460382d40180100e040701d95103403543c00002c064055006040540c0d5100c183d0310b07425a01e810a0f99611000d410140800f0501004000020304c0c1391b001c40542008002d2030140409140c0b659443c0b49805e00040b070f510382e100d6030240e030100ea2080640e0f6200299280030300136801070000040ca03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 581694676 1250 581693426 581693443
    0xb0a0b0d2f0a110106120c06050c0d1b06020d0b040b06070530220b09031002070305070c1512020c0a0609170f042402070b0d1d0f061602 60
    0x40c07800000c211203030ba0300d1003040c3c16480349201400900c801505d0302440003026048440c210344d80d254501c0c0000b540c034000d0090743e9041d00f00340c0140c1041140c1003015103070b01c107281c6e1036200400c5407108000c00050b640e03c0500513408003d90001440002c5c075082c00b08030b45042408500c00d03901402081d00240d00000c43c08080040108810740b0300c0300682d07160040010709141e141aa50f8081001460011800c03080d400750420b150300e0613000c950b01c49041c0240d110301d00c4010b401d078010115030811000c09400800d100e900c0303860560300c0c00d54592a0341e149407105801009001c0551008080c05aa0040d040c1c0c40b1449055011071800c07104403002c6545550505005000640344c200c60001d00c9404009070309802d06943e91590f4403103101e01003000950040c0180d420302004802c4c03000c0c0c01c61103c0030301c40e0010055001050628101486000c0d1030708074521214074952100d40d402017003c98012180c421b1100e602c02040100111030800303041c103800a1151480407641c02000886940c002003422 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 581695926 1250 581694676 581694761
    0x90c080a0213110d09030203121803072004110a021216150b0909030909010f0506040308220303030c030b01080f13050c030115050306070309051f0b0a0b0d 68
    0x142a412002200c00f403402814491450700b8039001c000340c140764000c402042650212003440c85a90b0f01d0b0800e003203000c4583c003d03882d0b2070740c424001d080002d00c030781c01c10baa51038001da0210007080540301c00040540f01f40c110003e84065011038400507842c0c04000100146002e20700160074011440803841e50b4260a42c0060500c08485100c02c02505081d41308a040c080060143c805601e000590aa82c0c0c4d0f1144040500409100c400011301c282d0b4112610b0541d4001440c0750b02d414034540310003d031b81c1c2090030f11048500780009850f454815440c0560011031182d100414044551107001d000c80d0b0f001c070321a41c1403040c440100a0a07101145074580c3c040404c101001c0420611b05240d031620031860351a503015883e180307821382c543c4200540300b8201c0f04220125440350f42e40c030300c00303c0036034103940c00082c41907000d03104080080143c3e441c10218010326030000181001502d00007000009258003d030f07076401d0005415414001c030740c003e110917403100500000b08840040c4018003405410b45091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 581697176 1250 581695926 581695931
    0x506011209080c0714030717060a20030a140609270304050a0f0e16020706080c0904090c15050a05070b040204180501050a050a14150111010c03090c080a0213 69
    0x941c02c000d00d0406498581c185482202ea0740e0751a001302e141c41d10b002c8080c2510030b20030f50a0004492640b90003101d024110390002c1d00c1d01e0b464112500c4060080d8202248500425016841150b1142d202943c03007804100c501050401101d8911000660007804490140c0c0e204010040b10810045981492100d0022880c1010b0070782c80e02c0300c0c1036000c0d6800196001402417030003e0b41828034041c5500340d45500002004a44414000c3c10600c08810b0310400035800468042103014029182c242c1e10032203007031029150a040750002000c6030300b0542c040701c86441400742170184401004604079203030002e08200e49404075040002c0d0981c090604003c00010004000500b1522560803202d6401c085140703c028132181450400d000c0d21040784c40c00304035880d060020b241d2140c5400b506585030041003d00445884019a484422104c1e00071581482295401c1d444500c2003407090f81240b62459500040c00d820078500f240345004207601000b401ea002090702c1001d80d07200d0110804644840100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 581698426 1250 581697176 581697191
    0x307050a0209180d121e14070512011203020c100302071131060b1303111903030f2d02151b030916060e040b12120c0a120f080a05060112 60
    0x28400070304401054088581c5500140c1d24030006c01c4c2d04070710f4045c60310f004128015a124007007100c00d4040d40c2c50251880b040741d4010422900003111f0600203a0181c41510642d00c0071401160401c1c0642003c880001d600042031402d101610045001c185030845104060426400c08030034008504001c01d0030b03004130240303806210b10742507000c0303c02010300d143c0e0103860304100c1c2c0461408450511065411070030030480202c4503c0c0a000e0440c034015141e16074919103045807400c951003540c1190040911840440e0700e04418142c1c1401e5200d0f5a0068440d0100e5810250080c00d1245030f443c3c200341050740d01b06200d03080d944188801400c400007504940c41c1d076103c80040d880c0840480044074001103074140807940680c8055000805803003680c00b031005d62036102c02d00c5a071000c8001c0c10355064020410040390b400404c0024003220000d181110603507040da458042880340b00320001c0000c20303003c0c0144000640c1082c01e00d81e221840c000d08000c80c1c908a40040d15003245500f01080300ca507540c51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 581699676 1250 581698426 581698457
    0x50319021509120607030c18030c210f150609020f040e0408042408090316030e010e06030a0203090609061e0a2705070801060b040b03040c05030307050a0209180d 71
    0x84200e03850362000072513130381d410300ca00042d005054490b06400080d2001c1d0800e211392003614030000489030f000804c1d022152034030300504180e150480440c0740798544100c07210042400400d0b401042030160170040d4159800d0708a200484101da80882c3d070407801070100c0f14002e0411801d0f81e01f12800480ba6442c540d540349000e112503c2a03800c5124000d4180456196103401840020308045403929180020f1702d07500b211660b00d008080c031040080e606404041c1c002482070700341484468060401c240482810000203000703406c104d0b4900d0501e036000c000c000700d08000300203803600308407a00050712080c101b13440c8648a5103080504800701e203d980010507450081e56011369900e00d1a6101114402a2304010442c82942d00506503010303c0748420118a420701032040c80112487d03480300d90701d040d203841407203000340e04018019540258240400035a584051000b441080c0c8038402030b0228040d03602c1085011040030b0624514880104c0d00c0d10040500000d02840300c6000c0d003000240d0214500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 581700926 1250 581699676 581699689
    0x601030c200c10090302090105060f0d0e0f010e01270b0a020313121809020a09120203010b191a0a09090504020d0210050d0e0d0c02150403020910050319021509 70
    0x215a040404551030f1002140d002d544401603900c2250040b050f40d82e00e82c10800c1340d00401c080351050358400c0050891038107280d400039560080031010758425103550b85029086488265449116944405500310b2844802502000414007541d58400420194071307858202c10005142e006e038140d0000210b1000c40c1800c0c40807440c40d80c4a103852480d2420840b004003040a80420040d45240c10540480d000d8040d000351a211000c90352005521440e10401c1d031000c1c2da00f400141d0305550383da800184561a1039000301403c403216803003800c0107440d1620b880041c0300c825400f07030403540701882850805913000b9140030442e00403038004078030394a5900000b102400c8900d0000c0d48040402d00c0a030f1956000f9000d00141e40041c030007081124103040083d61103c18a0301c0c81d40019050044400041c546802200d00c083c01040001e0b0405469038041207044400751021465110040020003451904015031162100d81c0610101c100103598085951080300d0210194595030102d14100c103030320f421 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 581702176 1250 581700926 581700943
    0xe061e0a020a032c450609070206060d02060f03090c10050a0503010311300c0d0b010302010c05032728140303090d06020c070e070c061116060b090601030c20 69
    0x200516590745c003c03001074a60030300700b040b0304020102858000901c6132800c1e4120521900207038000d420f06071741d00c100308040d54111038400c99202c48203100ea20092040c81014511904460b401004d01c0c004031420080a040c110b01540d042203010082812030070350101c00d0fa41140d07440050f00c100d4002c400e0000b4a1f200781d01e0720044131104000c5152a801c0e1402408a41000b120b2042c0c2c3c590b00585c00038002206c0c2d00d0712000e021a51400d0041005520803180c0d021007078000c6068904082c814550103654490f513030840084c07003440804c00b03500c0c0d24200c2c10070b4411620074001e50b010b118801c1c0d1040401e0a043c4502d10520700703a0140380074642c4083c02240e2074030100603e0750010051505d4881e0080d0440507841d04c00703104040700800c0240801c0711103805040c540d160480303000720941d07804010748403111004481a0041c42030407544665038500350001445044c1c04500e40c07044105200c00550300034105410141440b0520b04d0050300000c4582c08040307080100181d00101a440d640340c8002c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 581703426 1250 581702176 581702239
    0x11071b030837030501030c09020711091e070201050403082d091f0203010f15080a0c0309170a1106100308070c030512070b010f05010e061e0a020a032c 66
    0x41c1044802603e0707140d400703a070507244600340c500314503502c17580400101d000c4c005004064412000512140d440d1000317405030b100c034001e24481c5042d400070f5059408808195144800350303448500b80010960032000c441d07400b1041024040d040c85052180c03403814600d4034583c400e8041070ba00030580841042c0030716046403540e0b9a0122505807030035182402503109214541c0301006a040c04544131503030602d202c0c0c2c1c074030240c2c3d02c5800580b0354a600b4001840d07005081402d1640d1a60004002a4004c0410b81e0703a50a00c000f0031b80711030413101c0c0940f406d40c44560042c81500301344104540c4a17011030f11001501e41001c0d020362142244e29000100d52020f0300040d08900c01e849a103d40761000c24020402d4510032508405141d0381d0708040e440403d240c2c0100c60100700302c4142d00200e403c108007d042ca032601303515806c0728500f0000c01c48006500c045040801a080a5064000c1c16000ba51160303202d80044d03c9102d8603040703080c01c02010003020424900c80e04090490b204007040031244510840c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 581704676 1250 581703426 581703517
    0xd0b032b11031909050f06120c040806010b12090106030519050f070b040807080a03081803130902090a0f0506040611030d0f021b16030204020f040911071b0308 70
    0x68443c00d080f48076440f240b50000a10368400c0403816081c0128100c842d4030000d88801c0c10903145e940f034103214200003081c0b0003505030144000074030748008005940c02054001d003c07503035032126030101000f5902d005104919070307810004100000b44001503c000000c1007a0a40e82c61030600e41745c100d0400d1a2403001000d51311a4200c003040300b000c44002001150001402ca40c401070384c90084984902080c94084c01003070744100001d44001d2410b0070034090586c1e0105581c64083c0080807409143c015400014599901159485c41c4d1b040001c1204040c0c600d480c65103016074904400150355210700e00880040144611282160503000c0040c1c80030142c1c21542801940c035064003050094101d10030303444403500544204654190007040710442400c44080641c4c070107045400384006540301d07242c0384114071401c00c0000340c80401c0f8411004190f000000071541e42141d07040c420744400000d0400306458406110401c0098000c0007102d131400300c50303c0c080c000501c43d4142c0e001ea00c490704c0744810700f00c007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 581705926 1250 581704676 581704687
    0x105090301023702070e04031b05100b0604030206160203071d0a06062a051204180b0303091f0201090b0718090203061302030405030f0705030d0b032b1103 68
    0x1a410b0315070310341c3d581e00220300204141c0c0a2100703807402150140c01c1000358002c05000c4c07108041029134103078020300909102080d4000020311610a000c50700055480f50400c8036504100c1c28079001d0301140280407155103050500307540010f0132520810f11903880b1f10000078501011503c007404010010703c166411041000381041001c03210650803618031000178900040815200e00421400200c500600d80c00d4018070114070b1068104007940030140c550340300b05541211a600d0981c001c0c40a0025086004c1d4a440201481d0055404940c0642c0c8690810b00c624440303510390b104042c6ea1780d002107030084658230300c1100030f0b8014072042c4805010310b03100408024549030400d81420b190106002e0310740a0315540c110701c900f24001aa01c00f5408545003a0407002c00e0016005507070414050723001e8918280d144000c01d0716a500100703003140c1d5900017141c1d441c986400791141083c05041500a00b40402e05070340101d00c1402d5104005a0441c010320f02c4a001512540e24440d40e071096004695644 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 581707176 1250 581705926 581705947
    0x405040f050a0c080c010216030b0619080d0908070602060f2505070b090f0304170f100e100504021807050702030607020715170f190603031715090f06010509030102 72
    0x10681c2c01203604d41d04c00c2c642e01c40d5103944002101c6809044075984251803d040d076030340b040380480103404282d06c440040c0843c81030102c140d03980002844508014900b01419403405003c9140690240289410112003005895008600198041d0a000700c8410319907806944035400c41d602801e2441d8959140d0021400301e8015004200e4140910054800f550307030301c422030342d5501142d10307400081d03042400704014282601c8102e041c0c01d4003a01c1601e07100c1d400184560b103000181e0020f070813074030748401407013182001c207000c100200c0000760814010307403a090300812100c4030700120804020841e0800143c035284240b050302c2e800e0754010169036080c1821407000b90750302c17602c0c0686405941120002d4201030b01561882c0c2240e00f0342c09550040b583d5140710000d403400000d01038100e039103070380040c0a4403840034410000598403a44a160760403450110050000f8001820142c154085809034056a500c141c85290710020810030a0741d543d648100484041c01880c510303035015800480c145651 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 581708426 1250 581707176 581707193
    0x90903030c090a1802120109020a020a110103061e1a0a1b020d02041e05070c02011b0c051206040c140f090c13030c03060e030703050a5a0e0405040f050a 67
    0x206444440708801b180d8940640900b24400c8000c0540036a20652076100001c400f0109031040c030b503050500044644d1b44000f80d80d0042211210100500d00b540c4040c4215034480740a0040040744d020001d0a211007681c024000d6020b40c2c00d04143c4030f4581c20f41d1421903075002c0c15403140700e5018000f800118613800030521030241c0b4480700c2444c48d092400160482c0d12034003140c1031090f01650762040420032a110510030707820151069a0b91080000301144989604d01c0345c55817602c462004101618280c10040c032030102c030790400c1300164400520010940da60030a41078640d4011200200f00340c58a800400d1540725000044001444204001003441070843c4e0301011240943c2081c800080d190f80f4040d01c074410048014003098040c00b1084a0300c0c818100d074850a402080242e031104188440e035490b442c0b44401c0c0c0c07100000826895040d0b075000036024074080344001c1b039200020041500c003030601100040000d000e1552200040d00b0312803c01c012000840d0400140c40300c3d0140340c10003100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 581709676 1250 581708426 581708437
    0x31914040c090c140d14090d18062106231201140f0901020702040f02090f0909121c020c2116030c02120f07050f090903030c090a1802 59
    0x5a15050500c00610b00400c1e009803a81c10409560305070051010202801c19500b159102035180340d07444642040e60000d01002c14007440d0050000e20b41d11440860047c204a591062180340041007103080020a4100050080001c0c08819115064290010f514000c0c0075941c03015000b0074509041403560355115460340400359081d5404601e03561400599030a84041d000c5140506404000150a61281d80a160f030805c860700700152901000703800180549100103115000258001a4003100e0f00d02a004021104400d49000d041894160700c040d840351480c0d0ba05444482d00014100003980303039450300a080b000d17004170464688407400882580c178490004007680146090300702100103084917043da401d681d20341804035080f00d1281d81c200c407620000c58040b600059559415081c204080c81440e5100200e20000d0280910784410449410301c1c198100d4001d94500090060032040481100d43c01084455055500c17081107000c9a20140613a020b14030300d0f03026007852485440b01d90020413 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 581710926 1250 581709676 581709683
    0x90a0b0d33060201110a2601031a0603190206030901060e0a09060605030304030f020418060912120e03040e040804080d030e0606060405010815131a1206070f0503191404 74
    0x188140c07161003c3e03080721505190048081c3d424040d80c403906d84606144a001c0884003400d8564128181c01414503090a07003040b1440501c500c2191104022a41101d42c05002140104502c04880301c0003001c10950b0340b0040e000d000000002070807001c09411031002000102003200c02da29041c14004010043c6850803507140e0308080c400240c0b482c0000589050b0b0fa0803511007070254080342d080000404c00c140340236000303100c4030385c14401055031849018041c0e40500c150000c0c1d0b0f030304003500a040a24041c007889030039152958160002900005490958003003010310034154a543c2000c5100b8000c0c0d51041400d0321030b607007030b01c000c0c00e41c180c00c02d24401d074440049944075129001046100d01440c015140000c04900c00650a968212480504150068500040b40109000010580784c04503030361031030035500c45180c2c00c450038201c644c02422800500602043e040c071039401440360301a8a80c3e00b00b0404d010002c212100c0e20761355100030301260118200010035440d9201c100580c011601039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 581712176 1250 581710926 581711021
    0x903010b01020705220b130b09090d051c380d0218060420040f1e030308090f0321061008010b0a021c08040b090102090a0b0d 55
    0x6031a5400003601a066a10041200940301c14401011112402c103068001d81541ca032160040c03644c4400b41031f0406140c500c000414668408000c0c4004048084c0c004802903109007105945664004107481140e42000d801914540d01101010013415022640c250071500c0f00645419000b903460f01d0001c0403488807054201070104404000782c0c03000e44000039400502c0315400051b007400079102558400740c02440090004142c4462180c0c180406220016040700081c040c068000280d0091740202801071100940001400f0b00e901401100d120080922984201040c0c2c0e0079400d0000c0d08034024407004494032441c91003030410155401c0e14035440c54880800108040e07040c00e0008606400b07107900c0d404220703444c200c0310302e045910821214046020b00d11300c3c007002c08501307140c1c4010309005540d6404542042e0500c03895100700074041c082581c0c810802c801454441d0150101100e090b4522291100300051007607000e000410785c03c0c0f8003400026003010752500f120112110b540072602d070380c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 581713426 1250 581712176 581712191
    0x6090e07020a02010e090601110a033603081c0f0501170f210702090f0a0e0a030e1003060527130b0402060a050c030a0c051002070201050304060905190602090301 71
    0x10707a1a11070701c010190001d80b07210711020440c04c04d40e081e540c100c1018580314601084c43c5080034101000040f0450000c0c40c8102da8440384a00e00d03140f048440202d046000860007140621804090300e4030005003000804101c0c800b44c2c20002014154502e1016001d004005251020400402c1c0034010f591000386541954001c410b00014031240e400c030760400074010540d80940c44002c400342d203403040818030010009030005803078520100740200084014080c1c0d03420646c404c2020f4030f91281c1c1e829101e50000c100000481e601c80760b0354100000c01e81b142905450340d8801240501000c1e0000e6400644a12401e40b80201b5000400d40494041c503e20b4050f4a803071000b1240c0780390703552000c0d080341a12800705c1c001d0b141c601c0092011500c141021440d0010b400005415078101c505038101003025410050706106040c800900100c00300307482107190502c20b50000e4580d0001810203000035541e480318a08000c000c00c500421428000e0300340c0090109860654003950100341c00c54000e5080003003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 581714676 1250 581713426 581713441
    0x9051504030b1302130e01020309060106180608060a09180203010c141803010902120a03020708030f1804201c0606050301060503070c17040504050f0c031306021306090e 74
    0xd40d0160396011002ca540341e268040d9100e1a0040d000e4241da1045900c541144415403500c2501300032400c2c0b0740096101d24151400e1070038920140d01070010310000441c00c6401c04091800e00381540e1040c10403000c070752901008900d070a90260000d1513501e00d0140701c81450141504e822503214030071802800724101c0482c08442d00013941c00001c6460f5070a02c0302c0e1540c00b84100c401c690000b0088c00000b000c000d1600003802d40700c040e000d05481600702c030f0460340038150306201642c0a8000c0600a514105c24050b00e00300b030344222402c0041c0b2583c542001e40c0c840ea60342d00700d003e02c1c0d000d4906d00880803501c600449100d520134140d401000403400d0b16040d480589000e09003c8401ea03466450460b0f1804030180d800340e100400182c20080c0945105e00000c0d08803030030681c1035050016054446062400340b00890384003038508940404840108400c9150a50803070380c2c8840c100d04160302c1d14006142c98800f0703008820140070801e503041c00108403107500141500440e0348520002000340c56015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 581715926 1250 581714676 581714719
    0x4060f09030e10021f060612050c03010302010e060705060c090103060503070807061412010e010515070b0606130e01121109040809060f0d0f09140c011205041e030905 73
    0x400200802e82d9664074241500c3d020385000380c0c101203030041e502405078401d61080c40340a041d020102e0203940c1c03102071040b00c0c5e1254a007406050006420840b908003101809503038041444028104410702001da03980761207070016204030399480000c07152203007064040c2c09055084910043d0019141c40380c006090b2400190040c01c50741c0d141c3c090000b0382d0400d00c044880403550080401c481c2d00401039843c1c80030408072080d008240c040024032035941003008101d5050039404c0c28100c001028480800414000841242c00410449060741d4881c500c020794148105107a00c1800e0f003442c00400006d254040d81707600031038240b04070000c8030043c90801c104a2080d05c02c3d18040c2c9402c4052080f141d2508005000b403041c414005a01418160030400da00242c0e00d194002240194550916108004007503030059005105480540540c080c82000207110407104402001f0641c0c41c0d10220b010300400203005040759402c04160802490b007400c0141038103e141c401c2901800d42c1e8100c0102e690680e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 581717176 1250 581715926 581715941
    0x60f0904060f0b0a0303080712090206030708070e1c0c051008340309021201020f0d0203130501060b04030308010b030118090203070b13051201060506090d03111504060f 74
    0x808481160320340c0c0c0c4440c001070507540c140c0410706507540120001a910440307010b004500c2a80c0c2c000d00c40c64201001055521203140b00704402d030903c040900140c0c0e41c0e00690742d00c135180b45002d4a25682c1d90408070b8850351080351186e0885416620740520100082440c110103020f0810b0311400b41e560000d00031028038203040000041c54010128415108500100c20501c8200032003c000c540507466003000e01c600600101c01203540c50311544110f0501c0650329003820540c000031414400802c0002c401442200c580180c201d60010000704070440304116050b003117420030002c00c0b80d19250b104c40c124550040c0400d40200700490000901e4440c141c0407203050b54a00f11003000c100002e020700501524008100700d038540544840400c1c20b0f0161800b60031442e80054100c03041ca46030106020f4240001ca11248991b4105101405151203400413a000d4640544030070710000550b080c11903802c0a16000224180202c1d03001d280031110704521031340100d0107201c081104100050540c4d0894208 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 581718426 1250 581717176 581717179
    0x3040f12050d0f2a0503130303021309020c0f0d09150c050d050405131103010506090a0306090308160309050c21010504140c09010e15040902041d0105060f 68
    0x404460100040500c02000009000c6042090811100c91981010340740000c4128010954580030b00404508048040f10643c8000c07501c40d00b507400003e001040d9100060038900c400f00a81400707402c01d486917048607103421030401030b0030040744c88402c2503020b035008603001c030304520508480d200205404200e0154148480c1ca454a00f14035085412680148404490b0706000d50450840c0100e90140206542114035a40b52542c139070403c0100401651080300810845242201b4104c0c140e0b08482100c3c15642c0490b0030035240c0b884a4000f908000031900010a0b041c2403140d01c0c0c042540000ca050302035034500d501c000f90300d1000343c0d0840455000480151865010420b00c050f5820210300703c000c200c04400c0400002c443e003102e0b103425108141c2d0101c440104540c040c494642040c400c1c409103030380c121550307a041e5141c89170740c2e4078603100076141580c440da01e5828030205070b445501c07a503051076001d00207200210380041c1001c0315030300740d0400245950a002c00140c50707280140c80302c40ca0000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 581719676 1250 581718426 581718443
    0x606190b090f150d1e0e03090f0402070f150515030c09090705030703050c0a061e110c090a0b0a0501031b0c0528030e06040f0308031f0902120c0304 65
    0x1e90400b04841e0a00000010350032003150301054120140d0100241074a1022034070120300c1c055184490f62030000402c00e50070301a4500181c0300d001800110072500c6038031040313818041c1090001c002400a1048020080410301c88500c00010040b80b40190210500c101000b0402940d91803104030402c10309510103945600040010b1780c90f880c01e003074032980107100501110403d40d11040864581940c0e50000e131565848001402c0c0f4500c1e00840c0d5034041c152030b24212421400e02450104020a154101000d01810745400d8584240401c40d0b90100341e001000c1c0e40e100e041c55203080004111250b11280164a0880049065400ba0241803110702c0d0030710002c400084c4001045400127940401101e560041d81790104880d10107100010b0007014011503280e01e034800b40b070054100c0e07480c0c280c00703401107a00740410800078a03011441d90890760450b92150741c81d680d0b800c040010200413024030404101d08140460b0f500030a9014201c00030301d54180c0e00c45511b076141400200d000440d0002d11010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 581720926 1250 581719676 581719687
    0x30c0e210a120e0f150310030803070908060c0703020c130e010c030204080f010e07260d03021c09080313060e0106091e0b0f21011b1d1f02030c0a050606190b 69
    0x20001c5005503401f43e401c03441c007041c0c5070b1a5580c0103c039910903211200014184030050200403810301c480c60300100110740d468544503030303950701035225408001d10034400c1c0440840c00b4680b2686810108a001041000300603440480704044e000703401500880129200e000400319401d0303014401c0103480e075419801031076030624018200841c1d801000702220051581c1000200b500010041b04900d00c1c1c0c00d44026858900180c100c1055195031a0099181c41c146014640402c0c81201242c1e0407900144603130300b000c9031500b403800103003011040c0e507069076280000c00078004220303038403504aa078145182845d1182640c4400010f9070414110503a0003e0b103009651401c0c502071320007000400039084001058100d181449084451400500c540d090412030301f01403550b0700c9141c41c02400c4032b02c041a000f0b800740c00c0c08100400510301c02829404c40c0701105c4022140200291003c440e032080407100c80070501d10301b0540b139040c150b0b0b9140c01080e200400521f1410300112910589584c0c4001500b0b00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 581722176 1250 581720926 581720959
    0x31b050a0917010b121b06040f030609062403020111070b030c0a03060510080f010f030f060b0319030909050f0c2d28030c0e210a120e0f 60
    0x340003a142d8142150b50762003585034152038294042003c690701402034140c480c0080c0d01c1030701d110a400300340351140104200c02d2040f010503540301429207400c480c0000e2005854039113080200740c0c001d04000100c144206280903028850a9001602e1003a61340401100007041c040ea0313200c0750350085103800307417007031001503600c4201402401d524022481e000c100c0554820101c3c0d42c44040d0303842d1600107204142044201c500c40311f51940100444820b40c050741d0320b0741e12103008420b509640204101c4d1a14420103250b5010040c4150014484100404064441c40d0140c6a00d440e40f08104c0711509000001e04600700701903807148129007d03d0002d241c40d5568800b03c00d0744a110703807015421811100349140b00901c100c05010b0b0b440104020340d40c44003407140301072010741200320300c4010141045001c646031503005e080c4d000035140c281c0e800b4035088504d82d11004464146030300002140720340c0040c030003480300348881c84000d601da50301c1320207000003107400707108123844881072160b00600c3c03000205014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 581723426 1250 581722176 581722199
    0x912020d030c020c22140723030408130f0602030a020601080c0904032d0507030206060f1309020105070f06020a11120a0f0c020315060a05010804020d0b090a050105010303031b050a09 80
    0x1402403108011161101d0b01c0b210022a0405100c562128200304101f040c0070360015141c0300c0b1440120543c1c000d5101c2d1100004641c0b00060004082e0300000c101c41d0341e810501c210003c041c03c1d01450f403440e0340303840700e40081d40ea410104140c3c00622803070000080d0034401285481c200b51020342218080d941d29207040e62001152680300e04880800b5103454108209010300d182e1011071a501d0980e100d41908009140c05800340c0302c0361081c882d064000c0d40581e0781e0942103c46018005002c038060a641c0010380702c0c0d00032701d900900b0007060318401c08108030709680100302c00c050a0b111000a130740d80300f0355960f032a00c0c403c00113a00020108034928126014101150158189290801052180ba808607003008420a048103d42035641d05110403842c21060300400b0382001c2c03034600c00a00c1d0070740000b0611114000d01900c80a10034021490051003406070001d1150424000e12895940303150040081c65000d030600c611016103122250f83c10700c104200e445581c015034801d0111400c041e10b0209 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 581724676 1250 581723426 581723449
    0x31b0c0a1215020f1b07060f030507120b060c01060306050615180405280501170c0a140301090b160806010305040f110a090c030506030c0a03260403060912020d030c020c 74
    0x102c071105101c0612071001002d145c0c40340c00400001350090a2510b0710203003503442960304000606040c1010003070040e500c150070701c50203030000601189d42003851001c234095100c1c01000c0041d40d400c280c030101c14440d20b60421030050381c00740d400b2105040c11403d14001c50154a9201c001070000c0d41c09007440703144c190030141c0c001d00c0c08207003852150301e000159a0708100800480c51020346030070041182c080ea14502e0b0055115180140840e900c1d10030000c2c01011250080c4000700b084e804101107251800d5101c050f00301d0340070701132442500344200403100c40d56014243c1070002e43c41e04000f9241e135100b8088e42c1d01030782e40f0402901032101d04e5941c0810100d180101c0d2600b10f40c03000c100080e004c01303600600150101d1510000f8050034080281810320442c05c1c8040c1c01104d4002c810800101800c842e412802c42e08241031403201c4800c010388800d48219480a48a60f0400341218140301491850011a010b560210b860010010605900399000c04810b0f00140c1c02c009101d84850514208045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 581725926 1250 581724676 581724697
    0x81812042d090902010f020c0310090c2106050705070317060301291c02012c0303070b070f170c090f040606030b030f01140a020705031b0c0a121502 65
    0x151400c030412203000c41d5640c0c0707a100c03940301c9803207005030707015542c1150800c0d000e00d0781071010302245202400803070394654410b42410103c40c3d4881c0d224091002440813100503002211a90247c0207181101c10100042c02600351802481c1c80080717000c082c010000c4454165040d04c43c4007854201c8074240601440003401c16030035540b140210181181c1c0c2071043c000e0911100d90404d64140d070f1b40140711035945403400c040c5082c00030090003400350b85c012280034030820b16900d0360b08100ca86403d545824180d0b80003074a03018400402c10100f04080e0144107881b40e50240e80d44842400d0000003210180b5641c040c0304420952000441e001c640c003140201404140a01002c0f00391900002103811109244c2c8420002a6640e440c3c00030fa2500b846282500300e001e40c000d102c070415004054421110103040c1d110034540c0001c01404101781030044d9002a03c1c0c0344000e894681c0000c200c551501c40340c2005c20301c0b0b1211507c01046454441c20b510024a0700040728060390b20851103403d009600800082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 581727176 1250 581725926 581725979
    0x1706030d0c0501090c060504090c020a0f0204051314030715180611070c080114060306040507290307020c04050601033b0712030314060d030e060f0a08181204 69
    0x80422074900c0c40400030003107a55088d5030f4528143c8003030101c65603111b0f80740840d0072000a02c00440c02e02d50b0501100c80d01140d0000300c58485004c0c62024851030304000703019860b040441c00014902102030402030f400f5011004c0c8129038150340c201203640e16290844d550910600c940042440c5038009034244003008002c83c5046455101c1c0d480c14612684103030342d140e445909100d81a51001d03540c1e40c1008040c1c0080085040075521a51940340c0c030b0040850001071001c07180700141d02100c01c1d4a40da4400c02056640f8200b03150029103a09985c43d1183c0203500701800326500b9440b911440e00700a1a28041c6820007941d4a00d2016140f2441820513074070604030801c000c014030a000784c1c0001c00c45480707a00c080303a50503e801380030303a079030240d07180a0010b0031002c21a6540f44c41550300702155040ca8060b4500c0015400203038a0302400c016903442c01e6000c140b0042ca260440c66640c02900c04844800c03502c0c0800d424180e66019200044841c92000c1c48104090075188424134400c85c010100d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 581728426 1250 581727176 581727191
    0x3080a09151a030706030209011d0a17030a320c010605041d060a060e0c0c0f10061e0308120a0b04090f0b0604090203061b070203070b0a1706030d0c0501 67
    0x541c06540b51074015802200000114031800e03d0104030983c01403455060131f6007440c10480019100c0452080c001d481480c0c00da03680460b95948070306e508041e04c0c109904403196454040c805940e501b20306215400f2420140b280b050811034001c0403049002e58070102c0104150000440c0401c1d0000002014259280c0c5000f02d07096903030317010b401150156240c0340c1e61000d400ea140c1c0c51402e130028250300b1089240c544c0074000d501c080480950f00a08100701d507651520800c030864600718990001c011107014a1440e080d0607212a0007100840704102000313403000112201301c1004545920000308040010440140c40300b9018402e46e50008600d640000d03603115110125042c2d40000c4021504035002c00c408004010200001c81d42003031003950108810103060b0301007a5100c86c041d02a9000c461600451203100e80d184088684156016050b603811503500d01004405800c0103032211302290400c1010101c501220f002144208001001402c4600c1c140506a07a140710482084d0390719500d4480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 581729676 1250 581728426 581728463
    0x102120a0804050706030209030714011701031101090509060607021014040e06040c0c11090c1e0d0e0307031e0507050d090302040b060c0318031501060f02010b0d03080a09 75
    0x161108400e562105100d03071401d45070150030710f011608014107240c070510100c43c5a0b20006840c1c400d90746e14115502d000c0100b00d0040e22800f80307510f15580c9250030000080b08004540350404501c02081e290140d0447e1103404103e01079104540d9107030000818800c910140c5401138207035074003c0a0341003803144070f03008050454031035004d50030800c0410007401c24004c46041522035030460151a203400c106203c01d43d074607000c0c0b40311400d14084c803441c59000441c0d65040d80c00304030703241c0c08003040060030718401e42c0c0706d42e076155042000c0d4020007915090384040000300110484500503415642c81400e49800d41c10b00024100c6020143c04110301800514002003081158150081061300e5911549107184100801d645c1c511208502900c0107101c00f10501c08008156034442d520b00d80d4559080c40b9103004a813400c401c14241c02d1b0310840d400000031748543c21032800100199036900a10942a20b00c3c00c2c44401d000b0010010b0000d813000d0006031001509502103c030181c40303005140d0508580c000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 581730926 1250 581729676 581729713
    0x317030604060803030901050106021c051912021602090106050708120408071a040b1b04060509060d0c0801090b100923031e060906010f05010f02030c030a030f0c0215150102 76
    0x4d1b91268580c1d510790041c000103804114405d18000c15850030042c04103d808000c0c0180164214842c030440f500505221a5010703198914201614900c03c546812200108a04810307617254141e0095280d0301c0040f82e00c0340304400725400103800180ca603203007400140c0b1100441ca00100195140f00042c00484009481001041d160780300100d00f0018608150400540403240503185a120848140d01c40c0028010b25050307508489042c140a42c45440810224941d44210315a290b1080c0c036001e181e01801c1c0d0022645410b80d00c00240c20014110102c00b80505006403050000128030103040401c4003101d00c02034080e42d00805c2031030301603112405001ca8a0319042403000101c440300f14040ca0401c00d010021581e00c8200c0a00a12595161200e900080c1f5064014203041080c400c115207421340c001c00444640c02481b00031070f0740e030b4200b52000400500110149828441c1028002a4134074800244100720b407c02c0c015209030780e142c03c0c40c0d207103881c070101b4900e40c1503001d21900b0b05003510554 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 581732176 1250 581730926 581730931
    0x110d080d14070806010f08010501260f0702100c09270c1d04142a04081b01030903200f0615090106080103050304030b1e090c090709031703060406080303 67
    0xc1941580701d0030424000b5003002c000400c0305040102c003030304024420f80e00800d410704694082c28501901c0c1c03900d880c030401002030500390841c031b00f07400400d2001c008032242680788100c01603800e41d90588201c1d031003001900d903104113640000700c19480c01e210419040011580681012010a805110a0184034245c4000d0480800401c0300948403195044590001688075602140c04000b405031003030403804030520260602240701015050305804181d090265540c4002540315a0384840d82c031609250354141c0914540440300001c0365581d815400380c0115903680754152101a000d542011b00032942c50050b01d000041445074103010030001c6400d2204a01690034000000d00d2000c4107004d0010b0840180c1c094420080035400400c0820804429202500da11000c44c90a54442003140c50707680d800160303882102c0b0401070034450f0340580000d00d0341c0055400d8401e00d80c280d8590f041581d5940444c440a0700d81a03c1100c92502314045400841d44036500400006525032500c5449103150002c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 581733426 1250 581732176 581732201
    0xa02030303040f0507060c08190924030c03110f0a110a050105090d030203041e03030204050a030308041703130f020102031e0307080c0405030c150c0106060507050709020f091009170a0c0909110d080d 87
    0x5414190501540341c00b407001c0340101d50030244002c108628060317020b03110e00080e865500201240140c01144078000030140b0349401400c50344d400400e4140580200001e4400070341c188500c003d1525000d002c1e00035284110f410031091911024858181d15428600e21000c5040550030000402d20b540c960f100075010794066510146189030030700c0d20072610052100c0707502d1070800c144108485000c0b11a040c1070800c2e4000817140908030144010307499030203000e007440c0045ea04003044080a104640140d84114020b9448155540b500c0c1d0656001d481103005003601034106102404003420030a140034200480d0284c0189048007044e442821901c1c03a400071000108000350090621008100080181c001600c04501c0c0c0107900d540c5000920525000a008000c40007080003034601521180004100e01e031901c43c1c049420b04605130b111400700e14115034a0a600c503020407040c100340300d2008ac0503800005001c500070f1905c100541001803081c1181c5c08c260400c041520400f4138000c5055802c034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 581734676 1250 581733426 581733479
    0x914040f0c0f1503270f030311030a020918010609060f050c030c060103021003020a020a150902090405060a18050c01140f0d060f150e0f030a02030303040f0507060c081909 75
    0x900c500c000b01540c2144e001060121001700248400340602c8007000c28142d4440542e0b0108002880c05030050052a60724402d542c401008005080700903800500b0601d5003109c80046003043c001c5d490896039028040c8100048407400c050003080e00030000c19004071341e20704140c0d0400c0d50905c04289968007850704089660012401003085040ca0703544c103007211445007000c3d810180403000c000e5903109464005459048036071801070390149541d00009410740c0182080d4503918050802c10760301c49098400d40741441c5070001460b42d8410165030350150030f5020010300740c0c415616004440880321845040310041e420441c485000e00c0380c900130030444c41a64004120301d450703e0035203041101c40d980304840700c4400004152035168400c900290f00340781204c2425610740440b01191500c81e000304020340600c000014481400002801000309500c50300c01c480145454101c00c4401c04030303c480083c5000801c0c0110b0440c400301000c08004400c16280c0b034844165034404200d5040040c0c02014041003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 581735926 1250 581734676 581734709
    0xa03021b1b22020310090c0207030b060307080a08091801030302250503061605160807020f120a0b0a09080a211b0c05070504050f09070914040f0c0f 65
    0x6611907000d141408466102440121080440440a004404022803030740040094a65500000424044c10fa041002c0182c08525000070399140d186000540d44030340300000081e1680f0300010070109660000d4060281501c075561424141c1d040050f8180d8807242e032940406c0c05510b000316060095000340e0003070410807101c0c01c54030103084074100c844500e164003607024000ea0310000b072040d400c43c0e01c2d14450b501415010904880302c0c09910100d0100c0703608200303003170b003803028003030140050324022074648460040850070010709151100c0d84101e43d030040981440425070034007082d40d008a898002088181c1d00355240d4a1951281502e00003041c3c0000004035440110042d81a45800131001002803c00d0300c503d04043e44111541c20f4100600c4401d140e04210040c02801c0080070064407d1011381015448624035040459280c00381d40300d42e0301c00090b03912090003401717201c0c0c0d201034000426441d01d0301c880448042801c4140e80210000c40005207103441000c03404e0040c00c40300180d0000c00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 581737176 1250 581735926 581735953
    0x703050d05130b0c0d110f040807050406051011120307120b090402010504090e0709051008060c0a0c0602091206040503090103140f010b030615180109090207170a03021b 74
    0x7280064092120901c0e60185000055800300041c0e800c1202440042c0e120030a9840500207000c880c81d4424411901055140058078170501074016540780000340c0e00420746860a100c119907942c41703001c0d4003240c01c0707800220250058000c00c0b2102c0d0f082051f80d030303245c1003000a403003141d03c152130b1040013840c0f159a030341d1101464131580c0103003101101d031440e80b41015000200140900c0c05005407440e41c80c61210b070b00c0740c41003003140b000b4065040d0601007446c16031618000d40d511445505401c1c012500043d0700b4504101c2154000c0b0180d45812184201c9601e0750f00084d008601c000e5004501031412002071181001014070a511a100a40d6140740b803500060540d0103c03d101640d1045c2da0040c040f00c000340340906815180d03200c2c400d91b220b65942000400040c526560955040c000080d213821800c1d55103014075409200381c0700c003410140d94103407031000c03840b95240c003078441c012100f07103c107540d9a400001e22451803540380c0582005414240784110003910555034000d0790110400c045031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 581738426 1250 581737176 581737181
    0x70c030606030c1d040c03120c05071517070909020f0f030a0608011a010203031915080303010305151303121d070e010510090311130c050c0c100c0213060306020703050d 74
    0x64444d11901c20085040175920b120f03000c1c1280c00014426003001050700e0f0003500c01c0e084481144e4000e01143c4059640318158107801601c20a4200000c0c4540350540020f01c0070304d50315004a05545c0c440040a15002280d4002e4000b036000328030b468820030464000c2e48926010714007401180c080041e03014a0301e4403042c2110715003a114100f4681e19160390095031380200c107803a030107440514550744e01401d00c080100201034810b25140c02c0403150384049642a400009503040e684503400b240c2e070f1110390201c3c1400300c00040b504e9110a10000403001c1c0020b10031185140400b0003001301050b103085102a056145800c05444160b686c410b010811000d0a038040c41d0340144070aa901c0401d4a070488130040441d00e0704c1c00041e10a076014852000035840740308a0a0440c3e003010010418074901c804014503561110703041c0da01364411030002d070401e441c1000400061510f00e0711410031301d192607401d01040a002c2c40d15801259070b50320000010070441e00003410b019220740d40d159070391000e0700c01003002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 581739676 1250 581738426 581738459
    0x181201060b090f0402040305010216120c081b0f101e0b0d02060f1905040524030106210c022505150d1e05011d0f0c070c030606030c 58
    0x4150381014000c0101225041c111028128280d421288036050310001c00c0292199a000170810b61001810610002d2070030b00c1d01410610903141440c2440061108039020510404003400c24101040034000700007040e20420b08448034a41a5211035070003e200720b040104e41d0043e0400b02e0384513500300c40203003500e40c1700854036041c103d41040043c0d0420040350804103044002030003031400050340300103c4088800d542d04c00e0180500740c070341da80c6210001810fa820610805010b8000b0700300901d6502e003285001b514030781103c0c2d411811070f0300e029811541180031500e200180080b08680300700010381c2c2e00610704880d209800501c440c400451005048107a10000e0104527100b0000611240d6210501d044030305629a821300c0e203400b803680c0c0b240000e0000d09030141619031880e070901c8103d105600070604030340400103022115034034170040b07541442040303c150a54210700c400040b07140e030a000191005c0e42c0030f49043c846580d101da40301411507240b034100381c85e80c1c4c0c000602000303402c652110044 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 581740926 1250 581739676 581739709
    0x90f010203010f03030c03090801050c0715020313020f1507122a0305071e050d0206181c090305060c090a05040c02030a0c0809181501170103080904020f18 68
    0x10714543c54400b58158039145400002c0c00c2041000c070220902d0300c64040c22010700341d500000c10035403e00c4420182c860b07200280840c0e207000500d20903100a00c891080d83c0c864221074041c001d8111060b030070088240044110701d41e1199610760210314495110001d00308031413007110740c0c228400c030980c40500410b0b140c4290b068036490751001c41040b4942941d83c5000c840e41410060b40302d002d02d01d400d840f001440c440058000701c04901040510030009400c0c95441056000e0710029120419401c030708203e00c2038809055400505010b04800c0a9540140c0714407041c5440c0c2c03001500c980d1600c0c20001c081d21200b40309072020034018054a4031100000003000c084404101d800b11651003c0d450380942c2c2682424007800fa8401006d01040d88110380304100020300390000201c1a0180301880d8034140d54110030ad81550b420004994014280541c42c3e11040071854040c1c0e107580d50b6074807035601060100390466020b103c1001020300e1007002c2c1a000c10100301207400002c11006000e54080a400400f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 581742176 1250 581740926 581740931
    0x6150c010b040b041b030213050607150614011409121903090608010e190912020d0e091012030314040b060f04060b031918050d0908010c0917010902041103090f01 71
    0x2e040e2a00c12205175440c01040c01c0140c0c4405003040300040185003940321680003200080c1540822046130f0492011b0301c1c0c0c00204014080e15541d540e107040a840340074a0210f10007540e020403004015000c0c000c4840c0c020039111030300d06031140f16402c0c00d42d207a50601000c0710800c403410805401403007e1002d01018901741c2e0305036151201d0b0b10f07121580039011414030034004a4580807428150003030491140c0100c00041500b0003224004d640700300140d030300c000041c100071140307600303103810710029000e8094a0025030751070b41404018200715080f10021814180e0710607074400000a259101440b0f24000c41c0c03441e54500d05041417001861754a18080d1185260140601240503540c05903904610f0000b4680c500800e03030b0810000501035504013444040600c070f0f00e14100b00b03000500b5403c12000380d03206e800d40c0390b45488003070a840c1070000500c0810310803601440030300d03c5100312400e649002e4001296600350394010800712101d0300d010103000d400020400a00200c01c0000d2a4401c44180c001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 581743426 1250 581742176 581742191
    0x601060c0b0a05060f030a0b22081210170705040606020312010e0702160b0a030c0f022503140d0f020a0507140a03050d02010e1615030506150c010b040b04 68
    0x501c400c0729001841e6a000301e5403040464202d0b201c1240641e040300003c0e04031440d004050810b207140d40411285030503244040580700d401d034244c80080441250b40301a0507810000340000b40781c40702c28018944038034413490741c00010b440250a610031500c80421780140c08054140420710064031519080a03065503c1000104002c03415003140034111840d040e00002551904101242002e00c2c1301706151014409500214194000800409040d9855201049540c81501003a50104400100a005071308140d82d4410010202c0e005161207607007484030274a8031a140c0d9584c07481007944052070030040d48840450701401d034006070303c029000c000380002c06a0394110b60b00e03566101035900402501d012007000503801d41d00c1c0e0460030405140e0200a445581c4413001009009083c0b0344240c40880c414405204c940007281480c0b81cbc103564184020864203141588164064000500016080f80c800894103542d4101700300900ba50311b4401c000400d1110109003007000355944560414402c9140296 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 581744676 1250 581743426 581743433
    0xb120a060323071a0c2e0f06180c0206070519031a0306040f05060c12070305090f0601090b01030b03011a09071101090c1503050108030901030b0406120807050601060c 73
    0x280c1401403400c512110148a0b00c100c2060410001e50700920707400b4601119014140328080160905141840c112030540c04825509035210301200c0e0307481e03900d520070031940200d0b51072504400d07071800300700303d0100c0c10b40e50f24031000956040603481122243d9840d20744030301c4980e040c05a160841000c5c0b4159081c0103840303000034024200c0700c9581041c150341d03c140b4140b024843d00800d040b81401010780721300780307051b060a908550711505c0454240c007a240c0068603c032038140c01d075002031418407864502541d8034030042e0010032018104406510502c0c4104030000d004009260180001000105981240d0b20026040c4c40c2d40704a407601c2a410400031160300c04404005042c0a0303022205103259443e94002550f00340c5807030321140703000d50920045c1c005100018018070100d03400301c0040d10f40c0850307040b400ca0403a2800c0c043c0c40c0300c0350000c2103440103a6100350004004001c1c010300018079255580450941b0805052044544240c04200c000a1210510885004020505104014040b56903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 581745926 1250 581744676 581744693
    0x13020109061b060e01020c0d11101805010e0304180212071809020f0304020108091515121f060b0a0e0405222301060308071202030f040b120a0603 64
    0x18a810420010a400310030303601181e40c821000d0f082a001c000946240c036080d4040e503c42c62480b01c05105d0602404001c5104581d04050301e10f1400c007409a640c81641d08a0180035104074045070000a1820301001c200c003803041d038480d80c00d1080250340d203500c0c1c40c0c0035071360440c3da14010b85030b058414030402110340041c10803e98000c00c03030329116004644400d110940c00885401c084403040c80803807400c0104003c00c0043d0300990007600c0301034213030fa121071920307688058282c41d01d0182141d0101189042c0502e40700c24015040c0240700e18040001d00071014a8803c0c0401d0103c00b81840301c2c1040c00991491150a0207000e440c0c240905c0d000240c0b6016002c40b00d045200f5015560700c10014045142202c070103c44500d80f81200814900300d41030801075441e4004861428051141040d284003078140700e044100ca46c802c10403414180d80d61220f05507011010100415400308121001c46183d04d04001e001904903203220584a240c100070400100f00000d001e591660720b091000c2c00442e0713000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 581747176 1250 581745926 581745929
    0xa0f08100612050c0c15010306060509011d04170a08010f090c08160302070c03060c08011721070507060c06050702120403062a0905130c050304150e030301030803010e13020109 77
    0x54020441d600e13009404403091082081c8101c0f130b401440c458100d0100e00d010b80074101c034011142840305a80350010000030500a224a042c0c4c010700160169800342941d2030580e1190241d01040d9a04050070000c2400394484644140000c00c080c0060081e07050030202d00c00a428006170820031844403071405003207140c02612000b4000443c00c1d03148184d40c0319030100c07a011680700c240390015a9903894414003500d80300c210130011036101000070854803215090407090406d0b06000301401003600d51351464404586e80d5485250104101d0311021070703020007551004250954030003450680d01c9c00d100007200c2c4040d0419086400207155100440074207000c0c2c90642c0d82044c8001a00d01d42844010305032224503a0b40d050303400030100c1301d1084a401020081c00c5800c242c40c81c1805009118846049503501c03803040003c90001d001040215100c00595036100c42c90400008170f180f5246999480c54001760b10880311040000011702600c07039017134601904100784e400700b81000741c4c1c6680042c1008895 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 581748426 1250 581747176 581747207
    0x221030f0c130f15020c01080c0d2a1e230706050916050103020f030f100308070501090210031803030e2b080601021f050a0e030a0f081006 61
    0x420100e040729000c0c1e07044409000352940d841400583d82c010b400d180c0c0341e040c81200c20032094941384001c101e00210300340366050816500c0e4038041d03403000c00c0c1030000d0304007a9240c4c0325240c4da40c1e020a0001d28441002441032100500071100861144d1b00500380c00354242c21424100200103a004003580228031000c003d4680d8034205541310b10899101054007440318050706a5041006200340c018000c2a84a6031300109043c4040b02600d80c00150b081e442480041d1090350001c01c00102c003400344600280e000564540380c100741c0d9a50b500d41e050950801c1d81c0c1502c099564807003401c00c62410041541c6480943d0409001164000b40c90320a940b01c007d40203402e25031203c3c0c50304118880ad00500b61800100440c801072500d110001a04030440b154002010400083c0800c80c42c2d8000284440300c4195003400d00003403960034240070042c0c00c0107494201e18a403225800d40c2c4062090000d0224000984e4914000307084004004102c8040600901c10400030303280d0a0262a0380031541c2d0403020007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 581749676 1250 581748426 581748451
    0x90f071a2b062903071115060901050a080606040e0708030319051006081501090518010503070f1a07060906090317070305220f02090c04060e09010f090f0f05090d022103 74
    0x985100a940c2c448000f00e013032516018100f4103000c7d2081e01e904250142d003040d10030301100c1c0c1c0c90300240088840a4011034000d0303488070002038001d01c0d1603002480c4400890007603410280d03030341d8801803035070b003058400c001c3c42080e00d800318401900500c01d0662021001c80c0c0070010a140c04030207003081c00058582d100c019820307405000d4690040031104014072000d00300503c40748000e040c85008134000c2c09810310900628400180d0300c62a03080c0202581c950003010750300b03009442c0034440c0a900046049800e1911003090a01050991040140340e50181d118400c00110703403140318001e804020030400c00d151810301031181843e90100001d00401b000000c10802d0f140c1810002041c04009000a60000282d010026110600001b80048401340d454044911a01c4410004031000c2409140001101d40d2010009681c180d04581b1141400340000124000b803c0039601c16508100ea200406a000407144e4044690401c00c2074010b56100742d00060b0041e11403107400c824440604506051807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 581750926 1250 581749676 581749681
    0xf0609010b1905040f0b060f0409050a05070f39020118140d060b06071a0108011b031d010603060b100c0b0a09210201090b090f071a2b062903 62
    0x140e10851b01c0c1c500080103182c035201c400d500b051f640d40c01400344840f41814200031840d40043ca000b118003a01c1c958a171031885801c420f504480c0d10030780a6410030b000074030700c1042c00060f4101404510410380040170003004401400050000d907515027007085841c100c0202004646014a880d803a125021a031040d000d802c1424901c010782a020447c0d940490005090b03070401442e203030202410040c441844e81c80e81ea171000c00c1804c891080140001d0b00106c0c200c5000c9076842640903036400b030f0b40c03d4055902e080561840780e08460b000d4004480c403a682d0070070a41d0314034256aa5136207540d407a2030070406d2a5820303070320f501d00c100000c0c5c03c00310101c2d2200c10341d10400001d1602078a2180e08140b07000c00c0c07261501d03c0240a4034136080240c940d0f001d5880441d89000c40882c1403103111810500816900d0b1805011492001400d200701c01000414440b1400c503521201c10202814440000c619034a03030903080c00c10403190725038008003224416056808240c129452210718207042400e10319102e9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 581752176 1250 581750926 581750951
    0x110108090c0306130303050c0a020d03110409090f020103060f060909020901030b031002040f090203060d020d06060b2a0102190c0f02060403050307060b040507200304080f0609010b190504 82
    0x1a080c11440769041c0180d00402c0341070450042c5000425000350f5051040d900ca031030394403802c1e10070101e1040040c1c201d0381d0b114030101d00a07080120042c650400c030b80c0c50030b55a40301300700881d446c01d68200c510301da948a0100641da810b0084201070401c0b42401c41c1038070300d007a0340070306002070394458030550a03000b03e00e20081b03a00030f034000039941c100602503901007075402203042d009600500035540001000381e0085003043c01842568400c0c100501154003000b02c0d602003004079a41014100e4803651995804600c154040c0c003d0000241d010050302c40300c80a52426045c0c07100303100840100d90b0310510140d1800d441060800c100000e0600b82000100828140f00260b1160358202039040400050b0000400600000401c00240580c1d8100b142070506002c10080d903506646080025202000c10780301070070203110003020460003900300c900c1c00b641c036150b00381443c003a080c44200135044402041b80d43c520030302524446800131140a800540d54040c0e502c8002c1d0a40511401103558a6800840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 581753426 1250 581752176 581752183
    0x1050d0314070c290708090f0a0314010c020609010902012016030c0302030c0a030305041512140f0912032403070b0903120c030405090601120c09030201110a11010809 73
    0xb040d04015048000f584074540740d400d0102e48100c0130100c18404080c07102d0010004140c40c0030f582d00041311454550300c0d0040021240985840b00d81c0000d003407500000282418138990b0040c00d480c0d0007c51030300c0c0002406070518038010b10840c401d03410100000010b1380d100c0045041210302052056600c49946891441c20404080700c0321501c29440010060040343d07140f100461b4402c44c12100b142000506100440c01d462100401040080c4001d12a03061440b01d40b528008092034440401008507192400741c40c007816501104420080c00c1c01015900d10210b0f56000f40300a0003803c10004c00e00140001c2c4c4402405506075202103004d0485010720b14001c40b5411400030121074820351258520311030f513800451601c0c8684500c40080209418000555072221822800386090501d00018800711160083ca50b5040054100340f80107162694400e0300ca80100326910915000d04510025101040040400b1040d601421042d0700081062555440c412828039244203651030310b80c8100e28 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 581754676 1250 581753426 581753437
    0xf0a1a070f0f0b0105121507050d02090405040c05120d0f03021e13140d020d110303070b1003170304110d0821090c060c030403032109030e040c050301050d0314 70
    0x4900101c2003200300f400520080706050354000c42d01001c08821104015070746422851070512503d026400192666000f20043c08003081e6018002d454400744500240c2111800c9401701d5500081c51000d0100e400d19900c0c9072007260300c2c1030060203001c8100c240540848401c0c0380b04030403da00042c01c94010b80c2072410001e40164014074107510b80c030003030000c07402c40c00720f50040d103103ea42e000c445541a4507003524200c00e1140c000d041d082105000741c0703e03000030515404501c1e403d84402c100b80c00000d8040580c0f18440d041c403c00e01c90290f03007076280c0074100111161055008080900502c0b0104180752036000048108442c40c0c18881090b19104803540a0b4907000ba65003203070014000c25405200c2015032145050310103582a800441042000320b009100c0d80b00039690060006000090190800440021a03120451101c10707000d1105820344083c420300314001160480e0030300302400c00d8000c580e1018445c0c00c2c200d040d58140030100d0300e940300341c000150400c4082045039103100d0700f4404565 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 581755926 1250 581754676 581754683
    0x19140a0b010c03090e0a091a06120d0906080a060e09071d0105090a0504050703710a0521090d030f020c0307030e1804110607030522050f0a1a070f 64
    0x510b006c0c2e0007503202314030303202101c41c00e0040413016071140f4100d5000c41c1041c100d40c00d81d02d1741840c1a04001d41203a828000400010805660313800c040313681e65401001c44d204507000001407004605040c0303114542400d00103034115009000d8018081903640d010705550080c1c040c00d00003419601c9040c650b1502801b0b034400380c80c0007811000d080e203c1d00b044100c0d0215180c0c88441108035144100e0600640340c1e88030084500355001170320b00f400d44002c181c0e0070030b01c01c2d9101c654289941203007082100d40e5002c0171140000c60310000d01c0c1c4052050104d560000007111038000389151600780c680c3c50b160744001d519141050754811284c40b84501d60341c103981c013003000f1404994440c8002d16020b0001d107050f290282c442c0001540030790080d0b2240b410b5038400c5600007041c824010406080c00800e03044135000320184841400060b040c5039070809503244015400c038201d480145040180844440c030556628064440e0310801d0100621101c1001c6c1c00031044207043c1d59904113410201040000f5042c004d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 581757176 1250 581755926 581755943
    0x30f050607181206090327150206060d02060c0a081c1d0d1103130b0304020a0509100510170405010501150302090a03021c020d0b0105032a0919140a0b010c03090e0a09 73
    0x1187e0800003040c181c0581c6c81240201d003407800d022106aa03107a50460f121907001c91100501030041c10b0140180c06580507620848407640d10b00d940b0074001d0380044501d00701090076940445241810f50240d11445e03400b0040c965225002c90b00690b0315072020240040030304c48061408070b20540108100c46c40400303c1d44c100708407180c9400c2d84030002d07417040d54203030711621403d0404580e920340800241d0240300048181740b6401d2070282030001907a04c411014003801841e00741c10039034502016507140305c0e5205200001c0c40c0e60600034184251b40c0740d200c88808251061008200c50f4032404481c8090381d4040700c654060055214441c0320420520798000e400009490740c0b40100a2042000c0e03060718011001d0b00c005907514640111400c00804e6083c07001001c841c100c60260600c6031403d44c10440510301d0311400f82c924941c0405460208000411049d441e03070810185500904c1001d00c00703c82440d11594202c416100188400224050070b400000c2c2000803d012145590102c03074840d501900a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 581758426 1250 581757176 581757227
    0x1c0207080d050408060f0c19020705060a020a020103110903070b13150801030c06050f0405010f0e04060f0311060310051e0405040b0601030b10091203020106030f0506071812060903 79
    0x80c40c41e0041d100781d0001384600000300d03c46d107620301681c0b880f60108210290030403403a0300c0d4148202c48c19020850544c028108081190b450310001490801c032075800404010a8038800101190440c904180c080e61007031140c148a0755011991100722603407041b441e52110940c0040111080c100c2d40310008a403071900d0b01220b900d03040005581224024030002c2005130341d442041c4c07054480e00c40504036480041009100c558021000c1d09590f0704c461406401c09a559004a0129040c0c1d410407070f0300c034400c40d030300300204800c50714614560340056807410f00398181100d1070301101005d40201e070700c0340703454074010b4181c59007210411840b0100100140080c2c14503050007424400150741d51400282488030701102c03420b042107010340780007081d80c41e626070742d25201198421900c082801c40c00c44d501c8560000c08038039051300315a491030141001c1c0030b49050481d4007401e55041c04c02404d0304614260b074200b040d49040003080410982050022030a081e85103004c558015401059000c0d006040302d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 581759676 1250 581758426 581758453
    0x206030c070519120f0807091a09090103060e0d020c0f010c03050f030403090906080307120f090e0c03010e1e01140103020706020a03060312111018020607060207050d030501081c020708 81
    0xd91031080a481c1c51717080894542040700c90220444102c000b042c0b00410400c08402810300418101075511001401c0c00420000a02d01e400d0030b91040c0c8640351031303058020a241043c4500c01c0c64014500042c034552480c2c1c3d000c2070341306070307036042060621000c100000c0c18507002c0c00403541000c804440f000d50703d103001d00e009441807480b17000d49402c1d0f5146c0070002c1003400b4000107c0d803009c3d4222480345d80300b00040c2c0e0102c4515003c41120303010070500b40380c00500c8003501070b9114040e1580c0c5085a48a40c100724045181035001050307041e0220b200e1805083c6148000c40707032410344880006903402d000200c8010381c0603101d00708004041501c0058500c800650540c010300950384960040105a2840602229150704050b032003201c5030000302e80c0d80350903203242d4400403c80c80e14985c0c17020707820b0aa400003045908008000c2d111190002600000c101040c07010100da8082c3c1d080800c1075504006a10340d48038241807080c15044020030944140c503000300700090080008a0440740803031040c2c0c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 581760926 1250 581759676 581759693
    0x10612150915060f1203020303310305180406030c03060b0f06030403020f0609010c09180e15040c080111030a0b030a05061e0a0c0519090f0306021c06030206030c070519 74
    0x4030320301000840c3c5901040c0041e881840350105c540540c001c50440d15248070b00080e500c4203524255030340b0001f4401e908200340b96652607140a001e0b8417469111580c000841005c06001203803603200d0b034500f90301440041d09020044090341d070007420004058056002140411003030696180c0d020300c0120401040590028003213000550445c01e548003501c1d150f551600344d601a29820002c200c214030b040c0209006003c0a118000e400c0344085890a040c62889090512003103103c03403031491031800c120070b0040b1350f0b0340c2800a2034840000c10914030000b0f603682c1c0d50300000d410b640e0740030707110450115160b40c1040340009141d002802e8030072070300b00074100710300d4209180810980d880540b40040c045291522401c2d200304441d4484528085101c0714611040100700000018086c20030f030040340c0c22912280c0345d000366204000c016641e0015101d11a00c1c0550311114210203401d2a80a00040c7c070b4042c240c03500607810400c00e6807255040e10346142000710030701440c0010409183c22100380070100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 581762176 1250 581760926 581760929
    0xa0e010b01030504081b03070204020d06080601060e0108070e0d0506070207082404260d050406060905071d150f03041b0e0c07060e0f0f0106050301061215091506 71
    0x11002000102481001034050760702c00c68000e41001010700a40001c1845415140d6055000405a03454080c0390340c00601281c04c1410a1420aa5280d00510546070100030281c0904498100000715440c0007000030000c40c40280351070308000000c0c605114a40310320450180c1540d004081d40c0c41407418400003550b500c032a11445613103100d904444c0740c20f0302d09400700d0052412000500d03502da6541e41c039001c01c616000540b0b200044406000b01e248040f14001402022040d51400304090919007080415134959800658100303140c2000d000980d82c0000d100010b1510740d031810350355030080c500040d00c03158496440244000380044d42048100c18800118441d600c0f402038144003085495046880c0241e81c024444d582e14624042100c0c1c421500282503d2485080c010894038103c000090800c40361800d1740009a02c40100605241020b00800025250a800800107240b40c000f80012010005d0030243c8404510a501020003286421a0b100207812681100352411452000c00c0100b400b07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 581763426 1250 581762176 581762201
    0x50615122b09050906120a08070506100f0803031f050d0501151d0a050405010b1c030801081b01181d10090903210603140109051b010c0b0702010b090a 66
    0x19000d05950103000d0b0181d5426260302501c0d214840d9204030610001955014003040c5510030171520300700046111000b084118030560240c400f40c14840c0001001c5001604142900c101c03442d800d0020b4000001520740c890742c00c2583c80807803d18503c10203190725080d0081d6070070880ca414a03405002c015080760b032020506c8060140c10341d40d22904600c4030410748030343c92410703808100400c10070b0b400b5800050300310b400b50000040caa030310440010110808000b65100345032100ba0451309040d0040e281c03d00424034034000c2c0c031407142c540366250300c01e11480e0b000741d05101210000f61043c0483c0700600d4043c00ca80da502820100010740302088403d81111200307031070383d2080d00c0855800b101c1e0103012304440d07040d11203d1708290501a040e40c4545016422030307501c2d03660500007003c100e15404991ba200700072030000a00300d4440c105981032940c020f03003c0f008094201c00007070459a1244690341c2c0e1640208000b001034483c0d5404a01401c120410198803805c070b0828404100d20560008039008007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 581764676 1250 581763426 581763493
    0x1206010b120c0f040312090f1202010201050a0c0e011815020309100c02010e010503040204021e030610030608120c070911090108070c03080402040b030f10050906100305061512 77
    0xa49002d050301c02d03c20f060300302c07030f00700018001000050310b10843c482c8018000d040508081d52699066541c0c01c006030312103507944c00c05501310415035030280304054000c40960412b0001040d1040050300c00001d08004130304000d1100b2003000203010000a40d03010700001e40705200e1506900d08001d680f5001608010301c075402001e000c60313041e800703039014001c0c080d810303107406203141109001500c5035040104281e0f0800d400b0000005903007030180c6d070050f90150710841c80e5242e080000a0200440c5440a00020b25207009000d03c0044070001c1d2120440826400003030341d9510900e0807500307000340c55024031100d60809200c0d07103100d1001400f40400c030a0a907034004450303503200001c440440c11043c0c0580032500900110f409802c2c0340d04660341011021341160019094100e0382813801e0b40d4684c81c4441d25075500c4c1809840d400501410347c20804242d04a5100c50460721000c0c0c440d1005406200040b085010040381c6c1c0d00c601301209000c4102d0010b40b4170f800403030621b003c210b0800440c000c1e81c058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 581765926 1250 581764676 581764681
    0x120f06081c0903111504090c02010501030c0519030b0a06050907120c032a0201060807030f0203070603020c1b0102120a0314060a080a060e070924080606010c111206010b12 75
    0x520075842c0700202e0b60004040002c5a41c0b00c0140204041680c041c46034008040101042406941c0200d00400300a42c0c000a0300b5855418680c00c0c400054200d80d11815454480003032401412090740c0513a0740001c81c00700d080d01d072058040001d280c1a44034a4118200c1d100b041a900d421545860b80503480d20b005200908000340110101d904c20807065681080030006400c104d010f0b024120b031707000c07400c3c00001031481d11410014508040ca600c220360000742815038800b1401e0a000d030303400601c074504080d0300740300070018403e4984808a80300110003411040082070390388208005d02d07542d03802c0f000c020740d50002d80f080100074181100d1501010803130380c0b001c6000c5041207142c4a08031403040010309403500d03a0303030396440240140d011580c01c1440b400d08046001c81c44c84c80b981400003c1004000c9075520392010711246408a0360051002c1e4008404211107640c00c0381e80f6415aa500140003041c4200c540c0004540e201d2a03041c241c0746105000012407030715100303001420f9070800450f1b41101036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 581767176 1250 581765926 581765983
    0x6120f1404140f060a02040501090b0304020906090a1401172e02071a0702030a1205010e01050603041401240b0304050d050306060c033006030c01120f0608 68
    0xa411544402103110036400024001c1418601c401e04400300b5001540c0140b4540c000d61440c0280665207000441d50026040003a0368004500c84001d281b100c000701d0031841c1c80d4000606000005294501401c090000034800c034a156001034200d800c0d41e0701c038000d2941c640c0c2c035850002c1e5500100c0d081c1c610610500d1082020110780b254000102040c810b605002c43c203d1410281d00104001c80e5080d90f11005040c0034034000410038822400795009688171041044020903810a01c1c1404000c00d2403c401802090049090349040d1142982c80c00d40e05d4540c0e2418941009080075201999464a800c903040721081c0a10a00001c3c0c6402c0d1070280341d40c40f004140160711081c2d0f40140b0f203038000000400864042c0002e50340c000002000d80d801c1c82c607000c407141e043d94000c48241c41e420b18401c0d02c5c421400c0005428842c0710b00e10820242292820001007641c1d60308200e05241800310b04082c10040f260260003856a031b4039035003018000d05d503492524030740d03401e070000851484d0949840c003980c90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 581768426 1250 581767176 581767181
    0x7050a1a040b150f0411030402091b09010c0c09090b151e040b030f0601030501050a110406170c1b0106050a0801142a0315120d0c06051f06120f 63
    0x296000542040161640015001c0c2203c041c40c40540040316480e0041403951a8881c503110021145c84407981d130300c3e0902c100852440000c0400806025020170088080b90328030941e580743c5000c1c01c1211071070191303041c40d4110340341d1540728143c2c007801d10380c1100400014044440c000c0000761864101589103a080200c00c6016034100120a4001c0800c000300740780a8009280d51800070342507c041380d640718541800c00c40c2c01d801c00d8031a60f44810500c058800ea52040d0320b0a0b08507a0300e45424103040400040c0f2540c94594950001e0b40c2100c00706601c0254902190315010340420b0026101e071642d550b0314080e001c01d100b1180f00b03100da880300048581060045041941c45401c0c2c4007250354600b4516241780240701946000c0100c0c9070981400b2140703010040d801401240d10241000e05107a0802c20344100c04800d2602c25084602d03441d801c9608007050a49030343d03001502180c20342c0c480070b050000704020916007100002c0d00d135001443c240c00c41c401c01c00c81400c0c0c90081c80b14408040c091401d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 581769676 1250 581768426 581768431
    0x1181709180a15170c19050301052d0f06010f0311130905010b03010f0b0a05040812090306073009080a030504020319080a080402130c08060a050d150b0a0b07050a1a 72
    0xb05a0420b03189a1041c1c50201c0e40b903680c04280c1c22001b10702c141c840004c28219a0100d6081030254091400145104040d412049551030543c000441d18a8003906895810f800684814180520703582075800d000d00075080351240742a50014030b40c90300e002240e80d20140d003892065a10b0907140c4000801e800c005d400850b81038800d00100321824038900700d40400c165004510040c100030080c8400f05e0390391020300c00c0d4050400601e003c03a80780c0403a0b00c100350400d000a07141c001030080c58010203441ca44a20228141000d0b0000c0010301c02e056854914050455220010070301d920002e1041e0f01d56805520140c0514002c1d07080381c07803041c010755214103586c0004101034450704060285165291080d40c00980c0103201600341c1080f166110016015034004044001c082004481000064285511920014102241e0441600380540c5440b910313501c0c1003410907012600c4036800600c1e91a100440401401d440034030399504c0c021410081c1e2101054081103800c14403001c03140e48000f0080082a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 581770926 1250 581769676 581769719
    0x50c010f1106070528031a0d03021507210606030c08130f060603021c020f010f050409051305100506031009021309150606050c01181709180a15 63
    0x1110b44031060166416000b40d01090f454000c8036034803c05c070840815001002d164592804600341804a2069030140f10380031a0501440051000c0e01c0441e500107581c050301c0968a409015548035035204483c48a02480c01d01446205034810800e0207460703074464030440d5204d0b542003092040340f88089464240a031654682d8036205a03004011414400100e50190b00c41d07034002030020741d20b0380800c42d40d01141da610880d0f040002591001d505000b40e6801c0421300910b4003400f11050000003410303600803802942105a0f0310b400103051091146107411030650804229410a6800191000545000c4480c3d50190080c040c40d030004101601400c500194000c100350440d841281181d801800c40100c1642c88403d04031070613445c43c1c014490702d40941480e917038403696a08030740f41d2182525100e14001c50b210200b004418007007512049491210701441400070340d100c80c450001707080c010601182480d040400c8003401003251659000c00d020022125401c0040c2d035071900c8180f949400b600f140c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 581772176 1250 581770926 581770933
    0x160206070507241a040627090f0203060c071e020105070605060409080f0c0c061305120c030118031b030206011202130204030c061116090507020118050c010f11 70
    0x710006400050350b6410070340c4265000e4002902d60070600c0c00d0790894140410010107004c110b0316642070900921024101210035000d160344200e6203802c02006980030b0f00b2071941c0c1d0b441c980c410000d51100c1c01c00c0003174005003140c8850800340e2004282d940310f0343d000c5544a0310500000002e180c1603833180c2c0341d41d40584640f400c1c402d0f2134031400003500005012a5020365500d842d0000612090f026003001910710070345980f1210403411140ca01178203018450f05c40c010030300c5a40c680301c00d0b2892000985070300781da00784150040c20525602d030088844855502d03501307016000002400c900105080540030755074001e46250740c16040f0b000c2e1409100e0240c0160021001071051a030b0441c0c0790041c2620162490750400b4041510345c0c00c0f03800c44c1c1c004a8040f07003031510401c10310354040c046006000303101005e000103601c926240921110700d8070825a03012740350320020350342d18002e510070103d036107440d8048000e02d501c52618503110402c0b01c440901040c82914002e0403035100c0c221b40785801d41e024000303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 581773426 1250 581772176 581772187
    0x1b1b0f170c070e010e060d1b030c06142505100e011a040b0108061c0812100803040b030a050709121a0a0e071202060c1b1e030307030311211602060705 66
    0xb88850f40d03895210990388c1c030b8a048000c1ca8503000ca4084800110b025035001c218041c1403100060490f400e40c03a00d41d480107001d100d9601c0035819200305104485444c07800040c01025450710504200c20322000000b0245400e103546000314064000c00d0b0403511502e001198414202c08003c111096200d484d8000345e083c10014984c0d0500210f00c40c05010500d440e0a045941e0340e540d1481940101d41861850034001d0a121403480c0100071170000d825940c1c040d606044c1810f079291184e020081102410a4484000c20740250007100000f004d0700c50161540100400f90400351015a203299640740c04074145000140004540e1081b0504c21001401420825160900e42d103030b280482182079a005004104004003403004100a12042e1103458401c0c60307505e100d0081106080030700718a80000c074107442401d9456a400301c00c48a01940c5400c0c0092074104201500269010f42c1e610602c045200b080020043c42118220701d00c6001c1c1000094411180c1c04022a100e031001c2c0d0716003000c42c0c4140003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 581774676 1250 581773426 581773429
    0xb09010b01031406240412030224061311070507031a090a12050405040f05060901050a05060a050f09061b0f03040b04180b040501081b0a0302090f04060905010501030b0402041b1b0f170c070e010e06 86
    0xa28282031340000314040337100c1c0c40b04200f0f091640d000c41c40c00c0301c196100110402c10000c00d51400f0701c02864410041900e80340501109440e002c0c0b862000780b0b9440d00e0281144118060400d0310041c040c00342c01007000d5034800031081c00030030040d26001d115042e048000101480d00e0601c14054a00c0070300360a003018050003050b50a070304100c1028203901024010a12180c540b000944588600398280d0062084c00900550a11086c16000003080d00200b0082c0b00c4014032404071821a0801c9625001c072a044507040402007041d800200d0b40030341002c00006040f40001030740c8034403640303041c500c4003040b80c0107003000400c204501c03009401844c483d000440503188402003e90084c050391012800385659540c040c00c4500980044039000041c10034441582814802c40305140c1d010800400c425080c2a0003400603240c90360020850b502c1400200d00300200840d00c000300750382c0040641882e10b45441c0c51006c0740c02c09942c000480c4144540000c42c1000704680d85e040310342c0302d441948161074800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 581775926 1250 581774676 581774689
    0x504110d020f0d0602040504050f180303100501080402180108070807060e031002031801050a0207212f1207060e0601030b0f041a040b09010b0103140624041203022406 73
    0x18001c0d0b132500d81c00d200c00921a207880c010184580c1c0c494000c074041e854014003040b125525132808510651060041003e075030401140a0305031002400c1410041c0d8582c03001481704e980300c4510030f85200301000006040c2a0008000d000da40b0710030255546152500340849e080d4000d10b0b0700c282c1c0b540c0103105050300d091080c1c2c025a000b414108902d020848005585820750764180c6030b00d61800c1e0300040820600c002c480c2140c00c90041d982c8031034022040701030000c01d1200b00403004d4511961404418800b0a241e00390890007031010f40039034994242e000a000301036001540d00f52511418215020b840460200c1c42034180d0340d0142c00f030700554580024038480400c00030400c03660050700c8005c0a5000d80080d21140c4610f20982a600b40c80c54215101400c2d104401442811f1500300341c000090703200c0300c400c850f50280702514034014003400082072150028000c0025402110002804207083c64100040400b29000703408a030320070030000354001c0c02107100c4045061520301800100301180b030a174 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 581777176 1250 581775926 581775949
    0x708040b160f030203030105090c03011d0a2403110102031c0b0303040b0f0304230a020d020a0509070807090605091323070e0a150f081f090504110d020f 67
    0x551000e40050b665495019a50141c2c00c0d005a400400100114034001c103240f03a02001201c00d80303043d135240c205a034001404180041781c100c00c000001810400c1e0303607800102a00c5140c0d009404030f440b10341c002d0952000030b01040d00c1c0c0704a1102c8a00362540004101c44045a014030f00340b03945058190540000c0203d1070310680d00d80020800080c80d20725140141092084401000760340341000d1524600882034001c000c0d04280310f159000d80c1d18074000c05c0702045141c068500b120081c40f5440002d40921881e00f00940c070519040078002e229502040140c451840c13520ba000c1c00d1501c421059072280244104076500c00448202c001e03010341c07203070000c00201c003000040c0e51b0f513401046408020541c08858001c006445600458901d141140414000301120360301c01c211000310007402000c440303151209805011840d00407408150040822420b0034035040660381e00c1f41d03111a01c2401a080503501030700c401c5ca0025042481c8d2a10441c0075900a138001c10440d445800d40b000d000702003030780 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 581778426 1250 581777176 581777197
    0x30c090403170408191d030d020d0509010c0803311106160c0b031f1a0c070f080c100f02060105100e0d0f0b13030c080f0c150105040c02030708040b 65
    0x900c080680341c4041124146805c800e6251035584c20841505460001103407502140720350300800c0c40b400041c2c0c0104404542e03002c01d18046650758424001070341d04140003100140348030000804c01c400b905040801401c8061a0300780d82d03140d848001411032612030b00c1003005e0821070421582603030350300c0d008000302241070000040b00b542c40c20175114440152809e600010039020000304205001c2120b0b84860720040d40d00410103c03883c1410466549484001c0a0001110001401c880025400c00c1000001d0540a00c030720341e4291039a000a4a503490941480e000e0708941d072001c031855000b440c0c1d041c00400345600800b8982c2c40c040410015030600f140c81801c1c0030740c468020103161240520340c0303900c81c007c1c00008281d00302858541c0d00184014581e58124050a02c07580000e075212041100c01500581c2c0561112a40c00d502a42c1340f28030010341c80d4070701c43e1a49000e0681c845104243c12107004590030401105c1300c14041e44c0700d2160480040104404000034042d907100389010b00181102c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 581779676 1250 581778426 581778443
    0x3060f060c0d080705070803011a1201060e04140403020a032001060f03020a0806060a030314250209150d080310030c0f0e0604060b0f07030e15040302030c0904031704 73
    0x1810011400c0c075440340c0c0315088550007840c001c0c140d80e900156010b820046a240003450201140c980000742e02040c0140c0b400c1a40410300f030f41c40200e00c6001c4d00c040458000e00101e03036503543c1078094040010b0307403105401903040036819400440d072120f6191040e070301030300907203401c10300ca40e42151100c01c1c421085542c1d002034528041c0030002440b928000c1d114110f00074040c1402e5004119070303a07100368080200c0303034860800c002d042e485d40054101260761509050901c100d43c0b4030104650f01611040408200e00c4507020b030303088030811074540d101e00d000ba9405411620740d12800c450660b511200300d5003107401c903040040051001d20046078040c901006d0984d504d038490340c80c07603c3c00d01c1c80c6d0310116102406107424003070900015048c940004080b038040260740e10f011a089864000e605240b01900000b0a01d0800d0600441000c8214000101803003081c4582d440d2000b5180c115000582c024401e80c1d6064205007040000c3c18040c9070540c8407100c099122500c0301c0c0206400410803519800c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 581780926 1250 581779676 581779699
    0x6031e0c030f020a030b01020f01051b03130519140c03030a0c0602041701140f040b0a02220f15090b040918061b031107020a090e1e010e0628020306 65
    0x400501c084d2100e40f243d95004502858540d000902c0c0080159071800e9692406041c0520390030410012100c0c0c0e190720020544a903900c04090b520104030342c80c01340c11400f40921b40c1214000d0020800484c601c94002503580300390103541c0350f80e200070040400c0d4050b402000001d11031400360328910180c81c41410054a05515035418102c200b007031641d803007540e039119030f030320211440c54001c513a030311201468001d11240392a44920030442c01c090011a205580041d00c21440d001e6013140158078054445980211603980e24555800e10051003201d61404490302e407015514425001c0108907030300c04401c0c5007014100041100208050300a18440701005882d902c00a83d841c0a030141d2480060421740341d40800c20f20140559041c440024440305c2d003049504010b80e0313800d8000303064850144e800210f805504e0001c4c0c0c58624400d2800b83c48101d0014800e084101c150040081510300030207460b59500ea100135061001c0d004840308950401e0084040c800001690145a01c5480100f2401041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 581782176 1250 581780926 581780951
    0x40302102d050414150105040b041407080a0c050a021b010c0b0705031906060203070b0402010e060c07030507050f060403080306030a0803010b0903010e19020d0f06111306031e0c03 79
    0x40c0740514011032466161010401807110051410f014100440003400304490b0380304060641c00c80501841d80315641d185482a01600e5903800030250b00611030452066041800c806000040100e8002104604000541c80303021b00c10000d85050341103e4000340200f020320f14043e0005400a41e0311410441c2100f080350124003a901500d00130501c40d240c00303a0340c1c2046010000a403100d2801042242e08240c010090990700004440d00240c005652918903225031004079640ca0000c00f1090f48007101284070241450041510800c4a1240d021144c141d50345809000034212460207c42c2e000d0010320080002c240201d0045600000c001c082c0c0300b81ca8802e603034420b86030b0802c1c0c0103c80d03500404602803180c1c0c1024440c0401c4040d030440140320383c91703405141c04594031580400038000c10701000702d0400c000413074415400095020000703000e6041c600100c0710503500644080950003108010005030301e03020f881460800c0d00e41c01a0301c0741000c400b82200e0301800ca20030401c01095070b0788003030032281c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 581783426 1250 581782176 581782241
    0x4050d020616062a020102090d0b06041b020c090604050609070f0e0a0b1b07030c05040b04060e0705070b3301180312030b18010611030c0102040608040c0e04030210 72
    0x210800070b00c41503520104501004c2c0e9005034002c8190a6a104102d24407041c0c2c0c4410152103011b13400000816030341c0d03688004c039028042a480070050070901c00041e210f05a004500d100c11188241c0381e0000c80d64920007004242e404c1928200c1c1c208480102003005a0b11940320b8480100d03441c1031042c000d04010010442414103540400122600401c404188000301c41100310388500c050002c240072810340e110b0f0042e40b409407103010320650381d811600000d900c41b500032200908840d4555001131802c10005002036004041c111078034590400013460304a90580195400001e40011005050f4441d1403600c00c3e82c590501503043c08240503884071009440090fa0000d9407080701000c942842441e0003805507503451282e2481000c5600401844103101c501e444d0456100389040e240030740906140300e05511421285038095400000c000c00c04071340000318240207911039080b01ea01d850365030314a0040454207442c0200180c001030121a41c041d459041903000f119080c85402d45011004249480c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 581784676 1250 581783426 581783441
    0x3030807020a140c0114030906011413021204060606110c1c12021006060e031009080412050c0f0d05030a2717010516051207050409090303140c04050d02061606 70
    0x6640c1c441400d0301345550344655643c02c40c40c0c0e000e003c9419810080d4215813075070414050501c079034036418034508103035036075005003040546001000c40d5908000f120240900c9001c40d41943c2488c1080b8002982d14402d804041d203140001005d0041400c896080001e00c0c3d0214081080e0782c40640180030126092100041d101060360f0010941c038405a140041540c0c0c40d544664244420020301030061348000c5801141044100303000104420580344c020100d008542010100c0320200c4c5c581d104102001881c01002c8604940c410031440912003004a50000f00800515580040c400546c10ba0300502003030f00c0e98003a403900700039022488440d0b003100b13031201d034031550f0380b120108903001c9445028466240c004115544600340d030b07404824040d0031407042d9001e520700300350920f0000360031500c20382c01c4c1d07805040220400d00c800c42d4103040c01006410900c43d18180c503124080030030b5801c4e41d5a000c543c01c4590203043c42c03c0b04500c0e034080000503006144440c1860032040294000107045125080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 581785926 1250 581784676 581784713
    0x3090a0c090e010e1b06031806100314010b063705070605010f080d050c0102071a04120801050310020703110321011d0a0b031009060c030f05010f03030807020a 70
    0x182c0d940340c15441425500d20100d41c00c0b541d0400c402c0403600c92030007040000b4046050721915960746403020212200c0c09071441320f05c0340340103071400c1c803c1d1183c4900000007102d0103881e085012150003058a42201c034045c5105a2140040200590590410200c1108510400c135824000412a0341e1010310111030790300703d800140000344400402c00b491282901520784900d0041d912401c0840c65a6110100c4c4007103018031001060100102000750121034400e0703400070716951454a01d8010300707029a1b0a51341140e01e210a4504415400e104145840c100e82d4000c00600304100c0c1100b40038000d5200400603410020070341c000c0c0071040da042002f0080341d10441c3d00001c00112854403405d4072034040c1c12003140241102d0002409400201d0110f40106048000151914000d40028034116410100d00641c90401d0400400e00c84c1951000c01c038480d241d242400340350344080c80d4504480c000d0080c1c0c0c2c81d94905c0241400031034804c903010343d4040c025004030341442a0b40d44a00281e02165401c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 581787176 1250 581785926 581785931
    0x40c120f050a0f05130209100f0801020406120203100b0a0207030b01121e0f02040b010509131a04200702190308210103030c03080604110c061b090105070803090a0c09 73
    0x408480424810a20f0b200ca07505070800240c10301c00070044800020800280c4181c01c540086500c03081c10a0101c40103005000001e12000d136100c0700c00703000c0e400c00d00c40c42011804401ca0036a900350103001f180e201ea14800b410300c880b00e041013004000d80d00140910f00c11403013568004000100110b101901a007000b01460b030740c240c00d9182c089014140408024418080c4070641c000007201e03002d01550300e070750480d0085110343c10f0b840120ba90340158507509510415a0b0984403a050003680b0145100782d210621500c49010001404103652000c5e80c280040510308035045404059800500213a6100400072030081c0302c0d2050010340000b881c1c0003580c8030f00c0d0004132080b50264801d03555a0b121240004580c4a600d0350b14058008100d040d0090306101c80100054003076903441d800f141541100c585131a03103c404400031203075a0002226016200e50341568590070b0303100e9540c10303100501c8050307650600e803c0c0c1c0c40d0b40e03400b038540002d400b40f60640304483d9400001020140c003000904000d1500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 581788426 1250 581787176 581787181
    0x51002010b240f0702012d08010b090112021308030c06010f09090c0b0c0a0507120209011a1c060509042d020108070e06042d060908060402040c120f05 66
    0x204a1070032030003542c1558041c0314082d0740c1000d0b204079043d102000c01500c00e580e180c1e401800113840c11003030389a00705061402c41401400a8403902154001c1c031106544803d403d0ba2204010080da04c1380c241400d011800e0180300c8841d0500c0c0780c0081c2054004121003070340c50b59540308a140356800c0304031580b55640000006024840315480500010242c03448280300f180f2030b80e15034503956103d90285540f2054001030050039680100301c000040e603408011200c0e1280d4444100300740b0b00c14044100e00c10b403408000040c88038840303114060144909210646801c3c0303546030803070124295408a403109603d560700010f041c1d803581000e030701c5617004d103181038040009100350b031a5040c002040888800400c0101b000580d0344604500d900c048a814505000001840010807a0186a00505c00c0110003e0b4840803000e03400d08010034900407038401c0c150720f912160250340601140c019040d1640c05500014058505600300c03090702100ca0800003c40c00480c400d100680f03012000c00000c5940711802e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 581789676 1250 581788426 581788429
    0xc0a020a171c0c020111210306031218090414070803040e0603150c030c090604080f010507020304080a0b0a0603200a080d02060103080c07120f0605160e130204051002010b 75
    0x19400c5204040d070104042c51403010b2014001d2030a90001074100103407148580103d4000300550100d810070f994242503888520825030142d07038002c60b0708a001e4003441d2042e185000b5000107840616945843c071004460f550400e00c1424400100266071801c451484540000c000b401104050280480915611810051110280000944524000d60086120303400742080300102c1500300d00803c541c40d81c0c0b80c0fa48807144242d03001e240340003075004e00300107000225024009000302c0410f10580003400740b03580c4e14a003030380c507030181e80300d0007406400c13141c403031030010f0304912126601208644000070000d8883d01d4604000007021a5480a0b0440744100812884c2c2400c900c002011000f0060082c55401c00c4001c0d190700062000501014001c18100c5902c0c4040c890740001d030000341c2402c02c4112850920010980b024142515158608004104210328002d940031800005440d0018a42440310500135805038091340c045201d5400e210100352951030000c06d04554166074004580d2440c42c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 581790926 1250 581789676 581789683
    0x15050f011205030d0e0f010c0201020301050a05010e03030f030402012d11210322050a140105150108070201090606260313030f0c0801050117061005150c0a020a17 71
    0x30058508155400600340c0082c1c000401ca84442c0c801c0311011030b10640350803849107007101c01c02d8961415401c147c503110300b065055011314122030b03003251240201a960401519038114071074815030103800c03c00200144800c01001150003620601d08204241c42246940d4900c0302900c88103010300040c02c0c540340629502100c2c1d02182003503034010786140003d4282a04c040d1040d4444000b20000100004003407040182010b0b032401d03002228034071000c9440c50b2294a0b2089807100711141e46040c030440400200521800b4072a900450040d4000d40e140801580c4080b03004141008541d2544810710029402d17001c1d0384000d120b10f41c004c0034242400c49500100042c010802801640706205a0041c40e8820f6400c17000c8940182d00c031203900c4141d042ca00049061504125415801d000c00017684008610203810342d00f41c100159580c40e107d0542c12001d60400d44a0f003548001208241c8803402540c000410103844903008540780f03044140d010804014942c1d01170307260000c0318040c000130046e052 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 581792176 1250 581790926 581790929
    0x81b071a0f060f0d0302100203010e0906070507050712060f0c020606040c0e1f050c0105070e0a080a0b0a0e0a05070b0c010b0a0b1c0e0f07030c0f030c0b0a030915050f01 74
    0x86500c0e64080c03800310041400c0070481c00005104d812644035800c10b140c0240001c980c19810300d0070030755480d070710f0340c8820203c400c040e5410401d078480c803030002c0c000a1141060b5030190358400090f005107803034800c500d4400c5000c03441c2a540c05541d0304c031300c058554440c4035507082070030540c001c2c001500d80242000304580c103406100c2c0c1440030800720b001c9559110041440060030b0420400d14224039004100c03118040d40301c403c10150710b00001e1002c92900125400b2002c0c0f01111154903150311078081a449041c2c5500041c09906484040380c181207164012110090070941103480542d86900c85600d4014a944144000440000e130001600b9080c0a00400d80304251b07807418603940740c01c40d02030980c410302c0f0203840320642d403d0107601a41625041108400484004c031a030001d00380d030426445100e1803108540a5841c03100c0050f00a014203400801c5a412407080841c851400d1f2409c0c01981c48410140d04141d03547e204100041e841c5c171403008040000d070b00001003605c0c1404840c01c524506 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 581793426 1250 581792176 581792191
    0x6020d0507150e010e06070809100911220f0518030313080a05130b090315010609090221040305040f120f02190f0b0c070909020a06081b071a 62
    0x4000c500003050b10300388003000d411503145001448803403c0e40c00500600d0103052035070290040704140444154000c00040c0a014240196134015224550b0341040b210300100007060441c1080c0300c524245010605400c0e8021803104d841b2011882110310000ca49401d246051000d46e21014003207640d60211807640703404140750096255050480c1151804841510000d0040f03800081c102c2569104c1d1080d116001c160010118103240c5a4000b01e03c0b82e0411883c240c0688a113404408007556440e0b1a80e04891746500c1e040348890810328000c1c040d5015100442801650783d118210b0031440c401107503c118001d41c2e43e00d0f1102d08001c051881100c2030392019450304e080311090720209000e0b990207460240e040310040141e1400c28040c2803504507551001c45502e008003400a000000d00c00240740f0b10000d002a07a10068607a044082111000d810194014980400c240681401303403080d107811000e00c208115941c40d151100140355401800101d13907090701000003020792541c0203030756a0420751 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 581794676 1250 581793426 581793437
    0x70906090b0a0317070c1d0f0a090c120c0308030906010326040501050913060303031b210e03191e0509090c0904020f0f0339030621010606020d 63
    0xb0356110a601d043c0060460318045500284074410007100d4010b020051100c084013400704140d6034146130520f1307c00c54030400400854030008a8400440c030413a2201c0f98410003507441c1c0b0f41040c0500c2030701510204115105d4004400110220b01c0c02006544074109420007007902d907045140031501445290506405007503600c0e800104000d10f02c05407010b5880a1038815100d03817034440040c422858200000f08402c0ca85407002c0f0916034190000a180d0114004124120303d100408a44190100700c4050000c00810502c03245c0900da40c1008019016010489080c05004c949019500d001c040c1c4030004a220211009010403054860b40c0da40b0305203007000f60511403940042a880d1100400f01c400d441800103800b82581c0c1c03035030b06075600b0450040ba00b41d03c031500b819540040e6403041e00d140800e0360035552041c1c01081c4404d0f8105403202028421950040503001110f2560405414680e110306440018100308500800b03103060507212200100f9020701d0028041d04104000380d500c4100300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 581795926 1250 581794676 581794679
    0x20f030a051c030605090406090b060d080906071110170c0c0c190b04090e01050f0108190f020d0302010203070e03030405280b04080a03030e280c0305070906090b0a 72
    0x101d0105202100310705000b1014008aa42e600850040650350001680400d4001c01e210030f00c803856004001183c402c039500d10741070b1580010030a00c402140e0006005130020030101e800317800e24001806046204140c02c03040448280f0001d01d40c001e086d07404c0000150050700a0141c0349074899800c0d00300403148070162510460787d1609272a643e080c0c049074054044070000403a000c581101203401400074021480e15240c03280451000b811300d40100c0e40c200d42c02d000c089000711100e420554100c459400040018901c084100852130b001c0102c191001c1415511500160b00d07806c1e4905005840f940c001a0f41c0c0ca050300300a0544461318a5150003584140020b100c0340e21040e01c01c84819904d4180300c143e0705561101c202580d446900800f40d00e05000c03c5c00107140c0c1c00040c4140c8414400d072818081c550010b29182da0f22003507501560510002240c3c4910610011400c40701c14502070850f414020303448c1e031201840c010040e80480d00d515030701d20042000640700e10034500c0c001c10845a902c1c00c503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 581797176 1250 581795926 581795933
    0x71a0606090114070201021219090f0609050909010207081b0f162310020c01020f302a010b0303070b0408032e050a090b03150a0212040b04020f030a 65
    0x421103003440951144000a07941c1c1176a00030840018094407030a0764541d01c0f041000e0000b401c0b000c0c0c0c17a40d103012640d40c14004c40ca66010f100520b0544000e9652510000d10784000c211403400044d008084d80d540c02c0210a004c9846d072802081c2480e40f8244500c0881015141e1500c1c241d5003401c0305155070403102296902ca418040c100f8100c0d28030f1204100c14010340c20840103d6208210466030003440c48040740880d64010400c03031815036098080d21aa800d1108100d503c64009001071a110309841c581c646440c8025580d0203418280034101750300305002c03a820007034034503103030302ea00180f00200c1c54400d02981801d029100c0d01d00d03403d0b0055401c3c1540d50ba85c00d160b004006d04000e014940200000d81068411540700350340070300d12030075021889900900541109414007907203009510700440452079610074018020383c03001c041c3c01081400d40c89039148040c0880039014007600c903003c0001c03030300544491958a02071402449205d403281000d104010200f8044101d181c0a030b0029005103010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 581798426 1250 581797176 581797187
    0x30b0603060702060f06012715050a050409110706020318010507110c090630120403051b0303091306090b09060102030307032a11060c090d26071a06060901 68
    0x3000e45e080d00b03a140d01c5200040c0d4915004042000c0030444003240c64042e5254040c0c2d10b8100c40c404810000d1403074403581c040741d2500c5480f0000303011a1040104004003031040e8016841c0c45000c80300c15080410307a07501c01059910585900c2040342c1803070951031148000b0b1080c1c42d0841028140441714480080c12a03031200f41d455101ea1084080400281032038840319522480e80600c0f540480a4400600c0003903d0441d071300300c01c0071181c4943c002c80448450440201c07070a4981141c01440032640a1505030480043c100295415000511904000e91078041c010003000444000c08202a401c26020000f01d406c03640315140318614407800c0c040b0f140d0b00823007284c2c0c102c0054607001c04c00c800310042d0305101d2005100b40011078201681280d030880e91060080b100002c0120660301c1d252144850340d50b090003404d02541d840b07030060221000003248200540703505001c40540807119044014645c0040e000003d0588410b804010740030189003003440300d00d038010000c65001303003401c4c00100000e04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 581799676 1250 581798426 581798431
    0x41202040e070819031211030606031009020a0522120b04060902030d03140f04080a0f022a0117010308070b0403031b02010c020c15090108100f060504030b060306070206 74
    0x460381e410010351800414002d10010f040703454211103249410f0b0001410b80c0032411015800641c1c411580d10000c4110300890466040c4001e81a0840d15140c040110542c4094503501045040340000154140c19001410082925803034060b1180c0882419050742c80c11903d145541756100c0200f800b100008403903e88105800c9003451165036540c1c9456001001000c2e4083d50620030942c80001a540c0745d00002403c2c104001c007880305440340007514411030021790f0001c000213009d000c0400300a2241d80003281c1010684100c030402039022080041d40ca582c0c1102544035020082c60400558108024090400c0d0310400760880d0340c956100c3c00e460340903400c0c000b80801c5410700440c052600c2600180004031045400c00036801d11a8400782c001c18048090801500450350822540c0c5050031101a42c0c0b000b000c0b065140c11410700046444d10303001061141c03074108003030021881100300c00520001d00b0103500c46550300d42c1181000f100c074240043c4002d00c01d9026008010a456002c581141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 581800926 1250 581799676 581799679
    0x7061e031e15080a0605040210030c140c1603060c021614040b210109050106140607020d02120a0b0601022e270b041101050a09121506091d03041202 65
    0x42c028112030081c02c0d6908090340510064800e80107501d06000c1aa0b010707034003c900c00c40c1e18030622810020150706503080340b1181000702c0d0703a02103070001c0f40f05031000034200c00b07248400361191800c03107402c035428000c056001610026520458058404e17010403114401d06042c910b60060903203445800500100c9030010a0b000e19103c0c50f4226058031005030b84141281c1d424031906c034141c5c043d090ba50003810307540342c01e40d415828610001005a1105450355140102a2804d0300c0c004103902400405071508030100d070090004140311030314840038080c051000780315040c0c004140c2455000286490b154500d00c5032445036010096108081603c07010084080044002c101501301e410b00038561190404408046020100c022040103e0400d07050720452040c0c44e20440c10508000440740d900490100402050303a10009100e01410034141840d020321604900c00000d0344500c5040656900794800c41c40344d9200e0701c804000b017405407440d194031b0304068021410300e032410145000403221004041d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 581802176 1250 581800926 581800931
    0x6142107050a171b0d06020304020607020303190e03030301050108070f092412050903030f31051e0304050d05010207060203090c18100905070c0507061e031e 69
    0x41049806219220003000000c0000d500207a48911002c0e0b80c6950710711640d4140600c0d4048603d03d80715000c0d1403264400a0310700c020100745540c4000095201402c2a0b0380b0200500011005135000c20040046c3d40c014403801d00d0003848400081c5c101100461164425082400148505d90744011003550140c0c840c9400040c4a80b0540700f910030b0102908032241130060039403040740482d0381e50719040e034400040d62075203c4061128003403c00c07980103490b141000c2c1c00410100744413148550781945c000e0602c01e003020100d0314000d188807030341c0b66980c8540d8550020f2241c2000313100c820700070301c043c9040e400540b4580031100c810070703070300c1e07101e180250741c0714260540c0d80c0000c1c4042541039a1140e540050300311350b40d0420b840c0c55030799072020503c6140b040d51040260202c0b04070007424540201003400312114943d04000c00c400280c10b00a240d0000c0000c11100b03000802c0040240300000c0100c0d1f12180720465405158034814102001d0180c2418240740400c00c0c10a100e4910072041c00a25200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 581803426 1250 581802176 581802229
    0x150512030c0607050313020a0807080f01090c0303080627010e1303080115111002040f0b070b010902070303020918090f0c03150a29040b0418020d11031002070203010614 74
    0x6c2841141d803090203900900c890f5804290000b000600d041522101c100311888800003205103400e81d0300340c040c0100130800811741040000e00030301207150402d0000301600e600f03440c500101c480c9004115a14031500c40804010007e0100c0000140e811425043e00380d04024006c1e100036048520600c515900705505803400c10405104542c03c0240c0c05100c1d00b641c442e07281e44200e83e0302030740060080000882e4941800a900f103180d4003114a240d50100c0040403e07864034024200a40080409900f89034081141c001d05039075050350001e44515070b80809410b42800d0202d140707451300c503001e014240c1d400b2680c1d0360055a80010134001880481c00f16200d00e580c0c861703501000d800b0015034940c0c080011050300040a2610b960402404400d94040240255820400040d10080090040b904043d00c54800150400060441e00c5a01032905980352110440200c0d2801d03951b0410007840079400f04400085140a000f41ca0050641410358a00b48440000003496522040706428800007000300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 581804676 1250 581803426 581803441
    0x1308040b07030206010806130b04061e09080a02010c0822081201080601081515060306041508010c030e010204031e030e151c1a0f030a0204150512030c06070503 70
    0x484000c0c0031010030003600c4080a2401940d101d4080c002c01e6043c0c0291000a126035250401c0e9080d41c5400226500241e15961220401800b40a10741910710b1148900040f01c1102402000162841000519541d0007a400000c1c21a04a0b0080300d0400c030709801840340c0034900d404000d0166050048440c000d0001d03240c2038105100305010306c10005006000051038900105109040b41c58580580d1805503402c44c0c495644030b001c49542408800000c82c15100f81400009154040c40c050302c00210840400c048520941c82580400c0c01ca81d140d5000484a5a050003649511520340c80258242410350351030507020800082902c1c96204140245070515104a85917002100044c1c000459031003164803082540e40141107240580080504150b0400014070486c1c21040b00b440020050381c11141c204401c00510038503107a0b0600c6807070401000750340c07035114000e0140c1c501e000d03c1300d100d4505818031034050328141400405030014424805080400b10b901d40d4081000c0c0f0340290740e56900364 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 581805926 1250 581804676 581804693
    0x4020d0b13020c1207080409270b07091a090910030803090105042001081501050c0f160b0a09051302070501021b01150f0e070306080a08090a0f0b0313 66
    0x1040079031119004940d200d81c40469402031840300362010685103a40d4400042c1451031041c1c1c00c3c0141001e20410040190060690055071002c0c0311000b10303800103c0d014039001c200300c005c100544802614900f4400301e0ba80042c0142c0c020444021400644698581381001c9801080b4209002e0703840b0f000000c245145000048010f035521444907512801c0c0008070a000f0f00c001c0764122000c90001004520b041942010032602030016914807485030b40d40940000420001d8282c40c0c14000284400001c0220a108909282201c0c000a00314041000102c0c0b01044507580207103140c3e04104000f051007548140a14250760701500c01d080e005480f60314800003072062041c090982d51022460741041000000c0141e00c118205009000844150f016285688228400c0e00600c1602000402c544030050300d4160b4003000c14100052010b545189050030800030600807113000c1c03c006940d0b0601c4c9811010030f00900400701b000c40d04207081119502003440042d1070a207805902003044410004101c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 581807176 1250 581805926 581805941
    0x510030521070c08010902040c11030304031101110409091b0e0705031b030a0506090901050106021b0a090c02030424050a110a0c090e01060e04050a1e02061204051e070504020d 77
    0x2c10003c075036035641c01540c000e01040d2000c0b0312407410304042100d0984031b54030050715090181c000d1072035500d1707035503013503c5018810a0307e41441d5201c89005000091000252000f800d40080c00304191034946070044901406802500c61411034010500c1a00c1140c44030aa100c8110b003030084e600e4444c40600201d0144400030035000440c00020040c60007043d821280c00382c031050350341c19020b4454688040c00c2e64000d005810050740904591501c05621401c1040103200c080c1c00d00580c2034a03540e0410035189141340500243e40700060800c28201d2a0302340c5840c010080c1e03090201888034003802040d500c20b06428804005c07941000300b845200510900000a80c08008102d07480e584014100240150750f9245005502e481000291040d03451035480c8119408006401d16240e90740d1101001ca02d02c11800c004914807030f50440040c0c5030308004184070503c605401c42c462030180b4005107800a01d154039142684910448446000300082000a4070b00442707015071940f00c0001040000d2815 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 581808426 1250 581807176 581807183
    0x2103011a0f0301030311010b220b0103091a040311010b0f010c050f2a0123280302030a050105010f0c0b090f06010b0a02070e0c16020a080109030f0201051003052107 72
    0xb0000003015003160034040b5001200d4000c0c01207000d002c0420462403001c00081428420340820601c0c04007c80e400030135244e0301410b00141c009640e441c3c3c110284188683d8101e107100320400e001c140740d00040e04a9a0b900d100b0000c3c0005a0740c04003180080385038001060611264241c102e080001c02d1212500d500c01510440741d602e4416031010b1070003000d8452007007001d007545011044a51140804921903513640082404500503c01201d24036403101d2181c82c43c1c0b9550b2a81080803103001128940482401e58000d0303100d0a0048200040b22010390000d81801820790002c22141d400140f1b000314103400020700b420559071020399605001000780356a415000301c04c004940c2d12210b80c05022140c59079801c0b01d032850345502c1c1c0480f9241c010744100d10781001c1444219a41000d80090380d40180c800f5001038083e070350303803019142550b5900340200d0120345601c407000b0310b241d824811503501010386205070030b50a03d9a200d07203843da64075071442810b00703010f00c04604249000d04200d03518036a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 581809676 1250 581808426 581808457
    0xc070b06010e040c0f091e120303201c0204081005090304080d02061905011a1608430312060b030f07080702070312081003150207052103011a 62
    0x1130760303807004004070680300700c15000c42e00401c008035880d00031503200704680b02d40c0740a07070340c2444c1890300005000d061150201c0402d42c980300c401e22301d1403c0352170f0f06510304000340400d07444003241040d00d40c0340006030b07044c0c1c14241d10501c000c000c2c2e039400281d4424a0f040b203103400101519a01c010300d08620950f00700b10401e20603d01c4c01944103600148203413041032014070340071140400d110b06d5410b885082c803802d88071044086e16007000048540090010400341c1064079013007096a502c0100580015181d03a100d00340e5510400b4ae060002c071940000c031040ca200d07104041b00c0c403080419000e0740c107030809010010a9034440c1034203280c0380d00000c00f9000010060343c60b07190032040c80501d1801100c1d92000100801c0100c1c2c20b030340c00007030840166030b40840c40500c0040e4044046908000007080f4003440b0b1500000040400d00044245002c40d1201030050ba0b207603a0350034114901180d1a9150130b41080c2d220b01250544601415a8156804101d1828580007034a10001031070003880e062215405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 581810926 1250 581809676 581809691
    0x3050a0b0312040504050a0203090715180f0512150c0d110c060402011e081602011e020417160e180f0c040b01170a05060301090f1203140c070b06010e04 67
    0x2001c42e000b501c111a0211414010b5a488003104016804280ea995060350301c05102806100c2260003056200d0903035142c80c40703540c0001f0a00b410103240d5584100c43c549108139051069042c07130a49507400000040040425a5100e850507902000041041c2040c0101090002a8911b40d4120001010440c00c21903124401502c00e940c1310b240c207403001c0340850140c0b0f00b17007410500c081c014141c2c00a500e484000a031740e5031001054100a0007040082155640d4070b545030f0741700800640d650b225020900c0107842d5820140d103040301021440b0f00542c2ca80c401032216040c281c000e05524140d41c0c01c90007401300c0307849034400154944680c603103080f0b06011343e003411320010310001418020715100b2a0b0621046060100550f80284006200a1118000350001e40700f08000e03000710740c1118019000160000c055141c0a0000700b14000443d007a1010206005143c0e44c1b501880001c4007140c031070741e46d29080082564410307204090000302901c0f62000010032a038010f0540380c1800c04090420700501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 581812176 1250 581810926 581810953
    0x620060f180a1b2301050d0b1903050609010b1302090406150c02090c03070503040f050f1e0c010503160c061806020c1203160804080c0109080301090516050301030303050a0b03 77
    0x242d045000c0741d107001d0900400050a99641000002c0100c4c0b045101c01070107031304030011201644104982168607484040100350fa80705e0007484400c0301c103503d000c4052075007103181403410014060070001c4960305211569a580d522059a81c1e800d03011400016a0748810b180843e001d09030702da100800c0403210001007181e4581010507507002c40e03c01c50f03034902d0a640741c418600d018041174810200080381400020002900051034600302c3e80681c0c11600306e100402170f00c61600d01c0342d40a041d8950b540c50603c1e105000200010350020b44242801e40c11031402c110003d94008a980340c00c2d0800400e0303a242c005010040d4420b100f520712401c0c0c5402211210b0820b50086d40c0b0081d113409281c41060900421140e0000c281c90158181c03000016040d2041d9204841c0040090002c0d10341c1c1d60100081d421b905001d110b0b10007041e100b40304041d201e42c5020a0344044410040140001000006810007807540c850101d031306503941401c0000340d41d2030b02548a4010181e281c011501480317610b0040c16503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 581813426 1250 581812176 581812193
    0x9040e0d02031e0406050418060e1609050d02011b0804120c0512010603022d0405070c0308010e0702060a020c0f0a080913020f030a020903030c010c08010620060f180a 73
    0x282c40000700112804544840c550440d4402c0381724110000c0c03030500050104551098110100755040140070811f10703241d02d1200c440200a541c003140b0310b903d1102e03003504690040015001404115011403c0b108543c0002c1c0c01403c5000c6c5031170303400c60300f061244100080c10054801070100c04c000f8030a0745406141012031044c890154038803940100309116150f040500078102501d83c09000610511840955540710400d92036100003031001048400185450b1442964403650055031010b00c0409d80e401c02a00048041c4c00c4040701c07080f6101048a21a000502907401c9402c48034016920810801094141020100c1107000b40c064400c0060500c201d0b0400b41000d0b80080303916894005000e10700c50128030950000c5500c002c418400503220644903409450000c0000e01501c2c6054003040c0582d00b1291000c1659000c1032030600103028041c0c1c400940c0100c4420049159801ca4103489c640c1d0345c0d0b8800402c030454156a03d00024140c10007046540c048012100c101c42c0786102c68a0f02211 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 581814676 1250 581813426 581813437
    0x206030402031c020610210201031e0f02190206070804020d0309170f010b06090d1b03020607050703031d0906090c190801170a0305030103060c031d03071b1a09040e0d0203 75
    0x940814119020800300184442d051f100345c50a010001d0840380c69005501612280320310620502a0500c42031000d0814001c0c400b84248482d40180d54842a840030207030100e10b05080001c40d840309040040c1942c100c1542034015230100c4035400c441c3c0940c40c1c2118001e400d41c104c81201b030460b408480c0035000c0010b080d1808000900203200034400b903802e10116002e150b14155009a100801602113092108416a48400302074109525500d0341c0200c0c641e0f6000c060102c0d29644116000c0043c175510142101c0070f900b100000400302d1018600188aa01002c5c041500c070303100b0000800c201219880071241da03e003940b02c0d495540248000050010a030134420125041c0c111240c00070986004604881c11a0303041d1211415a400c43d210704005002074641801451342d50a000810440303195007c880310394500000b503640b0103051500f45500c2c5101c8100b86407415000409000f2100d40e4a48003240c2008181003944500501c000034010b090240024049030082001c241c000a6000c401000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 581815926 1250 581814676 581814691
    0x81b09120d120b0109091508060c0a021002072d0605100e06030705030307260d061d040804120206070210080711030f0a081503060f180c030a0206030402031c0206 71
    0x1040202d04007200099409250b041070002c0d103211828400103520354043c800b4900520344080c0030648804407585060001e89210388102c4020070945c803400e030304000380c0c0c910404410056046c150540d5805520705600161014074250050740e200001c01055030280201c2d030841c100340054107010080c80d102248501510301c1c2d80454400060b058100007c9520444030b000c2d00461801d10f241d11441010b0034590303440744481806203040b208803500f40000c0e1001009003500015480c0c81d041c001c0c0420040c102c17400071100700440406c004110510203450071149805060b101c540a10f100255203441605002941712581c0501d00502031f50141d10703a4810340c120b440c0c4010060300c00c0c0407580d5031700132024250740a00317041108007600d034070904c01141c0001c0c40320808002158417500290804404940780b00e91400345070200007030075410500c2d803441404100e0260203981c850038080380d115001d291001c1e020340000004601113440401240360364645245804042a4141000035140d14098603244c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 581817176 1250 581815926 581815937
    0x32709060902070803181c03021b0c0f0f0409060f09060e12030103110d200406050a0501080105060a0504050307030503030f062707140d0510090606081b09120d 70
    0x4204240c1602c200c40d2116003203c040c908664034075480441008640c280d0303030868011080d02080102c4242c680344130b025055100035803075000554100b0018003258126061551191069207070326120b000d5444036800050b40c820742e00c1c4e1014000302d000303001c564800900380b610340404905800d0300c542c004004075100f500306101506a82c03180c2507442228a15060084004000400001305030303641e5021003840140c01d5502c0d015980c5c0b03601c801144180300d4a54030f03695120550300c580c5401e00c5003201510045540201480c10940000c005c070405000b141e00a26000a0600800f0b000e041541d006207401021120815140e14000307407a504265101e030041851034011601500c0d150b01a035002d600c541c03e54803242090500001810140a014001448051680c01815040c10350040103030f4032000e900030480307050082890003926030740e42c03016100b90302d010000e02a007a40004c11a410900484000e45907000d015424000e40c418840001c0d4020211007001c4100400450828404185a2200b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 581818426 1250 581817176 581817179
    0xd030513300e09161706030c120a11090c120a0209030f0f10050115050a1206121403070b0c0708040e010e06040e010c02070620011107021915050703270906 68
    0x2c450b220b0030b84000a40411a1818820005c41e800c000c8607901000080c00c50340041200380100e408010009080c102d16040030550b4814010015144841c030107007074800e00c0d01440d00b885000300034001c1024101601c0144404945030a9050301501c004641c01800c0c0e807020944040440e54076284411440d41074050003503641200c0344944a800d040321401e0203c1170402c003490504855603070200001d141400400031402d580c0d060709106007000742800400d0900d207511581411810098001040b003840e0380100b200c580041e404441c1240c0080384924a60348030812403403c000302e401107800c4441e141d00030f030340001104d80c513180101d4090407007500c0402c0040c00402c3e120382640c0c10a584100540d0021000f007141c9842012401d54910100685ca07601681d40403501e801c0d940da1301600003071032a003c1400002d40c0b905900001d404000403094044e018544110310581c10080300c800c4c03060200126009050600074a214a1441502126000040c1e0b00403c03103524114280601c0101c030349002e60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 581819676 1250 581818426 581818441
    0x1201270309150c08090d0b0c0c1513022101090507050111151501050c03131401170417040b0c0f0705010302130e0402041401090b030d030513300e09 65
    0x16154690300c143e07450111818460b250141c00d6440000d1494100c4800c0c041040864100c401d994010140c82d108641e50f40901ca0941c2c0c03034260504000301c1104004014021060000140400001d40c10303140c415115418990f18000344011164030901035003880001d80801c0004915a03099540980b10041600760000031141d0340d0310200e0385241404007036008030b8000c0c0ca550f042c4d00161501450a00c0c0f03004000c03c1c159065800c0480391403041c0020390814800c101101d02050700608080c40c0200542c80384a03800c13000c0c420040e01c0500701000001000b070491801c0000c8070701034506000c0c020340e151107680c2e000d5522000d0004800321400f6000e4041034540c03182c0216640345440740d00d2030103414241851520317001c5010744201d80c060740d6510303030b5130f450400b02c91024001c10a01c04002010f0464005141c100610844800304051824041016040c0034102c2541510b40100002446800118545440400c0114020501031000030312096190307000807100006201500c4443c1103803180360 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 581820926 1250 581819676 581819699
    0x605090d09030b2802041202032401171009050c01080109020a2705030a050a0605060312030109021605160f08070b09010c0807060603201e1201270309 66
    0x80200816080000300b00f41140c218400b02100940030013810041c502c26410400705d81c031640c8910348034032410020340158907041c400740c1007452a241c20b0071566941c104581301140014041e441600c0c164107201c90081e2000c204a0300c5102072140100000b603501c3c20704990381d80403084414001281c803000031900b80c0d080d0003941d0680302c0d140c0b1041c0d48841c0441400303206102c0e5003081c46c5940d1251000051955040049600c414010400f404001c103090400c5d5084c1c4a004084900941c041318100040c1229207048034111914410f0050f121030228044c0314082a000001920780e20902d90030205151090207020101c502d4002c85540031990341300c0d083d444d1342c50740c1720381703140c01c2000e2100b0307105175002e240c1c9483c80b240f04002651600206a80f92800c580e6140c000b690145000030741c50006141103020300c0c5602c0c00454945642125103410380c0038000d0307002403850080000c039804609000003500030350b01030041450001440e10365002481c40080c0301c1c52007540003554042e0700046081d4684c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 581822176 1250 581820926 581820929
    0xc09050109182f040c0e10050403050d050d0b0405010e010815060f0d0206041a0310090216031803231612171210080c0a0b04091808070605090d09 64
    0x100d26004a5030f10305000322421a00c1e110800b070b000040c0a07040d250b5540303902c0b078070807103000507158a128004030805104064007403080c0c000901504000c203002007400010165500407107803808564a0410b80304400c05400c0c0845459080344c2014000f082c0a107816040905a51851085990160401000c908408402c2e00d5294000d5110340c03400d6070504011410103000b0380003404640c0f506603512010103040d0640d4540d182c01c03c1d0040103201c02000b11200c00401010b4000e401d50604401c55401561031385404401414801e045099440b540054a01100215040890101c0c80b000000b2042c60006a1110b0b040042c01515007a095000d44160901d00b9a0303041031030004800c080d0384e10b002148142110304507061034240080d0400c00011039285101d910307051014100d40d4039007804140741c94410701d0028850142410103000400d04403098400300c4a05140124007100a440c10000f4441c007610003038a10100000d0881c28000c2d5074005038050014841107880e45134000000304c0740150035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 581823426 1250 581822176 581822183
    0xc0a02100e090f0a1d0c1f02030a030c020f03040e011d072a0f050309040507030e030f0732070e010509160314091b15040302090703090c0905010918 65
    0x1e08002c18181095003442c030358444c9200c0c2c00010040c40030307000302c1005411454001003650080c0c00500c9103051442c0c2c1e4000c070450f0345c405016030f5501d030407020b901d80c0500d0031508101a0703280c1840c0152803081101900701070030303e025a507590740c9644001d81c00e80c03400d00500101420305604001689129005c13035100e0011a0f903001c802c48200d503285100349400074030315105504030340100b030b010a010480c2e035800248190000c2d55200300311000d11040d10001030404003810b1030070100e407040c0c1b40d010046540c4460000807080d0307540303924030703101c4610341c811050141c41c501518010003071851203090a00408580e0340c00c684600b41e58004108149809001300703034000701d9150205881070840c80090114059a0402003103142120922081e243d500b102da04420342d11400801e90b1060400d920100303150000e0382c0141c0c540111000c1c101c11031255200c028099000c042c0050b036014425480b84d400c06034000c041c04421661a484a805080203015410202c2d141000d54605010340d107500c4c0c3d018a50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 581824676 1250 581823426 581823439
    0x705031204151214040227011e0b04060804200d110609031f0e01060503030301062003031f12020f09270307060605062b110c0a02100e 59
    0x1808110039011140c003200c80140407103c0c5440008420314059038a079021000d544032590302c1c10340100084e01e0344200f07200c0c0c05603c813a510945000a2880c183d41500d40718075802030f80b414820654001003800b58020f6036030140c0860b01054007a40040c896000c1c9000c0c0b07001a08205800d07403210000d040b50954980d115110070030003000940703041040144110020481402d001c50a40843c4c10701c108200b07a40713000080b0040068009490f0f10039541401d40302d2008120b42810100401e5880c0300c1070048030180840070041c12509482441e030940f1a80406c2c05030703604c078100800040350307805680c440c02540030011100451000c036403141104406400620380682960350302c0c05d121030303440c01925450b000100300d080350420f4850702c44284044942c000085946070003900303040c000ca84194100f1480342c041002080380b1140321070011003c0105c00d003900440003401030624401011680c029401215010a162950080200341071000070f000381d0b45610480ca60388001c82c1c0700768001501562128 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 581825926 1250 581824676 581824679
    0x91203060904020d060212071128050106051f02011416031a18010f09060e0703051312120606030e150903070204060305060a0b1e04050907090f06080705031204 70
    0x1800d0030540ba0000e002505011450060383c413048180d92000c8041600c0090b0765040c4032560b9440280c0c005400c2e44c0038050f2600350780c1007141c900c0c28201d6114510086104100f444240202036104000030703e4002c000710f502030a8110389401c000b60508510004d5441c1105580c0001c4e9545010381c401c405401c4191003a405200058004140030a0048150301c00700c0c20500c00b50b2942999000030340c90103070780b441c00345d89030043d000b40d07215480c2c00590726281440d00c100402480320940da508100141404030b00c582d07072010740031442d120f520005421410ba00148000c21b0782c02150142c0030758000700040c0480c5031122820703401e499410106590310380c030441c5410741120704003007095046001c000a0301d2a2030150707000501583c400341c000fa9850b400c400140a04050326108104529a09a5a0958506212488802040c201a41140110f40710400200d01c910b0034030420000e096100c80400040300310390b01c005c0052080b8043e400c80e600c500ca0340801c50b86000550742c540c0d00300c007050845c940fa = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 581827176 1250 581825926 581825929
    0x604170d0f050406200a051902040b0d030c02010c110d08190201110f070c080102040f240c060e0c090405011505030f06070e030a0602070302010207171306050901140409060e09120306 80
    0x10441d45c442c504d2036004540e8481c3c0046d00500c210a41c0400010110385002001e0040200f11540041d5991060040000800000e41c000b00400b00c0c8035024206843d050305141440d18410600c20b80003a03101034081e20714420030840b0b6014006070250406911844615010280d007240e6681145049048003400150a1001400010080c4510501c40305100030b07030b100205826a0450b030041c0c0219547c500c0f040c0311641a8507c0190003440c88200da00811121110103403105100302c0703001c2e2000703031a0f12645041c050200010080a0005000c045041c0b9003810054001c00d0000950020283c20060024030f82c83d00040b1540c1782000e030740181c0f10548990310b080e04c44941ea1074500340c060046d43d502d03101090892019000c56406500056070762006480c1140c1e0051041d00500d40d00401405a140c0924000c541f070410380791035041c9140d0310f1201100590720703c00142c2903400300d610700140c00b10ba1181d09800440865103800d040d0060b43c0c56941c0140e4440c0310901d18001920418800100315 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 581828426 1250 581827176 581827217
    0x1707030c021210050907090c05131401051210030b01080c1c060e060a1a0a03210306091e0e240613020409050610140d0b0604170d0f050406 61
    0x5080d6034110f0f500781070049000c2d415141d049400f030401e0b41048400f048441c880307000b105410f6600b4500325240651a10344011585e0083c06450500d030364101d41510203034003510840b000289072030b4000b1803500d08a83c000894009030300044402c110110b00010b50b1120004041c00a503c008100380c2840c502c403074019501410340001503031075540300c0c0c4002c0201041030048500a080c030b12001309182c1200869581c111000c0f040c0b4034000c2a42000070004100050300fa8401e8103070f83d04c40d240503a00d100804501900b960342080e030b640703440c109000c5541d25980d10035917103038000341d08180414114000b407191603007060030910483c80505414130a8012903000340c50780c8584c000744603503212902074030300d8012a00103410003040544d44405000342803421000088145100b40f804a803a405134044107031150142110840b062a1034400d0841e00d80d031000280c4025100044102a2000166180c1d6a81d42010232030f510200c0d5102080a024500c940211001c1c0d0300140c40d100f1281c0004a15041d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 581829676 1250 581828426 581828449
    0x20d021011090a17071d1303090503031602031203040809090712020307090e090c031216050a06142a0c010e07060e120703051504021314041707030c02 66
    0x4403200400594441d55208004000a0400e011180d0324110410760445d1604101e5040340344a41030500ca04d520744482c1c1a8102d900190000c1000d21b030401910f01918020500e40040e0350500000c01c030171f26150803a510414000d40200d080341d0884001030051304070703841306844c0900070850030058440d140c104003852907006800b926000c0201e05181d400a0201d03002510712100181000c1c504104100e41008445e8102c00004040c06020117048006030350b5101807143d004102e040070400d000d81107c6210426405038100b41940c2001203079160071030050016041169129583c100460405000001c10030080e030201200440b1441c0c00001c4d0517000d412031210800c90b9900c8003101255030b0404d0060038000c04064030307002010080d100c1040b01e40078400c10095030702c3c0d00210042010460010702c51005401070100081c103074545002103502d542e801da25105556003000504800f42003101c180302d00c124001c0540031000303091002010a81e105556000d00000c460002d1140980b420342c0240c0c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 581830926 1250 581829676 581829701
    0x90a090305130f0510031e0c0c05061e070906020a110d140d0801051203041a130807080c010e1f030204080d0e030105090c0d08130306050c071101020d0210 68
    0xa0074988108008144032506401810f02c0f021401010042c0f802c10801000c80c0c2d08180c01d09110018282004010380e481801c20320316001c2e250020205d2031802000c1882115400800391040d80c0341c104600708a0b02c03008a07540083e17290307100001e10207600c03070040c000c10780343c60782d029054241660320303401e11014032500d94960081140d002c10001074030303800412000c03440c2e80c806040030f8061550302070001041640018001e007161070041080d00c1000c0700302c0c0d041e55402c070804046031116492032005409402241b144110b950070010466420001302c15007102d00600840d1280100c4200441c0c821641011480e00642290080a60400c0940708044d42c201d8502d030050426035114800780c500701200da075000101d030342210101a40c3c1000c4c0116984280d0703680c0200450141d40380882c1d460024200064403030000480d1126140c01d20680c040001c54001c00301344001c2c20508041f08440e4010101100c0410808085001a5002140506542081d5000340c54a817241400e0301b4003500010110300e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 581832176 1250 581830926 581830937
    0x503040614040509190e160e09030f0f030f0c1905220605070b10051c0303020d0f0506030c0901181104030b09010b09010902190c060b030105010b090a06050405090a0903 74
    0x3183d151500010144a4503014000c2207200c1e0a1103005400c540f40c2d0984d202c0d40b03070410403601c03000110026035103080b12842c002c648005d07a075000c010790560040d4219500c018500113078078681100604080c6000d148658400040c80c1c80782c00b0038110a01c140310806078480d0314142400d1031140140090b0485554118100584410414100c8032810305034102c08046100881d0358418807007105a429402506029104109420100004c04540380841c40020480c800c1d0340c203808042c403d806076100f520045100344135500e404040303d80600001c40c2e0300c6000c2e110b04404049a03280c4aa031482c102c80d00c010488002c0d02100e2018806000e0801c8408494141048000000360703400c50540c1c444d0000d0400000c90b00302203020444910010307403007048600e00521460320103a10a6005c40a400c5042c2130540a1031800d00d00307800902507090040c1d40c194a420000154600014028500c440080f1038616243c1d40303883c0c09842c0c2340503a010740c03a0400111800035800080b81d5200c81403a5006c0d0031710 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 581833426 1250 581832176 581832179
    0x12020c03100608010f0513110d080403232a06040b0708040503070609240e0d030314180a0b07051e0c1002040303080a0b040f06060e0319050304061404 66
    0x400d240c04000450400303078542d5a002008446801e200e00c0207200e034003103000d101d40e081c2481140c01e8201b0f0940c020700350100c601103d0b10385588540c1002125640f00c1055030702e46581c2c2c2040260300030210300a48404008101c10200b515011850700a42c40145140030b110b41d45a003940541fa6010301c05032a040282044081540140312001c0c185040c4546d03022a0340d1800d01c0185414800954002c0047c481d44000c103000b8101d0408603103c0d600700040090b400003402c442c0c1162115466640c40d074010745070290300024580e05400020f01500603d03404070300d41e100e0303d4641100c80c004001c0c10500b600031841800000c1d01d4240703004d81210f0549015402c08071500103544094140d90301d0f000c08004000341d110640403040c001c103140756035011011402c061a5840c068441c1100a0481d180f503641c484039030000e035807180e00180864599074010040e054a403030000c1c10789046039010510038400c5010001e01d00c4110207041c03d4145e070250140d400d10b0b03d0200152100c0c0500094800c42c040107010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 581834532 1106 581833426 581833429
    0x90c0102060c030c0a0c150507020c120c01082e08060108010207031e030f050901090b150102120a050915031e06061903090204020d0204170105060d12020c 68
    0x11345580c0ca000301141262000041c08006040410280b240c4c80181d5003075001512a4180313800701c5407104c00000401131400c2c3c0d0141440340c1d96001c3ca0440c41107520481545400032188140c9980403441c0e40c08156540032403040302400360032410002c00502c0d004019413401052054001c6240c400151401441402184e100d0b03808262088000b071003448c400d91260b00b044d403098408100b81e003820009603003e0000b1031700580303c02030004003040800b00b4502d121071071040140c000748030700c0080e00b02c21350868000c41c44405c24808144044111a00c807109000017507102ea907403242c2d803481c02c40701b070620300213040480d0610075a41c001005965124442180c03002d01e21440107400178000d00d00210043e00c1c440318003c0d00540041124000b25445401801c21b884403004548000300010425900300c480031180c169000d900390300c2c80c1e07000c0f030044074001c91400194410784070600040310 = true := by decide +kernel

theorem cover : BRFrame.Cov 581654676 581834532 := by
  have h0 := BRFrame.cov_init 581654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 581654676 ≤ n) (h2 : n < 581834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
