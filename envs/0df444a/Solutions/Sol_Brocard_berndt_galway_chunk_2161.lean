-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:36.394787+00:00
-- url     : https://prove2.me/submissions/26f539c7-5e6b-4691-9a3b-361ba7c51c11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 388489208 ≤ n < 388669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 388490458 1250 388489208 388489229
    0x60306070207031a06040f1503110f090c07030507080403051f110a031505041104050f0402040f0b0a02160b0a0212040b0706180f1b0806060d0605060a180f05060301060609 75
    0x42a02561903911065007110100010040c201c800c0401c60248400344c48250790168800c1c00d03400550501100320bd60181c00140140c141d9500c00911118640040d1020341c00c01c82c061200e44006030102300200080c5024000828418491603101c2c1d1040480700c040f40e0080b0b041110040030b100302802075401c100001c0c1004946d4074a019080d42c1c11100c0d9500c256171160804a46c01301814281d030003001035481c26100d1402005a50040c48141c0c450342c402e04083c203e00b5841000700b520b481e0081d22422a003441a1041201305078202031103650a60007a00d4802c40c001040c0012540400c03148005000192805050030f240c503000c3d080074004c10001400468031150006040074038540d01c00e00d000d0348a021040170084504040e141c6448003240342c181003049040101d028080083e04a200c2c1c00000c19810403402c40391740f140081e002c06000140c10440480c0d001c10076200364640340c120740f1078030100040c0000400d01c03d40140c41025203c0d038026454007105004055203d10980c05603400100ca = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 388491708 1250 388490458 388490461
    0x70b0a110306220c0504211e0c0506040f0608180706050d09050d0513091a01050906070c1e050103051302120f030307020c0a06030203072f0604050105060306070207031a 74
    0x3803080943e000340105000c03980c0750441c007002454000300035100340e40c4051242c42d80c08600064807110545081c80180c4098010011440b03081a13403000701d503060703109202c850841a56940400c0c41c1d0742050300f11401520000c44280040ea90185805500920742c80030f03081401c41c40d81c0c040d5102c96540c02180700b00400000e2849803a4515044200791740c0d8442c0c1110301804d6482c5000b1300c0c540210151201703810130039000240c848014050b0608240ed540c895241994900c001920b480e40042e0b0540c3e0000824021032000c40d10000d2094020080c40c8004d8035000389948000640c0c10090700841c3c14545030000f40603e00c01c4a1903948402c80d03051b2290b1058501c408410380c03502c8842c552802b19440b0000c100074941e071b40450242c03001c240680d0382807005610303458150240d0104491000008041d003407520324080c04490590102c0d07001182e9420741c1d011a5081500f4078800300c03411749007603441c0d0041c4005401d00f0041203912a10510142000c02d0039035890901c4040c411223030302d0000f2100c90 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 388492958 1250 388491708 388491739
    0xb04031b0c09020a0e0a030f0326011806150917010c1e0201090c030f0501110a020d030c0e04061d060906090a0b01031e230c0d021804020f070b0a110306 67
    0x171407030700e4908004010120843e41ea1030a102c4c1c5440318841140010703c40c00c00858040f14145442d0300e0035491a0300c0002681c2040480f00102c401d059500000079201e90001403406c01c1c801031006005481d40d5903c000d5400c1c07210603140c088110b404c1c11010781c940082039810035071150070101c8904580046d001c0d2010461000c84c0500082c1c8000b0700311001034400013080100a080980100b8843c1c0024044000c07011991510782c020500e8410150300010b1214060303a01c40c1d407100c0008401c0e8104011551100c40101d4100d450a400c110303900008a1080d00600780040c01c5654403240890b01006a03140032408204000c4000d021100c1d05c0b5210004028543e02a07002414061429005c21030120b10b082d038588042e1004c04c2200b901c0c9a001441d0301d41003182c0301d0701d6501c260001180c2614201102c07946100952155801000c04030300240800030590b1180000c0c00c0b20041c2400480d100e1620707040602a10002411400c08030f4500850410410303680707000da035485841180c0c2c4c034154500c0c18 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 388494208 1250 388492958 388492967
    0x1020705010804320c030303060a051009090c0f02010b0910060c05010f05151e0603180106050409060b010f05070b130201020a1505160c0803150a080102070b04031b0c09020a 76
    0x14003110605a0320609400300310300b007020b1650072610048100d51080440005150716071000340caa480d080042210107012f07509012109551400fa40d19211119698600a40d01201e22070140603001030f0040320f549a90340d60900803180c2c4240222085c002c142800c131f182041c1c0440e00d1181030140034611844109100342907100e0300500356014800c3c081c5140800404038252010340f007040c4034000e99851811081d41008500b09800d40c081c0c0050320f1034940d210b604034130805e1035554138003d41d02d990300883c407925a40640c080d998480c1c0c07004900ca07030481001410f00903602c81101e080100900007200454400c002d269081960760369a121030030310a000403400e148942401411211018036403a20070521580141c3c4509024035801010340c540e20003c55030031220050240003240280003091400c3c00c2c96401200c402001495005096612190b00c3e00703a0f0080001540d5000c42c01d01080141600408180d4060300d845146d5400c0703180f16651041d40001074001d002003a90f011034000300141c000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 388495458 1250 388494208 388494233
    0x60807050c0a05030909090a050a0233040503062523030411030c010201020a020a110a031a0f010906061d04180f020f120706080403050d0c0305070f0e01020705010804 73
    0x80c1001d80e80b0000090070950b13980d91004c20300a000c0c410201c002008000080361300c1442581c04405802c0722001502040040c08021240d050b00c0001a01605103407251110f101e01244011410300f80c855160404040c103150000304460888020310795512910700c1940640c6052903c42e05100e041c0d080c0c3e81d854468210011115408a14000802e1002741300c9034005403841e500003101155052000c0c03100490a0313000f928450700140c0e21104881d800140082a41502d0480140001c0d110329030740d4594104031104001200040182e0006020031015411096070240201c0001071090038a041c9004100042611000340b181d040341d0740e103c40f07030340d25500804005140711b00041e004140740d003400c0c6d001c407544d501308a12030704203081904002d0070f01c1020f0306603942d40d0b00098211140380c00c100f40c4540308010b000701d0410204009a02118025214401d0241400d60300000c1a00d848040075142e1130420800d18180032031204442600e03030340019084241c800a290a422070b0302e607440c08080b00707141c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 388496708 1250 388495458 388495477
    0x180703090611030412140706180203071203080714040e0a0b03060a0c08090a0f020907050d0c0906080709081b060c191a09070603050402120601030303060515040b030106080705 77
    0x300586a1042c4000c50b01031402a4081c509a5548600b02c103403c2e2409044c02441c403079014020300c150303000314015500c004400d0b900c031a104c00200810b070380024200a11038000c4e000800040036000145070f8003082283e4801020304290302c11034100d04c440e02c0140980d1051a12503e00100010341000642d0814501d80c10045d007202c80b02d082071707a500b0010701001d0205400040204002a040c0344000801200880c4c1160102c18419400d8003444504880140f0b90002d200b4100503000340c2580a00c40c00080d194240c0e210603040e400d1010040c030004015098608100d042001805071000c007081d0228a6041d040c007440d11038180ea00410300350300441d49400c115001c0c406490b0003594140300ea815186200f043d003060341178907040003901801415a0a040a47d00a060a100d910f001f580403d410134002000000b20107010350b481441c069090300110006070b01ca580c100154241400701001c8451035000d068141810300760514010b006c144500390403c0f0422010070712580c0510100c480c040c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 388497958 1250 388496708 388496711
    0x207150213231801180614011b08040608060a060c050c190b040305030c070b040602121e030414060106030e190f0c030501051f0b0703140408010608010608060606091807030906 77
    0xb03810690f00301810509209403562124032040c5480302d00c03000d1050302c09858060410030354080d07142c40111006001030381d0b038106140400c000040456150781c00761000b0050750341c0d28035032460f003081801112442075003d2824450380080b61030000c0c0340880c108002e00000d035000043c0003200c01c888a200072556001280581c1c0c009400720034010003100034403100ba1044102d40c0c60035503c0115100702c4c4101d1090800507000403103144100d901d1a802030404820072508a007076400d6002c109955548243c0f81205c074048009602c2c014481c0c284956401061181400c01109540d0340b02e0540b610315468908030f072100d8000461040088190301d004286802c01c4079070003580d40360f24002d0f00800098030b034101d11082e50740040d924544803261582c240c4003103030b00340790400f032090798140c92110440b03110080720102400040b0744810248a0f020003001700000229010f4544040a81480c83c041c0040380103203020042902c0350348a01400e0400c50105001b185619613402d181103004250038640208000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 388499208 1250 388497958 388497979
    0x7051c3008040c120308040303020c0309061c0605190506030903040e0709091a0607030810051e01080604060b090108090a0609030807020c01080910020705011b03020715021323 77
    0x69840206180300c2d62080905514042d12400601e00d5000a4800103001807071540000340068440d4010f80070003600d810480c2c4c249601d0100140464001005000300c801c00340282400c441d5050149100a00c4280e5800d00c6881034860440b44803e454080c060150b030000010400351441041198020b00314016101c2d000e003805040100402100d02c56a46030f282450108004030035004240148110014070807840c018681d5070555134030000130007011524000c040f0000301d0f505e5656128a91110040000e0b0700d14242c0030000d46550005441540503514022092049504000032100d5000e402d003003181165503003540040c87d040115000400260610700d1080c201038101d00214014416a02903801100c500401111402d0041b112005036501c01c400e442858036195008200d040d01070400403c040001c0880e011403440502900000203500003094405d002400d02c085494245409081d0716081040c941901c2c09191400b0f5502a103010904000c0d00081021203161404409440001380 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 388500458 1250 388499208 388499303
    0x15061801050d2c0d0203030609040f02090a020d0606020313090b2b0c0801020313031107031b060e01050f04180b0415090510120b0903040e09010203070207051c 70
    0x103a00c01d03106003010280b003043d903040d0310741c0b00403580890710030080e030007103045988203802c20004000c0034000f594811050000d01d009601c43e00105803080511040159482d2200700e094412a52958800c0d000c6410a002d80121810380c41c000404a07840110045041180e040c00121980b401d906004407140d07805900c021004c000c4095503990f5400307500c00c2591599600405030917171104580381d0069814104074400000c0c003684180041a0782d560132034507046d0302c9a075940c04010a00000c40344065141c00200850317980006d146404032400e00e0643c0c00c245081070031217a940106c0c007030980803030b034030510760180d8a203164080d00c50040c0041041c000500d030400c0000d002a19806010001420b0600040c0304550b07a103114030841d110440107241c07500c0d00d52500c003c000b0001d080e03042580410840010403080d00103240707004241c5107000680e2070410480c040d2524603070364081c500440000c4680303e10700c260391081401c5940c02040f203c0c1c1180c2e6140e2000280130840c007030f2807491890100c0d4442d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 388501708 1250 388500458 388500491
    0x70309080d180b040b1605030405221107050a150b130c02060c04051c020f04090320120306062d0403140c060919050d0b070815061801050d 61
    0x210b80c2c1418900e0499403a0012025284540c2c050b50184040801072255000c4c0c8205032010041d00620130340b41883c0d140c400007220000d1440044281540e62040c1c106160b4092041420808460130f019281856640d170380c58a0702c01605001d0050300003440d017090011a10f802c40d43c2128001809220b05051190301d40700104040d880348801440b80000049061180d90111010750304002c105c413503171729070703a503003e42450b120901d0032a0084401d030100981d0f5100ca001d40c1c10b046100341c48410401d1080c42c2005043c0b1142003602e040c60703018034402c1407018240400c0360b0300404c0070740e05255101c0200740355801081801201c0b82d5180702000391001c1c2000100e018100b03507842200301d0344460310301d40069540c0b2211043c540740d004408000000741d03440c003090020100995842203114255480c0700050104a10751405d407079040d0340c44200300f001c80d403003000d0079846600181081029551180071901c02c0c007480242e44c1140104030020000c1c1e80c000e07400d540c0c101018100a00c040c4441c2c2005c80c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 388502958 1250 388501708 388501727
    0x150901141303030b1e060f0d050a050103051b01050703030b06070f2301020414041508161502061e062107030606060f0e040f09050a0501140604110f070309080d 70
    0x40003c0d03d040ba0882c6149041c1101c102100d0300000c000c9903c07010107041026543c00311004500e40042001101100c00003400303450b109140c07070702000442c0c2d07140d400c100d0708003900c1081a2044c40d084500c0150103a81140c25210415054600003c1402610011802d148610750015105002000120040200d0828818488982020051a0050340c0c1c44614281d002c0e5029803004401c080320411801d08195001203c448840b044104c10070303980b01d40f424240403120030380c01440c0c40d184005000505071038400c061b084409100a01503407902d0900303180041e0112180d068141030120102e8581c2d0769259604500c600c005041114880402c01440c0e603d0405100440b4028285000000c280340254808590f008858403120b444444900800009050501007244443d6640840c4004180100310016005104000018107086c0d60b001c81642c5182c01403840d48254140136000003004440f46c01d0302c8010319454015030322008a403030255510140f070303040b805030b41c414a00c40102c825400625503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 388504208 1250 388502958 388502963
    0xf04170a020a0f03030503010b0904020415090608130b0f04020f061b0606040219030b0d15021b03090a0605031e0f160327030909060f030c08010e1509011413 69
    0x8040c0c0d6070f60b085150512503c0e11000e40030070800d100400c080c0120304014000a040140300518050300c030594540c200c6960108440000d040000a01c1010b400030b20f552b4000303125449954100005540d200040301c1d0080c03c59680c908907402140442d245d501303000582440007020981c0700d1004c407080d0010243c805074800c217144100d10224580b403d1500c200c90a24020f400040107003c0e0840c070a502410b45009203030742280108201c11301090311103501e502d07500c01d41207016950380d1a0400a5011044141c0d890742c0a4008120050160369107500e030408442003800e2050700d070364511034021050a02c5504904001d80c55000700000c9040107080d4512880c41d07484901c0440306607a0741141102c3d044442c50050100e6202c002021490b150217200b0711034441e1511160f881c2c5c4640d0980151400741d84290683c040b5840148200101c019454000c0c1410000810500c001002100e81d036130b1001d00000d2510040d0400314200b0b00007134020701c205204100c0819020308000300383c40d0300360f105e8050a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 388505458 1250 388504208 388504219
    0xe07170c01081f0e07050c0618100b010912080d020d0c11010e0a02131d0c030c01080603061b0417060601030e0609070e070e03060c1803210f04170a02 66
    0xc5801107581e01801141403443c811007026810301e4550030194034042c0412051002c00c3c0320010042e8020801b40d445011030072051032041501c0c199141c03031b1101c00e10390b03d4041410142040360590b032001141c1c08507620061000a40d54442c00d0981c0140720b0f140b46070f10410700001b800a600702d00c030b070014141114140c0d41c1c41803100b8503445803402ca40c0011110b003003d4201081e001c1c09850000b000c41018030b203d103400a0840c41024070700090580840b90050950092006010545030600142c08002003c0c24428800d1030003100081d2074040c010120000080303001ea81e8200130501500b61005800c25046507407403841c1d01015959614400c88034980024103240f651251072001041c080e001c0e04011004104107070516440007030030f14009042da01040101a540b0341c582da420009507001d442d03d0303068039070345210034a90400d034603043e900c4080c0642c2c00008200c100f5141c1c01408885016840034007510f90f481c1501c034001500c82d5901c090148404a0a43d00500a010880241c400d100300d58 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 388506708 1250 388505458 388505461
    0x40e07090605030618210c03030702010e1903020c04020c030c06090313050d0210030b011b0311120310060c1a0f06090604061206020d2304030207060c020607060e07170c0108 76
    0x42d01d03000c2030801005181c0113000400200302106c800780c3c2c0c2c02e140c41c484490401c10500c00040c5990421140302c00182c1d100c94120901034806d1043c000210001d20502e002000e15860296642c04010000c0e40210340c00560b40903104002d009031500302e1840405d03560701d420100c025507502d8100710600954825800f0000030940381c10710700403002540c0a000034070b9030070300c0100a8009000108550b03040c8402a0701d242011500300b6540f01c00c41d4032a413a141e0000d4820450140303050021190000c030900c0402c2444440c010400003001201c42171301e820031848503140340c02c009000342c04500c1c0455000300000e0041c9184051130680c410407003910181045d40da24402c000603141107205800880c0c07184940714010a5031034004002c0c3e904074502c0402c60004442c0c00400c0d52a090329405402d0000605101c2019414441d92006000d06c0c58007a03d44902d80d00058041c0c840d096004200ca5500c40190080580030310000005014000c1d01c00084022448042e40381e81380e006109000500090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 388507958 1250 388506708 388506721
    0x712080c040e0a050414061e2202121203010e04060c0306031101110a02030607020105061e180403180f14010819051e1e0f04051b040e070906050306 65
    0x40a41d02180d01444101806868540200c00103190140095856081800307406903400d80c10862640600808100c0482140b11011042c0b05002c0140840c101d0a064030350842520035069591030b00d030380d0103c5001e444000d0345042e8514190100c010303449418004000002c059902d00c2c416403145000741f00c1446442c0a4980450441f1403c0c00010303d025640700c0c84007140d5102c0c04030103003521101001c4607121750290b000a450b142c800c49400300141e440d2000c10100e0f08098820811a580390044900d031b0342c500000003403030315912888290007040c4000c001801d1502c901c0107042a184040031007400a600d0b080030302800001d42c02444401d0460120322030b210f5208015141c80f8680e1003e100d542c16416004280140c007001e080343d00190032240600e0161454100010b0080303c00e500c51018403049859003554041c00180310303200b8002c0c0380c02000b004c960081004104200c00020f0300c044451800002402001c00827603484082c0700d00600401c150341d00364802415100200c04450702d07546c0d00b2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 388509208 1250 388507958 388507981
    0x7091d010c05040504150f061b06061d06011e03020a050d0504050a02120d021b130504030206060901150207050f040e0303070314011d06010c02041503060203040506090d090911040504091b0902090a17030f071208 92
    0x38fd24100c801c0c0070009030713680e00034400d50191001106a141907860209401d40c4141a2641500d0039034003078108254080851400102e81d0704442d01c5400584002504514040d495805442e914600707120240c0110482d60341c0c2c02400f45005a125504000601386400d0081d901d86045402c28001e24560001089044010140e51030309181c0da801400c0c2c1c581800107002e88444540603854009450340ea00c2c08031468240051032241c0160360f80001d208140048820701024189c1c4070030808842401001c021803a10798529074002801e080035422503c1c14404035000700f07491500240c032048002d10110400c501c0f9001180501d008400301d48958854a00103074456500070000d401051140031300f041007800c9a0000b44440850503122402c1c00ea450012030150b800c07a450403101020313031100c0558000c5402c250540905562041142455449004100515014080c1046450060981d05c500b03d40401c11614014280300310720342c4541c1c0c64a012400400c00b11303d80c4004c5440500000c142e0742c070304c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 388510458 1250 388509208 388509227
    0x201080a1802060c010608031611010c150b1816021605031906110f0d0f0504080f0d201b0a0507091d010c05040504150f061b06061d0601 60
    0x389000c04800481c103900f007103d940d115140b81d22a40d501c1c1d190000300058184090031200401c0075001103010507501c1d104850003007142500b8103003d0426614404560ad000d0100a405005140095180c01507000a890360490b20142030744213100d40f0420121071132442d0950071036400342e02201d400140c11100c0710311079001402010f4040e4010403202078106040c601d0b808442c1d002d00d00002d41051418940103280d8000ae00010340282c0c00124a40d80c032196109654008070382071410815402d26580d076400a109400410b41f80b80c1003c40e03d4805a262a80820703060030802c480d100ca05c09003802c0028458200b80704103480300d16032030401541100003240c03140341035610801416445084c81c00311001001c0040c40070005010b2a0b114000181e001d202c1c1c10114200c1d52103468032a490700c81008103403141c50364a885000c0304c064041000640c22020303903007901c40d54107020241503084d60300000b80050445010788640d0500100041d00442c481c081541030312045d1003d40203a40300001981d01a94 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 388511708 1250 388510458 388510481
    0x1305090606030a271101080c1207050d0e190605010605030f04030c030c0206031807050301290418060b150c0c0f03030c030a021c03230606040b040e040201080a 70
    0x20704000080407001a079100c141c41c402d1914803c41114240200e074418208003800443e181075507402d03440c41a68001c2c841c80c2d800018a01283d2904224502e0b45200c4007014003010203020000c01c5a4072400d81980004241d91000d00884007111461001d0707500c01d041e10102998414070700000407036110303c01c00841c2e100d5400c010180010703072a1507a0451b01c00c3d00c0c00400b50704201038492a10010707074507100150b001b1604803039495046214401c01c1410a181c0740e0010340b02c1e82c5003207002c81d15003041e480d1611500f9240b840c0e80d8000300c406000319010385815124a0310442219505004002507507110070301c41402510007000c50080c1c0145600701e0310a60840f0406580300c4611450340e49840320319415900d030042e05690401e80d0103200030f0714540010000b038000d0703000040e100082d20004455400400028582849400416034111400b080c51244290104280c1d40c00103c0e16154a004ca03001410500c071210380d280c0d5074070324141214505a4040380021071940100c0e07849603890040c11a1200b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 388512958 1250 388511708 388511719
    0x306130501060206070e040204232818150303091d040804030803040f170c16050907080718090f1404020913031202400b18040504060213050906 63
    0x210741c102c00741d60160486400c6d40e481602000301261003851520132840103600404007050150840013000204100003185400d141c01d400c0c080d00303842800d10140002c46149001c102c480a201080407005802140210401404040c13130000815902130266400c50744600845540c1e0120f0b04582d03041880e060f5800703004502c4c240010310119403688021038100e84102001c91030416150744542802d0072881c0c0101d801714000c9900c61602f14240805420580d410030039001d098188400120032540c0070b040d040403c9821400075184034040c1d166989080d02d00c0c1200c4d178199030f50b0340700503001d01503801000c40c001d401c0150764041d03110610303c000c1c0115030080440c0070694482000b140b10841d80d0100313504001916046003c01d02d003510061521040c501000d1b00c120000803100e01d5400d052a04500010104d0300c845c07940c28100c54a060203941d005603d40780e4800d081010071f8880c590448600fa0b0280c901024002001419801010000070300c60703a01c841160340e1000c0104000d8111419074104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 388514208 1250 388512958 388512961
    0xc06210115110303060d120e030a03090906060527030a050a12030c0f02100209040609020c03120612100504080d020d1a0f011d120d0f02010f0e0a0f0c0801110306130501060206 77
    0x100078102c224107d080911f000030070103500000080c98803046046c1a0003051900105106442484c06047d003e0442c42c10210726006800a00400d015086c010090415180352011030055900384041501c45070000c003101c10454990501401124086d540f503400b0030310b050003540740913001d8028503840303240f242c0140659060592100010758070a2102541c81660740001088140321032000d803140b0078204004603210400180007100c40e00000c0d0200f0321600d48420b144207140400515015001c0e550380d00491943c80c3c034070b0004890301074445030b81b083c40e0000c1030310010034283c1e0b4088041980031120f0025404107200a0142c041321060342c4600080c140f1002c90008460491060b00d03d01e80580808109440c041000741044076007144800000d0808180c0c154560b8240240700e88090905003c2007001d138590703419661400d8840005020f0404490314a00740180f015510307006240d041d009022404a106038810103610859000e4840c0c0b05000311440c802000b44140c41c1640c0c0c06c0e4004010a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 388515458 1250 388514208 388514213
    0x609010e0f0402100908030c010204030c090209150c0a02061908070f050d05100915060311030f011403010f020a26041109090f1005010303110606030c06210115110303060d 75
    0x2030361404c07004020b012000e003000402440030001818400328003400142c43e10305501e040c1c400305045034400503640c3d00510030620142d440c6c1442c8030b00044078450080d0f6882000d0003881c10325602d06d20103540650701085005001d00341c29032101c120b5075a6555183caa58881d40180e8556982180810010307405100400700c4000e180c1c40741c7c0d082698400300303030401503407400c200701a80c82d18007622021141c095030800240d50075000303441502c0c80c00c004207415031030170800800050f24144176804410103100041d00f6681c50a40c00f503a60a0b0b680700043d50750303101290024090715610150710710302c03907004000b00782c090500c03c0c851b0b80142da00c260f401307550048400801c20070702000ba00c080c529000d01c1c601d01c00c1d580d40401c11074403036034015070020600c0c3d07140d400c0c054201502c052000707999030011010043e00b66404100948501400c41d180703510344104004142c85403900d00940711001e00d01c0c000114a4100040314508d49041030740e100503191241c0c46149440340019240d03036801440020403d0300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 388516708 1250 388515458 388515469
    0x1201051b07020d02030616110607020d030b06070b040506060a0602010b0303030a24150f1e0305150604030c03020319050c0d0f060c0e101805092d0609010e0f0402 71
    0x18520700042081d5643c0200f50002801c0500070354606944540c0076000d04201c541140c4803140b500c2c1c2050107040303540b17003054000c1e4407041402e007042d00f003654400003a50300ea6580c000350b03030040d038104c110702d0703442e04d060300c0d12503600c0c103058980034414020b038100028083e00c140900b024155001d005941035844003890800900b1350b2111250f8600e4072039411804d480350070940d040081450400d118001248002e014010074624202d480810070444210040c3c200400c0e42105898114503002901d50b58070708032000700d5030056440d9580000005030010078041c80e000200150390084054803ca41c1d448000c83e1891104442d0003800c94000342511041840c00c01c461224042c0503509645040483da03407018100d0304980913980210394071194441c2582003482601c11001c00d5800c2c01101d4034185840048080340d0381c447e46d42705203040400610040002c00c08045280c0d4845014000c09070200810908014121461406260325030000100c0011006c80d850103102e20710140c020b42d440d83e400380714 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 388517958 1250 388516708 388516717
    0x1609021b06130303050708010501020d120204080a0b0609010603150e04051617070611120903100c0903060506090f01142b0204060e01060504060f030e0304060302091201051b 76
    0x4162940c65104181554001e00c101480b80e000d0b181d020080d9846858003a08841029140c1c1080003102c01c01480700d40d800158100307036403502e400c00d400e40000061022000c2c1c452500503500c14005c2068132000c10040c0000700340600350440b05400203a0b03d40390124211291f081d02e01d012040f102600f00000800c00d07100d40e03001402082560001071001800580050441d4071003001811460502903261500340843c501601740d604c0c18410076445102c41b56641d021440100c0d410b69030014038420740d82d5042201e074144244002d018821a006034101800392a068441581e8141c20540001c00380e251035001e8500c0348004448500b03984e420700035219a0a0340c2603024917017110354441b09110340d45400369010740055210a00c510b0201742403050005070340300b9900c142e010350388800045c0041c40d000350544027038401510742040da00142d40c008601400b900304482645002c0000c011460340e0b8103400a01c22a5000c0d40e140041414200b00c1500303d440444e02d0186510783c00c01c0c0802d1f036222640050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 388519208 1250 388517958 388517977
    0x50703051e040b0a020f06060d0b071214040b09010908030a0b180109020c1c0504150c020d0503030a0c030203092e0203090601031208060f01050d0f050108060a0b1002030909280b0f03160902 83
    0x50901542801c00f102c1118042c1141d87c1224dc5001c0c100410081809400781c0d22100c054001d112007001503a440c00140005011200416100d0400500303c1e1640c454a00c010703d0416010115960340e0180e40c0002d501c0010303496800d02400142c41c10140c1808900360203401d656075402d29080c9402040038801c66000024010014481c3e001c038056664010b61401382070186010b0344d620b0500c1802c00b42181ca64000c02824075005100f00300341c0090116006220000e125a90301e10841c07200e01d0545208010075443e10214800300520040481c0001c0c144d058074881c08084d030b581e400402c0b05440c0d05030b04903507443e844800708141d485903502c200098002090042400709504010900035820344409030441100340e405501042040840f80c06a02018482558017004000c1405002512071040d00c00f00d03801003041c800481e00741c0729505580d02041c10002e0507509418040e0840c034028050480030544590303240c42c01a2128600411854601b800440c0b00320422880d2805c0000039403c1306041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 388520458 1250 388519208 388519217
    0x603110d090b0105030d1d0402070206070507090507020610031e110d0602072d060e03160503090306070206070c11030109020414100603050601050703051e040b0a020f06060d0b07 78
    0x14040003030680600300140e4881c441030a0030390304040034940b6154000d0b00b170004100a0011040c00c1d200d040c070095241060544002d6581e040703c1c00428064450780000424500c500600059051080e41c440e602885240e8260b8075603440303598000d40d09000300d000281030b0b224803015080c030909041c0020380c2103921509015000700c0d1128001148010f540314180d50081c0c0006c4c0c00740412406981440349804a00000f015041d0303004d0f01e64a2101426a00624041d901e06414925480400507910007003101801a081045030307140007900d07504460407a9009100c1c600c04503000360300106595101d11a04d07079400c01003040310f0b05e85100c1c900d04080071a8040d562405000c0150b117540c06140149504495541042d05140c5109000d03058158041d000b05460f207000d00210b41c0c0d01000b110710143d0146001501c983d42d4031000242c002c000c100c0c51002d00e9001034000b503000400d6021f0240e03000d00ea001d5882c4030303c0128100b070301c4240031118181e12021224001c80022504c44800390001c0d881d180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 388521708 1250 388520458 388520467
    0xe010c050f0624060f07081312030906020d09060f050906040807091b02010c02030a110f06180f0604230f03030403051e0a09050405181002070c08030a09060311 70
    0x8000d801c00d142560740724400001c090f0030b0905204954840c040c00d54094500398580402c024100600d402580001410780300300040e01410f108140d04040c0140c2040154180304540301d00d03010f0449a0684926800b41c080c500c071404e50140181040c904650703803901d54140c035006000003207883e40e1050030241d5224034248400b0a4100e020082c000c050031019000117880000c038640c0c4410b081000740b001301168140700010030079a0f8088240c5510a0700d07400c10191010324500e406081a90944094406120705420804684180d80009280d424000191101443d201c1c5140303440744002c5a0151602c0c010100f202081507402c034207118080d0607041560745046580d5a0281550700c240c90903400506e01255000d40080c4500c0404156200c03018850310f07094020001030110011403146d1407003659142c0004019640b0400c00e003458003040400d8640300326140846800030340004600b035400d449048404a5000400000c0b02d5180d440c58458020303043c50a84210081c02c203490300072984440920 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 388522958 1250 388521708 388521733
    0x1b04020f040305061b0f16020111030c0c040b1009051504051009180506220b0406031505100501050f1806070506250504030204020726130b0a0e010c05 66
    0x10700302540c418809005242481d00b00c507080641c0e0a040a9103080c003c1000c104802d021034125180000703811815a12500d1900043e1000c42c80d18045d490503010019441862640100c2d01907070b2420200d50800941c1c040701c091201a0301c00d80080e10201d280c040c07080c4030360301d444140d6030b84440c0040c43d0076181680b280301041c0042c0b18041c1c80d501280600d001030003c81c1c24500f05100c0d501184104014900e440d400040d07603481c44c00300d040c000c2c0c024489001c11459103038000034850036001d881403040c1d03a035915042c2c020064100f04107540a00e090003080300303d0107851405048500c140c0d00c60f8144001501c0c0504181d02461190a00300c2c28800309021036142c5001410049000314040c1000780f4084045031180115001c4000030130000d5404805403035000310584081c0d0303405840042c6c842403c0e141c82c0000120302c40c440c1401000d1f00301908400307840000140f4050542d0154046a42d958509000040c00b9018400c00420244211710b40d855100750000d551050141d401c545c01c2c00082c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 388524208 1250 388522958 388522987
    0x91509040b100512060402032523090111161a07020d0f05061003020603280e0319090303091502031603030c020c01020c090f070c05030408030405040c111b0402 70
    0x20b5410000c00d5020803c038544141c0d003060035a1059096905620310302d0b140e61880750b108842c403c4110f40b09014980c0000300c5202d204290305210351007501c11600c00a900ba8400141c01002d1400e00003861803c5030440120301140e03000e0035541e044824001c1c00e04007154075620b058007415906000506100150145c2e8440b8480324125000786c0c1c5820100f2818146103041400040103840c01c9440000b0420043e2500c100300d943c0010640c200400b0004c0030450303a0401400a00708040d01420001c400c9403030700e000b0004040c002415112018803240450741a00c00c21120b10014000c181c402d0010010300c805400c40c0d0710b482d002c0f071040e28640070103c140010401048081a40007d0b0394100917039206804201c0800310304024002031280345603100000b20460402400038440c1400000800c003603d00130342c0842061507201e0260303500c1d0340e1241080d507a41c3d0086d02c1460704c541d080003c807482031800340243c5402e00e262900a000b40707080101c0442c20103882803a05e40c2d080355080000318152684c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 388525458 1250 388524208 388524229
    0x30d02040b0417010c0903030e0a081b0102010c02071802130302031e07080309130c1b12020127030c0c091406030d0203030c0a0f0210050405010e01050c091509040b 72
    0x1007090544441c108a81c01001c82035a0104815507890020001c61060b08001c40c031044a5140c41c00400e8801e03031201040c0001520751001d1740b540b040c0c0c3c0d2007145801c13060300240010903081e402081500b016007400c0f642c4800d035128105c40c400303e214070b5800b07403102d0fa002007001403c0c1503d002181e65a035804240b405c1803200c0b1607140640842c111503418101403241c140240024801542402c40b0b4070002807a9529107010b1481d0190307503d4600d144607000d1035203803060802d104010091681503040540a040c00d4038414001940f0780348802c4102603944101040c499030a00b114120f107107503580c05407100c004040c001d40d14448400c0e800508040d4601501d40c461070f40c0307014290142452001c0c1440c082800c0352410943d0800d00810008a031182e05507403020141d4a014030191a00480c03d074181448071901c6900c02c1c1c10841040b0902505400040f6651050b1000f00007e940da4100403096000700d000656110110301c903010301e29448900036198500e4000c0c8001544461100012906034a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 388526708 1250 388525458 388525469
    0x3040e090102210115031a0303040e0703050907030314070302010605121b0d110607170a030209010216151808011802030d03020708030403050c010e0f1c0207030c050f03030d0204 78
    0x4000400350ba0101c9105940c3c083c4a022090b41c03406941040d40740301a644444c41880101075483c01102c641301c500b000100e4042c400682a41d5459448040300601ea20007212141d02090805020500880001900400f104e0701541e0b0340d1882e1002542004603548034113002d9046640710100401c01da42c602015101186880f001024142c078000c44500c0d0307013203848281d20300c103080d03101400b40800c04007544d622000300c040706e1095503042103151064440f4410703250100032901c04202c0203c21a0107600500b20030320f00b6000c5070004d441e10755607152440a20b000360b9080201400ea604203160040b0303100e0320004c3c0405540c99165450780c070618216046400b844542c1300c2000700b40c1040d030130240210351010090b441c0952601e4a180c0f1041464440913100904104000500f0031040100f076001d0300d8800f440201383c44401000902041d40c42040d200c80d11f0215a109202034051800007c400c0200c96000d6284540285000c04010440401d11640c5805000c1080004a2020306200070001b400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 388527958 1250 388526708 388526711
    0xc030e16081203090c060903190c0f24030e210a080603030703020a0314161401050c1206040b0607080301080114060f0906040c090f060302030f060a06080c03060303040e0901 76
    0x146014801ca14204180405072100c490030010300c45143d10118a92008107002d48890b90781c0c1417441e0100e460120700d0301c1041c00c0ca80710071920710100a10382c1418005c5034460012172902545995070403040320703005940001000e00e42148900c404d8000d03004403100785541e200b40c030b044004001713114162188401080700c0019000540614035a0400f1007560031070380030f40045042100030381e00a551141d003013101030240b0900c404050845061941102d020402d104014110b08030340c0d00e00f2401280c2008020706d881d50800d000222400000401da699603c0c01c2c0880c40c002c0c3e01c504044c400140301070180107800007000c0181c0e5002c550b114000794028510740000080300255003140000e107180160105100d40d03480d101500305542e03030410300c039040001218005000d444894054842d42020b41c0189044900d488001031a07030f4066010710300c01d1212a030110031981e1443c0410a9007103480c042c00000c6400400490030795285040070b150701550140440740391648a100c1040c200404aa461a15a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 388529208 1250 388527958 388528003
    0x10e220e070e0a0e010b060a0c080d06060203070605090d0516081b03030108010b01080609070f030902120a020a140303030f0c13030b04140109030503131109040f02090112020105070201030c030e 85
    0xd12103201d200c2102004100030402041c6d4040041c0741c5114100f410400c00071140ca4050902000c2c0c41140c00fa8070346007d040013443e0759010060746030b4025000c10b0b10414607010026544050109806a010341e80780d492074507046110742c07002028015000c0076610f0380790a000040701d10800e500d5265801ca2203a00641d184d41c5402c0046007928112a01c9504201d240010310400703403190800c198104426040c858400556020118000c200055019600804c1d51108000a40c00850298089402520041f035010b0311002c551f0818441d61407100c0c0c041c0d00410006808081c7c000745190800c0100c148140303480a4903d0035801489603401c2650108000000e0100f00200c0301101001ca44803580280044151500c001d0f00c1408000c1000542c5c0f121060208204200c00f003124074820742c0104024401d082c182056200078451500c103d002d12412300002c625a0022212042010f5050f56414508611130340110040c00c42c16800c81d040c5600d0b001d500440072000e1010940c034019010300e41c85603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 388530458 1250 388529208 388529221
    0xb0310021315200f03070b04021c08040915030215030408070605010306020d38130e1006060512040204110706291008060909030705070b0306030705010e220e070e 71
    0x168000b1141003c0c41e920107814005085004400d98030300b1504421b1640b003503a00c80c00490009004021204260408009500c1c04c000d0350801070400d407014a03000304400b08110025501401180c00040c0d80300f58800102030721140c0e4031000b954024490514141050a1030740c6480540388203810813200d80b41c001c00d0108000ba03207480b44c1105040500c0b10a104100d42a1202c0b00b031101c1c2c2c0d5111841310039001c051244070384540c425030301c024410742c00412041c1102c1c0c1c2c00c1c0d80c8504014403000226810201c00245e071611901c1a64480d1040c8030300c0142039122a4200310043c4a02005458aca00c0c00380040c00100c2c5983c89410104e900c04840058902030387d08507511240403010300310780f2070305a080c0b1014040340d0000d00395500c001d081d2117a0095848180215145002e0007070300600a1040c00720126451040102031030060b1001e90440307080e10745a01c015a4844240c080301600444582a20445446e1040307105281c50108640090203c403d49101820001c09820040e800710002052152 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 388531708 1250 388530458 388530497
    0x2030c040b181318020f0301020c030d0218031c030203130c0e040303060b0412020607020f04060609060e0a0b0f031005120d0e03010203090d18090515130b0310021315 73
    0x2040840807900700b1583c284c00301c0421440f600c528010380240100d00340c80406131400d60440e040c400c000e030101e0341c5540c0e5801801380654414803001020408540c081c004a04001408034040401e824914041c0c80e0349060440c000d400040410815080d406a0030000c00c9075070707072020003421101269140c2883c1904010b17007501e45a601c21110090f007000100985405041407120096040314100e0b030394015800040c9904044203a010360052a1400014109400c00b4240d02122615254580880104030030440340c01c0d094414182a07180401850f01081e5901c40115840308108400a02482c1c42e030001c81d10100308940c10300c80e540e00c503400c3c518109401c04260200f80b0802c0b0001c2d4614501003540310f4403110450002d505000d0506002e83c0ca06a0303804a40c0080d200d400420420b0340f601c1c0450b0701a61071600e44030303400782082159000c503801c15802126a80100a401805071041600800d0000d500ca40c2040f4000207603070b070000c2a040000301d0800c0801100e42e80d02801c0b158110040c20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 388532958 1250 388531708 388531729
    0xf09050d032606010f03020703091a070b0702010203040b0112081b01052e030210140d05010e09030c071710060b0903011515080c0702060304050a0c09090c0902030c040b18 75
    0x1101d0400400c03c0006a80e07002c03911910050302c6144c0541c49200710b18043c0da4201c03a0742c200301c10020b40a81081c0341442010041c0088a004081c80403007034903411000d03401c0b0303c010381d0007070300e1144600b006215021921600d200210f12414040340741010f140b18078024044a109a110140d44820901c07070449200c0095018449207410000c10301c1c804ac198005406072544002402005101d10494403d070090040c01c0d54109034010701075550b07107540b40800082009001c0c041d031180c00103010070301071403002041d203081904110060410b98141aa41406c440051000c11031318804e840c20072800d4110b80c0203001c000c200d0030041603100c41a042c100350039110030b00c50700343d01d40c0c00410040007050007241004618000d039081c003405030b40f134401821406128038100a500003100006000c01c00400155512005004080411805445a400b80151100e180300034080c0354410701c091026105580c02503401184d100021490700b696070310b00c11915041ba542d502d54107842035401d01c03607905110f20100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 388534208 1250 388532958 388533017
    0xe0705060c03030117030403050f01230105031f0e1b090c1e070c0f15030501090c140c07080708060f010602071a0a180909050c0904050d0f09050d03 65
    0x10307800c04448400160790382c0414400d032042a07000e004a88103500c81401141c020b15000401d956881200c810141d02030b100141c2041150490010341480f0200d502001034141e40000700980903198500c100d621402461030542856a56614090341069404004007041b00118052120000002008104038440014101d4084070001c2000e0300c40000407803401342c10030840c203c901e0307140e25490900f40e8040c20260001e80408010b200c003c5410340880c0102005c5103c16602070105070780700c50400c425690001c4400c5c003c909a481c0c440900e41401001d4070507840d9000031251003d42d00c0028619096003a4084417598200700d081c007084807003140c8050f02500581c0000d1a035149810901c6207607246058041003c410045152001c403442085070074002e0840e0400d51603000d032901003a0300203003240501240c151180f04030f50441814989645c41c421038100c4041c0c000c102d10030f403081d00c0343c0c2401c29202d0304014185001080e0780c0d6440c4500d80d4800d001e656041c44c0c2c00c1e11028080000f905070034a8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 388535458 1250 388534208 388534219
    0xc02010e090a0c0815060415021501030809030606010207080d0e01120c0804140c0d0206070305121504152105030f04080a060c020a0f200409050a030e012a020a0b0a030e0705 76
    0x34039210340346c1404880480d200440c4102090170b010f80220b0a00005841845600711034078000020302082001034039040c04102d003552b0847e1201d0b4016a596409413090308000d4100000003006c150155440f5020240107060465a03158401e07102c0e4101c800c03a00c1088045802c030428403040c0541030840b802c1605059006007030707511400000070209404044000d00c07684000400c4c00405100d60155150011404e511820500340308000c012804444100700303020b90b2a04000c030341010152051082202e014542d101c01c0c0041044680c05111100345060340c842c03108004000185210f10003c000408420300a00b042008038901134090380c815060600c1107601c41100a0007280d046452108020341c0541103459504d891a11401c0e0500301445155002d03203032035208828000081400341c4802d1081e900c010703504040600642c7c1c009404004e01e03002280d219810949940c0000009007041d000810489000b6656032150a40b54030100740480020b4840d116450b000d0302c2000700c0390103400100c41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 388536708 1250 388535458 388535491
    0x4020903010f052a092101020c0604120203040b160602040b0711090112120c030905041d100219030e01060e0c070210020f0a02090a09050609030705120f0a0c02010e090a0c08 76
    0x4000a0182100d454400c000361070140346c041c1c030a584400301c01da2002d0002d5485035000401c481e00c4240c225416100202c030040c8902500780302108960aa804080341141032100c11040404e0040c1900d01c00c4071581c0d0300700300108054407640301920700c2e90b108248800114124500344000c202040e80090610701e50400840d0018603070502608540300f00307190200c4003002a04080324503090b40d81c40b40790054544000301014011104900c2d0600500c001201d03802600002c040c4200e1040e800280c0300c8001e040300f007400c1d9500c00d4110341010703401c1030008100349440342d0581051100980e450081030b00d000611000718200021401800e602500203070805c11048580315444d107100c05402440380c0c076010300117080300b004da0380450049504441250110310303023160015035944c09064181ca80380b04030381101c02140c101c08121200d07003e450107000e050060001e4203940110041c40100e0502c0184450800941ca030740005034070801034a08040380007100f40002600700c40020703080036a82c000004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 388537958 1250 388536708 388536781
    0xd050a2604180b0a03060f0c0305060a031101050307021216140105070203030109090c080d02030309061005010905220c0905041a18220b06011b0c031104020903010f05 73
    0x2c42040b0205001c540411620703280c000148000443d80c000408861500f916868440781980c00320138501901d4804000a8840300c040010310f14152000070168075011000238040c0d40300f00d02458000b00c0b1401180c1d80400c40c201300c000550480d1286001c2041441c0c084014400c15520040e203155516000b0000c41c24001d0b0300a442e44014000d40e03e40342c4e100c0c0034030703002c000c03582d0240001001000d0075650789502e1410000d407254410740700a0060710030800441c100205d0100410111901611840101c600e000c0600655244d4203080500000034012805c1a104072070064000c003521a540e00d5000e6420141080201d4070900040d0311525000110312071a0344450803c91489801490ba8500c1a40ca0401100c03149038540341c0b041c50340c08500d40003410480314652860158600343c0316000030b0034000552078a08241d807003016150001508040000c2403d0301c40d40b088020740503001519140d00395000c40d080da9101921010400e07550400c111144090412a80102840b01c602c48012004117 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 388539208 1250 388537958 388537979
    0xf06090312050f0f06030c0306090c0108010806070c110a0509130b010828020402041a030a0605010c02010c032d020601030b090a03050f0d090204090f170c15060d050a2604 75
    0x1424480801380f80400310b55995000c120740c0d00c085600808650140c641440125200c038443c40140e80411011340c00414003050104560340700307984179501c0c0d80c42d4014a8880f04e40d07844212613070b1354224014800209840d00d03011011445002d864410701000301f028505203100540507031190b1500e0f00040c501100c5018040700c01c443d6000941c1c0003070903d401c01e00001e0028400c540c080c1020207540d501c615001000400550b03c04e400891007044125550b000560301d003207180100a00265070750b00350b040020b00415074030b8907120396012a08910301500c0c0505008080ca081000003507481603004004001445510325403007508540505402541c594001d003080c000c16030004c140c0400410790049000c85980458500d0b078005100740f100d01c115007000ca0320781c051050145c5545150f05001550250030008036429090300c18001e0050100106c085080c111004c0c3c07400f41c0c001c0710402d80c5c0c00032610400c072105849004d1100006545041c05045c00342c504140b0340307148500401d101c10031040176003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 388540458 1250 388539208 388539211
    0x30105010221041d0103030f03090201080a091412070c050a05100c031209111e011416120f0216120b090a120801060e0909030a03180f06090312050f 65
    0xd2100c104852001800d6030380500503a000000c240495441000d402a00c450b031340344c100c0340a505c4500060703c0e590710440503601000000b80c0403c036210041401b4103180c0c2d00003c1003600800390036054081c0714801904081400414140156010400a080c03080c211100c400601040782c1038035460f482c0c10003240102503450881001c0c03140e8000450185801030030303806020a0350810400209000e880c0c0036002d0b884e08464103000d074105a8140301040c08018401c4100300c016120b00d046882240500c5000c0c6d0f010012a0002c2004449070400284407002ca00c5011140d0f80ca81002003a0041c400030b1500b8520031000c0c0e0b16812001081194031007540b90a10419003001080c83c2c1a0340360610545090415070004062034010441c104240d98450700d0f10f0b060300c10598a00c5415949441002403101c415901401950000c1040000c01c41c0654000904000d4100322904800030039141d006010030342042c1a540603440f00561300c10151b12169003180304105480c100582d0030604424481c0790340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 388541708 1250 388540458 388540483
    0x90506060f01120612060f0b01021b0301180b0a0b180412170403030603051009021c0219030c0905130f0609020102070b040303050909070c0203030708070c0504021803060703020301050102 82
    0x38904154082c0e4841c40c01c00c00003600c5500c050201e6035680000355007011541009481051a10000b410102c2c0280500007078090160b00a04910700f0518080588118120f5603950540d03070703030110700c29050703480807103400c0c1c140035520f0002c09203080130880050f508900a11440f40343e0071b0221864002082881e690080e402c002d40903201c0001d02c1e0700f5142d10030000d180d903c42400c048200000c055254102c1c02c00d9038403400c1a40c00100c0344081c8042030341c040d5903009500c165044a024480308950014040301c50009204406c41c40c0103408007051210340e60019190320180d2142442071921a001302c43d00202d28921faa01c0c0401075480d2041c80644000340189026103c54802055a108101a4000d000c140b0080747e680d80d528a0701038240d40c02a1400c5014106150010307032600e014403510700510790040c002c1c5240c10302030343c0c07524000d9100b0001210410300d070b01c6010413681c84510107000c0e03d55801c00303100000c0b4000020107241a8004090208050040006201e1030340d001c10120f4130382c1c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 388542958 1250 388541708 388541719
    0xf0a2912120d02070614041b0504051605030a15031505090307021503061302031311060910081b040b0c15060f040c020309040c03050601090b04060e0609030f010c05030a0f09050606 79
    0x4403145480c0021303014065503c0304001e8240d0500c0103000c08c2c180112201002e000702404150f513590103000988030304417202c0c039800d9032004444c440207001c2c000660344034400f2040090030340d108a0500c41d41c2c0c111038105907040c010100c00401d40510501c60142c021107041c006500342407241e40000c02001003584841c40045020010441a454500500d519061440019502ca243c05c5241841d010030210080d00c03490041d60080380c80b418a041210030040000d003540d441500b01c00320580e0110005400c40301050140014045c00361800d0002c3c0c0003409101246035a00c5a80c0b068851a01180d510a451130708000300920155540d24680b04400b81c00a0382e0100303940a4200040c1e045000313002c000b9400c1070038004d1303100790680c1c150f000d0b510420007600c4410009803142d90040d044d0256014510103d20071400d1500c05190240152440d6000141124a4010502c6889003990007100075000400e402005014902c3c210b806090541071601404010044180c2c803855034525010f402c041c001d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 388544208 1250 388542958 388542967
    0x306070e01031824062d0e07031e020c0d1d060c0c0a080d02031222050d030b06120406020d150f1e0e0f0a2912120d02 52
    0x103034000d402c481060b20410f16030b54a054034604100300f100002c401c0b109540c03902002404086480c0e0700c100d4043d0b03100d0140500300003018550b004400902d800341450b0401030030000203040b61080070568490b80c0320303940200d540c0c030b00c81c020041c010301800c580b01c801a005116480e41c1c0000000c030715201d0219803030072048100001001071018510b0003071030b070780140c00041c440740b244400140c4150540c1c0c080d164140841d42e039080540d144c0d440c0201510058100b000580140b43d030490003140c000000190203100411510718840c0d4030b00081204489075000028010401074040c440c01400030b03406d45c5e0076460180b02c51100c02c800c0b94001c00091265902044540a0070b8003944400340089814020191481d01e4000d44500d0806038462100034441661f03403217900d05030707000345c91049904d070004104c46a01d03100c1c54030111803801000740c0d01190341e44140c00c42d000d1101400c1d851310843c000902101c00251000c1c040c4402031140e070344506903c580c118850070444d00c0100e41c0440580d500041e2603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 388545458 1250 388544208 388544237
    0x40b0f150604081b0a030b0f0c0918060117070f03050c07020a0b03010807090b060f0a020f0105011203020712030f050a090f030b1e01060915090503070e01050a080309030607 76
    0x11041481000c0d50070280c04100840d0405000542441c19480280c0c22441c4a15010030405444003078040104040c0400c1d0216480a5105c0900b80d00983c0700c4d8481e504003501a80406d170303803142020702c0c082c2203103401c01440842d5810a003138041c0d082d034000c0c03070a4040c0303030490703000e0034840d46910401e04150740d4000007480d81c5440300c140c3d0300880d40100700400844c1e9513008914a0b4000380640c9115000c3c10800180140043c800c2610060024102e1030904428607018841034100028500950150340c0c04071200140078401e15000c0d04000e180b10080070090308009103003204542041c40c0c1002c0680305840460307000004a805011035281596a400e401c000c1184d02ea0f5090348000706040c850320300032041211420340c0c40e1050001c002246003400c1c80d1400307130751204070038468240401c000720000d01400545d07482c00203001109040589081e507a403800300c1e203400c040e40c0c0700e9a01541d03903c0c0107000714076044412100030420003000f1800c0030040310000761143c0d00035000c3e4050008064403101c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 388546708 1250 388545458 388545481
    0x6020d110a0203030c0f120405030d030209010c06050a1a0103021309090201110709050f060102150a0b01091e06030c050a0e10170703051f180506040908030106020a06050609040b0f 79
    0x10810b40c041c1c25207454001403840d440c2d540800d0300e2100200c1c00b5003101c1a480300080700c1628100e03440103000709030740d00c1e0b40f030000c0e002980103a0031103042100b5100c40318081a514000c03540104041640001c6605040044103003548a040d50541050b00401c444007000215010030300c2503901580300000c09842034401030351410440b00440d0b140d401189800949103580382d000e07512584142070401e00c19030b41c60004a07191840c1e80d009a1074040c0c0600422684099a8428090000181886003445032541d40f244082c1600300c5850340c4100310340005000c499818003a840e4038040b1824101e0404110300070251444980500e5903001d80c4403403e229406902c41c40356002c4001080e000642a400c103548000d0181c0411503040413510f04001e941d45014100f49040411200c0310303001c8804002c82188180007800b07024040da5401a165181913000c224920001d60084c0140c0c0c00a040d00155171805d00d05894004144c06e00c210a01801c110106119011041e440744c051042d03004607644030741c035594 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 388547958 1250 388546708 388546723
    0x40209150d03050909070c03170603101e0605010503010b12041b060e18070f030908040f0f06110105041505090708010e0d09140d020d0f021504180606020d11 69
    0x9512901507458001416000802048810703015540307481250742c0d011094035074641200c801030000e42103581e07001c0e00d0f074a00c40015800800c001e00b55106011280500420780b140c940c0c1c2c0e42c0002040300201400305801e80301c0d14004007000c2c00c2c454115071400c031040000e800b850651090300a010b00c0041c0070030614100c0101e9800c07203110184910ba45854004005240301840a80582038402c40084002c0d44404094443d00c181e9650610140c41880f04a0183c040a04110703a201c000b4000403441c2d48a00e62140060b010113400322a44500d8088000c00e8060314020b4a480fa92400d424040420041c01d0116250340e1041c00c0401c854a940014602c3c259184e0310250f0f00c0d51a24203040030300d01d004200880c2c4075250341c0e65081c0e010b0b19007070440880d803130f00e50f442680030401e141c210006003010381c40c100015010b900c00c0e41d000c9855030046072132000c07107041000070003000040c20b00000c0040a01900f0000700d01e40100700030303800c101c3e0181d51080d00981c240284810300c010b86080000411200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 388549208 1250 388547958 388548001
    0xd02100c060b0d0605060102150f0711030c010e0303091002120c280207140906030601050910031202030301030c09021602011b0503220503150a0f02090d050a02090106031103040209 79
    0x2401c0d00c880c2402c05500800c030036941b41303006014004d01628032003030708000c440c080c03260302c004007040d500c484409a0348490f0324024840b8a000c20b201c9821440d0080c4102170500503d078015559a160000555081c1800100718000d8648144112080f00f01c0749214950302c4100c0e011010b54502c810729900e0f400e288142c003201c0001c003007c001000140e40c080790341400c07180003c105421104004c8104010700c03004480268069015000401c194130301132100ca034000c190000c0c035070109500c903212500c140301224507100c090b07800000104100012030005000401c086101181801801c841020300321200a1002c4e04008000c070b41c1c020304080000c00c07040301552000840799504150001280903806110700c1c0b044444c1e04400010b024200030400d01c0c02580108145100d41e91040c5210004107080307840151880da0034481c02ea42a00c40c03010700e00d144e40c041c1d03000780040d660900c1000700144058103c141054103080c0c2c40a50040804142c03a0800c1c3d04582016441d42e41402c01381c50420418000b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 388550458 1250 388549208 388549219
    0x70c150e041803080c2d070506090a0c0501050c03090f060d02040f030215040e010918352d0d110403050d080c0702040b04061806140d02100c060b 64
    0x80001c9503002001c42180c2c1486034590059580e1040002c1c1001d0043d00b0140c440c01c9080708852401541503181440c80c0c0305051280317800c151850300d5a0b443d2580880e09001141d10900500c0140b01c078060605009103000d18103c5d12b0040c83c41c29154480c06100007040c001d03043d030807000649a540c00107440d40d01450030070854070745903900b0b039202d6000d0980c4402d0740222402d100ca00302e0151068222000e9402d03a4408004036440c00c203024009080112030034005440d203294840005115861900a0302e00c1010744480890020355030072142c40700320594004a2208000403014840d0852054034100011801c68960080c400000d218611031340c1402942c2511b480d02a81e00040910094001d0301d0040b82114424a40d420054850b075800760b0f044030203050140a1100140b500d40c1080740781040c0503001017402c03070751054003480e50200d51201e6500e8540742c100034480e507100340b9590420740310110341c3c0f0007a01004e500070880310351004181004101d080950a014484103400c00d01c0300d102c02418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 388551708 1250 388550458 388550471
    0x1203030702010f0b040c08060d1109010605030a1401060801050d1704080d09090203060f1c050609030a12061809170403030c061b1d220203100506070c150e04 69
    0x4028028600d403031606410310320780810307184181170520540840d440d454442d00910f80b6444100180d54545800849440c0005036500110351035480c80c43e070003045651107854480c10070340c45440c1520100c00d4040800ba65880040205590108120341102e034156950454200181403c0342d103128420b800b50394403a00044c00003240032000031030401d118490303621074525030f0b150707964a0f050780b105071100c5070f001030801c0d084060303460035002880a135048840f07100803407441135850328180700d800c075040c030040d410208028440a030022046810201c82d880100165402d0081c0b62540848000c076080d203240d540c0000780c040100907040300301c05000c030458250b181c5503207180040c05640c204c48120380807824260884001c109640c4003044101d12626140003058800321030300400c400700c000056002c1070302900303001c4184075903035100d102a0141c1e00259491411640e48031340f074071680e404980a41c40c201f2401d408981c0024144c002c3d01e4820542c840030040011049035490203007001b4550180c607210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 388552958 1250 388551708 388551721
    0x10e06040e100510080601300501030b0901150e0c091504030302150702190c05041103010311030d12050a1d0d0201050703021309020d060e1f051504060806120303 71
    0x201c07000c2c45860015031800d2a5a183c0301400003600e0540040b5010505c40c4e0041803056002e9408000b04410780c1001540c01c0b0130b5440f07800028010308282140f2244d80354018070600800c1d000d480d5024a40c0c1d070003401f0200c0c003400115500041031203010710351142c001c0410380305c0c0d401800703d40031003030004d01d40200000240c84034015a0301c244001c6002d0700c5181d0581e820001d0380c1e00918450b540030740103400050742e400c0e4514103c00c2004001c41d201c210054010900c0d41e40c0d03100c3e8542041c22403421503160740c114644810003c83c1c040041c0e01c6544030f0810050340f1507100c0542c070001c8003400704c0803030707039484160100c80500014244c01e4104c0440e03e030780d810340760300016100c0407690b12a4002e00298030380690980803840340000041303961542030340500000c00c081c2c000300240f003c4031100199a598034459540c030190159040f0070444034000c1141c0b0355440b0826001c003c0c0900301c0f2072003c0d498010a5220007407007a40f0a110a101d42540056903690b10180000e4441070248140d82d500e00d40030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 388554208 1250 388552958 388552979
    0xd060905041a130b040807050f0f100e03030c0304032a11131527020301170d09060c062a020d0f0206060307060311040306060f140d0c14010e0604 64
    0x20040b250300c02d42d0100c002000541240008a081604045100c1d82500e0f281c8405900c3c0d80005829a080e1094041d1403c802d1401c0216010010414001e8401200100c5005080d10f0180d0380b0513820364424018068074805041c12203410a6050500302260b00c0d0325810110f00c25880001c60180b00c011005020034003850138804e074030580048684440f00c90100d2142c80c200c0e002d841484c04081000d45042c481409100b54001c002e081105501d101744120120f6a400c1e40c0c400d1704101c070b000c1006034810000100403c8003811000d101e0800d031091608280000780300c1319480034050a03082d150035280e51003000313030004250840421b10700361032080344040000e03550b808211030f03400000303142d0301d10b5803903851000c180c0e540201802000346c4003a62070640c00300d003d00038403402e01084003400c0000000045191060302e00802401c1204440c441c0703000040041402c0c5503e00301e004600044000001511802641c8161030204042142d4070002c10b004845102a001c034140e000040054049941c8129 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 388555458 1250 388554208 388554233
    0x30305040e061f030f020702090103110a06111015050402030f0916080a0b071404080105100f060e090a110f13080307050715050d051510140901050d06090504 69
    0x11114881154640d82c09002d05940100190301880300d07081400c40b0501c1c8a500120003400c0400e42c003508212003500010280d9000b13910885142010440c07845a508080380d031403000300958101180303811074540e800350312003800c000b901c0d240c941d4800d01004070000c500c035101d01400b8080c000b103449103018051b0200c2c0450540301d032706181c4102e001404132524060324020603142004090220729005945410700c1090203817105080c03000500e503203000352580601030401083d20b40700106042c02c03c1440c0007280500307a0004603096060307000600059421103405080c2e00c805441c0d4103000e41d641d07182100142411b203520541c400002500102c21018103010300190701c022000c3d016a213580d4070a45550303105401000301203030000b0b50704001a444010b0b22081144e4241130a40ca4a00c10300c41490440d00210749080d2020010029201d05061480c4010030042d410f0501000300103450303041c4501c5000d0320706110304105001411020303000329904410700400710440140107a003043d00e009115000e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 388556708 1250 388555458 388555469
    0xa030203060f060c0703080904061203170f010e06061b160f2310020c2106090d05030a0c020a0c030c0305190c05090405031201140a05030109080301090b15030103030504 74
    0x48803412600340e152180407a40b13448118001440420701d1035071407111035000f1501a541c071947c0c030790000445c80d40b140b040c0b022081c880e946035030b60301d480c02820758420750028002202c80200c1000510512500c00c12a58001720201c503140d4071925403404804101c110f0b03941d4480035009001c000711244050b0b4089509039444181030300342c855141c002c0d0000034000c12a481c5050010010072011500b801148881040050b1050315007900e903090100e4540d1007041d0718140f13100004904034401c00380c2800083e800200c5c01015101c0c60010f0030380144203000c0036000030041e940d19100c0b441c599000b08071024039542d101e84002c1007580d0742d051030240c4281c14030040d54a0300405581c052f010100092440c0c200394041407101c040d50400080c462401001802102c0503c010014001c403d048940101e0082c480c580c0c03120205540102072240302d80e403543c801d6000b0ba04050101c800100d10350290b078103555001d900012203030311000c00a40f414002d12090701d00054000004801d169101005006440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 388557958 1250 388556708 388556719
    0xf0c100c02030408150c09061e161211060601050a0c0c0f0321050403121b0c050102070b12040b0408040302090a06150e090f18030a0309060b100807050702150a03020306 74
    0xc5e16407400d0541c104100e492441503c001c1004078140d01c5c101703020b08074884580741c2c0d425040e4085c08850341c16038010070355190443c0394080350a040000c8000503d0220849160034940354412000065a401d00500718605203e00894208000740c1f2480070240d0307a80e04004505d643e40e9032264282c0304061070b404140c035401c00303414030281c441d80b0030100001c8404165903010319052650b100c060424920050000800444192103a01d8109e038400011507240140400a0140e103040006803070851039500c100394512040c404641a9103014460b01e6000e50006000c10141e5074034680190b8910036a000294002241c10505c00700d183d042e0f11070403d41b000c0f400c0708055049646401d035901c0442c0401c060344498550001000391011a800c81e0300447c0c10781c14015000c110080241c00d50700a0504400001c1d40c0f24040c40c140b0205004000c0c60303c100360b079411a40313002110001c000e40b20061641c0305014000a041045440d00b0b15514880c10826180d5a00c8191561004029610035030341d062060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 388559208 1250 388557958 388557973
    0x130303030516180303030c181401110d05071410090b09011104270605100302121305280c0e041505070801090b06070203010e071e0b0f0c100c02030408 66
    0x1d010703140f55402c1003500111045494595a0110080d1506d0140a010024403049800082200140000140103081e4910344000030701400181040d6010180c20825440018000001a001411541035a42210150181c212044081032501c001040c1001c507040c81c154404060001010000d800b03030103031200034405542c0b58400c15529000358062108050b51044449400e02e080143d070143c044810f040229030242c2d15000151800903100c5642e001c01d40002e40c0c580c00180c8042000c0d03014000e9100700080703000c2521515a1440031444003004803040c85981c4904503089040c90f00c04c59840311200c20704031b4480c00d100c00000ea06132422592120101a50345452038140100b500c110400c0e6582441a0b181412000180140e43c2e2600e8003c00200031030009614203004003188410801e004008541c03520b600c2e4000c120301c8121445880e901d48905009100801040700c000d44c00c040001c070380f11080c50700004c0c01c2c4500c881ca42c0648525007502038000c40e4000c000b40040750700040c00e55001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 388560458 1250 388559208 388559251
    0x60c160813060818030702151813020c010b04020c100c1209050309010801060206160806120304090518070e01050f0406080d0f140a0801030f080c06010605033304050a021303030305 79
    0xa034006d52400a40c415404200720f010044050094888902084502040107440c080443c8100341840c0864862a400140b10074604a00740240e416154050342c0451414910111507070329029009207030f4100784d440d083c441072554030403264526a00d0501d0030420240c24a4a0455544c1e80000d880c04d012a0304900001251800410780368400d1044440341e036371200b2007400446480000800c0d480e442a044400c4030740c8120100b0181c809003a510f940082d15060401c50304044241030b00044d04180c1c06500305100c1080034401e00c0e4110340c0151154402c01c2540e41c002405808560442e2500d4400c100140441d540c0c13095101c0d10130800d50b10750200680c0542a184807901c40d2958010219440100410024400c040700100c0e8500458019080021035020a0f0402000783c0c0600001207001c800c1c00001c034102c1e82c000e446a4108048031283c40304600c1d00d00f1244680c1d070040f0703128641e5140000c0340418150102d42e106104000102c5d4074548074a00a4001c100548081c5900309507080b6900c1c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 388561708 1250 388560458 388560463
    0x8060c0702011b0b16050d0908030a0e070302030312070c14030d05010905011202060912061807080607090905070c052e020304050303011a040e040c0501030e060c160813060818 77
    0x200f240c0161000126a9171174481010f0f50140081c5002041410410318481e074089204000000b80704941160b524280321007903805642c8580b192108980191001300700590300081206d04003501410b001d90186e0f50540203a81c0b0b540102805001011400b01082180e1800b000401c0d07203205100080103680d880b564002c0458500b4007404035050302441905000d031800390040d0803010401400070311551202c8480608000060307480005c0c40035000e610544211040c402c840c0076100e50b1006200751314100400034010b60706407140360341540c1d031000400c425611030464850a250845c0c101d0300b0080aa90b40808500c25032050f402c03203c03000d50700c0900b1501c01ca00899000c1c07074200d070045042da424500c08001c007017440103c40915410420001801c400c048001c0380c800c038001e0101145503840c100000d021340312985211400c98104404000c040c02d201d0042e66107240112441d5842c4070390034580520b0f14400e4024094141c040300c0000522964094180707446150103001c0843d0842210034030070b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 388562958 1250 388561708 388561757
    0x50f06100312021b060f09040e03040602061303051207110a11120c0d030e12010504030c02100c05060711030d140108071e05010c0f081b07050a0503030708070c08060c070201 76
    0x5070855408134007448034904140a810400703025014030385041d210310002000c82d901620900c80c0c50b00301180801100fa01840040d520508040c0e04001d1011590340060481c0324441030108109901d0b070114100e0361040fa80b0305400c0d2200742c12100441c00318100030034120703200d9099170700c5180100c601c0341140380049030b505c00f41880136007003012049242d1b6060300d0200584407010707000300c1084542600d01909000d120700540c007a8444c0c1c0d16115290042c01541003204407c241030080380050b000c000761002a00c0b90f4041d5151401c207448440c0d061400d030940c4101a000c0f15500c0c2400406040310841d103201c6412039404c0300031075400e1950303000b04814259850303800c08040541c0d68810401c42d405101081c4400e480341c0708501c038803d05595400044d0300030f449411104211010042c1d1106020400e03d3b01030142111074131445441d08001a07036030321423908000d0801c200814608200104849420301400021003507511701e240c8845200790541003d44181d000404d00f40c1e487d48001d441c030007100d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 388564208 1250 388562958 388562983
    0x31608060c0c0c0310090b1b0307030f020c030706050612010626031c09020a080309030a020d0f020a0605130b04060e010302181908060c030f04020904050f0610031202 73
    0x20300c2266961540600a5004503561400900451800501c240c4e003d02031502440c2c64200001200111400c0c01200707800c004040d4106000d01d018801c0ca210303140415668002414603011403a44000ea203610080d001c0c600d40c03158680301c080740c00c100304407540e00014410101500c40905081311000308500780c0e103a501ca04036440111003070144840c900c050080c681816070b481200e140c0034480b115a804031320103101100c0710503922140c4030704602d0821202001401798500842c00d0075440c1c0c0c0001e8403040c080c1e0000f880350344d985100e0010030050103044454560001c00c20710200d81c1d00c03030025005034082d840c80f40309120029801709152500f00c1c10364017514420354955428007075540041d802940304041a000c181c20031480c2c2c490310395a210072007580120958102941614106070240b800760090401042001d0520030440e0289c42e502034103070f029804030780c51021615181032050401c01000240d44060080b401007000c0300c00111507600407284602000414505610301c22a100c14494100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 388565458 1250 388564208 388564213
    0xc210a08241005070f08030115020c01080129030c091009030b131401051611030702060d02070c0911070309050d0b0402040c0504050607060603030f0801030f0b070306090e0c031608 79
    0x80501e04100b040742c82511402d003000391806500d0340381c00d0090a0b01003c11a0403000000c0140b0001c640030101c000300e8607190004040711031483c800a40a9a81401980c0d06140c901038000ca260341c19514015000e02c5010720540e80e0306020003020344990100c04c080f80260141342146504a10a000a4084a8001c076000509856120b045500099184415550305420180c0c0c5000c003c7c080c0f04d800e0141c000c0046008084070101d80182440d11000e0200929810502135a005070711200d040701c440d000400300040e0340f9041450312010113841a0010f940c010b01c0e107075040b1102c860020041801c9400394442c400f201d5950010020459502a00180440d4080c40441d006040c180c21213104000300e07040c040d0401d9111404034299400000c01516800e0f00c8110400034507403c1000094294810318240e4002c3d81103485480307082d050743e03800402c80c814450002d41c03001e20940c4080c0180007641014808503903c030345140c0d40d0702810315015220703000d5010443d41074900300c3c50610807141c00700701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 388566708 1250 388565458 388565521
    0x327120f0705101406011d0402030901060e010e060118060c0201030e030d11040e091513080409050c09030709200309070b070302100501090605060f0c210a08 69
    0x9464506400401010845403014441880003520601040c442c40c01900c0000031420403074882601010000340406040c084031070a41a1844d0380e8202c140400e00c01560050b80c0c17a2030342004e6600601d1075030b22180a0000c42c900104038461842100350107904242e803481110411349034069801402d6125504c0407541003088100107500940082245005c0c1c9402e803414501d24900c4081581d51000c0c0361017503500002010b00a2142000c0482d800080700ea00030054500041411034400d28098241407580d50000303103080400c45204101d40c05840410350600c21f80c2025800d448941d040090454800e00a500010031840650310070560f003414a80305207044c50704440c140070901d1380701902d061054050b026010a8244004000b011140e22940c020b007450740c665440802140c2040c0c0100c080681820020001540c81c5000d5038100010900150365031180d1041492a24001c409108401c01d426121021b4203d480000f41c003c00442d61203052107540c41c00c0014a51204513003038030444811256 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 388567958 1250 388566708 388566733
    0x1e010209130b0d0c0b070515010608010315060f090c120c02061302030102070606060503071706010203040e0c1612030c0804260f0c062202010c120909110327 69
    0x2000745220200c060b1050780f00b0150703521018090540758009038203004001841c0303400c0080c208200c01c0c0e10903201e8140202541841c40040510b14103100c050f000040c00e03814a8440307061a40704030b00600074243d549100680e20742090740a822031546140c00704030000c510a01c0095540034024020410b0f80c007809059a07003141c0102d0708902c400c81a60190750a000b03120004400d0311402c0007400307060712819140c0c27520030001080c1005000d4110705002c00c60003402402d07600042075070240c2d004040c0d0306110b0342e20680004100d01030918600e10445081500c1014044040c1075a80440c01541e414480400e20610680e80c103031043e60002d0072081c070243c036946100030f0005e0103600c42e4010480c1a2034180c845110301001d4226240c1080c0980101040c49440c50f40252042101890091400500c0050f50006440045c81d440042c21a420700411030f4070740d80c41030311030034007030071903800104010b0ba101c4028015079081121900c42c0d505101100c2d442c8506100c1e00200c047d0320100061404100c0d02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 388569208 1250 388567958 388567961
    0x1205070b0307090b0409050f0115140304020f04180302010e01110f0d180b010f05010e130506220203040c0909260714030a02010b01110c2707021e01020913 68
    0x1402c070001c0045128001c01c6100d06840140300402032804040389604200e0707070314005140d060340a22551424a140000d2040d040180034502c0c00206a000740c4a42c0c840c00810100311101c5801980300c5e282881c1341508914003034424401c50301960082103080341101d104c0b07080700d00c2c548031800300d401c050201c02c083d407500c0c20050000090301c0340042895621030f416040203820f048822240c4080c4107006020003003065844400421091810701014a01d03000410020310a82082000d03031901c803c0054001e4a03140304d0741c0c00d1a0018618200c0e41500940050002e400c152021901002100c0300004c400e1450300600a21680102c00400364410308400512007107100000860006410700903803000c03444c42e0318207c0425800340f000d140daa1800d03400080c02c56038040152070510088024601052030001888003002105440b44854800340da000c5004a50031205080d8030602d101c4100041d03da030124920b011001950383d8a102c20a48030b000c2404d0717014080d00190410203002e0701c481480c00c0c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 388570458 1250 388569208 388569211
    0x3070c080d060902040e07031b0504140a0510111e120c01060f15022a04021c0c0201060302090714030a0c0302190503060f09040f080c0f0304140a1205070b03 69
    0x8900000e050f540d030300b011001c0c0d8206500c01c06001002000b0040318a4050240507a1010440ca2501c5001030711280541140500d000d880807000700d01590901a465590380c0300050074009004e018070000c8094024100c0e01c54001000c514050110141030078000c548605191180800241c40b0744c1ca402c122000150300008910042ca6417a002e00007500c0c0300c02c441d001c020b45012102c003000102c10f42d40c0686401c42046680c2c80d08810000d1455401c2802c86281ca20000c08a501594078501e22145404400c004551091003510380382400010903015405a800c0b24800d0750f45181c00c1ea140242074a030259800244000b042040001420031113140d03008080c44c1140d4200141401e07007010256001072525000c030b001184001040c0000c0f03140000302c8000c00d44040390f4400c1075290030b683e010010f11444030b0052040384089001d02180f1001d020035220382c2840d074203c03611181d0303c040501c0032414a410036801550890400f00e2510280311680c003040350450002c200582c546002c000003070740f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 388571708 1250 388570458 388570477
    0xb0703140d0509151f140102120f0706060806310b0403080414010b0a05040509070b13050a091116020f0d0c052106041e1e0b09010203070c08 62
    0x208000c0352031000820b202d500d000e100380b20700030041c00282036840c0c504040041e1040c1820309800e0304042c51801c2100b600c200f544c0d05207406840e0a0700300c200613850a90310441ea4624460007107924043c0d66444405840540d010b084d0900845a448085586442d42540d420840c0d4030036a4111030800801c050700f00d80c22104034400a0f0305c140c9910f5a01c4e4010083d02d04400182220082c4018003a0303071540040d001d001400204090b0307201100107090300703519201e8140900d49a03000250124803d000300d00040c10002e079050b84d10b0311040c0c1707550004909409214400c2c0c2d0340318004078004280b4400c0f00946e5041c2c061051416600d0b074400741e407092071001c040340d10400510381c80016032076111108044910031038140d9003940c104810400303000800c21f19459506245094940070135000100141c020341c0003180604a95225035070f0b40142d03107500e14003512140e6030581e40207000742c8681c100302e8810700a01803810141c5900a109090303100540b01d55001514002d51100821156402001c0d00b15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 388572958 1250 388571708 388571747
    0x50a1b0b09030901200703021905060301060f0201110901080a051b0d090c08150c030c0c01022106180601050c161d0f040308011205150906100503070b0703 68
    0x25420303956141a180112440c008580020450004a50308460701c2c0013991904940c00c8802c406078002c01c0e550ba0101c1c40042d00c80c0c20410301c24a0604800603c4002401003e85030313541d070790784840b000b0700070f0b020701c2c8800d0703005618041d52016000b0031201550440d92059590520b00e41b90030b6080704c090b200217005029604440380b1180302903640c420051565600c030030404501d8540320f00301112184903d5120003016007001c4078130342e80d0a000003000b540c402034040c69151030b0741b5500809482401b5410580106600c0090030214851050308080741002040070800c22580c0e805c001e2140c0701782c071166000c000981c40008a0003640c042c001070040001504121011060b20100400080720079500841c0650803e00c0038213591400c07610714942c4030548811000c401c1c10141c1e00100030200502c90309050a11104000042002c00e20060081c0d001070780e41e50105041c0411015115201a9901c1061540c82c00c070010385ca00713000c2145022100b501c2a11b40c00c000440d00c0c140d031624080c64002c1e4048 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 388574208 1250 388572958 388573007
    0x1203012403020d091b08070308070807030207030507090504060b0613050618040f0605091b1e07061401080c03010c02300c0d0e0d050c1002011e0902040c0f050a 70
    0x10083d481001c910341e000b28003a0f02c21700e68038405001c180701d076500024000e4116960a00c041203034182207641a5134001242a500c801d6410100e080401c9031b04010902c1c060544009001281a00140d000d640128400c0204640d90303020003034203205441080c00005c11001c82004a484c0020152910680810429112022900000c5c084034005500090700d5684d82209211500703100c4022030380450603d0b51480d034908040080039450280700c090035205c041411800740e81d03d0000341a1180c1a40c00301060148817500310011611900034041c0b60028410310302480040c0c03505004581d042a8150003070b0032480c40441c1e64a1246801c000c82c010b9034540a1003000d280c102c0c0f070004042c0d46401300003a00342005c40c203400400c1d60481c11400da2041d90a000580041072010488808607035044400c00000c1e429900141c1c00750855002c2048108420b10201d4103041d41c64012142144c400c440070007003021105003e0341c101c1d09240e030801c00902d0034084c940d00180a441d000c1800b0b9a00106003145 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 388575458 1250 388574208 388574227
    0x1030513200a0b0d061202130c021c020a031d15030c0403080406050c0714130b150a1805030a0305030115030212040303020409150305030a05090402090a08070602120301240302 77
    0x80c01c040c3e501a080f00c1000083e01340780c55200f8401c8002030038808262180500d0303180c001039241c5c854001c0a02c0000d40d154000c44409000304000208480300041a00f0300c0058040003039102c0d90100380650220f0f541c00405001d81424969040d141003000300201020415000204540d40000b085544c40c0141048080007107884480980000c0c00030340c0e0741c6030351015000e5045042c1032490b8011100301c0c0034104808180c0e540e18118120020707450600213144070070300703002860303641094036024805900060f0460107a5840100180c0d8214601c1442c030340203a58400f0301d950344ea03c07483d0141c0001c0c024401030220f4468080945500c030854038015040c608401207040040c1410b907812400321741e001808105007078072030040740c02001580e160500440c0c90341c6c40b8540c0742d1080042440801000007880800d99441e54143c5a00031400340008112548480f80d540c1c1c0c1d10014043c250140c428a00d070701c0c0b00103c0c01c80440e4141c03000c40a001c00144c144440d0400c40444140300b1406254080c07000a05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 388576708 1250 388575458 388575469
    0x209091b03130c052e08060d06050a0b330f07030c020a030b0a020a1e1707050c010e0a1103031e070606080d0f0906090506160c12050c0f0103051320 65
    0x1030701880030f0b141c80201c040e17100410103510400340c13401c1402607040803c1030030340d501181010085c1c2c0045c808222035441c2c01c1403600038005a0a62944180d100000d00100750284090100d0303080e148020003880c08403020100c11030b0299010341d05a0311400c110034400240b190700c0c200b030083e20107840814841c0d2280d0b220704400380c00f100c030b003040d4650100304408820780c040d1495075450481190f04e15409045940182140703600b50817205958480408642814071030411600c80741e01034030080140108034030310300341c940c04107000031388045c001001000303000c3c0740100c219a9941408901d600020040aa01e103101e0b4008580c15180d00e40e84003400070b038010052104110020055803020781c1e041992602034009100c90b04806c080100d4100b0500c420786036002202c81c0701d1485082254203101b00d03e00068200960341010204011600b115010080d00241c03001000000722203c0800d0140c400044044a108a0f4010a01e80c06000c0c0c030800b01d18460410000c07001c440100900041c0403c02158 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 388577958 1250 388576708 388576729
    0x13020604050f2b06060501080106120c0e03030705010b090c03060d0b07050f070b060a06020607092303070303021e0303061804020f1c0203010617030f0c0a0606090209091b03130c05 79
    0x100c401440800c40c604004c294403c04016280c2400c4c1a04d4950402200415000c0d00c6c82c9007601d240e17035901c2c00710005800344104541110004049954030344540c6800ca000c1d00751440c0d280d000b4042280890710802c0e0030400e0364801c2001070001e16614045840305410800058001c4083c01800c00011441c50f400e840140308050140400391040e04100c0c0500440d034640d5402030046400c80814828a140c0c013504000864948445c41c1e122000d6604400b04580e40c4803c807180d05200381302000007050380201c0d5419101c0161000800b03003441c040c2c0803c0c0c40340310440d605d030340c004401603034080c4550340608081d80041c0040c10603060348500f50b021401207401904140c01e502d0840c88000c2c2146424042c4a018001c2c0e1160561140d581c4403c295882c09181d600b01c1284030302182c107050b070348000c00042c142c8682104051000c80e960b4000708000307503c40844a80500300c10b00019006120245141c0b00070161f1110392455030741c0d41254140801e44a0130105d9081d040c0d280002429a110707101d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 388579208 1250 388577958 388578019
    0x905090112020f0316060f050409020a090602060702070308030f152e020118020105090d0c0b091f12050901020403240507140304061d0109060c030513020604050f 71
    0x541d5003180354010030107040c210125082c400e6100071454080d01d0b0f18281104100d544a0400b011030381103822090314940150340040000c541302044038503280384d00c0710740001156810740a65500380c0b034102c0204d0b210781e485c0c080944108020030224980c8400b51804c103038001020402c404c448032044002641000c000256034940b4a0303880c88000100310440f081d0301504100e40020000f003040306050900760f00000e000a814044040f50040307803a2100850702c240c0650000310201c1650b02e03090401810340040040c18000c2285a04c404c0c01d00004030940f072640b005a03140c00f10800a040c2884028140003010a4400c0d502800b0000c00982c2581e1070120500c2007035560503803240552440411070b40014030301420410381c06400d13110b01c90110100ea0700503420540200f110400140395007030342401e44200340400d40c0790001d40402d00480c0d5100c950315444e196001d02440d10343c2e250141c40203600c2d18020b5030010080104004910302420b06010092002e841002491036800302c1ca1662061000e58 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 388580458 1250 388579208 388579229
    0x60f0525060e060627040209090109020a080a0b0a02070519020102010612060506130203220204060e010305150109051b070c0e0c0c1005010e190905030c0a060f06050f0d0309050901 79
    0x41c460680b80105e107204c0c3c07100891200c11300780c001c00d03029020b450794050000b9000d001801d0100702064801c2d049500b0b420340243c60320785019501d6206a075207064100c0140e03021307500313071010a80e0940c0714001c48000a07000303801800402040c0400108078004042c040b03065640c0c4030f800050034070b43c584160244c540540d100041a18015051081724840b80117030284030f5104204118606d0103403601172851038091403001c1c0703c40340d661002c80c0080129400c90b44030910160000400c0007000140813124441000580405980e41c0300c040c41612030544100303226900c03034481c50103004049805009914004d40401c869030341e40b454910344200c815150141d10480010b40300301c06000400c0302c199503420340e800c00c04c4103601d0503241c0000220080c041e00103a80c05001204020340d810b0304074805094225058960f607110340c8540b1503030390380c0011045900394108281241d0308901031160208a8802030984122410100200800e2121090301101481021080072a10307450303909245000e00b00801c00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 388581708 1250 388580458 388580461
    0x5060f1f020c0607020114030414060c0d0c0207050a150311120108070803090d03081807300c060f021f0902040b0d0f081305060d0213060f0525060e06 66
    0x40090501845000183c0a001d0420008005036808071070945455100d180701030b240e450fa8500400340d100e00441c45d40d000d2080b1313020f201c24541a01c00404003616411000c000302070044506a0700d4041c07901c50240d10203031900c800c00200881080c0301c1c110703001c0f5240c0010b2000b2034108071240d5800c40f1203000710119003080180480c190030816280900303407203401507041c600124006441a150a0350050800c070341c2d80040b4841502c400007244240c0790203400d951000741c41d0304408008090084071101d02c5040d55800200600e40ca0b4440310340b40d41c004040c80c1200c1c4c100442906c982d48001150782c114401c10841c024001000c0b8003a400f082c240c13040104907905c0328010402580c0941038418482e000c030503040303000942e0382020328110395070200321141c581000c40196002c0800c164004c540140300000d211448d607480d030f402089d00d10840b1100e44106034903200f040380e8691244505e0700200f1010007108800022500000300b000030564400b0f0b112089503074a04090751001103060056500200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 388582958 1250 388581708 388581769
    0x303150307050102060c0a05070c0b120f0606071e020118240503010b0a21090b0a1503240603121101060806061e030304030206070c06020c0603060d0605060f 69
    0x20000b0300c0c007440140480d0520100ca40868855003428100384000051800104120b080290004016119045440701060070111180a208903807042100500b840014198640841500c0082d5002011400000c40c45e0f40f8a86445540307a1050303041c0403560080078010401021820f024203248120081c04000c2c001e5902d203140d518140700c1050000900040c4544040300c0d00b41e0b00d141c88c0030305d4414030004107840440030740500050600e1015042801c170909020302540d031240507202c100020400c0b00d01c1490036594015150100402c201d860300109196003c200840d04c6038004900400944c070f40c1c1e255100c18086204032203030b901003202c0e02e91404c21b8900a128280040807071001420b164030700304c0700140121050a800c0d007074034039544260034456101041910080c0d580904440c6e902c89980c10041000c1c40248100300040c42403084e20310140c1401c40603280902e101914100b000300c2c0c1c541d0303181c001d454010516074010b4203110b4803030755603601c031003a280d64082d825040314103440f40c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 388584208 1250 388582958 388582963
    0x1503030806030c01140a200115150c030815040f0e100903050a0309080909091e0705180403030e0d05032e092a0806010e04090203070501031d03031503 66
    0x1482548642c0020030440c001c1e0341c2003003401c410190510103650f951401c90030151502c52104c4a1f6414800b01d91f10100891007055100f205185049010349603c141c0d030f01900c041c1140803201e5030780050f101502c0b580010303010b400304030b0b0060901440c848010103802e000c1021522024181301009031211503120080c1010f10024140c0c2440d04010701c448000350310050050310400a11004041d40c0e246a9000c1c4041d01090354113580b4014250601c81c240b607103a09540351801180300d8410407109030350308450000041c1d140d084031030107040910307541084c500c20131005070300900960034141c49400401e4694000d020400c96140580c86a44d113a04010110400c04018505608130024034407203283e1006410a509904881c0c012902243c80f2141c80c0365003070401d40400d061010011444145c84a660f00403403024401d0000380d948401d401c40c00020001940c042d01c1c1c029405812040041c07001d54440e4128000040504075428043e19030361050500d9030b401103c850301d0510180440908521b000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 388585458 1250 388584208 388584211
    0xa0b070e0402090306011e2402010608070f060c03050919031205160f1a010305010c17010302131505060706090212030a120c090e16030c11030403170d15030308 70
    0x507501103040046120103c0c0d541d003418014400c007011a0010150340030700402c4050b002d85006c0b0406a101c1c0d5141d2104840307405c00781a10009542007490100d54000002585002ca500340328a04005501e06041a02c040c40a44010390030020100422902c548900d100345c40c0810780b0b10000d441c01484c40c140a40b0440030804960304000d400c1107001181205002c41d10b086a0b0012150410603080346801c040320388190f0300d6403550142040c00001800300c1035001c01c009203820f44508000c001d10303020034a00c00c1024040250302c001c1d0500402181c284950113030901e0710540341da21030200e4448000500c0d68002210840b082c5c0d4950700780d5001c50411460500c0c120012a00a5040c500400c3c1c01808810300580c1c08d01502d0b90790075941224520070004440145402078000d0101d081a0701410000e10161210f0300100307080100c00183c0ea80305400c03085082d00b0341000b450900342140c0c1c500900402c1c0052400710202d0034042d40407801218032440c40e514600c2032040407403900c1d629024290110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 388586708 1250 388585458 388585487
    0x70e0f0604060512090a060e150601030603030f030509010f0e01061701050103080405120109021c05150412030b04060305030c0102070c24121b02071806080706050c0a050a0b07 77
    0x382840708001081c0c1250641c0c3d030140c0b8914003c20340c0e9844400243c034000001c40040d008905003050303100d40c8000403800e912048100001040c40381d450307000650581d5031903c1f0040000c0c2a600802c90814881e0784459009180c040022980307101e02802c0c40241c640c07e41008a550b5583e28041020002d20440d84404589000c02480b0381d42c50354440a02d14003580c4109805250402680494800c00f0760001e1400c80d40200903c00070b8032842800c02c005541e8920460700d6104003403442c1c089100c6880c03013620035603000b038100c3c10040d5145421805003008042607908180c40e400d0120010b071042c070103000c983d004038000584030151801c00c0c1000680c1944030007030082c1402c1d07549003030b08010045480301c1c40c00d41c01d07d0007085141d452102c0082c1000031444072250781c00301da0890012b0340840c0500840e50f04128801c2c0c1f64942e0900d4400b01d0780c0300c1c811100681e11140e42002040e00030809045000700c400181c132201256a200e01b81425102c1d4405c91350002000100402513800c001d8820810a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 388587958 1250 388586708 388586719
    0x3070501140a0f1802040b060706050c1c0912030f06081014012c1e0a0603060614210304030203161e03020f130608030d0902040c020604020315040c0b03070e0f 70
    0xa12a08012138682484034040c1c0034585401400031151941c00486141c82d5000d80c041000b03140c480410020340d00103a0100900203014445508010b04c9401001c40180c0c00400c041000c00451034164000c02442c81e000d10140c2d121200002c5010082c07020003444600300390040780c00851086001d41c00ea5058003c2c42d02c03601e41d9400d03855003400390b50400b1440c002c2c54218541c0c82e240c1040404803410140001e2006a903480200110a036079504080c08070380c81158180401c940f19031003042040c40201c801074000303800002c0100015010301c404a0f98004807810b80389025180c0d000b10b42440f070103402e42c6e42216110303a01041030001c07203e01c030000d080c6008603511019055600003140d60840401c510f104110394010500020382a41c00380c4000c000b004102c0f0b0342e41032205842c1010380f0200d103051b44610305c0c042c1110100c42c0041041885294000c000c0d0900d880f80301c14030501220081d0042d01c80b107068000120b043c091311801980503100f00e484226a5003103d208209000d5940c0805a0054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 388589208 1250 388587958 388587971
    0x903030f0605091b0c1c0c0c0803360402160b0f01060f0e0f0a141e0a030b1306060611240c0c010e03040b03010f0b0406050a030e03070501140a0f 64
    0x41403441645550f4201800c0607540700654817815103030021041c0c19500d48000d0f6403424440c0c94206c1100060f2511034400c028000f55074414860300c0340101c0c00c030300102c90000600081030b1b90b02e100340d11000c0c001442469440041c1070703004c501241c01c88000d5062490f400044101030000c141d641c10303800310300c00041413215030420324020040302442c245181800160207402c0080c0d170710032044101e1182c000e088418825520310803034410306158019540125206801841e1220401864101003040032703116241091035540d5000e1a0140141600d40e02540d030346800001600a01440c0c0007840310396500105810042d85550400090040c0350640030300350400701c8ac11000c42c201c41c95118030304a140c0358844004520071805032159074480c2146010019000c9169441a0040c50507118810849151103442e56144220f82c462400b800010410a00c00800004d202e90444611948050260ba08001d929610039023501c610b06038140340b400c44d2408005051166220b001a444440e10060040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 388590458 1250 388589208 388589221
    0x20c190314280815030606060f070309031407090c0503091507020c030601090c1808070504020a030f0c0908160302090114010207080d08060f01031a0d05010b040903030f060509 77
    0x2003194103403181454003404a603840340c03a04031000b08000b00390881000941c0914904005000200480301400098030f598000c1c0e11504000807054400d500151031245441c00c2949800410f8003c10411420030050a41c040f00203080342c40f81240000c41007004002c0c05081002040c1035901c150144070030044240108082d11100042d40605a4000e1324401c4c107a444409017203040c807141f1464503415109002c00010560301d60f50000f0304401c15540d40030040b42409625405011b0340744031b03507403196010002c1404280303401e50043c14000c00d1402e0000e9003002070141541500c041d2446031020509240e01008241c0c1d00f40a1b544441c032080c100d4404880c01d6900040079460706001307a01000f102440b8440350359000b080600040c02501003199940a010034000b0882c1030101c94550082c0c04a481c940030a501030300441040c0300c0f000320b80b40c0b2a503400070148410794030380300c80aa5840d03484107a44d610030340340c601c100482d440c040e99001c105901c00c900510250b81080d4416800342d00340c0420003d0b07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 388591708 1250 388590458 388590467
    0xd11010909200c0726060c0315090402121609110a0c0b1302040c0201050601080109020c0d050c01021204120906020615040c0903020603090a0209010e0919050a0b0c030703050a0c050921060a020c1903 87
    0x13000c9e04449096041d261400442c1d10b411a40c05e0f600550b101b0308440d089000101c250500850780040000d0003109030751281d0b8074a40c020b446401001c15040302040001595807120315500120180c0e03085441b88081d00010150340c60743c00d0394005030355114103014895034485502409800b09450544c640055030b041c165480c0c000a440070108080400d11054600081d012680703c9031003414042c8160510b401c145803038000c00000c0e8008502a02c4001440c9030020498900c0345c840316100507109000041400094000d601c100342c00c00c40340c2840170005a4807500514050b44541c001070603051810310511002020681018043d182c00c64100480a0400201c02c00b24070882c420110040042c2d14180349442c070300c1d010091940c8649d40c02c00400751403100c0503522030744190b0fa051207151900c9001c141119807050100300046c0701003103100880e0030241c0c801813000009034001d41c40182c002002e282441c90a903200c10305240c002174800c20050040003000c1075494000d070500d8031801503980140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 388592958 1250 388591708 388591741
    0x30f040e0f012d03020406090b180f1305030909090f12160602070f050a080d18120f0207080106232d0607020d11010909200c0726060c03 60
    0x200b8200300c20607a0030f101d10710405000c00030b55001d0420320070281c41d071600201400506400d18060304241c0c07854110107000c40c03000c0740107001d040c2441c455500e0b040040c116040d000413040d1050f2004118900140d100e682c6401d04c6011518003074110602c0b041501402c002e145010303a0090f40d000e02451041d6034000c07a9103000c0a9001c00010ba4444407468854580d0b0b03401c540c041d01e40c0c000e400c0001b0510603070200829840c3c4d98058104455050242c10b64040d000144015109510f040180c04100340135815081d00744916004a61800b669003080d02d09540c495000120241c2a80d003141e00000782000041064500c1210309941c001d0740d03580c0e0135000200d05038011000541d02000450b02c2d4651000302c81013142c0180143c2c0301220309080c0702d0060140c450741e40e400903400000c00108006541f0420040401448503461401230071043d035211508600c06104003030240e070000003511000c0d00b211800d10170495034000741812030341060505001d80101402d000c0e03101003040100000d008904803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 388594208 1250 388592958 388592999
    0x1050c0403022101061a070c050d0f020d030e0a0f0512070b0a0813020409050d08010b0301060c0b0406020c01092907050301051018091d07050d0201081503030f040e0f01 74
    0x40302d03e03c0c0c120003180940601d500611507030b6854000e2079044009400102900b9005103007250206035075209101c04000f80410103131001c00d1a518900051804090141426000e403808452200c030840000d0012502d40c0c0c0000d0340302036140c00401950603c03000e20748a82d81c40320080e2409600e407400318527083c0700c3c0700384a0040003241b000040c1c1480b00c942403c0340554000d1710801c8507144c0e41c507006075a040c1c000c0310b40d40800d0b4448000030b0110b40c0314044134143d81541d40c40305001c184a98400b080c00101a1080755441e4081c400d12107401c40912031100540e0082e18108001403a4240461070540d40750321144128403114100044140c000c41201c3c1114426113210103942011f407001ca888403100080103c00128040d8001f5184035036401c00d4039050400034035082c403603407889402542d50041d403161a400042c010700100c0598050411aa0321044001d9a407031000c2988000a082d0760000800001401010805001d5103004004880e0702c1000c1d0090003580d54184110002207006c00f0100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 388595458 1250 388594208 388594249
    0x1020316111002070b010501080a060b091504030f050703020918070b070503190203371103070c0308120f0403080103020621040606141e040f091a060301050c040302 72
    0x1c800340c4080800c59519a802c1145003103440752543d1802d1a0a081c00384a0340d4009a40400401e10a20941c4100c6084614000b4031921b005208000c1c0108c2d1480d003091140520402e000010100d0702000586a40a105002600708281144100601000043d00074800030082d08605902240006a004155031a03c141d00352204482c1c603015145100d280c080c014151542180c45038495000000b42410000d40c5624480c00c510440ba000c08072170150102c40704e0f08d07030031880e17244555000c0d43c480c0300300404803c182e0b480d060f0181c60300152103460368401c81d0b42e100e001a03040e9607100081e903100e03040742a00725100114205510000c0c0146010300000c1d110780800140000c1040e4641e4071b44c581c0040054002400340f52900b8441c000307002d58425a07402c407039007418080280c074000c0c000b42109101201c80f902400b1041c0306000c020107808000014140e80c44007143c0102e01c0740908140c0c0030030300510412003880c01d41c0505003554000f80045400c000305100500059650320159582c11288225 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 388596708 1250 388595458 388595477
    0x303043f0503030a1d010212010602070501030213230603070e1e0303220f0e010503070b090303030703020a09051e19050d030c06061a130e132603090106050405060301020316 76
    0x10842800300810380c0310b000541c4000760f0442c208c0c488503070b00780c129005c80e000c0e15a011344d02e43c01501644505900d524180005040070303c022044000c42c002045140c034281d40c1d16003000c8012402a600c02e84030300c0c003c2180c2074500e592500e00320780e85642c0740c0100800c5020429041c408a45c3d04d0103440e82815512103921800c207030b03281c04160400d00a00652101c1200c00c0d5962509107000c80c028010746020f80124500814040010812240081005001103280d40e940000850007500140180802c20025440000c0c080e0348a440502d06112907915a210080c3d8000800c08103511030035000030f5041901c0410012565403101c0c4901994150415089103030092070281c004240350b030000c81902d01e6074600d00c030040c0d2030800600150017002e49003404268076801d100300c502104580d1840084142103480001849a1004607030700307032a105110715a41d400c80c08003c8603400c116480d510307d80d90303620100034501d858040c494101c10217500843c550f04024242c091844400345500c2d0a10110f1030303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 388597958 1250 388596708 388596731
    0x20a050c07121220100b13050105030d0f170c0a02010b010c02010503010b130e15180f160203090d032a02090402060a05070602130311120d0e0303043f0503030a 70
    0x180310a200034040058400190205c41c562000305038a4102c1070050342505501103075202584505816500000c1c000d1461800300c050880c1d8007021007081404001d02d10581720243c480800700e030341c02881c82c03d0106071200e81d1844002d085428004c502ea04210351088001f000d030740c00000716410760f0504a2815912401203442500400080e80440142c01c0031000b04191015a00e401d40e80300e0004440103031071b042d40365042d00a80c03002503c40318049404000420344510180da650031a242039030041c2c0303080c0b420210000e002506040400d80c003250314500c200c8102c0c1303103114400403e248220300030a4040051780219588120080c80240038003000161021102d0007001a02c400982c0400c040d07580f5a040d030034107400c15495100031100c90341592030005003441e00d22000c030b00c104074002c001c000c400001304049501c00ca1000d40207405010070480441c000402c0c0301c00403c0714110301d0b00350f1000d40c8480101800065041419102c494680f41134500050020040b07a4000e26039402c0464414a2803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 388599208 1250 388597958 388597997
    0x3091502150f0402190b04060c0201030605031e0706030608250e0106030603050c01030603110f0f1504180207080a03050604020d0603061d010e071a0403020301020a050c071212 77
    0x7031201e00102028010041618036042e08644600e20a0700c8041ca1001c103c00d00da00c60030395500075000e0008041c0300034404030b0b04c1141c02003190381c014580030034429500c002080c14545444900c10022440a8050fa0708210421019009006520b000c02040d880d00a8050300d85c0507544000f443c18000180702f100513689100c001010b81054080310056580d6044050300800741440304a84500541441480310341c003c0c861201240d412462101841d1034990801500a41044401d41d2040d00c11500e915561111410780b04807005041c1c0c556a07c0f030038032601c10700c0034a00515000010b801001010700150a034415210801442c0c1400701b01c03911000b00040280c010b440c4007070034980c5403c81c0081400030a42112201003200e11f441270400b4841070306d050a0741d0320001c9901c0f040e44808000c012000740740c0c03040880440c54615150803c0d440c0e900090036a840990000c0000b00040740c419098201800400d00806009181c2540f12034550340b0b810048134081541814810b01c06109409c51124 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 388600458 1250 388599208 388599223
    0xc0d230105090d030606080402060306040f060b0c010207060513020604051203040e0406020a0e03063903040f02121f1e290109030c03060507050c070e0105090603030703091502 77
    0x980001d0020b49031480001da5900701c21050392000074182400003070080d0141c44500d020b190040c00503440c0d07681e0403082c80041c0c8980c2644280070360b90307008000b40424200c0003400700c010130320001580e0348660b81409000d8440141601c2c0e07a05460f0b4070500010380c3c2c3e14003214200c500544080580c240d2145005085002c0d03980700b0030124075814104010401c10b94001e107503001894845c07a038006c007031209140e030300c00d4110341d00c5040e444d20100c0c1c0308855007400104c0b00410300850410212008114010100741c205840c1150582031110b266400c5150107041a607100d4248402444c44c080c2a00c03240d180c40401c565030314075a40e41c1c0c4003c10f82c5501e03804210b09401c03900700c006000c03480d10014905e0500c811145034031040c2c406c01665000070340c4204c0100040b2a08021900c51301821503c4980081c840038091005201042142c0c11880c034040c402880103011441c00d00c01e0315854101072050a40340140100c2c440c2d002004004006900212050150f07100d2800716007400d042020182e00e01000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 388601708 1250 388600458 388600523
    0x13020102251d070e040b0a030c2c090303060603061512090105090a030c021009030c030f0c0e3306040b0c120901020a0f0201050f070b070e01020c0d 65
    0x441d0241415600e03030801c12804507244104220001c00380388040d1440321905560220008a10803002415882c041c1c03c107507003022004100101c0c140d40d90341d60402c02d610f02d6000b10340d055100c641c2c0d85001d168141500034000c0d82100507050358504606210385900c40100f61a11034807000c07011550355101d00c0f021002d203028900c5903569560030100d00d0b02d1042812034000006600b07150019000c1c2e05c02190181e6a1540340d1500052500a40d0800c07039482c00080c2003008014005000001140080a90034025405403c49200300e9101f030400c1400c3d0740d819080b0340141c02c08602482805c400074540e184070300703022001d0103901c0320704c8840007030038000e400c2c401d990301ca88045030110360f690120b001058100d8420007100d0b1000482200401c950184030203050160700400b564001058401508407150b0b8414034041c1d20b40070880034a1030b00ca4110040a80750a80c1030b2040243c1a03822105411030000300340001c20181c0109000101310140c40031004001800382041510001c3d046008141101e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 388602958 1250 388601708 388601743
    0x1015051305060307080d0c030c110d0c030506090d050f090f15250305041e120614070e0a060e03120d20070302150603100e01022a0613020102 62
    0x81001400001a103025039400e407082c00340650005e90201c0c0024504689603464495014464140e00e05545c0200d000c0825180980142004082c41d81d030305030003094841c4035000c802040c0381036081c40e030314141004061f400b1a130711130850004940c2d0800c0640d10810303c850500c6980d81d030f40b400810184c51800c010550001100c500308043c400d161800780000307620740720000c0d02030040e041650049110030f543c05008502c0420090041d0200080104504641c000340a000d050742d90300c42642194500c00300303448090740d40c0c8540305490070380040542c012116140480700060100b000441d071003810310031030090043d240c80218064070240004440010500a529101c616000c02080542540100515401c0c85482c1041d0b45081d24020b0315401500356004000311901c82d9105900d1000145c105c95041c070402122400c07802603130088000311407010002585811070041d030a0600400b4a81c1000002a1040d4021010b240011000d80c441e101c50314a10344c042090006030300b0042c90131250350100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 388604208 1250 388602958 388602979
    0x1080303060f12012c070509150111060f0a0f0b010f230304051605010c121b05031801030501060311070f020d0f0605070f05090d0b040321050105130b03101505 70
    0x500344004401500360342d0070210b0017841c1c000404280c41d4207983c05003d40c008210004104a15000b64030580450410304062410b6140b40101c149001804c94071006540d801004000070218103028958462200003010b000601d110340000c0c4c0521405200c00c0708000000312480f05130012540340f103901c0e5149081e163750ba41003500704103480301c10141c201c80005000010000c0c1c0d95118000890516800c0500345901ca605028222410748a52121050000c101a4240c1c042a803c0c401080d803468044c14581c3c14102110000d02076540580c441014103242180e020703507004014040315503e81d032041a443c420b58403031000810645003d64050007201d41c00120004200e43c60740114090343c25a11a10705202131103008840e24812100030641003044100c000c40000c0d0385410040d0403511038180105045001d40c02d41c07980742d070100040424075464500410207402d001ca401e00c08460000c0e8280100c9401e280802e599560014000d40d81399695070b00030078200840300c501005484020800c4206 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 388605458 1250 388604208 388604231
    0x100f0201180809030f0c090c070303060929100903030806040207080703051201091b0f021018030e04020c03030c0a050903011104060e0d1104020f090301060609031202010501080303060f1201 83
    0x250742001c1d0200d4040d100d00d540e1001c07174100000c1c4d4500b240e540100306900e2641d0340140110780742c0114800314180b42d06c07032102107507440817030080604d91181d200e80300300b00f040240c0045903464207070001240550544801e40c446560b015508600ba070b60181840350b92a2606400b03e00213105041000d003240301c000ca1524101907210005115180da0240129600d90f20740800004540024501c85c528080002491003944d010340f0207180d40d89400d0040c0d41ca11303c80d00b200d1000f80c40810040800c1e01c81603100000406820018000004005403011420300004040441d80c901c00544644010301c3c0105890002610480440c0c00c42c4a000d03000f4050f000c2c40d806503003c81d40150103840e020821303e601c0b219680c140078030351000b4103030021034890b40c0b48200f1080c07100a5024108480301c0c00030400255485850034058440145100c1d078404031000c0c076609000c541010504100e00459050a00400c206c4500000350f0360030281c121005005030403114000b0f0420011408425425402c0640c9031a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 388606708 1250 388605458 388605473
    0xc1707090608102301021501092009030c011124060411090f090a06030f0f17070b060f0d1a0108120a091e0b0d0e010b01030b100f020118 60
    0x458410307403a9201291145000c8400300e40300e6010f40701d04a002400070010700c4d484003110299800e01801501c0159201240a03140001e090f000508500e0321040301c144441c8405c0702140c0c886148180050404200c600003035210340b060325040e410002c24400fa2009500705000c6a03003900a0320044d035007054140a1030821010084846500c81c901d0105140740c025804401c0790780b40d8500619010b00301c9005010800321000c0900040c60980d41c6680200008140e10803540c080c42c000c11f1128550310662808001042c50403140941c03110050002d0303400285880210394100b0b40c122014402d5031207840200303000c0150034001038502e0035000180405c11511824660581d841c08040c0c07154004c01c69160b00940c42078403101800030340c6c02217042110341300d1034440403001081c00c440521001e550303020500898000c64100000d49035a40d0914003686403d1240303c54200007800d05000c2c03141050300040075051110626400e02a00a0002251381d10070340c88032a9448940c0c107458913814050a2205 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 388607958 1250 388606708 388606727
    0xd03020f150c0a0305070203090319020f0a030b0415020706020409140609010602030405041e02030403120506030105100302042307050904050a18080c011b110c090402010203030a0c1707 81
    0x61490040c1880014200c000c02030750381c400c40e9200754440c0350406060003280200310090421003140800c2c00700c02c6003941c052000d5200b102c0ca00e040c1c072002e111035004124010001c4044e0034443c04643e2702c00c000040c500400240d2182d0000d41c0318103202c20048000f4040d102d4001e006044510010700421140354550209016001e01d0343c13088081e41d54074041c400041e1080c020380015074014001000030346000c1d00001001c40c01c49400a9821841350303120003d0781c005a8048020455051000076004118421140d2203003086000340103d062170200082e141c010b600000c2e000320384484107131070aa4a02000085103010031040504a803410960040080d04210380061080d1f043c8000700d01c01511a00604643ca10303080f640d4002c010765640e0b030346801d6100c800061502c2d521004005006810032440403034140041d12550403008407400c1d16801c102044071410f1085c0c40d50342c140000350341d000054070380c00300c185140001c44500705001a03e12032860300e1950640e0809900b00b00005502c1117804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 388609208 1250 388607958 388607983
    0x2104050d0c0602100902010801090c09030c030605071d060a05070f0506090f0c0414070c15020f03160201020703021f1103041217090a020d0c050d0507080c0411040b07110d0302 77
    0x22180c0301314109a1000b82c0300584000380c00600e9031801403103d1003043d8400e05d0b09a40b60704040102c9540c940d0350f00e40380e441c0c5902c1500c01c180c2e0368080110481c1c02440010400d4410a140000c03d120507002070036500580d4006c00400c8808501002049001e20300c0e20b070600c0e0444c0450703000307141c207003071039565062101d030030b048076005115201203c3d06081c002e211564503500c0c01c017a565a0303240e004482125011106440c06004080700360303c046140c0c40284501501c010641307549191840d00d501c01c5085603031041d0116803040001602103a130100b59002000d111039140d020b0003051032248030140c01410b901c03544800b0b000040c041044039802c4c0c0400e9103a520707269104081c0c0f404c0141051411308039450b20540c1c0000d08030780018640481c2e85507109104032a4102050344501c0400d240598240e41215158854002030102c48003c11140740001d00c11030301800301c88002440043c1c5405544501c89007a98041a041c0810045041d4200e0584004d4198000d000139818002d6840b402c80e8902c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 388610458 1250 388609208 388609213
    0x150103050d032a0c020a1202011b1a15040212011e03020a12050a0b0f100b040b090609130212011802030c09010809070e070f080a020c2104050d0c0602 66
    0x20305140750182c042e001d604003110301c01c007aa01d500d83c41d0301c41c5a442260103c40400c1040700001005a44424106001d800c5642c4400c228054610000d000b818200501e504450344d0401c0b080002241c0a038404070310080e4000a56103500d030304d541c01c01480d10384249594028008070700380b00301c500c00951203070407240808a82e1240c0344000b00c07451740b81c642c54000070750001302c00c0c00148a42401c00000e901c10602c10000c444010b0075540340c0c44d48d1010261062074200c111715041c070050303914011004001d009080940740c1340c540f51000e00450b5100741c0310454000c0b44e02040ca60895a910070b110207502070f650409556886108800041c000c20034004c062400141c14948140c120f00351080d24171514280c045149049004001540e840e00b00500030303001445000004140c80c1803520780d180c010441625000412401c205000d0040c050042552030303828410b200e1001284d0700003894070312845001c8900000045c1410000900c1e114136000305404c500c010640c842007101340342201d012521250309 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 388611708 1250 388610458 388610473
    0x10209031209240f04030f0302010c0215061c080301080120030c0304080721050309010606020f0d0f050d1e0b0103090b0f07030b120a020f101d0402040815010305 71
    0x1150180c80c041e501215820040f00c650902e078040d01080042e1022a5a6100d141400b441902000c4503a209030400c46503030301649021010940c09001f000b140000900190007141c0d4400384100740114006e082e80e1003030f81401000da080b0845c001003003170810340003041c0642c2c0b0f60719030760303664041c040f00d22840c4031712080030142000341b90303040c01500d01a41d41080741074036544139901c6100d142c1e084100250340080c030a801c5c114421014070302d003900c03e11540e15000e48074035061510f9030840303000340e22070020340d003000b01c1c2c00c0c404190100f03400d4a05101d50130080c611082070b02c41101c1c00e0054020302c0c10f0711883d11080c0c2104115004480043c0740200702d061159141060044080c1c0d40502402040c03400040c002c58400076071081400d42c07100c218900000c0c4046950001381a041010700c0d0324695800a082040550403d002d841902c3d10003901c4c01e4400c8505998000c01c40c0310309050fa170078200080e041d1600c01e940d80b034045900030030b655801c564074213094084010304c8510a1104407600e105182 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 388612958 1250 388611708 388611733
    0x1e06230609010b180a0e04060f06080c010c0204020a18121518020409060f1103010806160f1b080f03070216060f080a15030813060305060d0f0309080105070201020903 73
    0x1c0034641a00c0705100c0c040d050040d482046400c14400c0300f0300b40c1c3e00c40d00c0004c010441c100c1039900e0b01d10803401000d01048541c07480054504458454004003455002409406200d98015242d2090298162001a40c0e0820b00608482c00483c100801c020380c515102c000030300d0724850aa042009016140021100240c095440211001803014100e0b0040c403440b01e50251801d43d000340036442c01210003240071519510040c0c1164440c500c08141f40c600400148080c0701d040100c80c0d4442d100020314414200034640142902c1d59028800e000c000f4502190703103101501e80390400041f54000708650300c41c1c2e0242c0100c0050380048422000501c01e02800001301000401400c04551403600c0301001480001c3d011269410028107854100e038039541c1c28407500804400a500842c0560768013921140101030307c22a07900e080d80300c00101030420042c03101c40e41d07806001040c0943d010007003504044c0c1a207001c0d5403803038281d8058900d6520f00002c00004a0f019002040e881c40100c007031303901000b50304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 388614208 1250 388612958 388612969
    0x151101050105010c08070516061119030203090d060212040b0610021b130b03060405030403021504030215070302010e0a050d03060506070b160504080f100507030203090a1e062306 78
    0x2d00c5040d0015101c0c4149901140c0500e0043c91054000c1082c1e1346107000c0c003000300304a050164041000941994100c582010301441858040140b24140030500280b0f42c800940d207002c5d4002e4684150502040001000140d0381210b0320760100c030351a41c0300b0340780908000d140054102c403038500034105103429614041c40810907144411030030002c4600c3d004e411040c0f128401c010009100000c0d40e9401ca00381300d0780c040041500c16485400110b40d9681188144080600003494900c9251428842440180e54240350300e02080304c4030112070389483c0181012405481038101c52405801156018814441c010a245c2e621a10a803070902101c0d0340c800a00c0f81074130030f606000d44a0300401d40859803c00052804002c1c0340c4ad81d1138264102074854a42c10300b8a0484400c5e0740e09544400c1005003012602d004080c0c0c0080780c3e080441c21480c060140f20388071290030200400f9814441d20f1a0319800b200c6540c1581190000c0081052456013038001000c1c140f42c00c9010403000000000032003d2408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 388615458 1250 388614208 388614211
    0x6052208031305040b0307091817030403090f060e011815080402030d020a0f0809120303010801090b070c0503071202100f1a030a03090312051605030d0c050c070e1005060415110105 79
    0x1400901d415460400b46000400040c0754000c40140d110041602003100020303c2800c00d502b00076504d43c1c80c181868040c1c4001003540c070009410300301c00820889160418a8840032000a01b0952900009510b2107541c4c1c8403a90440701d0000c1d6400c4400340d8055000707c029228034425404ca80b40c003010207030160782c0d40d03001150040c1105d0041d01c655000850076000343c11640d80c0506008010804201e034142190400d0300801d40c17036991858244140300c00d00500035080382040c10420040c4c072062311620b4803441101d0300035016a15014801541910070031490301203c0c3d440004220841e070700700414000d422105403124200d000e4214415140c0f0b80400e60003070036545902c425240c83d2a41d03031948407040c841030610050100c20300c20070301405015103804103600c3c40b42001e10b5070b80d41c8649130030b01200c1c820f0740c000f02040b10078003c44041e0400024254203841902c410011242d0b40c00c0e54600301c620040e088143c105070081400a6410250342d0910000946902d421002c0d03900301031110b00700d840 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 388616708 1250 388615458 388615481
    0x61e07020f0a140607052b031b05070206031504020d02040503100c1e050c03030f01051002070e150303040815040224040b09030c09100f0f0b040605220803130504 71
    0x100f1649003202468400014540103216070251121002081040b40c40d42d6001810407100c165800425440654588141c80f0400c018000c2c1c07404121003560010110300036144006e018941c004042504540541100d001d80f1000401c155601e285070240480179402070322909009104000710003492007034034051504440042d948213002c042c80036100b105000f440600e450140903040200c00101c0c442440150312406243d04000e91552508082c442c0311b41024252804640140b81d0a200012804c0007040e001110380d4030032284d0b03040c994000ba043d4800d0b070b8807612492142036007001c0d11501341e0241c14840d500854140e88142004240002c140c0640380d0000340141c0300308000d0000c2800040a080700c007102800b100e8016400c64081020440c0980b1110f80c980e0080400b040041074a000600c060013504614629091a0540c40c0c081c6001e14000d070030900a000c58243c0c0302e049064291900004440c20110325165140b421039101d5000d03006406c0324038003000000c80c043c201030280161401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 388617958 1250 388616708 388616729
    0xb0c0a0216080d03110d1104140f0904030530150d050a020d06180b01050306010501140717130603020c0c011706092e051f08070806061e07020f0a 64
    0x202c01d040890040445000d03030914040280941540d104c0d030347c4103000d00784603c03e00103541e55041141e03030301e24074401c0e002241c4900e87c05004004a52183c1c0c0786130360071561506000e40c5031240d05446106034056680c540510b1500c162403121480c01012540c0d0041190f80d40c943e112040700d000303029000e100c007000505a540107100500041c20701c7e0240c240c095000d05030000340f0019490840c50318806081e800c4c0d43c613441c80c10041c810381c03030180300f50390041170242800c2104002c0d090600c4498080d40344003800141e2511400a407000700402110182e42a41503c1c0040e1500d40601030003d4120881d4402140324540b8803003201c1d400b0329190704900a0010383c2c402c295445104020552100510303041e114589801c0030b500d4800c180f0094051107603504040c0340041d0400302030001900300086000c40b800001c1030018440741e0060321040d04000d41f4902800d80c0e075991800b240651240b5204603d00440340c018207d00f01941d0805414418800c4880003c207611075002c10840246a01800c0c4806 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 388619208 1250 388617958 388617973
    0x120109020d14070b04120605060402040f0504091a0906070215040b1816121b03081204030c08030a05010e090106060e040c02070b0d051911030105040c0c0b0c0a021608 73
    0x4448800c0306403482c09000848009a485040c502000d41141d41b1096502206030f01e4181001182d0203603030303400a000e6508508051a000e40890f9688030361040c0d40c041c2d60f4031300e81c0d0400d0140079403400700b012940c0400d02042c0c1c1030104060342c4d6001e0072580c04005000e1800c0d900281c8400b024068003c0381c108001d180640c0343d0305050515511004041d4002d845010b030032030803000d100803202e8020072103400d40042542150078801c00b00b6200006803201c142180380f040c8005900f40007500e07061401190f0082c07481e5035030314040d2601f086800000d401c0300004010065500001e0700100d041e22a94103400b0442d49483c2c5080742a12031a00503000813502d10885103c040c00c2a1b8010701c1052003910403554050b1751209408004d510401d110380c1143e4440d010081014080c80444429004013542000380360a41c11710f03094235000c180a01c1c3c0c03103252a14200b5030182e21a8140e84070b00c0b900501d010007603041001e81b206441d44100000009805003c03000c85021801d02c042404645040000d003011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 388620458 1250 388619208 388619213
    0x308071a061807031503141002070c15021608100e010903020c1513031a090d0e0f0a1715090f07050603060d050303101a030c0d0b03010e010e0606120109020d 69
    0xb03a90340100034a0404da554540068100c98060300d00c030045008465944203040c41c492050b013469420020a80c6143c010080f0ba800100006003c0080f07079194030303411200044400c0101e050082c10791100714292402d43c00481c3c1ea101c003042005185004541c200000307074900c3d111078244c4207481030290158000801c007889d0b6091440402001e0005803c109290011408421a4100c1b0940007a102c002006542d51035407109129007a030081d800350001c0c040f0a1103a04000d100d07081c15074846004241704092812036403541000b0304c001c0e14031160760008d02c500180d81c0c2036941401651703540c01c02d14501d001c00c00710580843c1c01c110030360310030000e4840f00b81410280129540080c0044e07411603200305070f0070045501407029502a50f0108004000113180c0302594610448000784026410030170401d01141910000898030300f1003c0c8003000c00c486480c00c000071300509075603140562070350074006003506040c004102584654011120010072002a1310014201d41007558025084541e13103100002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 388621708 1250 388620458 388620499
    0x1b0f0d020714091609052211030c0a030e0304030606030f0501050703020906070f0f0f050f0c0102011b0f030b090709030b160512100801060f03050f21070303020d0203010308071a06 79
    0x98600503400c18a403031790755541c040b40c0c045528006144010070109203150b000c180e075005440d5500c840300d00141c21800c000d8050f107243d01c83c0351254001d1554821018070002824000d9400968210004210840d80c0b4103206600030318050085585510b00f60020304414000d2096030103800014101c54148074090ba183c218103480c04200352007560120b41e00e2800240c400318500c01161044026021000c0da000b800d0b0710344000661706a066905007400701032141c00c4a40d25074080481c1e450311210702e40500c00d054008080c000340080c1c22a0340702c4204400719400814540c200c0b403241c3d41e088603544d2409800301844c80006c40c590005901009511a40303072040c0342c0107800114088290259540d2031040508440c515071164025141129040050103001e0141014031070240c2e028100d410145069500c03160144000e0112601000c504041410301c0f07603041c0c404482189000b15030301d5840c2d007003603183e0790405070084550072028401480000401c0180c10302a0f0f002401d001c4591204640c0d544 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 388622958 1250 388621708 388621741
    0x1802032212111608010b011706090f0402180412020705010201020f09090711010213031106131e0b13050316150305061203030a0f0b0f030c061b0f0d02071409 69
    0x207159104000401124000d0f0307900480013040c02000004080c0d07921000541128040a40802c09100c944100002500d42256031503001060000c070120940c1ca074800510310817a035541000400360400b00304000c00480946480c1d1800640e000c81b06010303a210012403d0384180454041d01070001c4c0b144d103407641040542076030001c0c113509000c2801d8110490803422a00840d803843c822040072041002403090aa0480312400d00030380d034036450300341402900850068207106400445c0798221000110308103120080003e0310a0350fa00c190396000700710710901c43e480b09029051180c010f00034403249140041079824212094090483c440c04031011080e8024030005010301e0304140b9030341699100030405d000840c440c46c45281c0014a540c00c200741001140d0b2400840e601404103440000c0260381e00040c61a0304500881e4019035484140707000c0380c8000410040c030307604d034424140f400000c1d071070101e0403501c0541c0c1503003120032581c0c0d0b44c450185040010a800d58120b50180c002c80c5440341e501c404203 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 388624208 1250 388622958 388622987
    0x7200327010c021e011d06091203091201090c0503030418020a02030405040e030319020a02070e0901061502100507020d050a0f11030a180f24091802032212 68
    0x3102800700e0700131400311410558581011090044040103942c0c0150f0070002e6912445481007050006101003107183c400c44941303500c101c02207608040409010411189001360180c085c0740303a6504212182d01801c4d1303010044403c0c0040c2e42d0003143c24107000060f01c04840146074250740382440c00c002c0304029804403500c8821400b0030040461f2540f110301403114103001d554000d40c3d4900d00400311200c00d01d10400303141d0409004006100009a0001c0c00800b9142d040b004210750b030310f88009903401861281c2c001121201c104030001c40094022401078591080780401344415510000203e0f21135909441c1c2030b021880230710044209600c83c81142035070103920305100300c410001c088040c4c5560041d00c071443c0002d4550514586441b206582c08005140541c0d10f5190182000d030300c008a807100070200442c4080c4900c0164010703101e4404e0000600401d241200044180c000110181d4022510107400903086101e5614000846c10a040300a40054085c1e00c950310b9410708890321410003440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 388625458 1250 388624208 388624217
    0x2030601200a060c08010e0a09050c040c0302090d0b06090703091a09010222170f070303050906041203030b330a02030c100f11071a040206120720032701 67
    0x5002606034131440803110a99261030a60b50700d04080104607405c0203108400050600e00c035007000440008403005025421a0b02050b081840d0780114020f000324541e20758414590f42d0100180318000041300c5c0986c0c8261003205182d42c8550b41502600d5400000510380840982004c807960f0b95660b2042c0c01c024804c001501d8201c1d05d1104c0404001b00310720320003046d0400701c0304104c4007200241c0e40301a00021070242011446045805442d0009440081c0c01d100c000586c5440d913039102811034016003100050350102101604000300144031144900c2c1c01500305030043c0000c48407003200c014900004c520f50300001805480d0009168000049140c2544002d01494a8051003840319031203902d00400006030000006450070b0507610300c0f06922100c1070f020003000d8049411210a03a40c4007400c00045a443e8a81c0d2010540d0707449030005200460801030300303109101d070340026042c04601010b0740030082c2d040101e140725213034480c0712a64008588203092100b205207030850301c482c002005040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 388626708 1250 388625458 388625473
    0x4020607080d0b03060105010f020c09180601030c1805040f020f0a05120c090a060f33080a06080d0f0c050f0601030b09070906050f01120902040f090303050a0203060120 74
    0x541d254540c0003080d800d507003551100440241c0b41420840c082c01020f007460824155108400041d44502620784014020784060700010a105c05042a4066044441044500039a5030b818a024801d940b402400104031001d03110290720461402000d0080c2d0f0804650880c8464503401c01c17142a1080d007002c0d4009a11240015065852031800400b810301c3e20b0152103081e01039010042c0f1350f40d000b042ea5410fa07150003410300a1607032851150341611103003040342d02005401c00d40711480441c04080400c80c1e8940c525000303480d0b9402a006da000300950307402800450740b1803210945400d100701c030645c00074588c0144a42d4840c440c3c4600103507103000e10b05540c400b04001c40030500b000e00036001620480c10110501030601020001403008100c2060104000f90400c00021030003826010310364100004520070043d0703442564046001d483e0300510800c0ba0501400e00800030700201d240036404070386020001810302c1801e0013201d101d0340d0160350700e5820140b452412490b1048144a10045218602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 388627958 1250 388626708 388626713
    0x13060309060e0601150e0927150a0e0c040501210c030c1502061b030f070e0a081f020f040b030903041a030f07020c0a0603111e030405061e040b04020607 67
    0xf0580c0d000e0304818001041501d8080ca0162580c11000c8446001d503603c0410880030401c440b070405852003800da5403412443c0c4000e4070602e41400c590040003641d02400c1481035071314a9501c40810507502c403081c0c4c0e401ca03081c8810401181c9091150385110001ca4481440e038101941c1320284a078858202c1407807858883e00c1702414000b00e03820140401400c895801c2c5039a03010410181d010380c03e01600c80600c2141c000000b410300024103211007049683c000f0418090050108828106001d8040d17000301e55a1a04582d5602000034290b112405000e0032010510301802101c0c2200c18255903540781c2851300204420300d5100070a0840c0f10b000c148008550501c5171340414103591200b031388090f1039041c80342e003d001685028000d07100303640c018a62440c043e1151049401111b01c9030500055124100c1c158020f14440c084c801d03a111304415000c861074944031070103180201d0007141110540d0707580810981c1e462003011364080310102500c0c0041c1c0002e40c03164005601038805000941800e6196 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 388629208 1250 388627958 388627963
    0x507081b07080f030109060e07090909390902090319020303160f230604260c0a05060108210a0507150b030d050a0507030c0206040521010605010513060309060e 70
    0x14102100f410000001005490060f00860001e4040034102c0c81e4035061070306c009801980940700e01d0700c1c92602c0f4683d100a01101f078500c030a864840407032800c420b200c0001400a00c035540b0b9000103221f0710b000ea021a0740540c5109452890300060003c0c104072030903518003108580c0d030b8141240d15210800621000c401e1050b00450914402d07146035858a0651400440703200034031000d00018041a40804105080003415640164102101484410346400c007030001d00c01d00d044031850350400042000315038500149401042e4040c0c2c00351480e59807201005a01d4240000541d80c185004400d41801e0444450041940551a003010303890701c04207070340d02202d10039840e58070303803200303a581e01081003d0400703200201001d0708614003036280904010f4080c0080c05086009001c10891007040c07011034580c0800c903406401c006102040035080144410300150a1400309115942081000903155021b942600c0300e01a0b4010ba524501e810603c08a00030040d810040e14122f031030b2442c45246540a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 388630458 1250 388629208 388629217
    0x60c150f14010f0509070e0603090a0203061305060a05070c0b0a0e0d09061803200a03022e080105090a0b0f041b0e0a031e1a0f0414010507081b0708 65
    0x3a0000081e075032500d0114906039100703074452405003d901d002c101c80b4560000601c8001003040715402e460b52614401d881c2740c014040c00094151203218140004484443c940030100707407007101160041e036110f41c4902d0a44201381c0740c20303002c68010226200000c0c12014005d5101e0742060000900c0c1801c650700500c2c100c80300a210011910504040c003035140e2001c851481101a8031000600d645590b0b68500841455210092400d08022034050183d42d2001d0510086400070080c19040804004260b4229401506018080c3d040440000001c0c000c031a141e049400c003c0c4003c0f035030b40e034071180700c07002d4002908650341c0185124111503403541c0c6c6100d0314140001c01d9014031000501b0341c802925040c01c15401512540d04500c0c1080000d5508100c41e294100c00c050410604503649840140d21a424200088440b503000c100030014001030306451145004045460200806142240c01c0310410740381c550020301c3d52400940040c012404501140c00c942e01711902c0c0c50a80d03161030359103800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 388631708 1250 388630458 388630481
    0xe0a11040b0d02090609130611040303110d121d0703140c030d08060906151615150b07032003030f01050904080a030507020c040e07170712061104030c060f0810060c150f 74
    0x9d01046c14070516a000814529864415000380b55841c603000c0081c0502692580e100746040d02c0709100d01c0212240401d030b084008602084403c4c0588038580807954035075402400130a44610040c0c80100e20700015a07881e8881e070740c0c03140500d540741c207010700489403801000c207031b080030a600c0d255400e20010710051a20310b51412000c0c403420001d00d800c24a00e806070414200182c1006034030030301380c00120b46030400c0f984160b0705c0e141d03039050500e000c3e15040c010a010b0070200443c41210b0034803810200040d40700c0c003041008610183c0c0c0720b404102d10540103440140501030188030a0b03040900030b9201c0c0e40c00085c41e00480355140e65060000d0140c80710b400c0e00701200d8002000402c01412859030201035406403001074181c0750f0400081410381c01c0ea506014200715240c00c1030b030498040c40011100515040800c4180c95130700d03000050f1451482400c2507001460000010303140c03c500303414071010b4400c1d50356030b43c518600d10b8681640400110318054070944c0d0b1410744240540c1740b446408a0101c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 388632958 1250 388631708 388631741
    0x9070804020307050f152d071403130306021e0c010614100f1202040b07032606031e010e0f0a12020f19060e0a11040b0d020906091306 59
    0x5003601c145814400554040d070b0150840300d0384d0b410710b9a942e900c2c1d50b408110b0780d4621a142c034000205440103a4a40c2800c403c04135400c80f2020424020300300070001c0314001c182e2010f203103202061080d40e0740301e04400c80030040040b14090000031180c0d00104605c2c440950601042c11208102e054036502a100302c80203695944c008114202d0601005580f0340c10803900c0c1d4000440d090800340c4803a400722464410826001242075010306a58159005410a0b0040382d844000321724000e031417442d0841d0701e245250381e021845500315a81c81105442810040d0141c09007804d8001e118100c6000d0303520303d00e041d5403200d401e00800b901c1008241c0c440d0b0603003c01410815000d0414040d1980b03d02c40040c01c540101d443c0c0076085900107101c01080c480b02d91040301d040b00318204040102071524140b010b034060248a102409400014103018100c2207508001211060303080001481002200039004420000092204c3c90035802e407a078442000440045441d500e65100d40072529040802103010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 388634208 1250 388632958 388632961
    0x1a09180f060f01110c10110a030306301202070504050a02040f0b0f0403031b2a0b040812070c0803030112060507050c0c090402120106090b10020106150815090708 71
    0x5281202c10070401d1442030a060b110784101840d42c035140c82c400408503001c5d44494044826951040a9144581e158481640c44c44ca0507442e000740500540c0c03058050000c40585c200d04408a80e00b0210b482925074800003981403520b90b1380101a0042d0792820702903001e002c000103010b40700c0d8020144907003480301c00141c7d5141070902c0d0407800e4005d500440b00320f6005100400303150210070304075820303680c05042c480071b09400410800700d441d40a80f0000e00c240b0011040304070700507903498881c00d2007040c2100041210385580d81404107000e0742c42080d032140e20132401d0340201e0360404002d0145502605904100c142c0b03986101d4a10360080c3d1104041115482060b01032000622426800c56128a4a00c2c81d02c50042c48003547c801b02100014800c04444000c0307411076413802c0c1d1840013424808004d000f820b541e00214401440d00b800854094104a03503070402c0c3c2c2e88180b08540585004040c1001c040c90221801c5034407210003050f40d01002082000182a40d5030590294828030480c0d851803000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 388635458 1250 388634208 388634221
    0x60f050c031009050606070213090c050102030901090b1803121e03010f06030f0e0609150618070c0809180703140108030f130504090c08161a09180f 65
    0x845400030322030400024280240721004040a201408498640201280544400001940611841b14003e5000c4848a42401c0c0300065030041c600181c0610a600c140c0c582e2800107903203a00c01d8041290000c0c03440007003070082d00d00e0040074116180d6071070a00903400504501007403906503400481c0300b07001e4000c82c2e01c03041c031100f280b90140c07942c1c802c00340c803400c551400d800d002c04084680683d000b4580c591302c050f11000100c1c1e000072000d0302040304403032144c102005050744507560400f141204400900c009915400d2041040a08003006c074283c0b0126590031500310344042c0220421a5412030421403400a80d0748d00f10b006415104080c0344032103134245500061300f1200c036000c0104449032564010800c0c0300d8040195403420300e861030f141e552690198420303228030807540c104551052600318180140000c4608007020f40d02e040c0110b070081c5101c180807408848a034843e10030b007401c14406c00e10440c2d050b1b40141500c20000707030031840e9101d0400303400303412950210781c0d090800a1030f2007000703031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 388636708 1250 388635458 388635461
    0x111030c2a0619020f0910030f1506020d05091c0201120603060b09011d0105330304030f0c240615030e010c0c0812060d0804030f0c050109050102151b0403060f 70
    0x1003c83c01d443c411071a0804040c000301050096070b0085201d80041501c881c151402a00400307084054032504106694200780e03048104400e03402400014450305076401002800380b0100d030b0f281840100310008104001050343c484100a010480c100880c1070346198559149001d142c001c0d5204040200b0034501c010140854184141c0c402c0340034100c3c03075800740080c001034582d2034195130044d141d0140064580381a48441c100c4441401e058648594080ea060030248002c3c500a42c4296150b0100e820f010740200da0346c44485002904201c040d9100b01e000301022419118405416100410300716503510032010004142e883c0c00c2d004c070780c0780d004000b4410340a200b141902c50490601d1400e509203601c4020032030045461900b00320094a01044190350359000c54001158016141c13641c0f20303102d02c0d261203580169401101d0030207042e04040b0f0150b0042032034100350f61040c1c0c02080c000e80e05c5484944e641b0000f8000030048070820030744400d1102d0540c010b10180d40682408501d0f00b26482e003000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 388637958 1250 388636708 388636741
    0x1020a1d01211b0302031005060906030a0c12051602070906060914030f1906050a09021e0f10110610050102120a0201060e0109050f07020111030c2a06 66
    0x1110801040044609aa003102000da0100c2601c101803000660594011000b0050b4820459004814200f0a40665850b4000f5072155041da041c0240d565a40d6007482150302a40e070207640d00290920000d101d06146600c00d9850103418500f66002c0f00c0b08902c464211a0f0a6901030740c0c000c2c01042d40015582c04008480052070070080030040545464030045ca922007501445407020602e0001c49803564080142410401940c8240c1e030940084020808202400301401c4030543d05102c0050007055441c8a04402c0035009003d060700c1100700362100b2900c414001c0340d540d00c91000e00400b2a50b0b296031010810314a81e94540c4503510b0f9030207180502d017040040070040000907550303003404180d0380402d0100c14011405a526221804035000385d0140005411512100c400c80c4000600071100d900658012a8070325600d1a00d45c41316001282070f0ba00c0f07020000050301c020400328011a001300c0c01049000c01108441611741101281d0600140046000107a20703403003002030002751210317400c001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 388639208 1250 388637958 388637987
    0x12022803170601020616090e070915170408030601170a061e080a020f0112290306150603090c060d050604180c0302010327050d0305280b0d02090901020a 67
    0x340701031a01c000000c1d0f5071000280106007040c220001d8450300e41c090118030019010790038000c3e65a00e440c0c1c4000b0113281c140d00c280d80392203a08105211515000307401900784202300c2e46054419507510f4031403050a50018244504020078880d901000220300710101c5d014030145107001c900340349402101c0800d441c110003240c034041c414045c100843c000000310003800590543d0030280400380200117171202841c0c0382c4128551400e01c049982d803030802c04101d8054290040b032045001030405c0034141d13560011203d4440c440c0d1000303401ca40600d02800610350180e0900d0440d000300c4400c201050b042e07002007014a000c0780d240e0081c8a65031400e4000e020604d42d80d4028001599107030389036410810060b21000c0d051540d01e044903448451780031000c002d5a400346145992213001c618246555002c01c0a001d00002e01c0c1c070b40815420380020503411039a500202da000d009510a102d0b040040050f02140c60380003003001344640051301c4241070781d1711030321032080011b840701623410003d031500001101c00e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 388640458 1250 388639208 388639247
    0x30c030b12070513090218010305100606020d0809030c03040f0f05030a0203060c07080d0515010906022e060905010e040b0c030720150c1e040b0712022803 68
    0x4030101d80a000812404540046940f1810741e42d0246a00340185101c5001a4000900c400700081140c80d0007644d50480f84100c086425100495411404841c414082d1324016003011038402000340c400c0d11502d820044010980389421858911149154480da0201030800442d500030032100a00107401e500030b00d400c0d0058040002141c0c000b94030f88400800c5020415004203050051000003800c2d200000e09042d000c110a042c45410034444401103035446000030480400402c01c81e20100c1c4002a07280800020b943c1280d026403190a02225442c40320f444a0703a0b201c000400c0055802003c2c020032003512084028141401d00c100359007001403240e03003010304c10000e2182c4294005840f0000100c4a41c0c400503a501c0907480c54140108010344020041010042c420004803900052017400340f08000b43c24000350b00341c004840350007541b02d501415141804120089140d180914803240e040f841602c1c0b0405007044d031940b542040030402000c010303011040e002050741101481c0d110b0300743c0c02071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 388641708 1250 388640458 388640479
    0x4080d110714010c030e0306040c030b0a060602061b0708031609080304030f02040f020c010e030901020706090e070507140106060e042315010908060411011e09151b03030c030b 77
    0x109108042100b680860400c00040c84210a06229000314a54810000c054403107509007070901842c2d144240c007003520288900e501084210340144509005c840700e07600648900e584d1610a6107401e00094080e54001c482001140001201c10300150b1041c3c0840500d14403980782c800c0002e046841f070b508820b20b04e0340100010b2011407a0b4180031003010740d044501051101aa0091401a008240d4013444540c02c0061054103540c0c08400740030030b00801e83c01c4038400d030340c1c4080071a0a1a0180b080801c0d1260b21310200381100d11a800410b07000b400750100d140c2c2c0d01260620300d0708580e402e52003680040ca44075400092850710740104036003000c1614589001138281c2c00c02041003140600036030040c480e80d82c5200707202d0f401599044010407100003501c0700c0d843c041c14080a10050301c069030380018200b00f200000442c881281a810940039690810342c1802c100c10070401040c401089001d00c020440382e050584158144094030314480e903008143c126400c080030707080d0380320012440e205016042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 388642958 1250 388641708 388641719
    0xa0525080f030f03040c0305030a09090515010815010c02100e0108011d060f0a050406090609060e070507030e03070e010312020f030306030a03030504061d03041406192304080d1107 79
    0x402e5443c080c02400000e55240c50303900d01104620b5a650000303000d0b02010070519449031304020081c00325a5001c80c140300d41d9a8019500d050101542c0304940070070781d04c4010032600559000b805441c0d80f01070408102c400b4568000880c0c603d81c2d8200540050300c0038040c51a5543d0265045005160111080c4190a000c6440c1a03118100601c848e0149207007445403500307990b50400072802044081e204000c13498882c0648405080c440c00707003a0100f420f0030400207a01c038040c40101d100b10400d13034415041442640c0d00315980010bd01c00300d641807098900101d00c2d1200e10300d4060085219505500105848039406420440c05601d80c41341a0028000c000e07054402207452052154180b5000600d941c65250200c01003042515101d60120030340081c00398140d001004200303a400038185400038041d0501044164400c655244110544c004251b0756994060002c3c1c180d8605690500741503502c07441407240340d0360084d81c465402c03540076030050002c044d00b04182034003000203900039180490030700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 388644208 1250 388642958 388642963
    0x90a270209010905010c02030a0816020109050d0302071208040905010909050d02010506090a0c03020409060b04030b13170d0212090d031a0603010611031b03071509050606120a0525080f 81
    0x1813140d81d05104851a610007150307001d11280490940c010301c010745400a20b1800c0c0d101c0709000000320302140d090800401c052174003090b2041302e1075043d0300500096003409150100100030784021280b1580c18400841c48518038000d80c1d028192145c0c1c0019500f5460801c02c1c604034004a403038042d640f40005004060301c5070041d403030b40b1960300180442c911075005e20860080c8501e9018040091808034081192410f1038003c1007100d008040070700b040c1d1114489501d80c2000d0b21002040d4200f05000e41d26403410310b0015041c0301d900020018240302c04840c0329144610304903505006900700f11024005035030180301d9265148140c4005001158580c400720f8601d02c018000c04050103d4048812021881081120200d0107983c132120180750344002d00b01d990390000300e802c0340c6280e441d8151a40030009842461000798120380141460349808050000c6c600290301d0801e02802089811408110100540000044018641e01440045070b030307407803640030040d003041d10650401146041c090000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 388645458 1250 388644208 388644227
    0x10305150f10050d1d062410050c1b040c050703020a0213060b0406030c0306270c050f0708090936070f06020102090f040e07060302030408090a27020901 67
    0x90311004042d01546400b501c0d940a258503207030710503041181d40e00000d10f003070a005010b010240704442c00b82d2108003800c2417141d440c070f01014840300c0e0b00d49801c0c15031030520b941010300091401d000f4038112041c03c040b81400e0b5080589440b21b20100744096040c18944143c20084641c0d107001c0e4107009256500940b01c00c480d0b00043c0c8148d01c400e00c004019507140c1d22400090101200441c0d0303895842c20050007411106070b00314042868800c000824000b0b0714064071710341031888159a480701f00c0c1c01204000b85600d82007442049014801e03404580c120000074a05070f0b0141c500356032502101c41c00c000f001d2100424207002000440c0f08484001c0c0b60700030301308020000c0c2c042c039032409100c0c183d1140790182d01d502801c070b009100000054292740660090640000075034008510b0382c0c41405000690740b441c850b5001c60b0f0302c00382c01000407511941c06150410711130341d02c091030200000c00199506400390090503a4555811081c520300b02002d8015000d00c06402040d4204040d50b00080d240c40c45 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 388646708 1250 388645458 388645489
    0x306050727210611120a05100e0f10081b040f0209010903141914010c0c08040b1e1b19050304090e010b03011401150528020a08070b0601030515 63
    0x1060101410040140c01c2078000c803002140b4a41c883d40d0703e43c00c1006a900031b03a40380c01c01c203141002040b00220762030340d10400d0b1109401100c0041e103950f00c031070142c00401446034860105030800865440014028215441030f402ea40c40c1c4106420010001112146082c4082d014410840e003042c2e030360441044400c681d041041c604800443c83c21040c185498200c40402e0b52589216040803c44c441ea01c0c2c1a0848000000308008000900140c0b140f000c2584050700a24091204201e074003884402071520102b00b00041c01000400130391920301780c0018100310341650a0b0700031035807008000c000c40000801a1120120303040b14a449150301ca114038000c038040251520041c0b4520070007504400c80e5940c01400030010605103140d2400582030a008505203064a0a0501f030b80c903214109407900d282005212580c48200c0740c2203004803d45000c121403d5008880800c0c0119552001901ca1b0780d00a03007480d00320f468010001421248000c03c1d180c45007110000030308094540a082289208 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 388647958 1250 388646708 388646759
    0x30f0603050f251509082b0f0c021e13051e011809020f0915040612020a05100e12150109020c0a030f051c021812120f040306050727 58
    0x1d1400c0130840d05201103030040703480c0d4410982105180d42c5101450801d44480103411410102640c100301c8110f42100394100000324020b03609000b5140080c981008003202e0032680c10740c4901c0802154540320300c5904844001d58540403c5200030404203280106070000090110380c0d8100700c08164a0303050751b801605503598076190242107440b441000551480c3c014903013102881c007468034a50468112000f180190b003040c00010345602110603003950607074000c0c400310703c0906042c14040301080c810b1a18082140100c0c03680b005446405880e5400c190400240c14046841c42c10701c1161901a4000203159104000f89074a1380008100c10060b81d626203082d6412402910044645005d589500003071401120b1304103080c0180ca600034075803d0f81c11358a840c50702c014034042203d451990040d0b4000ca401c841d00c15074018940c0700c0188101c540050156050507281e456240458008460950204101401010025141c9803228082c2e029054110300100c1c00d080c0317400c1c1802c1d00c1200c055110f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 388649208 1250 388647958 388647989
    0x101a070c0e0106140c210c0c090105010e060d1b0504080c01090b1206010c020a08010e0c0a0b0304030507080d050a0507110a1205090103060911030624090907030f0603050f25 76
    0x11780c03d210b1035142d0b124444170f1101c3d8020540c585005580b0884007003c00d0311484281030440c1c10204d100d103040f540141c440c9900048a0018800c140c0d10040800040a50b110540001d40254610304504201166500b03a100c034240704c0700901d44041c4425040c18089190010440d40b40000212030711005440d29100e01c0c0d807030321741c010784040411020007503000d0300d4440e0114040740c05501c0f890900520301c0c02c45071840d0000c810b0020000d520b010b85490100200b0020300840c3c015401400c803940316035481841c00c8403607840182260f5056541040094503031013440051030788580200410a800005030600c1c0c0141c0d980c100c2c48810b0f01310060705008000c00c080b0386503030195008400800c100c0405218480603542100f4040e030003102c081c6e22640301043c00c2000601d480000354482c005421855280c20f82c920204401c280c1c0007003441d010503446401d24450714030035014020086100c1c0009101060032542032a041c1040441c60180a0041044020712846074034078680803a5044856071a51 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 388650458 1250 388649208 388649227
    0x302190e07050c014706040e0903071a010344090307090f230a0213051008061314150d050d1e050c0312101a070c0e010614 54
    0x1400603a1502042c07a042d076a4440c0044c881c0c0b00000c1c468404610740100d084100040c0503405c60710b20b01d03841c2c1d04281c2c107100510499401c800000d0300a100c0a04480c180702c01c83e510160261410720f1a00705041d080d81c0100100b010170743c0d124944255500c0208510715125000c0030704210150505e03e00d6a48146e40b0b111003110090846044060140075200e42d07070703165039110307010781004010010402c0c9060300c0070b01088200702140589054a4040612646540c000d4034069042820071204101c1c008500007250b5a030600e020481c1c0e00d0680703a2500500d842010002d0b42c2081400e1000781a0401c20004c2103249607a00b00f0f940b1800c8103805d0305441b54040040351620300707c0c1c2c80c0140301c0d00c80d10b07a440340c00b00d4200b80f04025007078201980c44146c400150341211107005804076851581e101b03210b83c00105030718101d80750740007281c40507440890782e480484804a03110440c0c007410070540000c0003024000d604003400090082c66601404079490410024088140407c2c21483c045001c40c1c41000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 388651708 1250 388650458 388650461
    0x1d0f060f040c0c1e020306010303121119030c03060b121305241f0b030403030e120d0608013c1a210c060d090803100302190e07050c01 59
    0xd40d40000790080060a20b151400781c000074a500c4141d03841c003020303043c203c0455401c40c002200300364007401410f10340e440e6607426903000039440050b001c10b40d110000b03e0302002442000e03003080c0b114400165030401c400700c4050111803c0c1d4126004050500605028602c50001242c0501d01500201e111903540c004052031520300e404402440f80c01104e0b000b2a2510800140b580c080c0c0c001803c031b0703280c0c0d00d4000a01c03000f075080b40485030852500b40001c000100160014552140c040d050114441d9403c0c02c03003500340803050b280d10620400c0440d1020303501000e4410382001d001110000c0001c10a10009002074a01d0100d00d1000840b0304100141c80c96190b14140c1140303034218506001e0b071645141100000c80e20a480503000315001c044851000b440001c2c04928072028030064083d00c90700e00b0074002140c0c04400c6045101c0d031520b04a0000924180c02903200741c3c400f02d194084142180f040160100c404081d084014520030801d0140200c0c9a000716041149801c0050380c0e50341d13007009a0f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 388652958 1250 388651708 388651729
    0x1009050402120106080f090703030e0f040903050310140d02150d0207060515060a0c1101170109060303030c0f0206060d0c03020904060f0c090b0909180f0d02071d0f06 73
    0x15042400450504079051048110a044e15142d4840110701e0791100701150f649241201c00d0311241d8041c0c6001c0000c680121990065100050301d45104c0c00122000718083d52820340c4100d0001d8000001c0000c0c5c0a4072071025006040d1100d001202d25806000040d42c548540101a1040116443c1a00002e18600449081c4110b201d4295141c0f891403d0040c014101151510241030812900745001d1410f442141c40712003503505c03011031990054990fa071328407502104407414400b190100ca5103084407480140d0007844800c00c040740f072034294a0000e0655104406002c18000300700d4070013100750380219034598010006d8070507000d4400181006400c030042e6078070194103c821a800e003c02d101045c2c11482c40d01030b080c0d030203004d6001c1084048502003924800e07605205020b002c1c000b42882c06c010b9094001001c0c86900803401d80c180e80d014144035810351007c041d58002109640c02075014081c4500802e00120f01610307841058a14018085c00103020064002150001480c5691403c0464 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 388654208 1250 388652958 388652969
    0xc0d2d02100e2401060f110a0f050f0f1b0a0e0f0a0f0c03050a11180d020307030501150602010f0b011409030a050718140402010c120903051222060e1009 67
    0x40205070000d1245071480f00c00e00402c40010308180b1112031060086130304420307032100400100440111a21034038040259614100c0e080d00886078810020f26080000002403000040589000c51018131040c0110310140d03400c50203029134880802c481c02c24611001d50001c0000300c080581e40da211904001010351400c0340342030600d090a4406100ea06900c40703446220b019208108807580115948240d01a1035804207014100c400c8440d1642058440e41e82520320140845119a841e9520700b801c5d43c1d50540700c0c0c4a0403544840800c503840c1c0c24012031a8500d10203104120395503101c0002840d00e2000c0319100180303c03000030340070050385007004a220900d4100040c1c840b0790361903002d44115400c0b9040009211070401046440402c0d00e01150f90007964140c65203074202c881c61350f0b0481007510315201c4205103e0001000000f00e0009c0c040f442820b640713440d0f4159186105a035079900091410440443d9060104c003d02c503140d0842003048034000110354060600d0310880e4200c0c1d6150b1190000e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 388655458 1250 388654208 388654243
    0x1e12032304080a2003011a0f01030b030708210c060606072402090a08010e2503080a02030306130c12150b0409060501030e030a050913020c0d2d02100e 66
    0x103c01800340b60518016000c080240300c00100ca2400300701800e84d0750803451004088409540810710745010051b1112401040c1004102030382e54034002400c21300d050344005513903084402c603209240000c1c9503090300351801508850130914046545695030800805242c0a00000182e030f4041c04004a841a204a000088145103450411a4001a401c510202c80c0642648403001c116583c040c002c484d6904c59620050482946400744801003002e4810440c60342c01c3c40705000f0001c01c07000c03002840288025001556207040c1134062003030400e81406143c814501c0c00700c41c07031140d42c1d0110b02c12004181c501804900d403040350aa0032600c880f20b0b03204180d81100000d002680d2200c42e002681166000d813000c121540001c0d20141c6c691081c1c10100c0000b4008003e8090320f4908440f09038402103407260300600b07020307504c5640c40c5481245a44403000ca001c0d02144011041d11a189032144119100c4100350b581c01c40ca006952040c5050945001c1da8886080a00b841d02c20040d95401c0c200344a0b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 388656708 1250 388655458 388655473
    0xf16030507080307030b120d1b06060503060c041a09010f2d020a1b051513050a0b0309010e0d021e0c0a06051206030304121b030605011e1203230408 65
    0x40c007170001c051000030580590f8a4100b00c10f00b84602051501d00708501c1d4440d0203005881c82856a02041481800c0300d025544102c08102074034204161803145140342141541c50b400c1480e1826a44040c2c0c2c0e0110b883c2d2000c001109080c0da000c400341c0d69032009804c05c144440f8110b54151740e40b480902c0c0300303103011481e15000c04840e580000c0203040746004080c841c14050074074003020480280ca0250b0b94004445102c000c1740034400740020714040340041c14a0300c8181d16080002c03482c4203245e01502c031110000c414060080c2c000c0c412183d00219003002480e0595540b40065100c0e100d0a128011980003281402000d0b00c061040c40540a00203044100f0300781ca441e4080c2107904001e25542038942c440d4002611070800000310780c1951150714040c141e03101e05599007464501c402840c204440c20031980000022550f0041c54080c00720520020014000140c0030b95400205038001e2016120620707225004c6500711400c0d121015804500340f004043c501c3d4500610b100e1948060b155229401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 388657958 1250 388656708 388656721
    0x90b04112d0a091d0106020a02100903080d0b010e0a050108070c020f2e0f020645010b150301030f03110a08130501050903120c010e150403030507050f160305070803 72
    0x3910500b520a140014074130103130542d01c030340e030900300074018407015070302c0084000090b01e42038500300c4407100c492801c2c000040e125900d068041c1c100d40e1903002002d48424504240d0360b0404101c80c100c14007030f0380d03006000f8078000c0003e0803050702500b10024028140300360025510b42c0c0345411419140680300500c203003190200e20040301c02c444000d10100d44418014094284210280800c0340340766401004191140c0d040c01f03846407000c62000908030f0b140078502c0d11800030320300c0071020010201d0050200c03a0552001c182940d84500a19109610040c01c900780c40402c0c8040d0790549800400c0070041004070300d0242c5800b000d40c42c1c81c030000e2150310390240401080070014800d24400004400c00c95a450006491074011121000d60580100d80d080501d80e0070540a4040130000d0000800c0f000e95000000cbd041030091800e2007810f1084070200300c241601401150703000b41300341c0341c0540380c98610061005079000b91400d40c0c0c030603020000d060781814030a03010348100540060040c1d86e03904110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 388659208 1250 388657958 388657967
    0xe0307061b0305010f030f02010f110a240e0304031103150c09030d0e01020606090421050415050c0a0f11040501080604050c0f01090e06151201090b04112d0a 69
    0xe9041c0001074107110011074804440d85040f022a64032131301c00b03091210190700660b011501030b11640200001c2d401250140481000b480d00d075540076601e92000701c5404041e1b0300c000e090f83e201003500035003041506039507554000210f0341280d400c010b0010114250320001b034100910400e100c10b03910104410302215030402030060040200c11000c4600d0109850700549034100041c0410380940c103c10300103400d5040c0010b40b160704c10700c11241400c01100c102c56400580a4420302e840028401180501110b4101c085880300c1c0d1001c0d0400b141001c204640c4642d50b83c4d88000700802c0103140600c074108104010000080d9244002c1080c4241d40c0c5805460303a49000844042c2c2c0c003413040502c0580c55050a490110f1503a406030359603001241000c041a003035120140c05c044d04178040200c003940300d80300e0001811907440482c401000c80d501d40035600c0161881144114410342c0340941000040010108980240d0399402461b1910091010108900015004020140d00000804070300040d0711 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 388660458 1250 388659208 388659251
    0xf03310f1707060305311203090b09011503020105071502040b090f010c0b0a0b030c0904030806030708060709170a140304050a060801080a08031305070303170a02030907090e030706 79
    0x2140d040b94011039441d8011000e8442c19502500a03006000d6a52031300305200514103540c024402034000010ba06030f032000d9100341450301d48000603036104244001c0102618440380c10480381d50081c0074040602c2420b800300d444d50301c8000d06200300010341508200c0e1860103c42c0d0021115130440d107503640c9003220066607000d1202c00d44502940141641b0365070240c1c094082c0260081c04202041e44c82c6800700c0001d2601202032507052045250441e8199914455984201d01c256190000c42c1000814503150010541054072250005820042c401c0d07440181e081c11107202540c00300c10305001d60b84240c10618170703810140220070407000c1762109400000003002100d0041c0c1d511001c103a03032902c040710080b03428012221175400c00c0e0026404125100e000d1908140040003100c0490881e9441c680b07030001c540c2c0102c0100300403080720a8180707071850071359070311106103e400d510710b00c0c040c1403950b280c6413a40240c0035015a0350303d0002082c0000c0040c1c40d01980d01200030003840b2290010b03501522032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 388661708 1250 388660458 388660499
    0x1c1a010806040210030510091a19030506060901031109060109030b090d0e0f0114090307270f09030206060103111e130b130303050702060f0313050f03310f 68
    0x1080f04c8400505842842402e2280c05034520521202d4100b040102c0504403192400f8079246114010746c8160395020303440400036001582c40350b941c07842c41c80c01608204008241500c01d518080c01000403441d24280c0c03c1c49000c0c21214178074151b8400006a880d400c86810242003804600c08000074810006543c4004850a480d60b1030710f00c1d200303401c000403825014007071030000341c0b811103003022024510080e00218800400381d800454440c040c441611008a038900342002c44484906440101c6100381c141e14800c1c1113040c4800e64181e02d01950341d80015040504040d560402d00e000e1141500c1a0343e0a1205803c0815054901d58900049904a26615602001001d00003e01e00c8000700440b0500e02207280040402840d43d00c0603110f54003d4501a81c110804001c0c0c140c000545038003c51188800390700400312034100741811480d050900d40000010380c0108031807a0044030703030003812007108400c840302c5007401480d40e605891841c040c0d000c501101688900030400002c1d0782e070744c2c100050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 388662958 1250 388661708 388661719
    0x130305010b030615060703080406060e090a1e0803040b060d12020a0c1509030b0a0204080304090f05100f05100507150b03100c0f0e1c0503180303091c1a0108060402 72
    0x8030381a00c0d032044c25128250b43c03075002030b040008000080c01040e1640d8854000c1d50001042507035034030f40c00340303c2004940080540d00f19034000800c10041400002402d81c0032900814810440c0e540c152003880b010b84040c00700c03400440082c515a03a10090381e02070b1540703d4001c00890840c4280030790f980014003000c5500c032540e02e0002c00c400415001d8806255440c1d612035200d14030b103454203600e800001c0c0c50240707100d0b000c210104084504100920080c680c2000000308050b00025960860380d002d03003000000c14481c60100481000112004140c0d042200d90400c204800a4151154403c164004080b04030107083e950590046900c0721000c000180d080d40c0508203003440347c04c00c54045608080105a020801c840181d03ca22510140802d01400030910b0f0b12070b40c0342048001002c0c2400f01c6d141c1e400080c00481604040d00401d071184410340040d03091a026800080c00300c400c0f42d94511000007042030440c10306c0200e601a004100303040d4040030903541c40d0403d091b1965800c407400da0081c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 388664208 1250 388662958 388662961
    0x506180d080d0f0e0607030c020f0303040b04031b11010e010210111e270a090f06080c06070b131109040f0b101428060305041b0602030717130305010b0306 68
    0x1a500380284c00c120110320016005541e50703003105400520031a10302c84114816210064424a800c00c0198007440c02000079a04514051a00504000d40398010380084125006030400140034004981001d060908181c01d40e01500390040780707003018115460010038200b4014651a611010050560011302c00c103000350000d480c0707100005841110802040501907200380030300100e142c201e2216205000b840643c425076141d10000c10381d1080c041c40180a030b075800040003240b1003046000486070069440301c2c1031020300d4030b51848c3c0c80c03802070120021250146094081151000f8010500c0c50f004100c800981000e04013031000e0554032a0484002910314042810707100000c80050445a02e100800010640c90040c000100c1000000241c00c194000c0007411550150350100060000381d500050189440d081c02c46104580b42d2450002d10101101030190603808000c54581c69005103040051000c5411840250321460b02c1661440e0310407840402000300641242181e0300d000c4003110b119 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 388665458 1250 388664208 388664231
    0x1902030105070305011a2a030a020d020601050a0e0a020708040303020d08060f100c03350f04030206160c32010605010f11010209040c0e03060c0c06010506180d080d 72
    0x210760081c09081090540340c82d01e0040ca1000c81e00030074203018445100c20368156180768260328000303c0c0d450756150390070100709c1c4000c20341e041100180801741440282800c0d4907041c04a4041c104c03601840103000e10220028540d100650121601c0e240d0101004e0782d02c5541e824000e44078055000032130002040c00d0b0208074945485110807800f80001090b9040501c03003104151501b030b0160004500f40843c441040400280c0f000c240c0b0041600714012516050300155031200c074090003008180020108000d2002007640098142d43c03240c103143c400e0085c00070284041e142c46030001c3c4010612800000e000101d034800c000303e02088000c0852080440301d809405038241e550b030703020307660028071810748241555103c1d40c084d01d40d0518100005241011200104054410b80c1c10400d001c581d0841040c1800d040400909034454001900c01e81003840c48941c0c95140d20042c422a4810b02010455101010039001e00310360b1564001c4c506e4044020500c1c04d0401a0407416902d000c49140c064000c21 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 388666708 1250 388665458 388665461
    0x8060f040809010309021903200118061407080c010b0906040b1e0a09020d06030b070810030305031008011530020904140601060206092a09090f19020301050703 70
    0x280754451500c80c14201058011401051440b07003d0740d114010f002103846455495813908040c0d4091282c501d034420441e403a140c04c80150700e01d4241040580020f0358802c0b0340865201040d64a245000c0a401d4070411082199000b10700029010b52000160030400302015132242d0b04030f00c000d890b441d40580d10002040201c03500056a15007088550356000342044a10500c18480c05009092045490316000c8031000c0341c1114043e1901d480da82c5c0400e00c140040c0c2100c8a9226800b171410714050701c2d1581c04a900c4134032510004041c040040003090807446180640000f40c14440000c0100d00c01c003680701c00440342c551143c4903c07408801c1070710303c00000342e040410f12181030120345850320543c0d41c28042c02c0c207402001610030a070004035611135a18203000850007004640e00070065400c000110b0760602615401c1e07904a1701507940c101441401c425903c1c20908001c4400d80d01070750310a0b960f0b038108010f0f100d10107100c3c025401d04025850f010300d103544076180280c00030412a600c1c003a0030380 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 388667958 1250 388666708 388666711
    0xf16170c030d1a0918030d060303050c06010504050615030403020a14240705180406092c0d0c11040f1b1722080c070b07020f0a14010e011110050108060f 67
    0xd400c4190040011704019003a070103e0711031070403501160b1600c1d03000030304c1e501200c803d600200c0002e00001803030b081d150410410940503120840d402c0083c2c1c01c08400080c03240c21304400c1101010780200024003070500912500c06e401e900403420344240c0c04c0d00710405484950010041020208201000340620602c00f55240700d001c4076110580790100d5200d2005404044a083d07070360054440d90040b40807540c1c1d00805e03456400440102c6c5000101c01100c007950440b00d00c12120642c44040c0702d02417940d114881f11600d98009103840942a0182e0214001d001e40d0035450040310308281246003401c6803004080004c0030342e6555214181c001c0034101d1280b00c01a01e0303941ba24940540521060002000403107074943c411113045103070008014440381082f40c16070000c040c1c00c0001c25003d096090145030400c0a110460780c000380070707080c001a2410042c1c0400918100400b0603130480141e40240104003112485c80308448550070644d2403480546003d00640b6541d004060101c0e10f031040100e41d0701d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 388669064 1106 388667958 388668011
    0x20609060a2a180605030105010f021c08250216080604150e0f060c18090705090114190f03060b0f16170c030d 49
    0x2038104000180100c540c1400c1c009034405901805a0004540b0070341030081c038150a60000841d00d40b000c0c00d42c00c54416054510200300300b03801201550403100c0980e10000e00e80d04100c0c04a03218040003144260b400744030515058114040c0d00303107030742c80159240c0541900010130001000071a1203440c00303005d03070004c041411a0700000c0c942c02c4080c1043c04002e25540c03d051399056010341140c021441d14030b0340e9001c2c060441c401801811200911142192000d00701100010026801018500342d2840c0044d1a600141003142d0354512400d81031302e03214100000440103450407110080f221a6901c020030501c04009414001c048803001c42c1e6035000f000100e12203026089a4041e001220140742c00e100442c140303030140d001c0311019044d00c2d407030000d169a140740c07400f107883c0e01400218158038041041c81d40f44000202400c08010030600c24000900680c009a00c0f880911804 = true := by decide +kernel

theorem cover : BRFrame.Cov 388489208 388669064 := by
  have h0 := BRFrame.cov_init 388489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 388489208 ≤ n) (h2 : n < 388669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
