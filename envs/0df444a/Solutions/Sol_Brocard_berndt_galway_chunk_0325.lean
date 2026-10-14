-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0325
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:12:56.425698+00:00
-- url     : https://prove2.me/submissions/8a60e7e8-e976-4d4e-a4e4-e37fe349ead4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 58273384 ≤ n < 58453240 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 58274634 1250 58273384 58273403
    0x3060902040303080103030314090309060c030c0625020705030a080901031e1d060c090103090507030507030605100509041101050f04090f02030711030309030301271b0305060609060421 81
    0x1e0741402084c1e072900780303c01d6001c2450800e19540e140316105560384102e1244008529001e60034090203103941c0f00d8060542140014840c80c00c50240034000b250081e10b080c2c0700a0004428800420a122881644002954081c80b410001c6890100300340c098503800c8040d607500d650b084030059000c1e120141c002c00101200600d8207040701c000ea400101c504001c170340c01d4503032110320045c8030307540d08000d6400c442124014040d272400c6620940102088034410029240300d21390740d0b41c9491410a69400890310540c540c0100807042c00c0c00342c5c0318001850200c901646604250b03c4040d04010000422410820002000700383ca05040042700d0040c40350003403c110341c12184648000942054a40300002104408403400c01c880000c01d0741c6c058074180020f1450341e4038100c00380c00480c0390200a11620601140c400100020b01c5c03081c0c1d01140d4501031107503013210301004005d040f40d000600d101c6c4240420300550050342c40d41010783c3c0030b03504c0203c03401000072809051601104000e010042c08440d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 58275884 1250 58274634 58274639
    0xf070e0403090806070819060501080f0c070f0f0b1b03060409050c0a081b0312030a0f090204110d0506010915050d09050a050a030807090510051b03040f030201020f010c1704030306090204 82
    0xf0f01400881c4552411f901c0076802d02404821402a00d0052250074001081c01001c6400207100e1000d044d00b000c6161a640c0c98805155954144603414500c145d60001c0c40765040018400c402070038560000022407050000305e13604120300110f0002504450003282d60b044a0b42c2000420400400481c8000f000d01c0807841d078404034203644462591024200c0d00d6155400d0341c041c100094010031450003201c8940c11036582d551400020300c183c0002c2284103444400d05809600e840c071500e00d074500c4103200190f0300c2c610940760200361180a086941041507004042150500d003002d202e28580052130103d0307540d20070f0000c8030098418200c1c0a00305002c0c00d80e044040185c0003507400550303442034079552440d540781d610580c1d84c144544141500540618201081c2c10b200e0401000c0d0108140481f50b030b62b02d219411503186406c9a04003013400c1200e0601802991b0b01002102c54400c0008001c0c0501c1e00c00c0da5000b040c0344140c01c03010b100c0c4040a0041020903000f50400005040c1c503c1045443d6903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 58277134 1250 58275884 58275887
    0x60f0f05130b0904031209170403110a080d0c050a0203100203010e0a0203040201020a0206092206050a080303101e0801090b0601030e010209010918090807050615030f070e040309080607 81
    0x41451051910545001c1c03800a44421103004044040034018280000d41e036039501e00780c40d85007004400c0c00030b56640d0741d039880004042c44c8160b43d011044040054841d41180340003c03200b0b410304c1045101300c810110401c01360300000b885000c00c0f9110325040c1084805890498a040a090b50003035260141c03084411304802c150f4082e604070340b41600c0c500110340340c0111030000c81c032040d100640141c010f18250307000350030440010040d02c1000381002c61020780c0c4120b03404200c1c040c054007200042d16483e0400007440c0426400025000f010040c601d941024032a00300241090301c0f4505100040803803815032040380a1003440108032703020090082003813500d402c0c440482d04495031350100e0300d81a280007654105100b6500e0050381a12080301c605c0c00d0039180105030038034002101039147c440c400000020380390400b03050307410300c13400091060f814410900810498503100c2c19000b503020564910140000141c24012900340001114168846040c200c418040542004000d481803130123104080307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 58278384 1250 58277134 58277159
    0x207080c011505100e090c04050915040e010c09050d0819020304030c0b030f0711030903010606020606030c15030109020c010f0207050a05070608070207050f030f0a0507030b0915010e0406060f 84
    0x2c02c00100c542c0640340d103a004001c11041448a4a400114445824402d80c01c21b003560b103410003100340f0704d01c0c1065603d0001440340c02d001c903890780700c01c0340950801c0c0c1a414140103000141000388028040c1c503103c01c0c4024048034140c4510f40c415200062030070240450300c0700301c507000c1e0344969403100f00c110090006552030f8058401107030a030002000c0006c00700da0420a40f03002e00c4030012001c20a07110b20324200c49001132000804a180003c01c40003d00356800d200b00703001000c2e160060907551801c40105410441d003151404c0c05000420070710340341001160100e9041d504641001030f01e4003101840e540c0180000c65210b00c04610014140c41880300009008020a00c00c9046611a60b1200c40440d4048030645811015038003500041c8114a01032914207550305d8003808550090002c20105071401c4074982056601da080210709005000c0c0e00b40400387d11040c18002040e401c0340818022071090014421100701400100204081029a80051004000c0031203070825858407402528500b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 58279634 1250 58278384 58278401
    0x3040e011401030b100302071a090f010b030106061b0305070206040b0301050f011106070c0305070b160801170709050c07140c030d08010e1519060201060f0803031003030e040207080c01 81
    0x10403241c00054003984070b0b00400a40c034101400361034100c81d841c68258040c1d0002c5200b107486d08810040c0598039865100100d110310b903d1401040e032048046e20307d50071100c0841c072050080e414000b0070701c00e07a178100c40d0000001c02d144041c0102e40403c2e04048030540550b03900254009400900083e04505010165058680441e01500070080030b03001507840c01e03c924003000c059007004001402c030030300803800101c03601e029007030075480c1819565450344240d004845030300404003100c188400c15940000c4841c00750401070300070610340a10b58107250b0389411038071505640980311400103600c0c803c0702040d00c1d111940442024070084074810800c2d02c45c0c4540600902910232034070800c1200c6d1180d02d900e4100c940440c0701060710307100d81b08644141e0120141207604810144020480780c40301c0440c140050055500010b0700c141040382103543c41c0c1c2c0ba5071003082c00d60b00900c1805242242000c080041700e5050070300001d80e00c0350300f0110303000c1d00034014050719000000c10008d1580c01d064019a40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 58280884 1250 58279634 58279649
    0x90804090506040504021e1309060603050c06161101120c0207030201081f15140403030804050d0c200f030f031201120506010b030603010b1002030c01060609050f06070206070503040e01 81
    0x1541e85038010710003202e13400c84001c0d6003ca00e800d203441c60051440d01900880c1000b80c07900c10500c0c2c0b00141d050640d00400c0301141c500c0c4e601c0070300700f0606c01d0521058505260488040e482d00820700c0032985801346200c800342c900c2e11300c0c40d21010203030f009031801584800801818042030081d21006515150310780310a030701180034a4001401c070044075218406d0402192008080c00f0b0810348a681340007002007081d41401500c80007003032544105000b4100a52181d5545003540c6441e181050a005820000c40f00b480311400d040300000c2d00103114460a4041c0c1c0c101104510708100c00981c118040d200680d4141c01a0342e480442614044014440f00c0000c0c020300030142d03a1074428840100100401a04c55002203005202110700080155040f00d4010000300c2c06181c104001a1002681c0580170b01590000072140b1007104280922401440c903402e20300d01240c5020003240a00c2000a4a00d1264400051220440d0307600c509807000b89400904581e02c41e80c44003101d4001c101c00703000310304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 58282134 1250 58280884 58280891
    0xa0806010933030e151b1b010e0309060a0f0c02130204091d070302060a0908061302090f010303020d050c0f010507080910110403080c0a06091217010f050603100909080409 75
    0x8488600901501640b4450b035401041d072145001c10f16259164003409400801d483c4074140c55150007001d0180620747c0f0301004084952490f0301c0141d00310380d14425000000c1d003051000d6020f99960b4030542d0341d4803010341485031a8508601003240c9060840d100298080b0784030f208420102040d502800c1034481e101704c10080301407081070130000302d500800482d400303030b0000009100504120011300380f01012420000305031900c0c1c514050500400300c80c0c25054400e00d900d101d082d4540701c580140c001c1080440b080c40c650442d00c000352aa0000c0d00080f080c0440050b050100c602c2c03c0041ca103200300540f00800c41c0782040f601c0108841c4c82a5070389005445210041c20140c562441031502c0c81a0010082d4238051a554500030581c0020749151001d0040c00c0300c2e400880d9890040b184c1c2e41c0e21501c1000a0402c7c11000a0703c2c0003403040c14802d0360000c02005214034441c070001c0c20140c07201101d51a0b141c2d5200000c5056501c802d801a00c0b142e8200b40001b030400c1641e80c0a030003a101c50b02000d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 58283384 1250 58282134 58282229
    0x9051b0105040807031218060c110d0510020c0c0a03050a0c0503120a030f24090e0c0306190204170601030c0e130f140327060306060a08060109 63
    0x445160007a4001c00c210fa400c1034208000240c0d10690003042070130340b42412800700c100d0504581d080001a0300c10f002003204001345104021028803d94114001203d400d4022845d07600c03000d644444204544800c0d41e8006000c0c00984c00402c001c608821004204007400c6880385000d5840b150800c40c201c0e52188007a40c041240d107000f18042143c481c1b9025000e041041c4840110302504284100c0e400d030039620600301c01d9000c11f820f045d060620703110200d000502d15081841e0102c43d081c0305009071a80082e101d020041e50085041608031180c07241507000807a1171641080203100b1a03004000045140101c00c1020b4000308185040328040e0103803e24542c0e59050070001c1c400100c0311000300051000c01c03103002481a8081d030320b010307015050010943c101d452403545076900400c8245000d03950960260030407015807007100001a800d60300b45066050031004603041e8040c220b04a010b00602a0019600d40d12555119000f05801c00c504020709a50005103190555480c05141c10300580700f40c403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 58284634 1250 58283384 58283387
    0x170c1206090a0f080904140610050a1d13060f080d0c03090303120e0105100f05030a020105090607140706080906060d020a0909170403030302190c020d022209051b01 72
    0x100d10034000031000d440140b40a0740c41e034400358012201202c201109201d0061662500e01c92908a00b60a007404551810020200403101c9211509042004401c21540922036800b054882440e9004200c60034030402183c0055455030140c02c208075036900e040d00000315600065985001c031264031052f07c40758020701d901102c4000b6030740070188c0881c0c2150000c01c000392041c0c0c00d0510400802c0000540290044075030307401e407403090b0381c541044184e101060082c2410309144400500c412001001c1c488003550001c0c003d07019000e6603611418010a100051020f4020200a911444001c1d186c041d9140e00016050300b200781c482030110301c62000041e82c141040c2450f071100e00d03001401030f551585081003240103450300100440e41c00100c2003803034003105201d40141c40958820b850160300c0300450744400f42c810200000810410011040e0708000da22400416403903a601650343d151040116405120446600302c030b4049010325051500040c40400308401504d2811130382d11080d521400c800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 58285884 1250 58284634 58284643
    0x40c060801150e030109053c100c0908030705070608180606090603030412080316050406050409020703110a0b0a060b04080616031407050301030302011107030c0b06010504170c12 78
    0x10341002c480d6000e1200d01443c065090580c421500400102d0580c815686150a241ca403038820110070440c0d404181c5104801d181d82001401e40b803103100e071b5000b0840c21499444030600100b04155641d000038030b044520862045015002a4086940d01c00c0076150180e6240c1041c030400000810b01004240c2074413090000c2500c031402030f0b0013007010ba1162020490707104c1e40035003180d6240c402004001460b00b101810340340407500951245407a494181c01410903800400d41d04000c0100800081c00fa098000055600382c81e40c0d0640140c9032901e03881c05403541e401c4140311100d98400c0140501c03c0001426800b446144095800d0101e20358683d1818aa8055401007201c603800c9600090310300041d0100450b07598009250102d00020300411110002005840c502d000440010040c824144c0900408000d41e80d2142140e1800b011501d004109070881c100041c113201a403c04035041d42e00c00c0f0140c0d4064039807440c001050003130200e5801e0b40d0350305802d40c0e140100d000c0503002600c04000305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 58287134 1250 58285884 58285889
    0x3010e070504050303070b071b06090203060c03061c15061e08010b0f06070804030b07260c0a0f02010b030f010204030614010515161e03200304061409030102070803040c060801 77
    0x2001541801c85665072643c1c00c0d140100180c0410807080f07000c0c1007075480240c50344151381c001e15001400d8071702f5005150921a0003080c2c03442202c410004d0082d140c03110151034036555203108003102410032500d8096100308010060603013071810114045980124078640b5061110462224041030381d03165152801e0300c0c0d009031480e510035190b010310a91800c10100038030034140b01e460118034041e100c0e80e400e00745410950b020400942203044c60081c05607201100014841c1501c1e030300720146026112002c8034441c2840c40d40400c6100d069992070300d4001d4000ea000694000e054440701802115194001e400030700c82511000d090001410b150030900c0c607007034162907001d40300c015404403800141480c0d0780880c180d000410f01e0304070500c000c0303098400307903a94016402d50780105000c202d0800504400c0190120003503600c007081c012480160010881d070840d1a44c0c1409141c0d4441c004101d4010b001e0130b040190036500018180c1c0030441036200862055100d080032540d055150641100d41203802d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 58288384 1250 58287134 58287139
    0x30501061b11041802030f01020301050a0f030b0a0b010e030601080c03011104292b0c17040204050702120f0301030b070804051b04180f0606120807020904020303090a0b03010e07050405 81
    0x2401070207014100350b0010030015144c420146100d03040d5a01092a0405812200301141d6000c8014061841c1140c40140100b40f01854040c2107425519082040b02000c0c0403c2c0c0c0e0b595491104009690003003407400d0440700024159001507a48045094440071a05080386c400c0d407034140016803452010007924262011540440100540020340c1c02c00e0303007030103001d21441c410188810701103e62403181d0700c601e80030314421100c040680080460140e94050f617a480a00490010046900360344d0341c45598000d030100c4010582e900d52003016400c10429074200c1e14400e40004010301c1c1840e00c40000c504892280c4440c03c029541c0f24001c0310f5030f2601390340050168201c9819014000c4007011a8844610000c00002c2d95000d2090810a80701003510226014440140d060007400618411ba600502c04400d4a90903441c0603a2000703a58842e80310000e02c41d28020000c0707819500d0400545080340f034040d200d40300650702c3e04c401d4171403504248500c03800e00f0960030016828030300c01e809940445201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 58289634 1250 58288384 58288403
    0x150c060403030e07081b030f0f070815010803090103050619060e03070e070909050417180a0602030307140f070629010504050d0803060f03010609020c160302030604121e030501061b 79
    0x91042841000d120556503039450303c1914280e0061423400d020000e58407005c080102103c52410002500308141d900592a40040140041202c1030011040320100d41c001d28000800303513152000a0081c0d42500d41042c002c500c41c0102041898020310f080e801032904034226035101d0b83c0c03000d4010740c045040720030f00c00143b0540d5007048000441c1e04184d400070700c11a0390400d5007400d0441d000711500040310402c103078800203044440c142000b02ca660082c145500c099403442c5000c0c2d1015001d840410321300c050503040000d07229043c4162000307039020329038886014002c06a0140c0361803c49500094140611010200903103425800b68044800301c41c07002c0c0941c080346401d906c03034101640004016035000403215000c20125582882160301a1000402c0140c407203202800b003d1a040c005060b10011140c400340c24005640c0001303003135034450760001d1740c0b10003401184001c4070111f15103007100c002c01041100020440307405800440c10780d50380c1e9880514981c051145c40c508403071072510113005442c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 58290884 1250 58289634 58289653
    0x1060e0117030a0c0501020408010507080105011205060105160317150909061b0304060b030609010f0e1f11040909050a02040b0108040b0a1104030804030c0906050d03080114150c060403030e0708 85
    0x2600400c4c80580104001410203503654003650940305c04580b000002030030900103200c0c0e50380119001d00c038020303140030803c920325000d00060228802c95805124080124041c0020144140c91000b824500d5103c04202400c10710411000315016500c02c5102d43d5001c2c000440c203a900084a0384640e212040143e2041c6404114007000e41c805030054400f96200d03003260400c0d0724101328203405008607100010300d240410784d011301101c5018400540310303084445564511621060401421200360100141c1d00900101c080400c0c0b09581c8018501400d1441c50300502070b000c140c540009000707407010f07c1995100d8004651404040703d004001e410100040390941d406030f40404e010222100c90704c1d2405469403506471003900b107039000316811070724008240601445401441d0081109a6202c20307079010940c0c014084001c14015842103011070201c2d00c855035149085903150f03660b140700e515645c00c1c0d142c4240e915441c0c121415000700e800e0105100301d0f600001000801c94031104042c2984d9417 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 58292134 1250 58290884 58290887
    0x160303020708070203060f0603011808090405091e0309010807050304030519021e0615010c170f090607050a0c0618030204050c1312140a0b0a0e010e0d0201060e0117030a 74
    0x4009100c20b49190406101a200680b0100300301c60190b0b501d0340c00c0c1c040d41c0c0b602d4002c05007503c0905d56903280c503d0030481c050000070002815a10200c5044801040c00c8e640d58404a00d4070880d540d0b840706a04120080c609803140c040000c0108100a03652060300c1c0da00c5240a07903542c802540c0003000164100300c0c40c0c00f1514605c00681c800002171054540c50410034290040300010f07070701104c0341e94128409000c2c2c441c2036079101c166000e40c01e0030602824095030f1950190b41c0024107401d440040d0010300842c100c1300342c204940d40361700028983c50301c0703c00d1800d03c1d62ba00d410404080b2149002004045540e5005180410109140018610445081d80e09100140502904a0701416001e2015900c3c203e04c1c031150001078040c080d4003000384105424a00100030010300d000803282c00c00d0642101181c1890380b003681c001c03000b0344081070304644220300798014503141c2015330143c0624200113000d03581c123401102c1211418503501445980700d800501490341035108084180d8000c004c07046455 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 58293384 1250 58292134 58292137
    0x306010302070f0b190b030d0804021c150c031409070b0f12041b0605120103030815031501080c120a03030902121204150f0c080904110c01020703030e0316030302 71
    0x60748100c0c11034102e035503144d480b982d403002c054445040c4401d118441d82c2140059204446841000b10004d000d00c940360040680044070260019000341c030005054510500d0b40f040a880a69000044040130300b0074018020081441c10380e1000007078240100403130100780b11911f0602034056135010f448010310708080c0711980d502007607044a43c41002c1c0800e85c07a0b000c40b500070300e101e43c0c00342c5a8141c51200802ca024a081c6a9401c902c040c00303c24080c00900015881969056075403509101d4095164180c3c10f8400801d8190700603407600c18144e42074108032649600c28103c4001e14201c400b000307400020005100c0040303c141900d6449501e4a9010903c0307900540200c90018040c80c0705004061009410000b20844040046000140402001c1060414240020024600100301c1e100c546001841c20007c104060000600402c40e81e215980700d80c0404159510008942e59a12010312028040d410545040d400709181112a40e00c2c2c80002c01180c0d0064800c2c1e588404d5103a40e59000d8009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 58294634 1250 58293384 58293397
    0xd050a030b0904080903060105060a080f04080d0c0e040606050c0318010309080703020a050c04060e060d061e15060212040b0c0102040e040b04020a0f080c0603060d1e03090b040501050306010302 85
    0x10103440e00742180050b110358400314041c90080b885955150610030503d071a0401c1a44054002e40c82007160340f14081d8419500d41d00085c9150841469454504007000f4500420300f041c112940342001a08001d50490600014858203903401c0c407500381e482c502500c50740115501c04926070070801403a1203a0320707013840e503d82c0e0390014100012151b9803503c80503119081540c0c11000360b440981d60b4414000100442046144121000c0c002c250810300000f4203c0c2010344910301440801c0704400401c1425000001300410420802034101d0001c04080050035100820437207403095500080b030303414404180364521180e110759251600b441c0410304251940704403080507182d5401d000c0070601400c9050818011401202c051402c0e00305030042141e00d0306280d202c0c052000003807004005160380426a417144000840c1d150361296a650007103003003070304100401003d071294041051780707030703010781c011440305c28081e656003038030a42c031000601d110b44510f00410380410810f000180080d803107500200407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 58295884 1250 58294634 58294637
    0x6030204050105121806010e07090e060109050d0f08030a090b011d01050118090204090e0c01020d0f0c0f050f011b03020405010c2907080115020a170f0403140606210d050a 75
    0x8002035176111a40c14101c0030781060300e0380548841071102c0c480c4e214640300040c05412040300340e1410240300182401c40a4030529008841c502d029105115001c11a014441c3d048030641c2e5030b0b840c04920140c01080e5a0034200d483c3c10074040080f41e01c110940b18021640d81da42c00203001a4201801034842020071070181540302c0c540341d0042214100d0380040d00041504400214800d110490100d0411560714202030440d84847c000340401c1e681b02d403420142d1240b40c1400d000031112070400e203400e0061032030701401034820a0381010030080150300145444410303400070344404880070400c605a00c664400c00c0d0004582c8001c800100d010210076914045101141c04000070b805040c941203080c007100c642d00401c0c1d80c00010803040c0c07803440070312804280307520240c00200314990390100103450f40000201108000319003059011000421a03001d160099400ca2056150600342ca565900440e2454003030119400314885120381c0c00c0060500c0d40e260703000307412051800c03001101e03a6000300c42c1c1c680 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 58297134 1250 58295884 58295911
    0x403120c0c02211e01060501110f0d030e07030204110a02060c0313060c12150302090c0f1804020f03010b09040f0216060902040b0a030b0a050f060109121106040e0906010603020405010512 82
    0x800884c060310601422101e5800444c04a01e44000946901d611495611098101860380c041f0950003045c615000d02c40c9040008504055107462803800e0407507000290803510b084007095506400c107000e42003002c0d056003214000c0e030703039900130070858042590580ca003a00041c0140c4001283e58108010641080c600318032840a8074850304140e80c4004000803211213441801d10960400d0800c0e40e5000300c0b000c0740c25290002100502000744610030300030b0118030b489071b40102d0303e555030740440c1c4e00c1001d0f01e80307229140d503110522070031254032040b0410312482c41c10300741800d801b07814001c3d280d4070254207184030700740c20050309e03840d001d4140707140121781c01f036552144d00b0070130384c0d608150310b000e540240805087c92070500c1a400c2140d102901c0218800d03401000c0110170303070b440600300c070580d540c2500902c652400c901d00300060700380340743c00c0c0d60341f00d0000b0030f01180c18951954581d110f003494104a418990783e55600350300320302c6940a01800241d04000510800035680c21041c1c00c54030204050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 58298384 1250 58297134 58297153
    0x32203090b160f2103050c07111503070809010b040603030503070509040b0301020d140c0304020f0105070c0f2403060e22020301110309071401090e09010e060403120c0c0221 76
    0x11068030f40d52001140c0b095100390020301c42020051006181098504040010303003403007040c60340c060250020003080c06c02d01c00210038550312012110f1601c01c0340d549109880c3d050411010b44040011503003200c0315841c0c076481c1c0c6013030f103000c2c01103000310307030300368542c245141c60300304003103c0b164020b109042e0440d4036030300241c1c039648007403000340607603008450f0000c0c1c0d01042c2c0041c6602c0071005003494074580d100740144405a941e01c9900543d00d9400d08000d517440e01585060f200c50001c680c051101d0042010340002c10800501144102d0a00d007001c16103840c1074654183e045504600071045601c13141400a185501c001001e0702003000d01119100c0302002a50029003580c1c054200e0310300070600802070180c0717008100f1580000d041e89101100090020500003000078030a44200e014403011030001c04c90700324003903101701d5401c0d8880d010380c5c00d83d00c4c0030304018042c981400c107640d11107490620503a04c100c4c445c62916060590081c042404181c06804d044100761408034121001d00034410071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 58299634 1250 58298384 58298393
    0xa09060503090a02031509210d0519020406030c0e030615010e06070602031609150c30020c0111010e0c0f01090522050a182604080102032203090b16 65
    0x2c101a22000070110514500310101d1070500c513001034a123801040c40e2902e00c0606500d0010b89030020308169002070b20340c0d1100480043c0601c02103071107101074800a8041758450381600703d00d00401c41d42d201e07210700d400003100780b40c4d903a1012600b00d03040000b19a03021804e984504403103580004014512810040e076510794004980c01079880c0842c0c0300300c013248da0b240f454100003140c00510f030708194612800250000506005041c160003480036100d44c02031076502020207a06850001a82c0d2950303480003034488043c2d83c500004d03000c580070400500c21050b640b60705000d84001040e00340c010b081c0c52490b880600c4040c3c01010049414007560036004515501c03400d0000070108405801c214440840d200d140d01254009085800c2c01418000199541061802c0d07200c800703030740030003d94418000401d180d9801c60342004060b2b5541800140095000b01c1500990b000c0d100300007101071002c48668018040c0202480018003140290100300103081a40d4064400403070401c1c0a00381d035401503500c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 58300884 1250 58299634 58299643
    0x12030e041d0d0908070b1c0510030602030f190b03070515120903130501020303100608040f12030b0406170601030b0712051003061a06030a020703020a020d060b03120a09060503090a0203 81
    0x1900001c2c82c0c070b0380100040b500030401080201001c00740c547c070308011100d00342080380c0d441421079629526440401c00c04150f080c80900215003044085480382410030300406600016500f6000e488800892020042e40031b11501461050003002802440d03e00020710107095824001c400074130310184030b072116038000011864451803030301c40034665170000c0a009000103c1117412990441d4418003c0101485d0078480d8071060765000c1c200190161ba562a1425070030b00c82503402419a1000c00c4900e00c80d03a01034103e10500310b412102800621348079401001d04007011400c00340154840401000812180030107150400100d02c4d194401d03203041e14207a019107009580d0707100041b50005041041c040756110780c120100c00d000c02810b0710400a070000b081800007400300009154001403540c200b40c002c0107042c6d00aa405840703141418001c0c10443c2c0102204040d03a4024011090002c802c045998103c544508454542c40740742400c1401c21075841d003008241d04a01c1c8143c80b00c1c4405640d0400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 58302134 1250 58300884 58300903
    0x100509061f090b0303091207031202070b0f090310092d0b0103030c030504090c050304120302030f0106050a030b03010f050901060f15080717090a060c052110030f06060f12030e041d 79
    0x47c020510316146141646100700f11220110031900810805e00420a0781011103100c40812203000e07442e0418140003d003007c0c0f002e2100c0c5400f42c686810042049030018080c00002c202c0030031136010f00420401e50012408150b001070900c00d0342c03401480020b00601041c2011402031824071b06003902c4000401c01c80b42168201170120724080204010058840745400f11050705140075411401c040ca03940c3c02282060140c1d500b444004240d10816a12036032058507040001402800a12040040d0500802e010740d190381c600d50800b0008155102128403841c1203e0100d0f00d030f000c06d030802400031141030902500510801c00072030031070740b5182170030b2055501030a0104058050036800f8075201c0100c6d240c40f17104509002080c00381c5010590102c0d10f440008140346910040b43d0b48100d500c10081150350402400d452515499a00b07000280d400316041d2508000c240403000d4943e013400000500032180140010340190030300c43d081c00c1c15001f20711080304480340417403140d040e4907100e81040d8488 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 58303384 1250 58302134 58302169
    0xf0606050a09140c0c0c1002011e15090e03070303200406020d18120f080c06070504060207051507020607030e04110c0111070819020f100509061f090b030309 69
    0x108619107a01098101e0700f80c0013204140700c1450f14000c0c0940030f841e00b20145102e03100b4044d600c91030f101c440c000c2d0030106500701c004080b82e11382040080030070300819a4080450340100200c8020031241801e00c9041c83c0c030703880741000758285241543e044019154a03c0604200100311b4035011400c40c80d800500f0103068981c001e400f40d0714004500905203400744040400994089000700030001241031001e640d25004203407001e0034400360425480e18840c0d40220724043c4202d10402040e654004003920a03141c1c0d96080e03c2c0034541e21001c1104403e07200002c8034281e80b023004080011720b0b12000070320b07403107101e03041ca0f01c1e030350b01000c0000d0125201c0740051302e0303038000004807890800c0080c4540200e1208811810b4100b40064030b60a002d8010300300191400325880d50401800b0b80200494002c05180b00119015202c844ca8400c001e010103032000c0c0340900c601c801140c244a412407118013a6149820480c030100d01e0503001b0780246c500d02c0042501070000308080c0d04103445103c3c3c1e401d0203c910 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 58304634 1250 58303384 58303391
    0x40c0b0310030b0a02180414070c05150c120a0c0530040b1f1a0702030703080c011e020901020c010f1709030a0e06120403030b130203040c06140c03070f0606050a09 72
    0xb002c41c0c1d1080040102e0034a01c03923443c10421840850b02030a58580200c0c017032800c4826543d05d850028580300c882049030344501260800c110803400c4040080080841d1933070a2803e50301c0352110b0605450011700083d01148062010981840b21440403c89410289450781c0602c00c440810380782140c0140c170240c80e140500390402041d040e1002c9042d1058652a200903410342c580b41c681d817901700b82809101400d20002171000c0a44d40e0030030100c000b0b16000f442c10340c0e807a0a0024214000d18080c180903000c00040352410b0301d40c0c00c41c2e02c01d5511550068019220181030000112a50070440245109010140850301c2e100446451181d1003030700d48070011681c88000e4100030f0441c1c100c1298440c410041080345141d02c3c0c0080303013002d03002603050502090f0400c032000062103a40300003282004441c40801088180110401b0b5178044801030303110340d444010012410342d0107200b01029074803640e008010160000d02d06000050a01e400b0302000500c0d5601c490000781c0d1420b4503445041d90944 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 58305884 1250 58304634 58304647
    0x2e15080106030b0d080301090e0a0c0602010c09060f02060a0f0e0a030c0c0e070c0803130807032309010512060d050d050301081005131e060c17060603040c0b0310030b0a02 75
    0x1050f21500340c00c141c003250082ca4480e490341d02e5074103e00c41402086410340d1144800420300c1010000101c0180c0d0020010340e07016250340d8000d00070032001110100040d1110000a40140508041884060700703a000c0c0115950f000c483c1005801c1030300041c5c80340707607840c217808500d11010301c01040f0091090341d03000c00c0e650315420840c08120b540d030060001c40441100388450301d600701e02c41e100141e50200c94152281e44403407000d1025507a821000d443d01800003142c40c1016402212200c08154104290654521a10882c00030740660300c1054003041c410460241d01d5612400060360000005020300142e035060b070307907541c20000c1d0003d400c004110040014003010701c090002620300c5440400420681c40c1405052005580f041030203004841c040203140e024075502c0754034403601900400248410303215490001c02c5d0f940d001c020740c1040d20000c00441c2c1c503403400f1000ca9000755003100c0822500c0d414210b03203e10952000d0880004440008000000503280100c4144200c1041c0c00050b121030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 58307134 1250 58305884 58305887
    0xf02120f0c0109080601050a18020405090709170105040b07110109080d06080607020c100806130908040602010608030c06010311030a1a060a0504090c061404030c0f0501030c082e15080106 82
    0x19801d4102013800d0304200c00601c9180c8603c03966904031243c42811501c26164510004c0082c4503680140b9009948402000078941d006840390089400b8030004501d5201f01a041e142285c0050310010154116180425107543c492221640d411400c100001803030501e40c0c0d6204aa6401010303105501c98582000700700c0310780140b081d541d00280a0014141440c0c0080003c2c034035602806016061011107800b10703400791101c0071100210400500204840f143d0f904160100e504944500b800541c00d1680101d840900802610001034416004000690030f40c2d031020202e030f41e0401004e82600c148404a4081038503010f015200031803003040100d650900d1001d012b408500c6402c014001c80c180001d400015443c04e2608085501a14010b10411491f100c0202e061049600c0079005110016001c91407c030800c5000c4126582600e04002074040c01c2401d0f51460740c1280c0f5001040c2c0c0074848010310070040c901440c000040184203c0d2941e481e0b51752103450f4280000d03c18001014000140040c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 58308384 1250 58307134 58307147
    0x120306050904031202070606090c11100605060409020d0b06030f010608060a030203030d05070504080f030d050f01120602090105091f020f01060807170f0d0203120a060f030f02120f0c01 81
    0x208020350395a24145002d4a000d80840881d4104e00c044660000c1c0074001d100b03a5610042c003612040600380003118030500010b04104a5003ca070782c80c0d00070360702d0401341018148079140032513002501c5a410300f4603100070400250420407203280c4081c1c0341c06041c42d266680b036008620500c03848d0038030a4954140000205005001000b043c0903801d554024000b40c0e5002050b940080e00c10200418181d6485004036498040e90380080403500c901400b0b4288180084081e14102ca8a25000c1045680701c00c0c841c0c40505003813080085010b12022030b08003143c43c54004064009043c107111f45084005004603100d800318080b0002003080881a101c522541400401c20301141400203000960401d001d00b03072184aa4420102000480408501e58541c24001c60808609181c242c4060b6111000083d490390f0055142c002c425080b04006040e60095120b4401590381c0c41005510803030546d5600c54103c5c075800300990340140c0b1240c07190aa0601082804030748106031000d045100034840016190 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 58309634 1250 58308384 58308389
    0x903080124050d020306210d031404020a061b170403060513050c1002190303060f150903030e010e0306070e100c1a100806010801021308030304051f0e0703120306 71
    0x7049401d9071400422540300080d104686030103140180c1c0d0782c0322103001905004048034803014000298524003000000482c3c2c5200c220080e40381400403520350502d01180c01012100258800c54450040c481a0f224804450110101101403044201c1c5526810201c0040390f101d00d00f03c03103000906104102e8180510b6030001ea022000c41d0708a071003941c4064441c842c20a40d103004811031481818124403c0102450316100d201c0e034004581c40a041c000d010b020640200025074030380c0c0a00251004007809030742c00d102c020350f4a1742010790455404840301e2481442c203504009519100790f4159806124541c0103501d246c03600d03809a948241404490705100d040a0103006070200300f0404105071140361074a82da40305440310f09590381c568030601e840b03100782c00204141c2314410000c6901c981c1540101084258644443ca101d5590070352a40d4911044800820a4005041c4d0070303220b030802d04500c01407200c1c0980214030030312044107441c9010825402610490304105803001c150341c0601c0341001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 58310884 1250 58309634 58309679
    0x1b120307020a03060e1002160209010510081f03140604060c030e03070b04021206040c030b060a03050c0f010e03010c0c060b060c06070507030c0c1805010b0418020c03070609030801 79
    0x8020031034000512000c1d241c807000d40700031380321000340a404000341b00d072500c00300e8101400c545990302902985100709048100b01d000d000550000f04192070410003000b02c440541ea41c98149645065200e4090a004034001c49d068103420000302c002040c9502c00b4503a8504600141120302d060704148050b55859480001418900880b4160b82200402112a56500700d0000c250f1612607201213003400fa002c41144005000c0d5805220801c00c60306030440c00c607406086002043d03191101000380c00755082c03000901c80c0d800344000f4600740c20f0085481c0743d948814140b4608140384040402d00707481907441501c002414010b854800c0048a1003401442401a5589400c0c01d07540f1100950703440e8081c00480a0080c0483e9440400d4824220103011743e500c10010300c0306a0383c8100400e1404c00500980c0002030a004c004101d42c1004001d40b8103d41c1c401d0001500d03d101c082d0100000d601442c05c100240c0810001e0b80c000c90507034041d1000c0e0314483d903900c0d5000d40c5042c0f24010b030003500b20310961 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 58312134 1250 58310884 58310887
    0x8030702100501050f09040c050d05030703020106060f080f04021908030a02010f0c0503060d0c0305012d14070e0303040e13030f1b060b0d050d02030316110d0c0c081b1203 75
    0x180b80c480c44417035600000b00740c650000310f840f141042000d03462150f01042d4011410b20407001040f601202414896100e078000748101a1992802d49580207285c159130700003041d800008801040032400940c020340043c000c5104d0a000c2e040218503905260000c0815500020304085010360900c150b605100c900501006001103d24000f010b910001e00343c18802e02e07020b030703985042c403d58500a100966100008104098000c0d0700d20200c1c40358030b0f424400888131200c245403800052300441e01046003044403e0104c1c1c0d600d0209545030201c9000694140c07200340000700d524501c03004828002c2c0c000c0340307509181030001d240051080c7c0c05075550100308056811a140b880d40303044800821306901c10400b0505100305004240c08105051002c1c10313620680d140b409225402200460180507005120500c0350f00003042501c200b01804400145540709407580002030b4450175244004a00c24422130040a0707030342481500c1d000d6a0000b034080c801111140401e2071a0841044221405440140d03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 58313384 1250 58312134 58312139
    0x40f0b091806060d06060c02010306060c0b1b070212070812040305070b030402041e0b1c030503010306020a020703050d05032508070f020c030304060306080606010e0d0f0f0f08030702100501 83
    0x1400001801141c8201c28003018003080c481c0d900d0800b034940c0d481c10954200091651080000e040c00c1e084041a80400e1825001044182c4035080039407160790804c80da00c09945803d0480721450007480d8010044550034403491005980d6555808640d0341404024841641800c9901f402d00000345402c07800c10074100402c10000c1c03c08598002101c2c040100c60f034483d81d4070700205011f003544017a040d0340e8288906401500f01d0b41035000e911109404e0300c407084050340c10fa21001e40e2605601300a0080307501030004000248094008040000051041c0d54200795641e503014035103020b014072035012540201c02c2000a2003009400481c100381c20981f0a024030f078115010b400918040e2a420401c0400405420a24000c12900194a40c081c00300d96441742c0c0c1d9000200203101a0003844c69a01855010410562140000e141c000000410100d00f882003940d0b8a1003000440303104541960445419030003045140f0100c900e40340c0a212082c3d503030700e08580000d04111009034411000b5103400b006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 58314634 1250 58313384 58313389
    0x51c0b0a05060907180909030807080709080307020d170403080717191211030108010e0f06070917010e01020301030b04060b0109060504060c06020d1104051005030f060f040905060705040f0b09 84
    0x1034220100342080c4c3e4110074000e8a000c40e0300c000750070480b52141099200c1f4105030b44011014400c4143d651a0051500c03600412121911907200e40c0300ba0740d02c188590f1002d460300360403d00d42171384110741040c0703c0e40103a04506d4854010750b0040e80c10001c0441d00714280581c1c0c1031301d4101038850301d1030507140421040d0944001e0701080041c004200c5c496500ca90820000d0b070081c602c00d603070300802c43c2d107940c1d449494a01a00707100407420400d010b112040c055160300002d0309070190695444018504d414000b50642903642e800c0c0d0a01150748552034404100d00078801940610300800160f5020b1603c0e0504409880d04800ea19040003458601044002d034860700751001c0d40c481d80782511841c03444e0b0400da0064080c4030740e042151454140001d14418405004104480003030b40c040c0c15003004c203201620759000803143c8a440f400d0000004005c1c2c41e00505030201c1ea000100000b03030030701c21900c2c1d030b518080301115424007040000805214174a02c568a0400500081541500e0b00803084c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 58315884 1250 58314634 58314649
    0x30204080d03090206070c030b060a0e010b12060315130b0c03100302060d0204051e010f090602060a0c11031602040f090302030d18080304050d0801050a03210306051c0b0a0506 77
    0x48107070415903596426400c6545500807510324513041580c2c0c02045840b0309108100203020b55400d07228100d21000020514a8003030000e0480703040c038100a00b440e40300003080520540c003c2465515010b0486d94501c60300501a1203401203424400e030036032907880c514080e0030520004c0c0802010900602c01c00074008a050080410307268191000303034440c03441c00714520190085d50440e540c06058080d156407103294041c0d1054014009903a8400322203030302c1030269944e18070350207403a0058020400040c548aa00d400c210003002e8645040c01a8001c1000f0081c00c541103880c42400030303121349660b0b03c25071905004100765040703190740800600b41c155401943e02e00c10052580501c03510f601c0e000542c41f0340c01ca060000207405c4106159a8a042d1030320310b0310f80040320300001c00305045074008510360030110784001c26607a011000400303082c80d40891103c64201040399008060301c829004ca078517140c040d12210414031040641c0d081c0d203c1341c1781c9014035a5004084180c540d11381020400741c1d42c0c0708203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 58317134 1250 58315884 58315903
    0x115050c060a200705060619051c02011202120601020d141b1e030a031a010e1909060801020703020c0d03050f030a24050306070e0307091116050a0b0703020408 70
    0x107074005420080b11484070110345100c1e48000c1940404074845090100105d0070910a400440b1b07034100c0b1031602002107061074041d001c9d05811003034a080404150310402c5c00c4081c0035005042910410b542080403034240ea00c600c4684024050903c00c2c0b01095804104c0749000c0007460400368584a080030640c001c5004d40000311403422084e809402c5040024400d0801490701c4002403035000707400c040d0890f902d510260201000901d81521782090a01d002403030110a03070f050392106c407081035180c1040014510500c43c403110ba5590500004d540c425403068500500d41e10001688aa2880c03d0280c2031010079403100f4090f03000120468002a4044101c0740008000c0a800d5260380340c912000004001400e108440d402007038103c0c1c0078540d80c0368695412548124111045907803840381c219420780340c0c0d07131400d034040c0c0c0014814098242203410107180d00c0c00c180f50150401da4040860400c7d0172031a07000340c0e0142c0242c0205d006024400c0d5446501202e1070809614061a25040551b00c4e015039 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 58318384 1250 58317134 58317151
    0x1412070b0a1404050405010f180b0f1e090708060102010e0c030304050409030507060204030303021b030901020a080c011103040c0305070803030c180a0e040b0114010c0503070f080c030c060115050c06 87
    0x3450501c0b0040400035a4043e0801400c100040e40c0c50720911011351700345004401b06429540c3c03030385038031032100e0152408868000c0d110700303203200c1170006001c14115401c3c02c003416294400002c8010f604d0700210980f040e1103a40d140b0815040030780c0060b0840b00a050010030b650090220507000c1c1d1000000c41d822a034095400080000050508660b9801003103001042d00340001400818142d058001d00a08426681c0009103022281e24140c2c0e80d00c41c00e0145805a00010202c80c0440c400385d02600c4600004030010030501c921202c071a00607402120110f6828001e25030038014441c0401052014180c150b008516508203080340407010b00a504c85802800c03a00c01907040c20303403104c0580c00001c20b0f1a20307140c8058100351500c1d0384403400902960741209070445415000b58441c8200c0d2010981100185207000c110341c684140c2088801c0040c0c074070207800c00401114a40410040550504034009408076504220600c0114080c03111071000300b04052101e401e0700e405c042a0b958000a00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 58319634 1250 58318384 58318397
    0x9140f0702071d1f08010b0307050901140118090c1709010c0c2603070c110306062211072307030206030115020c03030c0f010609050103080a080405030d02041412070b0a 74
    0x2240745152640302c89800130503540e0400d4000140c8072005400003d425441181074918003038a801c01c0c0f10480300c00340b0030714220a2181040d42c0655001300d40312000032205603042c450441e200c03e196802c0d1181c1c150603400007400c901a0050001c1c0c400c01c0b054108550000074000c85140c4e0344010461941d122020b07001c040c8074610b030280c011040d0741c1074500c0880301541079128904010054076411800c0c2d82a143d00130031950a1a05213404654a4480d050007080a8194400c3d810040740001c0203458034454559140c0100f01c078041c0d140c01404500c1d108000c202c1c1d0030103140f60411803a00b07080c2e43c031038030380d502901041c001a0780d000b054a040d034216000401a042e542d100481c42c01528409060b0580400203200301901c001103107200100e01040300a00c5a51350b80c8042404446003440043c00250013801404a0103214001040d0014001d8045a04142a003c2e4000413039010743d019001e160b42c00d9041410504203130401a000c220700754003400c1c0292a241480f0114441c000318203081218 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 58320884 1250 58319634 58319641
    0x9020f060f090d08040303031a130902030f07030b06030709060302150d1805010203010f05011b020405042a03030807081005040b0d06090503042904090506010909140f0702071d 77
    0x7210054494048005200c03070f20640303040c206860943d10901003500080d003030413030340248500d042c410041294005462001c506c3c081005c000000c0c201144101da060181958049d03059408010700b80140d80200c071066943d0501c2c404043c41d08000f580450350441c10b1030420805a61040c028143c194880b03412907954103030740812000182280f0740c10044500c00381c8042001d010701580510705850b400c00000e00950b4403007005550030408030a0380303822120364080001c0107080c19004290003a102e0303411450801c0b4120300072407200c0c9918125848001002c6010001d160b1300800d940e030844400c3c2014206410826042c00802a95014050103580c0b104002a01380e1607180489100750f030001d80411600c941460803686942c490309c03440c40340d8144000c043c2c00e0390f101c01c10909508100100b010b8505403400c40c41c8005440d000304000e05000301e0b40000510450207028075008080d84085500031440c0521424a844002400c50b804550000d1000d00c403401c152030101c40841001c0004008644c2d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 58322134 1250 58320884 58320907
    0xc070204020f0c01020d0b01030e07030b0105040c05040b03090a030212030f04060c0207051201050411060306060a1209080703030c08010611120c0307050d0c030e010305041e0507030602040b090a080109020f06 91
    0x205103c2004060741c4006010354000c0c0311540003080f05e030801d0740c0034000c2030844040c481e580d50641c00302420868616004001504e0664000c100440741410003905140ea10603919666820448140f5101d4100070465410154140400b840050310f04080d1415400e00203001c9688640c0140002d0074555030381000b204c03260080040100074203008102012007500900120302030101518101c5401750052650841850310b101500c2c402c6a024003603038205120310300102e59480c2d07403100e032400381940da030121400b160248005102c80c0d030083e1000b01d41c80401d214018000c0005030701c503000304100700d1041d000710200450002ca20070030414001d5154084500103d045101340d02c80113100e0300c903100100301c000b070704331056001081c041c1d19080b404800c0e182c0150117882d4203d800801c0144002480380114a500401500c010302440842d07420607101d41d181c000301d90180d040170307030b076880c003c94401490f1414800180181910303500901075110750383c0c0407510003814180442e10500000c00d038440c209 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 58323384 1250 58322134 58322137
    0x7050a0e12010609020d0b090603010606021f141e06010309120c030e060309070e1b0a0c050f0607020115091802060304021c031d01080702070501080907030c080309030d080c070204020f 81
    0x80003500405c5680c1c82101d071440b401012400c80032401003000d400010300903d8103200380d4040703c140360090895100050621051094003580c07007407520b555541d0b42c1480c050b155138001d1003180030044950101c064480f4054803424000d005d18101414003007800700280a5030680360701e08a0501305880c0c52501d0789400d5400c1c0342d21602c016004a400701c200813011800007014030445420202041c0c05845080610b80500700c10352440302a801c00300003446045220308250781c08503010340706651515424017411418a0b00c10360744600180e45841517200d900c4607001c0d41c0c000030114000d007041080a5102a00c80e2078181c0240a40b00f01404400a419500c07014600461096190fa021511400d83d1a0280c4100490041403051100e81195512a540211092801900c983d001080214503140c011544902c004055503410b0050500020004090403994005071158001558480b1003480c241444e24481290210402c2000424080034900c01c000301c070744030380c0c0580e40541d581c2111103002005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 58324634 1250 58323384 58323389
    0x100b0a03150b0a3c0801051f0506040b07020d0305091009081e060406020d0b2205011d0402210f0f0d02010204030b0f07051306030504020909031305040203090a0f0804030b07050a0e120106 82
    0x1701d50070a410800c1d41c1c0f01003245642c0201402244200303032915a01070003200c0c0580e004180c0c000f4001c000c500b0251400410450070f0700d1003850309500d0314090308089030108018000744008148030b03c1c410300c0788510500c038551810070200000e00100ea040032a00307070756501c0070380701a206035400240c1b5682d8005035006202c0c0c80002408090440c2c01505500180d41100304c004801a4501000450300d000b21103000d0902c0308003e80c6120003901c4036003c01c88040300100c107244092200602011510000780220000c1d44486000b03891418400c2000394105012101c030041164030411062002401c641c06894001381051050f26695489440075126480390307480301c04e54105422400074080364181c0110384680e2017540c102c60152100ca810a03a40e014180c0d28207080150780e5414401c07424107a024551100d0390314121200c1c8801170719002842030340030b80d0607128410001000d0047c410300c0500c413504030b11503207005841d20340d000400810031030340501501d201d0f03205200185402c85094000c3c001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 58325884 1250 58324634 58324649
    0x503040c0509010602030c010e030a05070227010b07020a090b010203031305070801050a020a02190804140a17060403080f10030807060e01060602030a0311040503100b0a03150b0a3c 79
    0x1043d42c660703034040e503039070080c1021a03415070078090366620045020094650000c40e0b916000d08050b203960070010507034010828446200b52054241c82c100924104290090000078003583c8d42d05558014000421403580200f0041400c20507446903a9a0000c1201d5100913003031620703500a900c80c40c0c035908100d02c03039100d00d0f699820601848440d00369503005021801c595000c07511420304404041010703291618000e480c08a06000c10003006005e00c5401c409424000d000c0b000054548440711103400303d03004c007420350340d002030704001c101030300f00031402d4001800e0003800f212842e020400c0103103081c0e1400002e08090b0086001c80c104506900b01d4141c0001a074000e015054035100300954a0708414480f500180c10314411a00d051210b40031501520000b03005080704500c11000400601010500b09410103400d500000100e01d102c444040c44800c15080800e040000104014010307045030031101c42c01d80c0481d20511403040c0e885442507202100c0c004d4207054a0080d6450300104000c1d0300120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 58327134 1250 58325884 58325899
    0x301030c12050319200c0109030b0c0f040b03270307110609040509060402100906050306040c051308010203010e0f160e0112092603100b09040b100c060b060f0a0503040c05 75
    0x2c3e129900001040318801e80b0025200d0340c942400541c86d5140d80c01a00c0794040b5086110900c041416101c0e40e642c0610b4500c2d07000c3c0761640350018440c1d2907100d548140b02c141004811307c4190400750700c03c844e44000ca20382e4406038803455030399643c5030311603100c5c0102040079030f003018007241d21120180c40755200001c1040009141c00c45a0f25103c030f03011035040344512150103800c012203001d1482070040d98019038075141141d441c0011b03c40105036000005040c000c0505c00101c050b41c0401010f800b070040100090b850307500d042c170401d90b02100a090030350440302c04401c10000e060310056845010900c2d181030408042c9840041e500080030f102070f020840d0030020364905010f001d00b03c210481014049010405400840404d00d5010980d080441c03040d1200c410041c0d40d9501c0c001d032148401c010000901d10010500061203414034a00c0c1002048901c0800814005588030b02e00300110140c56a5140c0707108801400384030b100f9180b40300c0a01c480070010800f8009c250b0ba80c1d8018000162404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 58328384 1250 58327134 58327177
    0x30d020918010905160201051003200409030906030e0712020409020a0509090f060c04030b0f0712060e1504050103032a0203010204030803160c03080406052206021b01020301030c120503 81
    0x840244c00210340c01c03413800a555100d2044caa20520845100341d814600400700b0a007541d031144110903543c0d400040180710041c8148140c0c3c0c40788a99080e80f403207511481101807408038040c0503182d00102942035500410f6040064a041480b806042581100c00180c000d84501c00501c00b41041e401443d002003c0e041009481c280024280008080840c01c1712041c5d5645000f08007188541e020003028503140d80e010075003040510310311a0f049a190b0505c2420044d03403100d940200c68250b0711140790010080d007800b402d0f507003440d01078021190a980070b20003581161000340951503a600c299054016030311307106200415000c410001300382d00178000c0d0b580c0c0381d49080444403a0000d0707845040a003200c20075464082c0c040c1030500f11140d4941c0320418280c0c3e540d02d40c4001044001c0c42034140c80004500d580f540b240081e10200300a03c80ca0700140c035130011800e07416080e80e00e400562907580c410401030010900503006001102c4101d100820625080c0c0307455401d501404061020b05020001e08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 58329634 1250 58328384 58328399
    0x60c03020a030605040b0a0b07051c0f0e1806101101020c060f060604031e06020903150a06080f060402040b0102010209060a0c060f0204211707050a051b03030d02091801 74
    0x900c000724080c0d50500c04181c8400030002100e81c62280c0691004d40c0480402040d0314440140442c240180280c03451040d0141c11001040d590711a000d000038241508032111a40044d01c005544006448038407007415489000d21700c007140607225074801c05d00d05200b082020311a20500003c2c580b640c00964175400272240191b039800c419152030080e07007246000100c0c2814500180d400b10380e00649105c1081d05845000150160003000641e07801340c08210f0440b035038508215808054448001c8002580350407283c000c101c480355000380b00280c02009165241e40000912540c0080d0103c030300007000d008490050b402445940d902a0f0419804154005401c2c0c1002829621902401081c030a03c3e0b4103031103400485c41a4060818103d001055200108c280e0403060f91400c0c1c4a00807211142c1ca03000e003203460070340080381b040f60a40d004000250400c9030900440e0f003641c0c0310903c203010407100200000c0e2207001c2c40301002c0301c695001c64040c00c0f581c0d4503d661115124501070611240d6100e642 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 58330884 1250 58329634 58329637
    0xa1407081f1a041703090a0621020412030f020d021e010603170301080d031103010b0714030408240702071a120a0c03150b041203020109080a030518030309070b03070507060c0302 78
    0x9903013603c03641402035400e428408003c0b03074179001e4000c0448804504012080e07d6480019060081e00001c0e101c1e0311805110501c0248003403e00c00030f21420030030b003614009105a1403180c11f0340454000700d825985107500060071030305840c44001a40341c1d03401c9090929004212541c4081e181d0b00119074204444401030b0019030694014a040c1c42051440c0d00c8190166048455500c0380940704100400c4400c09007030181c002035216001102c9900515032075103203190800d40111309142c1110400b8a500141001c0e190801d0392401684205840c1a520194842089100307013100e00c054001140c0801c1c280403703e0b5107106d014840313101c190404030f0002004085054401010900d0151a0341c0c2c1800101000401c0701c1040c00018a4981400e090004040e50400d08409541d01c5072070140010315204080c0515030303140d580008640c9002d507034024042c0b0320442048516003040081c4041001c000c505c0d40c090f0f80d0015616035881d00c07032520464291045a401070150303840d200e090110309a0640 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 58332134 1250 58330884 58330889
    0xb09180d0302040b0d0504020409140c010e0312030105040902030f060c090405011e170316080729070c020d1e03020601090b0d060b03030714060a1407081f1a04 70
    0x1110000c41004405408a00ca24007075124050024004000081d0046c5c102a034007610150020400d90740598401d034541d00042040d00c000d41101c0c0d00c9000700c1d64000000100d00a00301c00501240d8208000a601484103014407809a81c4515046c415500d0402c050709030311102800b2540719184c9032000c01c407641c20055243d0322450620000103a142425521440b038071881c45012580c03249400f0395111803025404500150340003e1142a0a6508001d080c010304c500a000150b51501c4c00d2400d2484034081003135810014044c41185180b4442c441c4401e43d100205060854420344d181c0001850510b0481c80213207101c0010f5500c2540071030301ca0109080600c2a004c44a40e80d1f251151102a00c1c079040c2c100d904100ba400342c84001c10300d160032030100080080c0913a80fa0061684030185562840c0568074040d034000414084031b1405445210300103e10000180400d040c4100010039461020703148018024440310015002c02240e0031240c002c2500014218035102c210200c09626003061 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 58333384 1250 58332134 58332181
    0x80406050a0207051506011107080f070504060e0c0d06030f120306080613060207080903011104030c0b0307050301170f0f07060305010503030f03041202010608030a030207020f0d02030c0f040b09 85
    0x4408075500039118000d03149459400300c0034104a00d03c0484400b940c000090010341003160480611381c2c2c840c0184110f001514480c0040c0400c1307503188810740d103000c02c50f9004501032460060104280c5590343d40883d04895640b40480e583c62003103512030f024002c0c0e07400290020550b002c141003002580c0529400c401e4064805029103070303840142c039403079210031180500030388000d00000b80056041c0d030044c5102b902c284c0e1983c0c01e0101c80c101080c2152400c1998400c1c000e40040d081c0284144010a100240f1800d41100c1c82e41c60040c1c0300424900040c030030341c0760410010340111000d80c800d01803845449040d104036040003814241259036440c140c801c0101083c6004004581424080110b0ba64000344d03e00052854031540e0710b00a0880810075550b045560b620030204900b4414402040100d1042d40c1c0541c4503000c034010014114110704009121703110071649800185c0700400d10000c40e6404540310312811001201042c05085c1c0c101a2036801a141c0e410040c0d03030107241c0145040244507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 58334634 1250 58333384 58333391
    0x102040f031103010e030904110d05070c140d05040611210d0c0201020702030c0105160c0e070f080601020d05030903040f031b06050f070b0606091e010f09060e0d02040608060403080406 81
    0xb050500d400c840700035200c400150000c000900e0241041d8119078108100300503d00d141201c1941d002048440645242c0300103125119403101344584a103a416294200b88090326120000c0f00f0043c00c45d100c0d911031401407010707100000725002c3c82440460042021007800c07050070b640c000c8024400340d1003440790114142c900b81c038a000da01e1052003034a144036806030003440d4503200040191071981040d2408050124030700e0a2000060341481014020100400701b0743c1030382000b240180805154002030020800c0340010003680381c1c0c1c00281d0030516410350406a680b610703492062401c6105607040000c84641c100c00002c100004401780c50082e5080c08049200c0740d4840c4801c4905104650760003043d000244141400302e0440741c10103801880c02408245072034606000700d4861240000070740b8090000c0d0301106200d582107804511040c41c94603001000900b028030180940405c03014103800f800c140441da400319161503018a0141c141c6000701d030158546481c00824075103003105e0881e901800e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 58335884 1250 58334634 58334663
    0x50102070609030503030105150c070b0910030c0c230a230c220207020411070201030c020c011220040b04031a060d02040e0109150605010809030f0306090405010902030102040f03 78
    0x101d42c94500580364840040c52541c4d10340b40c100204210307010a0b17a014100104030107682000100409801801201480c5885541c2c02c2c08224040800c890307080241800c0154481c00d041d406005c9950580d48420107185030400d2405003400501c11039240000c5102d6042140c05000140c40d070003508116100c00d400380c260f0111a41516071142440d030035000300c0d064801d910911840507801034000c803a00001424800703190005010f031901c01d0002c0c0c8125200003990025543e0600032090240c0c0103000600704551030301d000a00c10b201d091030b801040c50f5034a10103003909032001c210804040040d5800750319a500e42c034940501e60311074402101d6201400d00c1c0352001c0503038122010311414004003908039000300364080c4006890000600c0c0ca0355561510580c001a01d1024003410070b40b1030700b0001400d541048000352081c00040c0090390300c1c3e80103100c2c8203000c81c40003040340d911203020754400450f80c4a82c600a03004d004a010000e40c954000700d400b08603c20300c2c2040104036805012243c80406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 58337134 1250 58335884 58335887
    0x71512060f0501050702060a020a062c060403021b04060b0a0f110d022e051501170f0402190902040902030609011d0604021602030304090f0c1106040209060d0602030a05010501020706 80
    0x42941c4103190204034117100b484054980080030300b0726241d050041c0c0c0d10070b81281d9140701c2100c18016880440d1001c000c1c012414040705002e036404000c0b800001c11907400e2585001e540c0307a80d1a90041e14603154110748107415280d0307400080052032522516900c81941140c0545000398540040001035107215041a102400003108000b101e8035030003a001e20100361800c0141e420440d20070b0880140c0c4424650492040d03842401e200b04000400030300c0d500c6110000618101504c0395a1447c0044141804201e850503010107400903811503c415243c2c8581030340000e0742c1c1160303000d100105d1010400194800f140d80040d48074000448032900c1ca40e0b2588a1510541412041010410307000800510141016801030108035030340c2c034240144040c0b590000e895603000d0341148039010303203842490844a03981d001d6004850b126007056120640229031199071800300600c060721408890011490903211b1481202000741c200205554078900101c112004d000700b845600c0c018402c5003000540b59 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 58338384 1250 58337134 58337159
    0x3304081b0a0309030201050a1e021005010906230a15020705030c0a0b0a1101020921010b0a0b07030e04020d0e0105040201020c090c04120218040308150604050a0902030907151206 78
    0x180c0d0b040e01c0700d41400d03046400440d06030700700242e000c09112a00c0070010006c001c0c0442d03800e28854030350003040080c66402c009000e460303040c0d02103462103060030014040709811420308100e11002c0c1404403a84042180011002c003030561121000c2050030b00030050f01980803460328240d400581c00c179606814140107108102015206001c80000c0070303c4038178905071081000014840c000d000140c107041086001810103c401f4400800c00c00d10b0203541003010030300f07001d0110100707004c035105800b0918004800c034541c400c41100408008106d12070920955139036058403c640c951075004c0280c0401d88000078000d1500f1345041e030162040130284001403402701e017682d10a100c02d01405090903d0280d1010341408070701401c9038482e0304c070808405a243d00000e440e2140340242d8400c3d890b0b00307004407100c090303401502d1064094141000140103644542c8100000c0b40ca20420050343c998564240d00e04000b0180c119081c41e821003250b2079562917020900c203420ba003811001700306490381c515114006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 58339634 1250 58338384 58338403
    0x2090708090d05040b1b010e03030a020a090801020306030c010c080d0203010b071428050a0f050c0a08010b09060904240c021006030c061110020c0102180907023304081b 74
    0x9000410004524600940081c0d500c0c03080c20b400802c01d0808daa894078216002202d2101c81158045071a07000143d100c0040401055401c00843c6035083c020007280e152948001c015062140d858900010018a030044841102940104548a503100e00041d0150f9115100585043c0c00100248280c4000850420003d844040c24100e00512140c014401c560480383d0690f0203010380300500000c240e0383d000c032a8001e8851000b60050301c0030002003240382d500c40d130400d00d81c680c13410800ac2d9035030312182d42d0310741c0180c400c070381213103060b583c900c3c0203511a5584101e48d24102500062000641c0c0e03035801031001c1c2c0d01c158003920401180c0181c0700707040300c1a40c0b202030305126810604101c428015038010b4000d6104200350781d0082c01909102c026603114140c80e4110303a5000402d136000d40003102c0c0709583e0040407211a020b1b4140b0f410003d5652600e5070805241c1e800e44d498240d040a04c54000340481000b0b13100704040c0c2c1c075190038040311b076401c4846007070011601c031080700c89a105c6c0458848030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 58340884 1250 58339634 58339649
    0x1b01031406040f061a190203043002060a02010c0201060b070804050409060b120c030706030c02060601080a020c0a15060909020112090302011419060603022a070302090708090d0504 79
    0x8241e44110420000d441c0c070b042044022542c0700000710312016000b510021941220644507600c0703001e01c0c0c0d03c03240240450401d0301150010701041c011201d070400da041104040000071b190070030658661100a4400e032074020351051001078013110181c1c041d0841d440c415865002040015a29102202540305180c8024840d46040005000c14a4a5844507071114012034000565401c440080351141000d8504040715a104500d8164030349020000000904098601030002c56400c6801943d1040007618075818026088009429141c081c0d042d42c5155009030301b02d41c4408940d0034408a124031103102400c20b5410098007281c04407241c01011000790303041c2c4d108003500d800224401300a120441c030450440d5210b4214101060240d503015010700011400c803141011030894120031035030560301520078140140800c80030503602d0000c41c3c14512080c4503130826905c908050034101451034000a500c07000f290280b040c042d5014500511600c51501152602c1c003000e502a45c1d5806144500380 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 58342134 1250 58340884 58340921
    0xc011202160219180b010e010806010c0503040f0602060c0403050312040807150203010518060901270c020f0d0c08071401020c06011512090f260403051b0103 69
    0x2962080d40c02020040e041e128015480c0c9125400a81803607564240104180003401c000d10400c08407034410900b61040392000c101400c1e0f1030001905c420070074070415043c00791200010b58a03074080c005001c0d9155010040c1c13030703a5a4682100c443d240c0c405009400041c03181c107000403420360503c01285c0075a1b030040b0042d8100301d8044043c518102c0c0c010f00031035480c1e40500034500020001c2c40401c2080c0340b5103034050703125030421007440402d80c01a04000365990000b8184412a121100034a055550b020405c2c10f0040340d2843c046100d280f00c80c0d11b1000c00d072802087c046a19030210b803414840c5120000da84144030220000c40c0c1a0500000c00707450402c003007150000082d468881c038115141c4010016042c211082c002605060b07090b4843d16040401e542414a50f50f4000c07a04044039000183c02c10441045c0d844004004c24845002000c02194104071190712840c14024202d00001c1d4450582c1c50f41c492901c651034020421610001c0d1480744562f003c198041c4c0100d46e94030b0700b14040391 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 58343384 1250 58342134 58342157
    0x6091d18031917060105070c0905150306090606190806011806050607060c0e040e07030b070905120703020120030307030906020904060b040302090601050301060c030c0303060b070302060907080c01 86
    0x45040403a124208205403000b00004046440c1a45a407402884141c0301d0f414a00704a40d0120424900144000e0410804011520018070034110003801c0d949510000641903035070301c030000d04400c90321508642c148101380400c145d0031340001e0a113108520503030b90104050002407140180e8903540c0900d041b640c00802c014049003803064008032a4070547c070804620300c8c0c0d6070004918140d0201105444e040e858509a1b10583d03044581c1d07407242c1c041614104040c0a441603c4c40e1180224000145481c1c100e40c0402c40d8640711b06d0900c005000c0040050301802e261689130303907450310b2031b100c200e011443d080c10107c1090f0940c00c00381c24025a80014615640d40e40c00c00301c009110075602122100d6082c09030006640b9641300d418040c1c0303610611142c0d1f41e8118010003804040c010700c2e00741004420001409125170100e49a8071441c0d244c1080c1d41100c55518003a4082c0c051604124440e0070045510028075500041003409840781c4400d941c0080c0d00c4005042e1036020550070310340072030507030b4070304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 58344634 1250 58343384 58343401
    0xc050318011b080306041a060f180406171c0e1c06020c0102090a0902040f0e0408090603160f09050105091002070918020108090105071b08121006091d 66
    0x410540d014074000c1050707600e10626040000880c4001d8494503000710401c001400e05200c0c013020016200740906058a404000811034442d40000d200049008030f4a0404050740d29015122071030300400c28011640c41d018014186000069192120b200b01a071181d15042181c024034101015039896442c4507200e601404203009440841001658195007240d011410f180301400e0b14410000001d80e8031110101080241607064000c0d41d0050300c104810482504403c503070101300c07214080f8062840da65402d01105038010080b0040d04070b00c000003044048005500144260030254440c01149107900008450000c1d580c01501d005c42c02c01c0020070141d2900310041c554001d21031044541c540e8032085100195203110003000d03843d84d00024460219030b0070a80c1d21740c2c0000890003c101501e0100c40081c20b080300d0101c5480c0140300707022360703906101b00c8070112283ca001d1115803408500302030700a0030f44a4114032501000402d4041c0c046210400816a802c8013210410400b40c2911550300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 58345884 1250 58344634 58344667
    0xa0206070b0f0a1505061b0114010f1710090f0c0305010f0f020a09091a120604051213050d020105070614040501111606150f03030306090c1e140d060906150c0503 71
    0x140381151f0a0a03c03000104400f402100074041a45000e000c2c80e52500c5031f00320105016400007030a4001a0780d103540800c100144007107942d0345140001c00c21105a003058a103c4003054006009098140c0021040c864150448103210b805100c041000c1c2418107980300490080114140000790111420082102d00d034005103100e158a000c0c80144581c2070b800113001030500c40d017080c1207070044030802082c0722013070244138200b4944400a91a02e0120a0400700d0b180c0c640c0a01803094840d4060041964440c109035113445030b0108080008107105d50740403a146008070f034100c80540c01c3c00c000700d4419142a05a40c1d8015161000d80c240d04600d582d8034000d08504041c0080c050740c1d24800060300303c1110440740066019450000d0130b04d05146849080e5810240c0d00f0b000d01240442c01081880355414090000c030952030b10b4036140f10a040f100c6400e100b8a00d403010f00074102130005c130704410194007aa0440e00014001e02d8501024802036505450403d0302030403039007040c080103111290008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 58347134 1250 58345884 58345897
    0x617070e1f050f0c01050a0e0c090408070804030c09050405070501030608030a0309060b1507050106091803050c0c0405090114090d1e030905030304030905100e10030c020a0206070b0f0a150506 84
    0x240b49040c100046074840050b00304802024030303a91034005104031142e0f5440743d070b00300350140c4014000c421000c00c041034003003c0c09000203009000c002110024051500c00b681d01542e40011911204daa80340360682c060031050300c05842c1703802100800a003541c00380c4101c5003122000d0b00a103081901c0380e00250018070600c103090b030300c1ca9121001d83d000d540e600c4000664600150030310301d4441091341800ea003162800e030008160741b45410603105c08154508070034245160b01d490600c1d901c3c0b00c03424034181480800f40001ea00141070609014540d50103420201000142c550f0100c5580d5981360110ba94800c1103031b000001c107403004030384080c001001080d19140c80850401061080540c1d513054615801202e007507001404212040c800c625017810f180c5200e030030510b4815400104200003034204200c00b0020700074560fa400000d5401d5000307020941c2e16540007440b19844000324180000d003980c00b00da403ea0060700d4140011122101ea100e1400c20040030101c0c456810f08003410b0200c20751104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 58348384 1250 58347134 58347137
    0x606080a150e0403031d010b01120506040f05070203190e09010b0901090b0708030a0f020a0206060f010309050604060203071e0507060207150f0606020c0607050c0d110303040617070e1f 81
    0x1d40c408214a5488980540120710954001404418110101290701c0002030313040c0c40b0341d040021201e0707641e910440005480301d4241c00002d4035200c4100141c01020002082040c841c2400708000c0c1240c2c0201c05008200e6094203014032200700032500300d50000e039500b40107600c00340b0b0364010301440280c803024001404060500c450084e03100c261a01241d080450101e500540000c2085122035003030203110741c2c1065140c3c0640c10a4140f50010351101c80003052940540403540e080c203000d070f00c00d41051000503040300c10b030741e86801c080c00c154020754021140350700801c1280f40100204a00e0201070141c4100c160749407400c0026564a00000e0740c002c80040e11401c0d60702000c021002e8907441501c983e21181175001801a10f030050103030034400c112038458883c100601c248004904003080280f2101003c48501e60400544e19010901d100c3d248011070309488040750215005410240112803840f1074241710074241c4c3d8011085902c0c022110101e80c110030100301da640c9003a140404c04880b1b0150303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 58349634 1250 58348384 58348421
    0x307050a08070606080304090213090c0c3201020c07050907090e1b0a020a05010e12040b07020406090212090f0604031403060a1a07150204080a0305070807060504030917010606080a 79
    0x180d070381d2141b45400035000309150302d50000e036600000501800f6000200320202041c800080307030100140c14403800780c01c00740503519510b010011034840c04810640c00c0c0340d401d9444241700401c1992034000c1d0007190340c001e042d21074000d004c01c151410894062142c412a80c4405955080c00811070040c0b00242401c2002c518208071180100725001c05441c401e40c5507401069103040c1c80c1419425190500c00c844215080800181141c0030791908860a03500c030f060515540d0301c2144003090051890313070302c940e40251010400118040100200b5400340d6415002c9807450803034491806d131142070666008011451070310180e070f480740d114809154010700c000c0080c01c40c140d03900898980d4110480343c0c0c180c507800005a0f48204060b242c003405440800130021402c0500300000182c4d80c10790301d44040c0034490701241070010000300034211090305030700c04000c5c002030625207405070801c030003405400006400401a0881c201c01403040c14101d0b890703a82c51911544451a040c002051240c0741041034006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 58350884 1250 58349634 58349639
    0x50d1803050a08030406050a050c030a020a0c0b0112021206070e040b010c1b170105040c03020d02030a080c060105090702010e07051c020301020c0d0311040b071203020c150411030307050a08070606 86
    0x7420b0040d010610f0282d842036640307180501d4440e00300c982c0109140740311482d02c001e202100101c1000c0c5c907407046c0c4140780180d0b22045003105849080b080000100007191800006c18441c080740250159113209032000e181c42042c109103d42c466404031480b40006881c02040712841c1b40c20b401644882c9410304208844403200c1d00c50802c0c5403644c079045846410030000c00c100c8442043c8280c001221403500030030850819a0320720840034510f2001134498040e08109405541d02400740405899002d188540d40d8034024007010f403100300902c01c103403040340c850001601550060103110200b225000c050b000c02030600e02000f0036001c07810108418600038505550041c0c034248000c04c40001c0f80030042c0300441c1d088000906450050106040f0340000703010810100210605462a565120140181e4082550012002809500710700113051003044040c164215a082c00c49004038026204004103049450506540717210311503008103294404e011800c082202a0040d2804074070a01003c80c0895 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 58352134 1250 58350884 58350893
    0x405040e0a0309060f170702010e03030a0b0a12020f090411041109041503020a030303050c0d11090315060a030b090a0b042d0c180b03030a0203041d04050d1803 70
    0x8424429810695100201e680281034000d12203600501c880d2400c10250035100c078006081c034007001066213103884041c0101c3e0307001d8001e410000407030003030200712078403440c20388050806480329500c00d50141c2c410202c080f44142c074a0014018054000d460161000109020704c00950001442074951002809031000d55540d98010b200d00500e42c80c41071500c581d1410100002c480e074000000d00182d41c400e01c03c00040e21940f04480c122901030400150b5a99606090861441020352503407440385809520440b4125541c0941a603103002d80803188170724941e84c00821545010b540c03460384000c00307070410800141303260240c0307900210403c10f40300659401c1c0d4a20403104010b5900f01c81c68100b203181c0203401c51004185018030340102c1039000314099907485051140240e4081c40400390601d09203000090203135081741c41101809422280d41d1181128001c0d1650820302411920401d0b040703544041c865844610b074000e94014015100110034450700b51140b44030a288070314040050180000401d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 58353384 1250 58352134 58352141
    0x4060c0303240509060d23011b080a0509061005060c010f0e060601020615010e01030903111e0c1503070c0309030c060306030303050606030405060117070e130201030c050c0604020411040504 83
    0x150031421408030701c3c2c10f020810164440041800c0e02401c0c0b5044c90101252000c0208440c2c4038500c1a242d036003140d0300010a01401c1302104040002112140d500c035a2688140e01c54400c2041c07003401c0010f41c03103510055850300f0041d240c1c040b12188012040c0514507009004196442c4802c0c0005100340c440750b541c005036a441140503a080c1c00040c200308281d601881442da003c0381481e421509c121401c40042c110661240f1240d0400d50341c0c0381100c04040c000c080503840c2c05c0588040b40d120120401c15242c0d0381da015880d001082c01080c01c4a40642403049065003d0129600680c0c190340d0380180460b807015038414158108212802e00001155401c40f17004080d100981c0c1c041400390a41c01c02034155000035000d240102d00400420022407000700d001415074440d40c0310392050042c00110903140c591660442c10341c02d0301070402c2c00080d64560f081900c0180c400c0c2c9080c481c0043d491415506401200c222045a03000310001a0062909a00040710700705d0101000382003070785442c0828100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 58354634 1250 58353384 58353431
    0xb1e01090209040b0109030b0f10030209040b06030d1b080a0203160c05040606050c030702040c11010612050f0a080414031c020303070e030601080a02040504140105042a0b04060c0303 80
    0x55940050070030060700f0107000d000049002800d0881c0c4041ca940c0c0e0b8051580e00c01040100c40c0d070380c1c503000300d12846104c3c5002c03001103400070f000c504103007842c1c14034000c035038001d581c4503211f845a0b00b09a0300440c0200c01019200314050003130082d0000b08d448400040d4050a1600110f020401c03c801400c080901c1904105000e0a211036803a400e200030303c400c03242150007082c1800000c0c40640300400c800401c0b0b654696058601144503c0c0441d020360b20709602c1c1c004840c0725400d01078085030400514030090401da003e0710844416600f2a01d245440e1401080082c100c0d410400c1b050000c55180c00e60480e4403103000c0d0844d00b112502812850308003000e0038511006800000074000c40543c045e003002251001100500f0300343d40b5160302c0315542c03074041e0300c028060703901c4000042c180071035440c0040d61039141d08000c0c0828a45417900707001800d46090383c0e0115204030482410100704500b60303007081d10350707031004649400e0601d9410748001260312821801c0645694013504400000c5030304605 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 58355884 1250 58354634 58354649
    0xa030f0503071101050403120c0615080309040609092303040b0d0507020c01031a0d080c010504060605100314071b140706030e0604050601050108100e040b060108220b1e01 75
    0x480315124545078110740c1c01c91240d1030405c40207020910118100040b55a4910094148a4119042c40c030384080540602c41d010103010800c040005182d00020005000c1410204c07010840030303071034031054001c491030500058945042c1280b50100102d44108802e56a040541160306183c4d6542e42c40c2030b10751205a80003840c5032502c06104e8035036010000340501c1142421306000219070315820343c074146543d40f0b46a209003040c006050a00c0720072000c40308840702c3c8400a2202e071925041040140070144550303402100340c0710b540300d52148a441030055108070b070b40c1d6044c1d042d00c406508480c050b003811804002c4540c0c007519580021006003c000b0340003941c4014003401860104080c0031144030390301e14005070f000075081100061000c220b00c5d0545100f400d00d5056502e03101410405082960030010000041d002170100b0302c0302681840c0d10600d4241d2b101310190f07550344d00c40212101b003a0089080c041459040e01e0000d0014802e00f9032007041c0c10107045080d83c0101c5100c0c010082a0711122 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 58357134 1250 58355884 58355887
    0x40905090703110609130b0105041205010e0c0108090d08070e040c0305040b0603030c030409090503040e09010f15080a11040b030d05030906010b0307080112020609132c030a0e0a030f0503 82
    0x410040c9400001c40703005011212241041181000b041c0c1e40441b8076600c240300c5590314904a0141c3c091000c0e00c4c060000c144400000c002c503450114000e144120b42c40a042c0300d60a0000300540c401c2c141684a11000800360140e41c20304201950501000b91820341800b91114003222551124825a4003600d40d550b0080b40c681010306014018000152115000f42c01c1008194260300e400022a03041b900c668500203981c0015013801411400781e80c00c5940c41c0c40144007808241e032015045004d201c281480100107202031040c04ca19000b4062250761481d0b0003091400c004100d400c980d0a40307400300500041042801500003d040030b480c3d5510001080c004001e01c0443d01c0c04000e064050305001040e43d01d98200800c000d84007400511504010341408280b00046485a8081d6091040d01510394074212103180410340181240c0c3c640c2e0140b08140c0200500c54403840b1054542e2455014051450318041d0141202c051031101881500001c9000300000000c0b0030302c4041c010240194080c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 58358384 1250 58357134 58357139
    0x50a020103050105041a09060d0203010203090303010807050105070210030c0903050f0706030506090124111207110a0308030a0b0301020702090106020f0d03060e07030f0e0a05010204050406060305010e0406050603030409050907 99
    0x90200e40381070308854015840d001b40c06851040b40b0320140494003040301c6d01622681d0711000a440c0d184083d0000750194004401d01c000d1600000145041c0d406400a981e80f1350b46500045400c2e0140741400307980018480000c2e00074034041d6002406041c1e0740d14003c3c46141d16034680610305901c200b10140c0325031009600b00300031589445401d412840032a2004e034035516020419001c02407101c41c01c881410314200c00c1414500800d49240e017004000c0c240d580c0c08040c003241c5045c50304000c0c801c0c1d84100040d954083c45240440600081e030780c0c0504070506548a8200d01e6009100c991402c54040d0344c200014400b59450700c241e14000c1c082035000f0708000a0b96a245c40c28080d118450f10145820f25000740072040c004c0d00801d40c0444203140004215141850b8200a0075950030407045901074520312909000e0190000c0040d41e0040c0e5003400b102d40e482e107040b42210024462461840b188002050002d14143c11075500454024200e82c10540c80302030752001c8400a44c0c010398142d00c0403208 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 58359634 1250 58358384 58358387
    0xd0c06050319020412020f0d0b0403090311010f080a0509150108010207020f0604030b07030b13051e2404020c1c030203090c061602010f02071a0c060112050a0f02010c020607050a0201 80
    0x5220b41652110040d800c091400c0c0c2d0f4101030039125000203108600101c29841c0c40d4880d10f00380b04040d900011b160702c00d8100342c00c02815a003285d000030760300e00440c2081c03080e8650184a610200d042d0345d903541819542d401c0d80000080801904400c00750041c507001d1620000803000c007038007911149000690707a410030300c1044a0f090701039100c0c900510050108101045413991082d600150704d04000c10b58029040019129030740034104011503074a44800c0c085507106101d21704686c02c02c000c24803030991302c0300c1520f200014030200c1c40c0000080c500301450803904041e005030041c100050708640100b550760079102500d80c0c20b181960000f95000c800c00801c070100f0003001400d0441596060703e810800707810008400600130b40039040c0184078600c4500f9a108005c0c0c44002d01c404061405c2035804418109250350190720b0041e95849104008282d40b54902101d582c4190301c8401480c0b0103800d5607600140b02e80401060741489000e0300d0300409138071454001c002c464401c501814010580d03200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 58360884 1250 58359634 58359661
    0x90d0308010905090106050a031205090603010308120601050c0d0c052407021b010c0201050c0f0d2006071b26040e070806010806060f0c01090c03140d1403060d0c060503 74
    0x24002d44d40c0e04000b010051500d0f028452410749400c03031000f10410f50710402c1900c2512500b0041500400000b0001040c00441d4000c0c01100c03001c6c42c2001c0b21901c400c00115014007032041d5104240e00401101200d040c081c1c85010080c9220301301f03460b05650300440200c6280c0e10a162412202e41030000c00001d05d43c107000700a1502d4280c40512600c0310f8020000300815034414009042c0040010544013245040000e9406012910221402001c0040c1c0003400000002c4084100300c180301c09940c04c0003008501240700e0140c5650f43e0b101d140084110709041480c80a040d2401841c80c2201526050003001c01201020398580f89030307039980340c0000001110030080554027001000380c1809640e0b0f0b03004e00f0700c1d40c06c000c1c1204d8664039070251070aa26503901c2100c00f409203039868500040b00304106244807100301c070300030070f040308041a0814506490306080860340c4002007148034001190700489000d0b5402003000f4000c181c0a18041e07032284490101a00a42d0100702e01000300b091705e0544a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 58362134 1250 58360884 58360891
    0xc0f1b081c050405010f02010b03100f1103010e0c160609050a0c08060702060c130506040f090b01140313230a0c0603020708040302060702030a0b010e01080105160c02090903090d0308010905 83
    0x50755400c1d81c0c00740100400c0d90055020300c80c100809071501080c198030035001424001130040540b00101020000f2000070304101f5800034101c3e0402142c04605d11824080e03134100c4101c404060410b5550107144035440e4010200001c0a202c100101004100144154189988280d004104c4103c560500030030602c484c0d803240c034155103c20b00700401d0590200d032540e000300055410548030301c1c1c044c5030503240e03020981105401c9103000c02e002580011080c2d00d00d01711048654100f100c00c6510004545105104030b00f1200c0030b00070004265001c00720416810344034000c5d07000c0c840328201c50a11f0130050300c4861721280745900c0168844140480d8000180c000c02c043d05003146042c08517940e454050083d031001070701c1110082814015501c05004c0c602e850f82d0700c410003114a45e110f0300481e039850401e02032403c082d072810001403140300d95110b0801c0401000e844941100a05600b00b00c20b45c100209002d000f800140006c00d42911130040307801915103c0d4980c00034543c1803d09080031070307000a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 58363384 1250 58362134 58362163
    0x5130501050f090603010f0e0109020f030a0803070c0203032b050610021906060b030106020f01060519030605061201020a02010204081c0503041502090a0605070204050a050c03070c0f1b08 82
    0x240041060360346900c4070381200712040e581440e4683e80d24000038010702c1a2606d42050a0030701c5c41120600206500c5444005d1003294036000091006092580cad03041c034035000030204001000441d45480c011000d0030b4035a81300904991070115000c0c00002c2c5000a22416801d190700030081d121104011302807558018000d4552507050315510b40020b6032032140c581c0040306d003540c5401c81402d0124a40210000c0c000c440c0d040d0307a8950b582e43d03000350faa8080055801e825449d0250100766441c001680c3c412480b9100f0180348124156104c21000700000340c001640716503100362182d80c4031400e002a010141990700016215480c191040b030a20701194021040601d880e5441c40c1c0b1b642d04442565006500305440381500305001e19608000e01c83c00b00d01d20350080b0340030400a116540640200303e018802c0d5410302090300c0d588681c40c1a9001501c903010011411700004404500c60b0345c1d1241080e00850030b10140e440d490301d62402c8100701003410002054003520a10000307000b084804a40700c440c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 58364634 1250 58363384 58363391
    0x100501090b030f0d030902030f0a0305070308150609040c11010501061101060801140c09011403010306050403031109010c0201050d09020d0c05010201050108030f040905071707021b060403020a030807030311040b040513 95
    0x10b6043c558035082c24107800401e06607036124503400d40d102003100c032420a6500d0104c5001030814180940750360099101240007070070220005880c01c1c0a401c007021124009810f4608045000c420070002d08000e44a103020800c41501403001c0c41d03401d00070b05000313098544841d0b0025031254001425901a50049400c583c10001d6007a03103483c071580600e41c49450b039a802c2d0b03184e8000d080100c82c2c10044804402c07141308084004800d21141c0d5000c0e0340524840e0328100000607002d03400d02c4550040c29003940c00300705425180009540a540103180c64013140000140a40c0c0f01d900141c20a140c104003960350307208580085c081542c09114070f601414440e00294244540d56411903076502c1280610602e5984070030114901c1070007140459109015500100801e20b450800203640b082150008210044200d81e400030324241841100c0a0701e4020b04110441400d41d02c40103429405080210101030b51900050384041d81c42000c1c0014207469088203a40d41c1c508003c100c1c0700c010580d408114680b8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 58365884 1250 58364634 58364653
    0x613051b01020a060506030309060a08090115140d0c080109080d0b010e09011202010314041b06090f0b0f0c0118201e0f040e24040506060d050a0203100501090b03 71
    0x2c0000e245441d0680c01400890f113035807540e02081c10b41c0200421b0541240c8003181949109800000f0709100c0c50610340200400f2200180c1006000b8481c890784040041c9800e00724000d040c07054003070003450300400c0e00d80860b95a4110072401c5594a40068482d8800031031005401c08943c0a1491141c00c241781480f0200700c280001443d86da41880740c084c0301459451401e08590007604850f8254038441d1550649213090b0600d0400d0303600800d0702c1c040d0106160000710b60035001719449070990b40070342904100d4a0070708084182941c000d0035240484030051004c00040d060901079901c0412006060800740d070780505d0105407041072400e403c0c4110b58218501c00b2540c982d000b003c07043d0400015075044054030600070950703070700840141a402c181010264407070280c0c0050341480a500424198131824110f200d503c201203002e0720020300d40d40219010503201d1400c0000c98003201d00410036a0440403490b030004e13162034600320003d05601d485600400c43d1100d24402c03001c0e41f084c142d014240060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 58367134 1250 58365884 58365887
    0x3060806091e0109020409030306031e110402070f05070603020c12030c0f2208030a020d140901112406041b080f180304030b0105120d0c0b07110613051b01 68
    0x140c0030300e42158290300c0502c491100e80342500504502078001e0300800c044091802d000340944241d020599000d1380300c00140f00030a4a40140c100029004000c0320228000c150400c006540800350070307951b8200c0c070003003480410020310188005240c2c07910016515482c0d4030005060105800c42c1c01650b5100303104001c0202015002c881d8568401c1c1034141d03071900c4041008810022110390501711000e012004603503e0000001000c000c0010307021200c0800523030000b00c400943c10070002c0c040d01d9003441414400e501400320300e00300b86440800c0d81e207030a541455914600000c00050302c0e0b040007040038402c440c20184a902003010f00349203540b1100c0d101101c05040c0c034501400255440115500040c02008003804041d511908007090341d07600c980e030303040c103820300301e401e010303151181203244c0f400b0440440000313002369a1041a02e6000e440252903c404180c100001c01c900103210500d10204810002408003900c2000328941006140340303907090262400c041100751642c0207002208486090307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 58368384 1250 58367134 58367143
    0x90604050a0609172101090b06180604030b0906040c060e0603040b0c040f03080409050a0e0d0509010309021f1106070512090a02040c0807120b0f0409110a06020703030306080609 78
    0x560001d40229051400f0b241004107111030030700009a811010910307686050424000031601d1340b9403045d442003a41c030717030104d00c1c1180c07210038103d41e004200b0400b91021000240074241d0f012030042c641400c00740d4984503100c0d00c600c1200c0841c03845c2c000d0301c2040708100c50800d0050141180d4071307009202c40001000f140c0e00f8440604041c00b041d1103200043c001c4019401100c000e81034041070b034980745d5a80c0c9411a426001405010f036850308140003e441d11100b03110b208039080c841c83c020950b86041000685183e03010307a04031810152140052400760700c8400006040c44958a09611251102c410041250109070f844200750f811090901641c69440004e68160700c2c0355181509a40e22442842c600c0d200590000a421904007190b040400e604070702d03150312400007030703c070540c4600c0b04860b042d04072405198240d50200c80809500500d04140d803003607041501c030340025682da030800300c001854503100e5070100300107a106100074410542c1c03600400000b04025070081660b410814006602c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 58369634 1250 58368384 58368403
    0x9050d02060711060d0e0106090c0207030305071106030f0105010305180c21011a03060c04030f0f020112090b0a0e06010e0c0a0203270a0b0309060c031b0c03070b09060405 75
    0x301000710340b400074808006103001111400500c916580d0039034501da040501305110060304103518090300011218541e00820380032001680c0a0700380300d401c40d80c040d61326400c00300042d1019054502d100c8056200c9800030340c0070f040e202e0900383c800e600d0080010f0a5030790003440403035800b8003a0041c84e20000005500c1e0700c00d403000c0b1411111082060307541001c000b502060188a9801c01140300e80c3c00e040b860341000851801c0e41614919616090641c1c124401d0384002081343d0903c00f00c00c5c011903c0d1554400400d0310500d884400c5420400300b03003059690788401902d5140c0c1c00700510910307640e1840392104103011500074222030f40c54008410320a0000401d42080d200001844080f44c520920440e8030914942141080b4042010318a205644052081500981c0e5440b00851300c00082015240b00b40b884800502c0540e0750715619004a400c0500801101e0046103601c03c083c841c401c0291440a40c0341e070040d5100d01090506042103580600b0701c010b00d400440c06c0c0303c0490b1000c039801c44d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 58370884 1250 58369634 58369639
    0x3030702210f1506011b05060c03151f0207052e260108070e010e0711031314040f0c05180604090c08040506180304090e0a050102040b070c0609050d02 66
    0x2a109551020541041c404110411990044001d001c030041c42e4070035444e00888080c0c0e1010b542c10080e2a0b5804108184000600030354441c0b0009a001001c0c50001c6500c0002000324846032422130000c07459800704070300003008086a4030314804a1a0303040056400070401110480400003447d1182c036803140d403c1220380704c04004800c031001024000c1120200240c4142110a024615840d07440560242030081c032000340640b500000340314144d804501e0503980c0844a811795512801c0c1e060721804025480c81ca0030740014004e07042c1d180540a141c500a00f094180d8010414110301000126001e80c902c40d500700d0310704400103810395030150550340103240240d024038040038882c00041c0580a20792010790641c1c1402d504006441e40403810500a51048080b100c3c2516000c0d01c41400c48401407a40d002640140300030044c48059400c055902110780065032000002e076140d5909a1340f007504029501e13100015440108a910700d100002000a85000c4003102e0070a000141404180c076800307031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 58372134 1250 58370884 58370929
    0x203030c1e041e0303090b1218070305030f22080c010c0309090507170601030902090601050d020c0d05090112051003030c020f0909010b03010b090f16050c070f030c0503030702 77
    0xc0c4030910001154007420300003c0b03405104180a900c58803124550004030b00180c0f040400042500c3c0c404255001d2106007420074076240d8405080c2641c8a02221001180c1d100390000040031480500c010684441c0213100d007542c51030000384990440300c2580c1046940c600280041142d000041211321480c1070910b00240e520610342421039041c2d18580006a6191801003400302450301f00b424160319900e00b550b545410742e902801901100d101075806500454041c00140306984200b0003441000340d601001400e144107141842d2a0130b07013a01d034120100d50f000543c09103540c0c2050100d402640a02d100b80420316000200d03502012451000a003400051000c450031951609124050000054040c0040b80b0340070f9521400307040f98600e15802035217071090031085800d00d0002148074240780c2c201c40506848007162090030b11a50fa42c140b0400900f446141110802030003e080185002015010442d0443c2005c801c1c454448e84a81e101703520404c041c034010f80302c09124000c2e07900c81c03100c02c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 58373384 1250 58372134 58372177
    0x705030307060216060f1e0b0a03080c0102161103070b0c03040504110c0f0d08010b04061407050106030506011e090204050102250b042607050303030a023a0b010203030c 74
    0x51131940340940204220b0414000006003c62036200c181d0f10400880c56800c50792001080c80308481c1c0c10101c5581202d40300b882440031486580007817550fa2000000145804913980d40703644201e084403821078803d10080e0202c0d10a207002c000660107004c0040d0007514200906816995a10661040c507028907220300e0415149911041540c4103010240103541ca942081d40b4010346a90304c07103003480080394895001042e031002c8082601d058802070f48440005102203e6008219040303550300315110340d262100400007400901c400da0003012203041703030b180340514541c2c100300c540d103980c2040910900c10b0208000d00d030b034009a040c000c41864010700d800d810b444200118044026081140e40729000100010030004441c0e00c005103035110340080d00691801009181c88071007a00c2215410303402440807404c08030295000340314010a44004258a07004005a242c0d1065450b954135001404c14171350314400e02d5140a100201c580900c00303540341d480c3c070a5051455004418509031010f6034483d94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 58374634 1250 58373384 58373407
    0x5010201020310410a0609060c0209060f04020714011b0e0904050109060513021201090807380402030f010c020717070504050a020a0f0c021309050c0904030807020d0207050303070602 80
    0x418201c030110500d00c1d440001a140e41c4ca04100d0a001405000c103003c0c0020154410340404058a600d031742c0705006107009808002c1c600b0805004070307512040030040d001c0c9954940c4010070005100d4840f10822a1100d8000c6085a450784079407001e0b50501030510745c59a40c007144444401ca000c032102c3e001500c075410400d005080344140144800d29000c2031085500210055500700c9100304c0302c254800c4d1145030110700b0380e08822001400210f05002c00710004050000508910040040c480420a8075204201d01c203201c111003a15000140420f02c819401c0038008544440d403034400a220600f9a450b00075601c07401c1c2d10649075440c0740d0503484030f4920014880c5c903005042c010814440d50400948440c001e51000c1101008a566a45420f003150701603411605000d03001001d4200b16080907048a0250100c4002180c090065005003c01a43d84c02d003c24000e60290b038480c8002d02d012040a1f00d03000c5590030f40390555000d401c003000190f400000300d500d00c550100001d1386509a0911 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 58375884 1250 58374634 58374689
    0x9060306150f18030b011505070803070e0d0501050c070605010902120601050a090e0f01081c020c0d1e0c0e0912030a0902040b0a0602030d060501080108030a140f0c01050f0105010201020310 83
    0x100e8201c003043d103400014046084400c5040e00c0001183c0314070700000b5074040c0c1d02d5100780c140013081d000040c0700048030a80602140c0005c4030016100d6072001c1c07426900d031401c444040f0741000e03804a010840000340031645c0b01780c9014020000c400c40c80e0494820708481c003c10020100350420000081d804201fa120307040c5503005140e20b405001142c104111008941e200901400c0a40d119416070042e901c9142a070b0601110706580162041e00450b005200d9041014031081d41c081000f4101e01455421401544010034084c007801c010b468248145462821405010516280d1101e10301c12003003288039080302d410403001c60000400428a00c003050203080303607030541d0b0742c0002580800280150084024024030134542810003025455000641d070304c070000e00600101c1d6101703209012a190040c1c00c00911200300011442c00d040c00101e48020750303032003030b400d113a91651a18203202c807851005c520180035000c24002507040d45030210700c2c40b030300042d5845203c1d04d8840310b0070300020304143c155 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 58377134 1250 58375884 58375907
    0x120902040f0204030309051003020a0c080904110a02030c0f0705010f0e04061a120609010605030c0307020c13060e0a020403021513050d060c170606180105040b0d0b0109060306150f 79
    0x7072007952102d6a904015156154070710440d0b0080d0300d015400c81c0381e10b100344201c880002058a600c10036280c1512000d00c2500910380030390300140d850340000c030f84136061000340100c108294000d580d58010300340421b08002600030301e520185d02414041c02a40e0700015614050710081c83c040710040c4503500050081d1019501ca131000c10003c0d01000e0900311020f00801c0d000d10034078918075450700d4103820700c00d0012003485280c002031010300110740100304490056400a41900c1103a6205803180005100414800c2150b40c0070341d03a40c50304000132948111443c0d4410310344a400c40c1414510b030086a26000301c442585404c880c0013a08003600b01c0c3d03005010f4007404000d03020301e4502c40c013840c0c10380042c02803800041c04154841d02440000c2000b02e116407082e2405410741d810000c000030707125110020400580e040c002c0501000c1030054800002c0e0100c40f1070600042550842d00001420100854000303038205418100107210340309031051400000c407124070f4a001d441e00da00c0001c423006011318 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 58378384 1250 58377134 58377161
    0xc02030312070c17031e0a0f060b03090f01020f041a04120b15030303090d0806120319030b030a030c0f030509190609090c0e04051305060405030c0c0409020112090204 73
    0x200a000080c1d500c0348014104911802c1c03030640c4c02d10600b04100c0c082c00308540c2d071040c14400052905444014071140f070b40104a0b1007000c18198641ca01c0e440588106401031405540040104086800100908050342441c1d800071403601e2500d1416101c40d2046000710f4400c2c0c5a0008140c206028041c1268003e1121504c00b50b1114803504e01980c180c541982c0385c84c1da1840301401016249070210807a4012410140180740600c010381c0160361001d001030046501821507003031070000b20700a000a009107401c11850070b007020307c8070a000d0116203440c84c0c10f03030081d40130034049000241c00003170181d500340c1c0242000e20440c9562a003200c051040190301500b15074050000e074034503905400c120080c0d40f03c545500b1082c3e900d40104100320383c02c000822000a440142c54199418164046a00180c8080d03491002919948405251503010385088406034800a0f0092480c05d09018001d9003403800c40342402810040c0e00000c000711000f10110802940e5008104115552540300350f1351081d02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 58379634 1250 58378384 58378417
    0x5150c0705060a021903050c16060204090e0606030d0c0203030a05070507121a0601050310050d050307080a08040b01120c030308091f0207020301060b0c030406050705030d022802010e0d0c020303 85
    0xf10a2000f030f40010100d4003502000e0005945d41c0d5010780181c0303200d045001d0f5154206015030445100800f251502501c2c02c550800011401000700d01501d002084028020030a50500100741407800288040003030400c00e804100c10016a8040704845c48401e036460b10503224456402d080d424454154011f40c00c43c20450805020084200012400c49200d00440500350b981d81d80151018401243e02c030880750b000e42424007051030804003980c80300780920700b201d0506d80b0607510a0410340c040b06001d40071504040400082100748000da901400343e4070304400106410b41d0303c0f00141c1c0c41602001f4140290b01001510004d82009521200e0845595841c0402c003016404002036101c098207038001d5003032120204814a0030000c50350007a11000086d4501468260215140e403c159170886540c00100912104c0714240e0001c0c0041d05030a94041104900140c4441c04407107140c402c0c0b0055904144883d060790401007407000c180e4205003804181c4201601c0040e04520030f840415042c10603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 58380884 1250 58379634 58379641
    0x3010314030d0c0e040c030501080d0c1502040e0609010603090203030307030e0f07031b082a011709070e0114010903110105040506040e010602010608190f06060b0705010b01021905150c070506 84
    0x504c208050000801614100404078080358110141c503402d014050480c0d00807129000114881d030b98141000740034908090b81c0380300010a100a030781c060740c002c803032030410001845210b25104014034010415420300308016840c0da8042900c0b8000181041d081c195181869000e011041c00703030f15040d5058034155101140c4030300e0004501300315901201c80381a110b800116045030f0000b0b4a00000f00c0f0b00c810f040b8148417007000c0d00c031a2036005010a0421250401d640c2656a800d40720502810008000d4001e442c00c002c0ea2140450f4141c2c081d0302c803c1250a214070299030860030440980c0c1e005440c00590230103150041c0c0d114403490b40030680201d00020001181801d90035064140e44081d4000e000c0c1540e10150360750340e0180d80d01500c1500b1a528003034400215405450081144160008101c02d07582e9001d496a540081c0700030744850b515141618600d42c0c6c14001190b0f19181d440c20194105190f40f20941d803440300007908682982d030b040100c6c0701c00c4580c0050b2002e0700e43c040d08840d450324 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 58382134 1250 58380884 58380887
    0x304030215070e03070e0c0c0709091511160503040503030f0c01060e0412030b0103060b0c0109062405131b09081c080a1d071d010506030c03010314030d0c 68
    0x4990605601460500c1c004510072611419090340d502c0070040052900a041c002ca14000c42c0e00545000c40360f2104208000c14405c0c1404141d000344044c000000d1002450306080d4042d120010452041038070b070500401c510955001550300c80307900311a81c0030303144405260041c514402c94002c0c43d418400801d0401c079403580c0300b0052590301010b100902c0b0071340d81c0b10342c0209404010b84005080815096182015504c42d900a600c40f9005140c00304490341d5460b01d0840d10380c051000780d00c2c0b0365110a00481403081c80d000344803042045146100c2c200e10000f403040c4482c1c00b5030082d5481008000030340d00c4082800d4005031100c0302041c00c1540c1000c00d6040c09495216944600d00035401122040494610069801154510541c41e40f251a1790346800000081001d050398050181c0504c03203100304403c041103d8805058442c01c000b034801d102c98042c03012504140e2210f4481d40041007045014500305041c0c0b4112603005040b601d1907120509800c2c02d500a00040e800b91300e15001c031210085 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 58383384 1250 58382134 58382143
    0xd020405010902180a0803030c030a060e0c07031d2d09010806040210020c090402040e24060f19031b0305030f040311030d021b0120060702010b030a0b0f04020607020603040302 77
    0x40348000340c2c3d10030844c00364092181c900c420348070b900f10380c2d00f007440080c0038454880025648040f0b0b21500080e002d468100c00e5140b990f080c0c41c1c03040c150101044400c10141c11002d0790715960600700400c5c0b20500d400c00041d1102d070644800019130490749103c10964612207051b542d90b000010b040b41160768582e25800e03603646003290260712904040300c407291920700109840f0348240f0068094601c5030740d682c0078000a804480800c100622030004405007151511104d000c5e000b02c83d402c0012181010010409070b00c880b51200c2d03100d40c01d441d1031101d064074485110400c0340e83c05440d071a0000e8841890f44803204695002a2260000207483d9450501c101c005200f9a84290500c00d4504c0104092540e55a250920440580d008018109014064082c00751082d8414500240b03003d401c4e00100e05c2580b0124001844c030341c800310034484180d40a000d140c40720034082d40103000e031550307503221340004040c060309003240170300c0001c00b01c0d00359250001110340321500500400d680303041c07614009582d03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 58384634 1250 58383384 58383397
    0x210603060b01090f0612050402010c0b07110c030706080417041502010506090a02120415020c0a05150901050403090e0603070e0420040b0609010e0301060807030302061b040b0f090d020405010902 85
    0x140c20140701182c8034456201410a954059448810f01b4081d04081001010701400507414041141000d81c005101040240e1141044ad60781001c110f84005025182c080da40150511079006960203200c41c59000c00e00e6580150400c40348510349070031007651031262085401403c4a040f64001ea50252a01500304a01466081d10010300c655100083e4104a0140894110099019401107004035a4020a004050380c004030300614113110800704c03500d08603030040100c90f41c0c0c008401d00160110b600160603400400d2400900441c500742d034001b441030303020b030086c02840c0565a01141064600b00b0400e4080e205101d06600c4a041509100c42c42c290101101c048804400d80b0b800c40ca420309000d681c248840207400141880b94182c0151040c00204113501c0d0190340c0c0e414001082e500420188004501a0f0080c0c42c0d58205284010424220075440b0341408004100c01c00034020140101d07071070842d061003400d44070210600020400044194007030741c07081c2004004540701c205a8000e046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 58385884 1250 58384634 58384637
    0x8030705070e070305010311040506030c090a0903140a021e0f030a0825080726040b0615040302150a17090304090c02150426070809010e031c210603060b01 68
    0xb42507494000c100d00b0350b042400010310f071000005600d0f107541015045503410080040941e00d40c8120301001c128680c008070f800ca5041601c0b84002030900d0b400480da11214400b070181306d0301d02004440e0103540d40d8600c12107030b01860701c08091034216001c24000318000e4202c58040e00e54480280320000c0040d001903480b12107030b407019200e0b50a0700c034042e40310320345810031a1580591035039500010744000c428158490507103014605540408208106064411881960b041c4604c0c1481c800380301622098408203801c1c02030410052001d6a5450301c10400d8111607d40c00e540d40d000f0034012141c44681d51490340210b244c0f178040c401040c20210241040c0e54111508204060105000702e07074031140c0904648031a0b414070f0100d004200c500004035165a00c040305d51103000c84102c1100740552251006444015010800200e1581d00c48101c2014403021002400300b00c10342c0a54500c2c0d50900c040c2c00c800c2c44000018000320100301c14016041a40c01c8000f0040c065032030420030050440c0b0b039038150 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 58387134 1250 58385884 58385909
    0x1020904050903030402090f070c060f050406060f080604080304080c06101404020f03060d0602090907120b1e0405060f04060e16110303011e050406260303090a03180803070507 77
    0x40e0b40c044000300b9284a0f6400038080e911079140d9140311106002e001d0b000b8005c0210000d0388a01040c03a80c021440c50308040c1200045a20f81410041c0842e4001e030002c1186800e103e07820084408005920ba0304240c1011045035a51103602c0d142c8160300c20003c0740c510310301500c0200906d00c440e0303922000c2140d14860f003422b407490311401000124401c041240c0c18030310b0706001048050400d001070525280c41400014504401600018410441141c4da84001100ca03e10090381074118007416440e2070b0305880d40e1141d88028010035511442d500c01c032a010382d54607000581c0c1c9030794007504403000c2c40d0040c0c420860365031640141221031500f00e55000f030301002e02e00051040c6100305061034100420a002d1411a4240903444044042c40e10003111a1500c103040842c45a486106000c0103100a100c05001c0307048281900c024094243d0000085e41c000307108010640e0301c00302e01c0c4d1110300ea061034032048003031410480000100351a04080c456200204600c2d04000e00011140107481095002e070f0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 58388384 1250 58387134 58387141
    0x10803090405010806160e030304050307080d020c0d080421061814061501180b0f03010503011a0102030901050904020c0d05130807050a030f0302031c02040f050114160f140102090405 80
    0x1c3d45c411041d52000500c07601c41c08003083d42031003950350b0900c1040007400d607807900b80d0383e41c002450829650401c0026800800180c02042e404220480301d1100c19a901030f00c3d44055202e01e190380c0528464022400da40d94001c0c141e13016030f03800145000d603000d00204018030102200a00d1a060b0080440b4910941e40c40c03001c0f51607001030b1881c4202981c0340207050008209004582e500000850382000d44030402c0c02040920b10744003d040b400f03400c04000c41c2c481d8500b40c105801d4a40d98038503010001c1026154141a0b64084100c0e02c088401382060740e50f60000b18003190003881440304024480c0584920210350b60303400070003446c3c01c0e850000c9c0c5070841c50303e503c0d0300c40c0c48241ca84070705039016186000410005084c1408006014000d0042d2814611f008001c034081d890341d11260214a90b00150912500c022540c4250107000c013840e00c10b000640c2e020030140e50707204080c1e6084502c0440c15600003042625400324000c1903001e09201043c03d512003050f070103500804440340c421803c08001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 58389634 1250 58388384 58388399
    0x30605060c06010909020303160501050601090504021215010c02040e0309011e120f020c0a0b0105040608030c10020702150f03091009030c02042a05030a0507050a170c1201080309040501 81
    0x5454401e150a006462540d1a022141c2c0c01401060b00890301400b003804030001070014050f010f0b54140c0030700300121705c5180c00c0000500000b42c0f034008d02d100b940b0500c800e00c0110a84164540e004c0781e005400328005030384500603264100003d074029400b5080400d803516028021002d00790380078081c1c9814115820442c05501480c0c00c40c3e103800005601401400090b07100381e00700c100c00c02d404440041c0b80850918080381001300068040e0b5034001240010020360405116690080440001842c1810122155151104a21228204059004141c1409640d03801450200c11107480060b2036440c0c480c10001e100710f400841e0320f03421034010080c4014502c00140990200954140c3d08c4102c802100d40c20000142460707010700200403c60b40b00030040c24108031030050038128030b80300c940d101e1070034a120b601600c10041118040040c14030000400a42000407280381004501035000c507075494212074207082c000c1d521a04110050f4400014140f0340101c0100340e40d80c800d450070f0021382c1c4c0301d040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 58390884 1250 58389634 58389637
    0xd15090c1403040f0803090d0f0201020415051c18110a0b09041808030a0207060605040c08010506030903190c02030c090103170a020307080d0c0f1e03020a0509130c03060506 76
    0x48140104000000c1c068000140d8002150f005109030307486040c82045031151151a0412103500e0401d1384000c00381c0300d03180d0300b00c2040da0f1401030341e200030343c82d040c06d14030070480000240d0000f0051000203d00d000e1080c55507051078224000c00c103010051589182d60f841c01000c40c43c001910054547c58407542981450b0301c2071010b07280e00305010391a00c081d4000b404010040e203010040d110003000722280001d82c0441c000c5004483c6488090303101c22240c04c042c403c40c0c3c01540046e20891401c80c1420543d0b422500c1c0b035044400451b01070341ca955881030300c0750840c41210429030511003641c201c618182e412a0348225054000e500322016007291205000300c528080c003000e024880c2515104100400d108000c000255082c4140c81c20310303200c3e65a00140340c000c00d440da80259200d40000d203610741d006840c401f040000d841c049150001010204070a81d22404804d01010380000390039000030302900884080c0200608406a918801c01840004062605984000034208070300060b041c03030b0000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 58392134 1250 58390884 58390901
    0x3031e020d1b171b070f0311030307140607030c03020c0c040c0c020405010306050f0c030f070c0c0b0310030506060604030503040905090717070302090106080708040201030515060d1509 81
    0x1001884556414002600d00c030111803a440300107080a00c0300c0340002c2843d903c40030300b1103022241c252140000f1820400380200c0c005900207584c020307007041154014100000c011a5000044100302240820102e82903102e90b0b00050f0000041800300d0391203810002d48540700308480d6a0800141124842c110164820031f00c05c1d807155841860301e8081468694802008881c2a0034503d201c02c0c1c45a0104003601d009904c02d55040f946c5a0400166081818001d42d00c0280c000c940340c51072604032400000030501800010030005904082c4080181e580080e0000d0310000704600e480749080e800c07a82410105000445150140001089c40307424000b0a42d001d581d406400f942c1450f00784004c81001f00401452000b0904c0742a0002a15000140301001c442c00850007400e840c07811401804009401039108008200c1010104443d443c0c0c4034040f5500a682443c0201e581c0c0c64609000d0742201005c20b105034040c1c0002820ba28200c0aa440300b00e0021650032012552079440e10200c08a40301c2d50b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 58393384 1250 58392134 58392137
    0x90a030c030611091f120c0302030a060b0405090a09050703060e06090106060809070b0c010f0615031103010f090203130b07090501030b0306070507030807020708011506021902060f09011407030201050103031e 91
    0x80710f001c14104080e17400f4154040992030303d030805400c2c040c411025a0113160386580070a0740041800a1200326014540142c40c000c00118605460007022465408000308040c580e96684c401640070803006106140080d6001081401005007598007151140c0064652058540c41d080b000503035030303004041c01d03131049103010b018210480c6024003184140d0720000c90040203541e02d4600080980140c0f20300d6004d403104090345000c10740b0804024003220034164404c0701c5d11005100410015030701c56080016200e85200c05030303c0c0e40b2231900b01105400759001c0100611b4401042005903544040a003040358000d0341d040c00310b0401d590605403140002e80e2240c0c0090030403c800000700c3d000b52442500112503104075407a103a074500c1d03e507084449080d02400709000b00070042106c1c55041020b00700d40c9006450143c20b9411540c002085403181109285501d00c0204d01c81d00c140c4c0c0a849441c0381da030b280e10b1a882c3d6030121454028000d0000f40070443c0410b8207440202c400e4540b0102134110300c08076 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 58394634 1250 58393384 58393399
    0x30621050601061803060608030720030c12010212010905100f0e0403230a05030f1f05040c0c020604030c15020303150411090d03080a0c0f0503040215090a030c03061109 74
    0xa21208030344c601e40210702660680c001000c0007001983d14071034000103054201c050741e00c481c0285000c10384420b0750100400c005000c81740c03804407940d0104030752849010464802005c9846840402e0190103540b0500c031000e41e800340001840c41c40758002c144210700d121402d0480740d8a40351040613081090194040c494001130000300041d001e00380f80c1c074600c0e14030700e8400303e4090444030f035852a9122035540d10010703a001c410300010800200407240c0141070b4040440001607100a2900401c2040c8215407141d6100c0f4525010703c2e007d000030007086070b0050078041d900ca8032400e1040301c2499a10854414006410344c402c01076201000b0f403805a40380e441409040b000d44010000541000c020704e0b425420104085c540c2503a0b1a40c4403c0707454440d031141681d5152041d007150485a42200704400e02814421001e451580001120790042e8119040d50000542041c003104e0b03400f80910003500207103600000700078003290302c00761030840b44100c0c41400030b05c0701c924094116029080ca0550408030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 58395884 1250 58394634 58394639
    0x609030503090d0501140a02131205101a031015050603040201120504050c0d030216060203030c0714030403021011010c030204030b0402091b0a0c03081008060105060a0201020f0307030621050601 85
    0x14150f8104038110f0148001145290704940d4003c80c0d40f109a40d001a451b0f0300240d080b10040380745216400a000005d09014000c016840d010b4072003003c0740c1d110001039611540c8581590016008980c0c0240c00b804480b0080c81c1c8040c10401440480484141c04101c0700b400940c6140c41e10481c2c1c411036040e07581181001c1030b003415202402c0050800c0b502c0d4051000c030300340300c0c0d200d541e5181c541601940c020510a828420204a007400d160002c0007150010020041402480c0c000c5920ba96407154002040c2e6210800b041c1c00d502454100039403080c40c201200205c1948124000e510816580c0200090488444198120701c25880001d150001c240001005498802500ea50101402c3c120403410218a52003c09503809032001c18041a0380d81c44d01000c0c55030101d0826449010358442d401d8150610504a60703d450510a181c41003000068130340116100f901580c0418041c040050388a0516440141c00f50800780180066102c2040d480013240c18040e4121809640020182c8900d90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 58397134 1250 58395884 58395889
    0x11401051902010204030b1e0a061412120a09061701030309030209070516081e03041a04031704060209040e010b09190e031305040509030304030207050f130c0e0307060903050309 78
    0x4200301d141995428800040031802d803001a5104806041c07142454000903501740c1d00902c030140c1035030709007071602ca0140031031400e1031451840e1001c11500c25401c200c0c075056061800340c0207012144025400328500c03020b641c000b060581610180c1d1a680c3c0e081ca404000104c030410f09100190008104280810240c2000381d02140c001c0c1c114600036260040c0f070580a118113480b04411640e85100144248180720482418041c860030040903d10b10705154030780d403200341134444100e600ba6900901140c1014007030a5420001c2c13513802c103120781c6480c160514030000d40110140030b000ea0f007410b0320b40388685010f1007001304007030006089095580311040080d8140e200782035402e06095490b00c001ea440340c0c0400c09405000d00c070b40c8603071841174101001d110a480c0090b020480350390040c801e002c002500803c916065450980c1e60807001c0e80108002891012b04561103150689054420075045500541c840248a000e50440d03000070b41c1c4102c101c071441618407019207250402d010b81801417 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 58398384 1250 58397134 58397167
    0xc071a0901121103040f0c1208030f06030102040e040308091209060711031212011e0e01060c02030a0c0603091101020d0504120204020d0507020618070e010603020d09050f030901030501140105 84
    0x1540c4107500007940f10076038100d5616584181c405407400c0c2481d00340c141c1044850081b0750080e0100010803691165166100b07105804050440c000010100f800203ca0362400d50540c1c0040c00c810003800101d080c5030070050705141c4182c60b103804500828100b0034000e841c40007240c02200d0090003da141c80e6907503e6140380c28150141c81c0ea0b050044508802c0417841690140114181b030015600385c651600c021440075031092070306040540c0307030312004200c60300d81600c1c018119071080c20700704911031051000030304003404040300074901d2950780350200d111645503103c112032602c214040c1d1564004070005a90351081c50100c1d0001800400084c4803404010319404900c80c1302903c00350804010080d24006d0790421180e0a006078020340c10840403000c05d050326806202202e02501c2010306043c1d002800d40014060181810b400180e1540a4441c40e800102d901d90003100f0745085501c44107643d603c1c0c0e481500c04600103420f0000108141d94501000744c51910305031962460401c0c00703032216050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 58399634 1250 58398384 58398407
    0x14090a030507061706040501060e1909090c0510020c0a0603091502030108030c060c25030507020a0e0601260f09150106020a12021902040e03130801020c071a0901 71
    0x1524005002001036800c0048401034452a12000c41400081a80d01034006005105510a03410200100a85504201d0480e21501c058801c0204001c15a0038500074403216844106014500012102401600308462080d690221990303410011481d60490b89c0c0c0c0412411160b01c19401d00b0104400c0c1d00076800602c0c08c1d03216001420b07010b8103440302c030004c9130401d83c092400d43d000061385c06040c4e041400303d00e5100183c0c1c90304034105903d00d00749406001c040449100340a845440c80800d1502030b809860b0015802020070300d15585400c100303030003c1802e0b581c16021030354010408102c802003224110120308280c28500f9291380b92022003c8041c4050b14000c0b041c0107901c902c240c410f41c0210780e2400b809032900140300c90032480c0b9140700c2100d82640c0c1c0c4802c541202c841c3d440d403110142c401001c00c0b90111400701d802040003180504520410b0183c205041000344001048030043d000341030b03808800c4099458543e914103440aa458944038101442c44e010010360440b50300805a5110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 58400884 1250 58399634 58399639
    0x2003070504031e0308191808130605040627030203010912080a02040833090d18030302030a1101020903030703020105041401020304080403031407061805011b021b0424030c05040209011409 82
    0x80c0611f80d03c10940f44071100d43e009451400c4005041c0311200701d80000800107104524205103041d107800c1c0c0c010041c2c2d000c02020425140b002c99680d2006000c800c101019540050081242c3c2e2b40b94a00129040b0741107c10002040f000b40010340200f465209850817181c0b00006031888011030060b106521000180c440b00181c031b8039064040c607103070344030049104261003001400350515400c0003901100c08114081a100d039520000d0000aa010054a1003040300d42040441c441d5a211024064007030070000540510000c124a010716605412141c002c50085c5449140c036407641c0212070a0b40300071200074200030410001040020b1151070340c44a84071b0b074403680c80e0810707440740d0b1882c0035204042c0700c1c1e4a55191440804041c03080c20b11442005103001d442680c1c0000341d034031340a516035940824400302c02d850100300e0340c896156500321240301468401940e04164058078224100c034001e010549440300c1c40c403030100d6682400c2c4201c1c1c41c1d40e031050312055542c08440000b000d0360350008a0154 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 58402134 1250 58400884 58400891
    0xb040b09060d110408070515070b09120a02012a08010303080408040503120c16140111010e12040f060807050322140c100c0c05042003070504031e030819 67
    0x8480040f4072401803c0e00603c0105540c540c43c15100718a00703030340c0f604514891001c0981e40c0c28a401032004540455a226200c0d05050f520107080f03604005202c03200c1c01d001c49002840e0074034240d0660090984242c0d000100b00107170075140e0034500311030081d804440891a00d000510200f4080d00289500521603403203286000c0c0c45001081c10b140040a0125403c640070510800341d10f41441034201c0d0400340d4608014131460040c0b01d0020002c0d0512180c1400103846013405205030a422501d448110001150400072400c5649407803688030348140008401c40d00008a00300d0310034025140591102d60783c90b81907803502135100350485070401c0106084491540500300040d07e41e094501080070310006400401c20355401c1c0b0803003404014884040002c15000f1000140c0c9416004080d940207450002c0c00d00e101e151034001d608140140d400b440310780401001010390b800f10060054901c034002081d41080c0b028144909203d0003540100429140310000d5001d50f442d0609404e14000c800010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 58403384 1250 58402134 58402147
    0xb030714090403031d1537020912010203430807030b0405040308010303091409040b04052401030303060e0105090610031e1a090c0f0309160602010203070e0405010b040b0906 76
    0x1245030500039660660410726071010000c1c0100e01c0840b411040d81408050700140c1f51104c22810940c07001e060b43c1c40c2c0c1c0c582c0403035200c0b8180c54281001c503820500c41c0c004c65890800c10303051035000b49640442c001e4210031008200740c114800000034248004ca103040c1c20b843c81c03092010b8812400040c0b4003400c056071103010101c5c5a81d140038690280e4001c0c0c441c1d50065044d03007001058100b054221580c090220484045543c8031080c0f03590f4001e0b040644030b6919281ca01c3c00d9820410088000008008000041c0c000c01d440503200d1412684030352010484940d80e08402d89080f8000d204a83d80310310140b000404608082203114201740040c9000544144400001e1040380c0308085540c075150350300c10640303013444004170300ba0340340500440e00d80460f450080d1001e51517214080e03000804040210100d10808810420440c40a1503452420822038603504001d000350000c4034080e0000781651113000c201d0a0500c40d5905071313100c10780001d2030181415000241c0f6032012514903080300042100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 58404634 1250 58403384 58403441
    0xf0301020c072102041b02010c110706081503030703080a0b030703020904030e0102070816050f1905151c09050d03050403020616120e01090309060e180403210b03071409040303 77
    0x942da000c10501404220008888200070302715041c0c0f040601c2404100884090a070358001005422203100e85490400f640e80c030300510884940300708406400d8400821220205600715003110b20401c04000d04005806902d000c0654446071444003a400902140115010910462a0b483e40c1034040c0119482c4a0741c0700c030300618107814070101c44c04134a0000b00c280701074a481d50404070059411201240344501c20040c0510000e81842000c0c4241105400006181034550641c0e242280020140b4040d1800c000a0400703002d00b130710100e805004649044e000140207103e003500030758150f4010629651002003006610301c500390300d4000e0103201da0440780455998003a810f1a21402c0300042401c041a203400790484000360800001e120f49010764075a144c441d98052a80f446d8449d050340c1d291f403154103041d1030300f400d80c030201c23544540380444a0b1800c002c4ea401100180e4010390440d014103a440151500b00d00c80c1403000341d80100d00c003001c039001c2031181e00003400144036000b50940d07114002c0031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 58405884 1250 58404634 58404641
    0xc03060b03031303050105010501110f030406050702031002040306021b0a0c060305070c0c03050304060915020a06090c03050d08060f01050a02151008150f0a0e0a020904230c0f0301020c07210204 85
    0x10880c5e041e0b44841c014401940d1011905800c5291784004000721444804c00944031f002e540102030800101007903400c20341d5070400ca1b01660410f070003011942c480d201c1c03d000d4040d5206640c290626020740c000141308510000c2c2d8181c15a4002c00c01d440c1a6043c020120003911016000d841001025489240851000b241c0c0e9001140f14100440e43c80f80380807009814800c0641c402500d08411101801c030340790300442e005290950041c0001080b9669181560b05900135802c090a140b141078082c01030290080d809a018820485810700c2c40062140110707060711130408a0b200680010400e40d4684600400071070308076035071007607070120300d620350004501d0103002c03003143d41080b0f11540512540c40d0b4000792132038110050034401d00c4405120003010f960340360055802401a9040310000e0180702c02108209110414096040409071050345a2980e880e1940c07901c92180440d1100a4a145014400c03680c0c0d441c0d005010300002480d02049000c0b031003229a00c0020300c5404100b21005a40d20310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 58407134 1250 58405884 58405889
    0x204020d020c071406030702061306090c06020a06060503210c030708030403080a0507020c060703050c0f01050703060503011401300803040303020a1e090b0f04030f2d0c03060b030313 80
    0x2c0052000c2c41c9010500c840c044904d051482c0955410828000c0280d07002c14096404001c001e000325100804c0d04d0b00c80001d01c10381c94007404d0420440b402042c180d502081500c039103401541d041c04100c2d244c50805803038281f07204a41040d489040540c465000c4c07100082c1074019031120903030b03040c0314458880c40410b600842c1e04500184140741081084005442415002211840100341c85001400820500d104119010b003c0c014049500d40c2c902c9001c1043c1443d0380b5004009002c01d00b0001000380241485010b481e11035424a0b03801007010300038000f8a8121480c4800e41c442000c108c0b403032001282e10341741030109142c2443c8100d00200f12580011340c0510b10036a001a9103440980000b044040701c4007180c0ca18a04520300144515070105502d01903d0020440303503500e02581e02c1c080c02e5446a5840141844030141d019402e2155910065481c088110b08510508454804421b00007400040080c402c5107500f07018804618282c2c043c0414420182c200c03071801019004910000c08980d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 58408384 1250 58407134 58407157
    0x3010f050601080c0307020a0609060f0c020f1b150708040f0b04050907031802092802070303051b190509130903091208160512070803091603020d0605040204020d02 72
    0x3482481025640510820f900c600d9076400c8509604200000035294146130f00080c00f0151500c9800c014000c0359404a8440c5040c02020850780c0c8043c0c201a44a1640c452a818a4003411600004603012041c41d07038004200180040609484529906280e8100c0340003654a1002440081a0361501d0241500544410000103441d245440200141030200404c40820581400c002c1000b044116915040c440d604459807100380d40c41d0341c3e80203400070702c98001c0280c000c91090301c00c003240c03142d9006124841c0240d4003031285540f49940008004e136000c4c141f41c0ca41c44100604122804008024010ba40051030700c00d182c40ca2400003e1100360b00803641a25003603880ca4214100b642007640300340280f00b1001d40e00c00400d22500c407015035000b42d01c514603c10380c8104c100d104029090003000c0d9464020302d8625280e800311300b050001c5400469009010340b10f400100380b6041e400c0491201100c0c4d004103601c0ea0b002c43d6642e150041c00c80a0f104a030041d4080c00401c3c8680000d0011f046c0d50080c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 58409634 1250 58408384 58408391
    0x1050603042d050c0d12030515030a060e0f060603100f0f0c050d050a0b0a0315060e070206090d0903080f130b210c030f0610110a0c150206090303012303010f 69
    0x2d600f400c0b402c10303040f100700c24812507103080080005080c11505001c11441e506000034070307a60380e100210303450004806c200e84c9130003100a00c900700082034bc0406928070750501110346040b0100d204c203941711010b41e4901d50603441920100b00c510099040045880d049890128000c40a4101c020940e0314154841021550100d42c4100e0030a0390b00c0b038990b0241c0e0484081c89603079912000310300c000a080c0000303003124548828440458074140c212a0040801841a04403881c103850029155541071795900382c03c2c000c2e4200009001e1207008880306880d08051b003286030a000d5074524450350710105620b050721204c3c40000034400c4180c00580a02c4040380035420b5014141c070190440380307a0080094158036424800d0210300e00328119480e0b40120240c490900c0a040e119060755040e0140c06005054402c4d620341d9802c001c80d4503490021681d54000c9007401c020500d0007661604401c403909c0d04640e00600041248855076280c81100c44100395449108c01030307040103e403d4440c401c0074010030549 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 58410884 1250 58409634 58409723
    0x6120109020d1112070506040501030f0209131401080303010b030a09141509100e03180112061401090501020307200a05040203090f070f060906030209060d090c080f010b090105060304 80
    0x91104c041d15403031030103902805146041c100010321f5409a802040d04044d9661101503014403a941140c1707181800808125200740d00040003030107024102e1000242150400001030700032000030989042e035900715001421581c85100038401044e00e200141e405882c0c484911302404000d210458003080301c484220003924100c041a13141110f2a5042d14000e8605950b80c106220f021090b074007a45c030090580502c40c801d08004030340c080500a44900e0300c2d890a0000140021043c0b52000042c6007a21480c64181d07071000103a8490144030409170103a100b050000350102c2c1e0009032a0781b5000c00a001080b06500d810105040341c00c200d8030251942d201c188002401c140420a00300108648060a180c0034101000100b07005068461141410740106a2416030f03a07032641030f10041540b82c80100040138050a01050b210b00c1071052040d64040c1c8017400b00804018010344541c443c01505464140c1d1910090000c01d42c0020b10903070310a64002d0262545030480c0346040c01c214614005030541c1c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 58412134 1250 58410884 58410889
    0x601020601080c030601030b10080304080102070507150c0609020a2102030c10020706030e0c12030306010e060f0f090303071b0e0105030a0b06041805010606090303110604050606120109020d11 84
    0x328180c01920041d440240c0d45400c0d90350006042c1e0640394082d14082013900e426031948001a0b62b0307004807629000218000c074030301c101503010300404e40c004c00403143d00c265540c650070741c00328201200e40d000501c0140340401084140d00f000b00482d10141002564546d618182112038540340f21107058040c40c2c0310042c0a61504120042c12691300316041c04281c001c0c0f40340031391750704541c0c822401459240c420410010b0014021041d04050280c00044881180c803d410740341d5000300e91440c04214582c81c0300c510b07400d0030340a40d09468070540e002440c02601c42540f180c140c001114203981440304124907000034803840d40e42c542c505604215511042e00341005003070b08100581082c1e0103a80641c1030100420149808a90086415140000e00c4459821903103841520480090002e40c20100700090040d4041103410407240203030385041e000f240100c0700741d4030b404050301e0140080d8007a6002c0342c0d05107400d2514401c4880610300000b03071060164085440800d40920540380d1058402203030b203070360 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 58413384 1250 58412134 58412143
    0x424060f0302031005130b070e060f03090d030603030212160f05060910020309062e030507090e030702030616050d050106030501060806181f091a03160605030a020d061805060102 78
    0x800c110106000c580346c00a4844200d01402c0806481600385e0030100710001d01031075400f40503040140400d5079407110060b004031961703c05d5074481c0291051811000e100c0f88a84503100650740d155028180c004820b00140369150442c0c03c410b028101903200020011340d050395000d4400d4884d101810191a0540c08582000340b0030302c078501150b00410030400d40748004150b031503100e5440034085a40444070482c49070b44045400c03000882d03010a2201000b4490001043e0084401c0d800d014030405030b0fa40d040c1900e034090050b0082d0564080340202d1024131950400c8012805541780041c2000e00d011284815203600fa40014046035880d4018096290b02c40c40b210b034802c0060b201c0c00f14211100e0620302d81d9410040c890250f8151404c40000d0078000c4801c000010b00580c2c0003407103410195840b42d1640c0d403000a025100348100503010340362244c01c6100307000720391583d12480d0540d5070341c600710070103507000b4120306441b55a82d62022440349456580c4001d03020f0300940001c6e8520300700001a192 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 58414634 1250 58413384 58413403
    0x40e0a060f0f0f030210050c0318190513050a0b060a0509040b04051312020c030a0308060a170d0503060301060f09050612060603030904020d0b03010606080a1a090424060f030203 78
    0x41000014000c903c40d040507a07084030f9055981901a8500c204215540d01581600e0007184c0030004804541240750162582060f00c22030b005040e45043c4510b08050101034410b46811801d6100d8040600d15030f5401246c0c00704e03040b203001c80c8142403100042d8566000748500fa0100384041544803040c1040d100381e520b60390080e60304200b5424100d5003855180b851020041105070001414009580700f0700c86403441c01c0000d012a241c40d96240360281c080030048a06901a400010000031203503000f620b480d024600c00b401030120b900032881d0440300348d440100015090b64a842c0001440d0040203c104010080040005214203000c020442c0352001100b0400107548150207101481e42d02004403038001d541180e00513a48c1055003060800780030301118155065103080d00024400d41c00840031031007030a0400040040c02002c00000c01c1c51000500582d401001007070028000840041400150340103645400b1310712806188014291407480e040000b102280100400c11400c1c1040341045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 58415884 1250 58414634 58414649
    0x90501050a0b0310350309060301060c0c05090a020306010e0a03150c0c06020406020a1514060d050a0501050c0a030b040b0f01031d010504061401061106061302040e0a060f 75
    0x14552400e000107079201d4141c000d10702c00100010200d070b0155401c41c4440000d2480c801c007a0390b408491484502e2211400000c090b103480500e82c440c55040010013101d5029030000c20903802c507401c200f0115000c4a50710401c580302e6121010100e09a621894aa440b17203455220269aa00c1c0c0728000400c0707546200140c5000760103414043c400100709000100301403000110008401c4524501156110009100903000b00e20002d80031400690102e4120f28190156410075080d200d803400400448a031400c01c8600f200350480410700340d06c2e00c0c040c0d010606000e001110750000c010b4561608440099421078003070100011004411134141c007c0b048058802c9030104000c9600101085007036041c2c42d10705040640e00c0ca45902c280d0005109040341d001050000c200c14078062510300c0050100c40c0d0f0341c0b4640c400080001548900c0f442c1c0503118440d005020b013501c3d17100c01e4113002100c100c0b08034200b00c40da000c2c8004030b02c1a51000340d070351240c1c042420100e40c3c5443c2001d1428286600c1e0055207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 58417134 1250 58415884 58415891
    0x30207081b040c0509030715050f07050f0c090c04030809041b0206010503060105030106060801152106050405060402030103080d0b0a090e060124020601031203060e07050304020f120c0d1121010609 86
    0xc0541c0c010611030102c41c0c50710407040c023404001c202103d0f14421604040c0c010380b0046841030901400003000d0495031000303000c985556600c4010001c440d541100d002c081414100014400111340d8406480314600260001c580800030b100014004c4203002042401a40100d0040215180400089006160650081001c242004030040400300140901f90b202800c280d8203082681c49040d0701c8034154031300c8050000c5c07036088292a1000d014bc03481002e10860070f000109105140a00c02c40381201e9008008901c1e00c6040d00700c3c10050300700c41e054254001d009160000e0542000e0007001ca003c188140500a107606000704c04c0d1074400c03001440c042d001e031080340840070143c0004006054a0b04842c051448c10610ba00c2200602516008103004072446418004020f42000245001314400c60707039101900102414010a4084000300180e9035118401040c101c0c24003d0012035900d0142c0708038290051082c4c0401d8140494514900465500302242400d0490070301c1448003501c080c0078240b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 58418384 1250 58417134 58417147
    0x81c030b010c02010309020a0f0b041526150618031204050d08030c0408160602010f050906070e04060b030108060f180309060c01020c070f0f050613030f030207081b040c05 75
    0x8100c9500058004c1c181581c6044c42015503a561560400400d12141004400303922401e81e08c40b650024030660424001240f0311a50745801107405580540d5000480307950b1340e2701d8400560007904003811500245102541c1e40945464140052050b03d042451034042105118141407404040c1c40001542d100d09110601c081d648003126008195003042c919030712515850791075801407080343c2c45002c2a10640b160070480c2d4066440070401c1b0341081d0020052105a911030100fa141c040303503040c6c419004400000c81c1680901481c040304c42001e07100041840d02c5103100e900c25842a0044265580040108024001407c10b00ea41c0090000489a2121400d251060b41c03801100d000b1440b81c0c1000c42e490190400950540c1c4034284503000300d400c9c4950340e25461241b03800c1c4d80100c0c0ca0f010700601c408034407410064100c4001048241021280030301d1070b21118070605100104030218007172400300040d83e000070441a51112411204c00002c00451781c10481240d6691020300c0502c4410300c00f2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 58419634 1250 58418384 58418387
    0x50c1c021302090112051e0109090b0c160203010501030804051504030305030c030a18150e0c0906040b0103110711040c030c0e0111010b031614060405030d0f05070804081c030b01 78
    0x1d0706406554005038880e0381640060b5448800c400c0200001843e0808115034003034085000c245126550b21000800d03622807103100151482183e0207029094280c0105040d140700b0401802c1e00d50b1000007032540c600040d030000307007514030070b90081d90703464404103041c09685000bc2c00c4900d0518070324002883c1900e165406086402300400080d03403203201100080410403541c100a00549038514098100d846074500100c1e180003d944401c00145000050203103030500160444010b41c0017801d64103156119410040034141d1560058100350303e0b9052800740c1051034014003902d91080048030240d00322a01030004594400400d50201810443c07180e49942d000300e020417440c042031801008661100d40b646014188140c1065054881d050701c3d00c12903840d81c6141c01c1500d140101c500c015008203c10048a80214065942e150f00499850030110b0300500b031402281035a420003900b0b044854403444819085940014501c0d0401040403198040080944c044c0e444982400c10151050900 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 58420884 1250 58419634 58419649
    0xa08010608120304030917010e0c090601140705010e06010b0403110f061b0f030f07060e12040b130503071409070804081e1c09030807050403080a0302030a0e0a050c1c02 74
    0xc2c901202c00000118051502c1404500042c0000310a40c002080030791021500030182c0c90260f22241c000c01c14440e90510b850404203004d1041690746102900c0a00e001410300c2d8030052045606660719198040241010306c1810f0003807000501d80c030f454520b541804154100802c80e501d200711407480d000200c603600d92098601040030584041d01010b4802c034681c1c500031905683c00020302c4042002074525010000828099124040503c201c0c406547d825230303145455800700088c03d100b804244141c89040e0b0103042c0040c415002d10102c0c0369070704041ba080080390381000202c8402d56161500303e00f0040140303038001c44c143c0340c000c01d83d281a0301c030001d090003401440004030380309510340c8102140071015036041090099451458003203031240c0d03800030f08503541c0c2280400c00080003e00b81034054400d641c2141d40001c029854420490f01c120000d50009204071055139541301d40d009480005c10030341c84500c1c8a000140040c81c1c6802c00c100c0480e0700071514000e00c2a0301e040300780040e02e81d2036 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 58422134 1250 58420884 58420903
    0x21c05060c0304050109060504050c1c0f0809010c06050702070314150412020f060a02071209030f03230313050c030f0a08030405070b0d0507030501120b040201081b180a08010608 78
    0x106070394590711a464084d01402d001d9202074401c509050611060000104410014240496854008518920081c0e810080003e0040c20f59240001100c0100d00f4400040c00800414540a040c5000e01d65032241105d4068911000591061b5000c1c4100141c1c0039058560703041d040e0040a17502210f01801004d6000204010000e4003490003001c0b0084c000c0000d008103103103c2094903514941440070900075013002c83e05640050b20844008840d90049001c1000e5079001000c01080c0c11041c0c07426a00c02c03044c0d81003000c441d59000d20707280060307815001540c060b0408007201d4104901d2030412070300e043c0c03400c86c10034400d8100d03118500c0f40030400a001d000090380254000c0e12683c2d41d041050400f8240e0b03011020110001490791424076445e032003a8492003c5407010230007642c80742050720b040c114440005222041c40d4000c28003541c091b90400340c3c4214141401004480d80e41184400e43c3c104d140b08141c0701c903503e107151581e854104510400740c0917400080007074a2401212b190f0310010b05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 58423384 1250 58422134 58422151
    0x601090e0402150f0f0910030506060301030308040f060207060f0f18030809030c070b0d0501090b010804081303080a030b01020708032b111c0f0b061c0906090f021c0506 74
    0x3c810464400c443d802600d201941020089440e841940306101c026884206c100d44907022909100005078040c0c8640e5008100180015085038210755090710320b034801070001e44950300c40c05051b400250b0140028440c0790311542020a08000c603803040d009481c800c0c6120000d890402c04d64040c03c41c4002800a00c040d01803510003c0382d21400c0d90a4210b2080107029160360240d9000070448003074200092210748102a01004203a82c1d90b004031007118074004000b0300041041010901041d90302c0060801c5052140d0b09280e01581c0b0759912074150302c076140d40c4003c01c5d120f03100c401096030148611340c000c0140502a506d080500d101c0d2000c6040d0301c401900e001030b24094810051300041d40249421141110344070760b00c4100480c0c0398030140c05010300c140e11605107403003400d50340c1442c007886c08603100c060f08140c00c080d1712060620806840079800484659102c690301e0116000e401900c00c00d5020710307600c203a103100398014000340001c5041d0050203103081580820005100080c401c0c1c0c0001e82 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 58424634 1250 58423384 58423399
    0x1715100309081e07030206070f0c06020c030c0a0c08010e07050f041d06010b030411040b130c03110d051006020f0a0f0c05040516020606010c0b0112080405180402090601090e0402 78
    0x340c50b08010034080c400f000c3c005407020708200080a01201c0c02494030034001d030200c801c5562686c10440e601800c1d030140302c0c009418800ad0303400141ca02c1e005888100d0380c0c40162414200030210181c82c1c00c01e0300d034060350024083d9504102400c400e00c10740c610640d5041c0039002440c01c12011030500c0d440351040e00c0c041c80e5110800424031003201d00a182d40031038034054403a6940c1d5104002c441c0d800a840513120302221813103070030721072070280300d900c0f000b91015203000208940e11006400814040c0003c2050580316002d0f241340d131061100418004241050008190400010040b12161a5008042990701044081080f40c00002e0301c0030145a00c007031b80f85103a8141d440c104229021650215030818140024015001400c1d07844580c4552641e00300c0da6596076a00044030250140d24001e081140c42000501100c0c1048200b081c400703000f00d4089103010303541e0010400441d2000343c024528449802480110718183d01d480d81c10400074a40100150304000d0100342584001d440284900c1e00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 58425884 1250 58424634 58424651
    0xd050f031f0303080703050703090b06010c0302030d020c07231c0201020c15031b041d060d020d0c0e0c030408121306051609080627030408030a17151003 67
    0x7145100128144000c00314891400e54a01d80905015402d0700c2c0328000c2814400045c0485110740310303c060680c2c01c030f2585031760313a1a007100640e01e01030b68140940442c0010024050415902e0008182c500454402010060724160003800190b001c1480c0c005480c41542014a03250313202c2061504c840780061031102c04507801d10040c6d1038039041c1c0802c150402d0b0119069505840c891001d5031240403100d40d1408100c6285602070b849105601900803c130845441d020b50340c0c02420811540248040e2a034007504240d60005600b030301000404490740c05601070705100e000000c080542c4c22003050b0f51000d0a44c201682d913442d25003d409110034484014000080f0f80c80d4000400306400f5810100c02c06c41ca00340031241154460003590b074040811510341000131303a5280001c101e4461207004035031108030468400c42400042c0b0b000700c1c00003948018400800d25034800c1c00100103081b40d0f510b4560030484034900c8600c4507940180506048805050304003c0358680e81242800c49446240005241d003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 58427134 1250 58425884 58425901
    0x90303050c10050117100b131808040b0415090b0405100302070218061008090304030201030e10110a0923010f0c0c0b031e01030c03020609180703050a0e0d050f03 71
    0x50750001c0c442036400c020002964401030010280c1c007069170016030701d402d2110090442a600781100e4a50401c0d40c00320b0740d0340004825480728088485801c0c44010840c119103603101d06410603000203011540c0058200825a5000b080301c20340c0003213007450342c000fa1820404101c58001c600c14540100200c0703203601c248074403d604440d505a401011212411300300480800e41038422560301c0c1c094880400c0d94a8500d000b551076900c14030baa41d00841c070b401d0a682c01100034040110300402e41e4821445042e10308107050141010400c0381394081a140c18400340010942000741d4000f04440d02d0240310041d04903901c05242d20850700a003000091110128401c561000108501505800e0010000719801d807804000b54050180d001d84170741030565500001240a0081c0b0001b00b0b590841e103020401810701e0b07005003a040704002e01c040c2501a000c1035010840038112081d50002c4e0ba1a020454420458451151804d5840c0004d050f04400078901a041d44582c0c01d010046550120000b00c410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 58428384 1250 58427134 58427143
    0xd02072003160608180604030306030201030b030c06090f0303090907030b0f01080405030a0e0a090204080307060606090806071b02040501030f0510021e0309070302100206040b091203070305070207090501080d110c01090303050c 99
    0x501745030003141c1c40c1d4902420024001c1c11680412070020307040544e0315043d4680091605000c80c0002c040602d842c0c41c103410049000204c81403590940000d00c0350003156550b821070b1a00c115185d440101d25115294104010713410b00c129001d040c07203c11000d000c0810400000d940040320742e81844206410341200080b642d554580c000b03101240001030108a003103010015100c003522070790003441160384a2109a0309035506000340d402c690f0190001502451090455000804a1703031081001d08001c0c1e0041130a42c1d009030410b0300c4102c0750b2000c41040203001c100464081403010801c508181003ca000120100c1d15610400210004408554048000d12038100210350060821030820b2900801945422044505688110801e40003481143c000700c2c4000314500c680307041c1859942c4150060b401404040c0c080d00c210b21a0781d0000c51404001e00c41c8a01a0443c4802010310b602c0307200b0001c003c13103a00482d840300c03078200c00c9241c11f2a9800c2800c0c0000d49a041c04c1150700c42c1000c07100380d440d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 58429634 1250 58428384 58428421
    0x190e061b07020103060e07020721170304030507020414090c01021203061017090d090b0405010203090409080c06010e0a0b06090d0b040212101a0609030d030e030d02072003160608 78
    0x11b0310502030103000c80c2c00041160031640405003030b2403840070300350681c0d015108170b030f074042c00001c01400090b030301800080065500c0b40c0709050203820304909070043780803501e010b1b0060304009101030030301c48007a60030480c00c0041d10092008000420100481d4490307030001034500d50282c61155054049030703004410742c0040d0741485050480c14504130042d1035035601c0425500012600076130010808031400030450b4196801a0000c42c5000c6010051000a00310366000707607803510b0300303115080c1c0d41c3d0390920105000304403480c04c424844c00e1142604003160012400148102003c101c005116210b01c0940c0d54010340003503041d81d4940c0e8074000300d003129100403000f0060380100035880c1c482401d1903200000503020001121044d0344c0724000d000c03540c0709000e1030a274581c0c003030007030042100d200390001411070301d109090340c5c101200c000c807000517a00210000c0301c1d0942c2040460150703120308420080075500880c001c2c24008080c0d040700c1c20b9181c1c5070080300104061140007803819084000761041c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 58430884 1250 58429634 58429649
    0x3120b12010f1d0a03170c0906070b01080705011701030b0a0908041707060f0e09040203010609111e0412080304061d060609010b030105030d1b060203190e061b0702010306 75
    0x18020b01c8281c44002c180c400e4080303000c1d03002c0070701c1408185000640b45050640c96240e88400040400144c59030440040c98005c1400003007001e1072541e25664048d090081c4100c01e015555414042d00030f0070140150056030401819880c143c045c11422a0400c0c1169040608108551111000c2a014002c5510041c0860000003400078418100807600710403c140142aa90b006403100f0301210380c0c506140ea640c1c0002e43c0400d800c54649854800250864070040000a00594600302c80050b50b2080d50445204000802c10b80208004540740704480701090303240914003410092003201c04624900f0127445468080005810003c00368401003d542e841c04880302142000580d0b50b958034400c603850360040202000005081502e036041c0c0b4161800140035049115610000b1621100e00507600e5040080c000d0007a030115000d131000710300503000811a40d400d160000c0b60f001c01e4a4401080c101e8681c89181044100070714030408412002c11401001c0d52030314079000480203851950040300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 58432134 1250 58430884 58430891
    0x110324030c0402070c06030b01030b010518010903051c0815030a12121a040b010e0f0105210c0a1409010f080603010b1018090615050c030f040602010207030e0d03120b1201 75
    0x170700990020300b0303048402c1a40c007444444000c0c4011801d0300d02088609000c0369081c0079012407504203a00c00d00c030a036018986000343d56640e407141c514100c15600c07150b0f440b01405030301c400000c4d44254455446882807019404d81072052000c80e60f00c40380004050300c428414100740d400c03141b16002c000f151801840090180b000410f200f418810608100075103d41d10b0301803e100c0550080584452601001300002041c0e00c608005441030783c08545145500240421800900460500828003800200c55000c1d190390100100ce040412501180011a9400d12507000d5582c1d01c01201201c1d200d003031030304690303a4440c01c0100b4090581c1c48104c5900c5000744281a2901b6404030f0b487d0b00c0e1844040c03150000d90380e41e488a0040380c1c0203025580c001540106011240d6000714024590081400c04403407805007100449041a0059049200141d40000750441810752084460b11a61401c03500c100c0300880300d41d00941209006070140c40416100c4c41d90190b81d41d0f0300c110010442d040c220003030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 58433384 1250 58432134 58432147
    0x6010e090708030a1e1b021e1c0302070501320403050a05150a0c0c0204020702030a050a050706080c09031c030605060d020301030b01090902010c1e020d15110324030c0402 75
    0x7602541d403a84000c071460104a0f0f1400c0c0203071041c4020856903e641c0c684d034840800e0b0703400340008d1500042640300b407003a4030810401107448080b004060344a60302c15102a1504e1450f0090038901d081e40068104078106240ca000d0242c1c00420300842c50502c242c81d010340c0503045419845020342e0780094070794040c18441c4c00900402081a144200e05c141100c103060303071051150005c0f40c0d080b074050800a0f4909001c0c5006042541c01440c0352800182180c040115980d212480c0c81042c20302229140c125810030401540c010946e00d80021104c103800d8208800c070740100341e90350042e980c80e0421000c40801d126245011b640000d02409010b00070640d620041050310000c0c0d4000c0c4411075022014500002d5041d560b40f1641c880c07580d05943d00700107000309864840c0f44120002040500540003495040142e8466420141c0140714844004141030030307030510b80407611004044210315904008000d010310a400303501308405001c019654031541c3d2000400c0c0341c01681680301d5041840040d64 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 58434634 1250 58433384 58433387
    0xa02150306040b0105041d04020a0e070908190b04110409120c03090f080309150d09030305040b06010206010b0f180a03050705091f1a09030607030c020f0a020306010e090708030a 78
    0x25407040c6415903040c80808440801103e21788245d01c40d0000a4291001f800b00d81c0c1180014284c00074002025080d609413180c0c0c10f1640d540c416034207040030401e902001c21039440144404d0f5103840040007084103a181640f1034825115004000800c03020010141401c079a45651011501c0d40d0007031410380950150ba41c019000c40200407050307010510035180050604007424a100655030200040e50802d9001002d2114082d048084643c0c41801401180d01507090b84c0720b102c0c185030103035030081a00e08042c00c1809540f03001402490454001d10f005000020390501150460528003140f20b40c1c42e110703980d00c00000129640345a0703100141440020a00c000091040e05841080303412440d15140c2c103900500c1c10751003140c55003645040c640100b104c0207034541d000c0c034940200015a032034060000c001a081100840362a004641d03112030f40101e05074108911150107079107000429007a0100e40000c0e6a980c0c2c144121702e000c070603107400995504e4007801450000c2003070343d0849440e04080c070030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 58435884 1250 58434634 58434637
    0x1e180105070806210705040902120102070f0c05040c0212090a2c0108030a0e04110c030a03090b0109060b070b0603070e0103030903120918050604150803070b010e04080301060c03020a0215 82
    0xc0b114401c0040d4180d0000c070707004e840c803081d1300038040300c004041c003a280800b404081c040408050742e00026101869400070000e00040c0030300c0c1c4c4500a0702c11604498035024002c2901c6820160203189488502144640c000820805031052400004c1d1a0035050340000d805240e6500b002072615005045e0f81282e031401d800d500d00d210599080b02410f41c0c3c0341c4550641d20f0058500311000504030b840e95020b5030420742d00c44428000c910041c0c500e841500440300b441d5070302000c0d0010002e5035a40c5c50074180010800300c2d5000d0550705200b4014545020841a0280121701c006002644034601258045d641044901c2c028189903214450540c2d50b8140540036450a00c801c4c0c80d0221481d12007110244101c06117000d0711140094600c020720480442c10090000400d4650095501c0700151189284402071380000c283c1c260003542c0e13880c041d190500401174186d200b01c0c2d0700e4456005001c00a150fa00036241503991600d011031600d40c850800f08d02e0304012a00103500403000d100c0c601c1b400c010410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 58437134 1250 58435884 58435891
    0xc0207090c08090a081608040e06040e060c220503010e030a020f060106090605180913030201110313171c05041a010605041403010605030111030906010e1e1801050708 73
    0x408001c0c4910420701595022022240141d0320340010301000e0024070b8035070142005003c0903104911040245e42e03241c1150340150841ca800540384000c1041070b1800d4085c9541c00c40020003d0002c5003400489210180038401041515040c010560480b9180c041405002448010001d1103002c0030b0080c805c0d01e0380e0240314914010b001d40c4103100580d00000680504031100344d40ca040d046490214111a40c0e08020820040d80804960007280e6a40b0807500034050400f941010f0094880c901d0043c3c01c441c600c2c0002c001842c4d0510400c4004484c26007104046ca40018010b4034224112900306070512607020a42c58442101c40e8140301e030315a0303a1205200340e10500c04609800b062000031028040309101d1900007503010003083c8140711180051012540008d03001103001c5817500002400c1da003100359100c60300311020080001617401008103500601c04049001142d00f0302d1075044401110840c941041400f0041c00706846409001030392101d001d00034002c08c880c2c01d040c10018900c1c1e0054 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 58438384 1250 58437134 58437149
    0x5010501121103040311031303050d030e07080c010f091206050610050903100f0612050109031b050a030f051b0607090501110606040903020c0a0306020309120405130f0f0c0207 77
    0x6848800311030a1520a921400051030000c43c00c5688698003182c018410504000c032034041444030a0403604081445406148548090880640803580080c2240d13402d104a440a51260000b04000c0002041291042000b0300c0c0580c1510701088040c1c4995003290b102c0d42024000790120317401c1c0700840c0c3c0110f0003071104454040f000034001c40704840b030f80034080d81c00e54950030002d20342074090079540c40114154442440480c0866944c03d480c1ca400c42c8200040c0c419035103401c0c091041692144660380d1041070300b022184d00320303882d4a60310f5036030141c410010103200406410f1012580600242c0e152070400358107407020a00d0648007161180000d5641c800800c00d04680858203602800c08012030400820080001e40c3d510420440600080f020030340030b43c02480d81d130b1035180c0c4881000b000130754000c13080940d90707041080c90146440c80c022202085001c090005100350b03a241c914028440900350408144d01c00c08082900017400c0c400700c02d0950602d80b505000c2070503008141803084602c0c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 58439634 1250 58438384 58438397
    0x901140912190510020a0206060904050106092a020106150804031407060b01020706141c090b07020d09060203120103061e0c03060315020906090d05030f0703080103110a030c060f020f03040905010501 87
    0x1c03062075801d0303008030b03003291b030143e04260700040d4070382081d44410781d21900840011030b40380e580350b0070b070b404881c60700ba00c02110584006003803040f44510305c04403601301101c0c80200100d0385003002d90040400342c012664104144000428141031041c2901c0c00c21641c7c0d9040300e660340c03043d841c2000c010f1101c000f2640c0903004104c800980c2901482c40d440740c1c186030321030003450901088104140c60103400e41403480242d6854030940425101d0b12064411234242c9c00600201c010404098a6600aa0301810865000700b00c141641400580c5080c1100d6100c88081100d41482d070000303004400d180c2d5003d188a14000b051400154140c102a00702d9008034845844080031001650581c0700c0d00100640100d420002030006007030001c86078800c41d002d042564102507a8084444440e4460141540043c001d07200501c2030080c0001e00099a2104481183c07120f0315590b1458903002c880c0c0305da04180060b507800400c96900a200d60a18000c0820079203a8494540142c10001c040a005040c0011070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 58440884 1250 58439634 58439653
    0x312060b09041530060213051c030e0f0d02150a030c0e03070e07091e0501110109121412090601080105011a0f03070302070609051c0509011409121905 66
    0x3c01c11401403d940308440c0e110050b8103107105800044100c1040121100001050340020a40501c00340000f4807405d00284180e92912042080345c0c3c0ea60340e0806140e51841d0041ea0000750081303a503108c8a0340540c0d840c4080d85948000641d41d02c0d95440c0030f9040300c2c080002c880f8901c4480028080ea03034141d1010400340451840842d86040080300b0641c26030b01805007485001c844825281d0722010b10300d4004c180d07030b448501284482c1600c404010055040b0300091140d9a04011510780090401c4004c00040c4e103580ca4041e454a0100d40d010240808281c8074254002c0403422a21810183c600120b00387c14041c0d40c040e03840809114441555180c00004a070141e01640501d614000705840d0500341200e60b0b01d10442036101400c21010303d9030801240000490034040c51382403a0180f405801401009502400035200f880280e00c00c0000420180301140e0300700050180c141c0281c00d03102e8941c626900450314910f10a030a0401d03074814400e10217000c003260606006042d01c44d1040d25021003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 58442134 1250 58440884 58440911
    0x207030809010e0a0b06060304110d0302070905010e0c0702100e040e0604110a0312050306010c14010207030e010504050a0918020904050d020c06040e0c161502090a0e040506070c0312060b0904 84
    0xc614181c020100b05d20340c000315000c1e242c07640103550414040c1042c140e441d5803250006a41d866280c400303e001d0b81001e8010071a54900e44a0280148490307600c035800da251984400005110301c0f0030080c0705015040c00b61000c580300700e46015980d03902400405c0303542c00e1901441e669660880342241c40200341902c200603410030148110840783d00c07805100705403141d01400d440ea600010b08290401c003070f588460001c40c01d1082480c2d80c900d8140001030b520012410001c00c26800c24920368144030041100f04142e4a41801403021114000300c0001c2c0076008d50580d050003600c1c281c000e980400b611003404280600455921706021164003201c3e607250815041c0300c44c50185128100c00c550841d03001034010700d020802031803034a41c403890342c510825559a4111920380360f11900701c0281e9004c0391a040c07505104200c04090f054400c420a101c2c0b52503580c190713540100404500130800086c1407141058011400007000342c0180038180401500c1d006142420f4001c1000759200c0c9040c082c44950b040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 58443384 1250 58442134 58442143
    0x120b0c040b0306060a031b0302070b06010807120e0a170903061b040302010804050313060216080c06300a090b0a090b04081309060e01030201090512030a081005040207030809010e 78
    0x8640250a0314115078521013006544e400c0381d140c1c07409041c2c989200c0c492410011703000d5542c104090b1001171301c4042c142002c03002401c004110030b0501050005000c1c85a030050141501100d03850004030b405070f0010541800c04000c1440100007a400172a250007a041d503030041c000c07090381681168450b0b91203800e403601a8584218074046030303100300030030710265201e0140c1c298028000c008072443c050001302d11488041031540701d64016044040c1201d051004c00d400d041c020301907034004002400e080030004006100308100d041400500b8084030780c603072500d5100d0030714500031219081c0c61840c140210001514210707808540b04800d02d8009401c0c2140c1d4841d4604141c0c006980c203000c1e985075a103200381680214071200d0305119809c000a004079041c014140030700040900c6100f194954400909172000c20740140b0b1161030b014602d001c0c0f5480c004141c1c2e00c0700c819807514022a0703c4586514900c81612742180307030004e000007609818150000440390007059101c008001c40d202445846484 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 58444634 1250 58443384 58443389
    0xc070e070c0c030b0c070f0b0a11070b0c0306120a050d0210020304110d020f0a03050c1f050f090a1203020105060a080303061c05010b091305370609020a120b0c04 71
    0x180c2030b400900c045650384420b543d0040030040ca90f8941801900e079105082c0d03100804450f01c1c1d07100000c1100500c0140a98440030007003410322170801500ea0b842140e6902e00400d451b500480c081700045041e6a8410220b0307002d000c6505031100820241071540d03c03419041d4010700948035980d4841ba0009117482282d12507500a00b11205180c0d9000412500d8200c8101c00d030390000044000c61610342e6801800350046100340024582c25a0350380500190b45c001c0512601e8491040d0000c94540790044100d600c0300030300c1c40c002c1d580d62480780c00040c040044c030782103a0210318001444504041d01544000d0040038200d0f04030750110390700c804241d5603120171581300790031240d050440c101c03400080742ca59041901c9040003003840390b002404200030107000c580c0500344034441c5040809018041c80301d801d240c030f46881c4000c6450b61130244102c000b408002d00303084941c181c80180701440825071004120950080c1008666a624520724002619004094070702c00c1c01c100114220320010400c42c0c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 58445884 1250 58444634 58444643
    0x30f100501020d1d01020111041202040506030c010806010f050f13091503080d0b060c120a14030702060103111201051015050310030308190e03030a0b0d0312050a020f0c070e070c 78
    0x2040d44036134079041c0b040714141e84810b05564035a0300e03403688221001c01400181450803102c210b5032841d030040106840c0040c004c50300036000010700744031a0368032450050303100c0000c0c00d24410000410b60200d0b00ba100c2d02d01d002c3e0000e030703021a5081825001544000495100c40b0052204e0340c91006c05084811640c0b000901c8050704004075800d070380440e00071101081005241a082c4039260850714180400c4403003080000302d00050106c12560000d0958070390780071042e0b8036411341c900550013a6444034180005403909030f285000840c00d50b110034100412140d650021300c070604100b0a4201080904e0040d999036901c00c00310301c4a918490001d4a1044040c07540703131440306145803400d4480380000b070921843c0c5407881e980074000450030b004014180b1580301c01580d5a18040700e40400700c4000e206603510403c0341c0c5840c1d5003c607a008040f00031480c85400e00080549072070f00440001e116030503200c00c60640c045160791409001040000c01c507001007001114076503c40000b102d403010384050050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 58447134 1250 58445884 58445897
    0x30b130c0b0c2a06040305010c031401150309150f0615021f0c05040e04050a03180305030a08060103020c011a130c020d0e0f180a0605010212090d1106030f100501020d 73
    0x1c0842070310320b01049003d0000f000c405039842c1c2010891951040d001076403580e44541c6200c01c000c1c1d1611411400c002543c0b03d40c2701c60350409840e442000d402000e44c10805485000120034409580c0702d48000b140200420000300e030941c01780c00c0240c40384e845081c00c2c9aa000350845031803800402e80c19008100c2007200c0aa821402005a004080910551003000803e02000c00d4488144901c00d01030b038001c40080a01582514000303084803641ca03050303054070809800420008100100382c0d07140c3d07289810320740403d540f0f000040300280981e0820b40420740c02d00c1c402d143c1d05c0b0046030f9141103041e420355400c243c0c030701700c507840c501510030855a1100582c000302809402d5841541100c030007040007001c074072503030140790001281d40784000800540b075040071080c051003440380d1041400800c400c1c0040c16803803a006050300c82074011882d5080c020200603075001c080107403000402d000c81d00c004114580324280f0f0394046650501c200c81c008458500a100810150300000780700324200d101d07940c3c48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 58448384 1250 58447134 58447153
    0x60301050a0221090f0d050c060604060509060d03031506090e0f0402010903020105031b030c030603160b0405010e0d060e01021306030b150f0c0703060f0c03050408040e040c030b130c0b0c 82
    0x403c5030400c01400031419008003100700c00c10080034015600d880c40f403070b0307581521b500358004103508250001d40703001d10035490203078100300a07200c901c0040c0c0d001c400ac0f51003044143d101c0c2020785c0545501340c900bc82031004460080746294111420500b43c88030100403000b02d56980312882d00c0010241c0f0b010b40450400c00e810401903115000850740044a40380e501111201c040b4020968ac20944c2c030f00015032000b0082204a050400c581c0005c0032070a034001003440c0c030301584640c0a1103103015031070420104507108a000d444600e507005040b43e000204000e108050300071a4000c0d0011406440f0200f0050400521a442405041c10089005044051809205401c3c88160b0300248408400680034000489400014000640154090080072071014145400780c002c076071000422001b4545000c0920011803080c0c4252410340d00c1c454518407594480b410070a500c081c1030ba2008042c130580804011640c40300b515144242413107a50010304854a80103265900d0203100c40c4100c1036800701c81ca0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 58449634 1250 58448384 58448437
    0x80d020c06130302060c12040303080f070807120b2704030306050303120703020307030f05090a032303130212030703050c070501080c1204020a17031c0204030210050711040f05060301050a02 83
    0x9210b15444001150b1071000300c1f4150580135042a4015000704002000300444078100c0c8044c0c1c0d61143c05440c003610300b46050701002c0c00c241600070084017002d41d64070306888581c5038030130402c1e00d1000c1221800d01c4d1a20740e88040b1500780c81150218000783c00c01d000002c3c1410000280c3d122044604c1220b440342c1d5580004600030f410007040751003015100c840460440303406104450040d02241d014001001190a01420300d0b44401c040301d034000080402010b508a000b0b06a0340c021019400450311440c0a0000403075201d01c0e144040554000020580105a0044010702a080024090b105020b54450041d20290011100c03d05000c03001c00a01d480c1c00100250503074024030041c0743d0980d01c1d850349903840c07060240c200304101d03a9000049944501c1004124811450702e4100d05501e803600b075601141c556040034a90f0000e114003c1020001c00c0030184034580301d018090020000f651103444a0000341806580450081d440c22000c540714000e280221600035680440c49113014010300203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 58450884 1250 58449634 58449637
    0x423010504060f030917040305060a051014060304050717060403030b010c020a05130905010501060314060906280902270d080912070e07170c0306031506030a0c080d020c0613030206 79
    0x1411280c042031b42120400e6660038402400c06507000e20010241880c2c00e104d00340484001900c10299040201c4041203590851030b511106400c0507603d0b65200c3d00d60f8a4020310340709007508064080000c1d4001700140c2003001910324032a078026501400108220030041d00c80d0f4021003c0030b9080b00b081201030259041c64442a071038502c00c50000240413107540c41e0142140e00a8001500194403840590203040300c5910707483d0404402c840b013030118100000054914524100a541d62550182c7c2c80c180070509034001d8402429101002e656401c80c849802d19424009182860800184c0d541c101e8182050b603661030141e80d00840c0d0916200c291810042c00407108030400d4214424003801250400a008116009000944848105203101001c07015400c00c0203000d444012014810404103a5001901c1d082581e000f41d110412501e480001c42e080c0031102d42c1c080c10389a54400c00054a080024000d02804619820f41d4490301d2840c081007814410000721241301041018241701602c1c0500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 58452134 1250 58450884 58450901
    0x30e01120603080f180d12031d2d0607050702090a0c0807051602060d05152d01110d110d0201020a0c08090103090c0b0a080105060903030313080409020423010504060f03 74
    0x24610366000c50140002980d4510f407180450300e1209040c4aa031f102034050180c14100e5201c9180203610801c040480d503a1160610f4026107079001c0c0e504401e040400604030b079040c4540d070301c0907604d691030030600203061a0706c6190101d005104010004034654158072035583c1208066803035201c6511464411940c4d034120107040130302103400541810059840701c0060000d40d640c00c4e4041250318100100c20000b8003480115809151881151a5110020b42040c021089a0281003c06d4513044004803403205072404980340d24482c1d40d4101c40240d4000c012000300d5905801140e0110500280032404d0340510760f04080800c6503040e0100020310020013a04100d10f043c90001901c150300c2d04c0b00d03240300402e03500c6510401c2d0005158051154001100e0707002d800c040d1011480d005082c07000c04d50300d10004015665000325040c19000308034810040f43d004080d020001c0d074031951282000c411610513022801c0d20303510020800c0078070754080d20940e0100c13640790720307080e01001d10b0706802d42c003500001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 58453240 1106 58452134 58452157
    0x216060c0218090303130c030204090605060a050406060507080309150c0408010608032514010c02070503010b030a030822020604030f03020c040e120c0a020a03030e01120603080f 78
    0x4100e07504011091b40d0031200f00d0f014105a00c00e004141c00003035205040c80d007860240102504168040c03e003c40c2c6140845a036001080704139003151240c13a002c80c078240b08a001140741c04002d1035004209009a46840c0b1910410034038456007143c400030015070104e001e1040080074440e030000b501031203004501c3c20074500c040c850b004c40da241d20100d00c070030002d15650422400504807100c0c041c9007070081c85880702421010f5142d41c1c071802824082e41c60004045650314001401e985a2605522484102d031980900c030490184260000e80049182c641c0d400010384904005200a5000b800d00694591542c0741c0207040107000140503100d42e0a019002c494240b01080d055040405003070032541d81c0300d040309028106280d07020040e40c400e90000c0000300740b6400407405680b42c00700341d88041d0b062075052040c0c011501d40c3c2c000a420404144a10011030f0a944000c002002d5903 = true := by decide +kernel

theorem cover : BRFrame.Cov 58273384 58453240 := by
  have h0 := BRFrame.cov_init 58273384
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58273384 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 58273384 ≤ n) (h2 : n < 58453240) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
