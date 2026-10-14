-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3259
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:12.23106+00:00
-- url     : https://prove2.me/submissions/1dfec3e1-b69d-4d8a-9580-f0a3d1723edb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 585971223 ≤ n < 586151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 585972473 1250 585971223 585971227
    0xa0b0a200705101e1d180a0b01030c080606070204180b09120a210605060f070614061305060d0c03111e010c150e0d0c03080c0313020112060306050c 65
    0x40000d10070002c096039500000c0004000c007000039600e0341203801130790743d2492a10908149802c41d0101c030080401c01d003168000703c90650084241c00007280b15124902003e818030900104100550a56214040c000301251242c400103140781400380103071030708070300040000c43e013900d0507080420381c0410300000340d031002180300c10460810b00400480480300d2007200e18519080d19603078024600d0204071107406041611291001d1101501d4003d0700c007821000f007a0513590181d03800c1001c556401190100da100b428842e41520038452003030140d00c19000585000198408881c0403001040000c0911fa44140c4001c240c1001c03d0700304681d40040c51140c0000010004980d007081914244070088045040d002160244075990282840002550000c0c0c1140d286009401d82c2019150811500d000d5114208603482000d07840b00012000b1400303a203c030402e54603090344814880c441100c5090610359100510720041d4402da0308403100e00880304001401a89a9031802e040e2981a101c400c414000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 585973723 1250 585972473 585972479
    0x90109050904021f170115090308070303060f0b0421030509190e0f04030221041703070f0309030b010902270612070f020c010305040c171504051612020a0b0a2007 71
    0xc8541864003402e142e604803d5403091f80000100200e549000080c001400030443c42c0806020f504008058071982001214142e122941003c60741c100748103600750004040d02899540603415070f01c4400c5034140d6502850180b40409100075107040501c0c590b0b2504400000182c40700303c52811030b0190a81100201c0c1a08007818000d16009400d03c0d030104000c2101d20400004007440101d50171607103400000500d0302a0210740c1c0303041d4000d101d0040c2840307400b0291034041541c8010074006a038403800e909025a601c031990a001c90040c0c00018890103500045011240c40d01d2003140030010b001405c9503d040b0412840c5e841262007543e55002090000386500c01c42e075018020b64101c40d00a03e0100103a00d8141c40725480c000152140201003000e0b40b029a0106005009a40250600d0850031001d03042a2500c69a15034155002da81001c0300d400000c90091089102ca04144d5001002d00b8003c60402408002c00c2d44907600071070a008030a5140125003030a203085400180c0107001810f1542c0c0303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 585974973 1250 585973723 585973757
    0x120a0506040b030a1203230108060108030f090405040f0f050d030605010203120f0402010512180106050111150c091003020403021e221401080105090111090109050904021f 75
    0x15014000314801d509111032203110340c0300041c000540701d40010501021382e0511905a0051210584641c51900e0600b17041c5982c0014000d103a040f03c18990444040d03a80c0c0d40040b42e100d0081941001c44c5400801851728103141603008540c1040c0508054080a0100d80d14030000c007030320600485040d004a09884a000d40500c18580149020b00255113031246409100541000081c001240707042120042020369202c1c0e01034401070001c12444ca0b206080c940d40d10380da4180030040100c019801c0c00d0010410b544a4204551041c01c22002000005000c84d00b008070140e000f0820b02100b02c040c49008801e40d01c2645440c00c02c0a2a10016902e5040d801403201c88e118140c41d200702c0c040040980422600c61902c4c10401e000a000380340304801501d0010310192050300d90310307030040000c0b000119049006521481c010800d04008010680c5103440030003180c0203002c1c20070702268102d00100064204164044c1d40302e480104001601d0b0b0843e000d0001c0c00302e0720b48010000681d23040035102118 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 585976223 1250 585974973 585974981
    0x1020f1803010b090c09040207051905161e03030f0c080f0705060f1e0a0902061206031009050606060703110304121b0e04030f05091203210603030901050a090308120a 73
    0xf8105840300155031900030001412449400d0040740100e03030000b03c407002d0100a0081201a0340d401710a05118a01c0b8100315a464600e0310f01e50060319411b100c0020818043c0780018242c459240b8401c0965280d0384055410074100074400013449100402640020300e032000401301c1408051042d40c841c8044d04116103050030062a40700807031034903414482c801c0d00c143c8900729a01da03803410350002a5141c05215029008046000390021000302d0302c1c24500b420741143e0b510450003501143c020300d0095406c802510b000b158060543c0d0480c1d0082051420401c00800600c1d0090a084410303c9100f030603a481e6501c117901c000608008a000102080010110268001e85400c1e18021450030311610560001b00a00018248000c0364040d00100703000340c0c1505d030040001010310a000503070f18101c07a10380d40444103807a154112040c00c0c0001c07640c441061402580c02a00550400b00200d0040d00c16a002002c10820310205100000000d0310040041000542030000c00c006403c10b440d00001b61 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 585977473 1250 585976223 585976241
    0x6090106050109140906011b0b04170a0e0f0609060f0405010801060c030207051903061d06070906171b0c01060501030c030c080a0f15080a0b090601050306010b0a0201020f180301 78
    0x888007100800c40030b40c881503c00503009046800202036142c03403006a6081003407482300e085d021010640390050080803240b080c86640140c02010240c141ca1902d22201d2040013041d50100e0110350716801103080c4103a110a520703e01602c050314010300d900016400390411144030303c0f40400040c0c140200e5900601d894014122800c00100c4180b003030b40d02175150030781c2d405454002c0c0e0036030720a5200910082d540c0c0d001960011810891110100f0803000e10011a00c400e41d410301c100004540d0051043c3e00050072614281e645480d29910500c112941c0c807400740c804000544000301c503034610240a0018030b51005088000980700c0d141c180050f059a90f1511641c0034985025241c0e11130980140c03001e5031001c0284000034455a07440000740080c01c40c20213100b02c04410180115102d1000611448010301400d45076403281d4841e00250782c0c41c0c009010349034054010000402425032090098644c18055000250412016041404060308000e0404100c2d810b00d1401040c103050a00c40c11101d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 585978723 1250 585977473 585977477
    0x14162a170f0709110f0f0a0801140d15110a0c1502040e0f040c080d090303030501080c030a080c03090d030c0218100b0913020304030801030b0c0403051f0e060108060901060501 77
    0x88010001c01a9441c0c001c01d00c03580e404252990f0b0341092a40c00c490417204c96034042d1800c181c650b501030700c52198030f4001c100001301086000c8008207504a900c5004510080e000340594142c0c003881d641d038412454041a503c090b0b903290510020480b0903400900f81c1d80c655940c03200036075001820010140040700d501400024810041400440c402c90441d179400160300c50340030155210751501d40b211b1415940444900d0280800c80c2d01800d5000e031070b03072046034041c0d5420301143e621041d800d606c1e60b4810100300d600d5400b0107800d07000103c980c4050001101440c1c2500c3c100350964000c16001c8414180c11000203401d080b0741d004603d0400c1e50202003000c030402c00252460030117901c8004003414051000c0688010804c01caa41d5246007050641080c0010199160b00b010310f0040c00640c002c0c0000c8914042d8000084c2080c640c0005440440e9004802040c2c0b001201c40704440c1c00c500031480d88502d9484500b4039000c4182044124000c00741c8a0090105181143c086400c4034001d40010381 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 585979973 1250 585978723 585978733
    0x20307061403041101020a0501092a0f030201030506130f3602221d070501020303040b060402091c03081501020114061215040804050108060114162a17 66
    0x41c40d001402aa0f82c45540440e844071280c800500503441c0884118000301690f080c21500b80c10000c03600c003000d04503c0c1d0070341081c03c8902c5007005d156200b040350285c0c0c04028003000040016620941029400c444041c041c03000d0f110a0141c900180c0d403074803412518040d21307011a640c00816592800c0221400410403c604403440303005c58682e002d91001c085d210780c00d0303400220000f8400080d4100010300250040101511581c9000841c40e41c0561542c0103004007100043c45500100883c0d10903980405507240fa40d44080c104402500901503540e0016010503084001013a4540e60010040c020740703691081d4907044500d60003180000c0c1005046904160400c0700c000742036903000350401011078210082d440c1c0c910045140102c4640c0703c804025181c0107010a0010b1007008005440003a40c883c00c0c0780c0e03500401991004089c00022040c020104060350b48000d0000040074010302c0303452050740c43d41003410034508640d001c2c46601c0d03410381422401c0012410094103c11250403500280c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 585981223 1250 585979973 585979997
    0x204032307120f0b060f030d021e030a020d11150c090a080309060a080411030115030c060206010b072a060e0906090c0f2101091b09050f0411120108030702030706 71
    0x16980c0b0000c4203009100603c2d0707030b000c2500c039501e00e20352550340c401c0034003120034123441d40b903009585000d8544001442900300c0313110701d04003a010084508010b090740040c0a05105044211003a6030a81c01b1010a4007410a0720700c0e650300c1d0b10743e110780250b000102c59a100d140080401c8400b090641c8911981e50080142c103001d40c80358800c2d181038a4407410945020b43d580d05101e601100c07a40444e43d45075103010a1404c69600e462090030581c1d010b02407145da41070f11004140d0303841600707002d01d00d4072103410b210000000d9042900b0340722952480c150030841080300c46406241a40c19040b20300454103900003510b850a0204803503900010485000269007070909018400780f160781c44200c0c0c4440001007036020131465501e0001d10052203c04a80a90703512032200f00184594a03182c04110341c4500b41a0300140310b1100c0c0e00c1640e40042c05020241080c038104070080c200801d00c103035882814800f080d40341c81c0c0b03c001c00b40200b290300042d669840303c510400d401d04189070418010700110443d40303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 585982473 1250 585981223 585981233
    0x4020a270513020a0c050102040f17030405091620101103060f010309020a081b040c0c1101030203070908030301120203070b0f1903090f060f05131505060103020403230712 75
    0x2501000a020b0b0041c1e0b90b4081c00c00c121002c00c4401006030156000150010b01541704001e08000c50b5817515402003030452690201c1d84a210758421070364000f0300c0002292004c0750305d2000300c0102c1e0450800b00d200f00798001d10900540c2c60001c2c0c02c0315030340100b0009180344a1600400f00000b050041540c0385143c45800030780140e28903041e075410595074000000440d1564070307002024051185c1240d03420361140a240083c00265034000d80264105050040c4603400f50700707540b5205a000320199010780300100114002e400003080742c4c007000b990000005030329006000944c007130549101030f180c403c0b0407130041c10f250058a60201c80c006008006140421101c031090b22892022800e64012904d088001203003c0c080d800005040104410383c1801008013591000d03502c500391210074400355440c071031480c10303000c401c0d44090a050103a8010780c4040005500881e4807a405044c01428070b61252a400d1100d185041911483d59080402045070702003005614010300c0b00041140f5040e9142d622 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 585983723 1250 585982473 585982489
    0x510150c0c15020f510a1b121109010212090609130209190b0a0c170c0d1205060d11040f02191209050c0d1104020a2705 53
    0x203000703001070302801d2802d01c0d98424482228080352040484082080079440c1d50341c2c40038400c0c41c07041c41c8001441910a141c0c140907408040d10300208008003580300c0300d0030100c0c00074001000c9114140d617414140c2a01140c08245920075403072540e0350800126030142102c222210b60040c031b0142181446400c000340c0c0e0000d0381548a0b581c47d41d000751a1502e02010500c640a520f0046500c481a0180c104116005a01802003a40211000350505002824009000405008000c0d2800c3c080040040c42805a060244ea517841045541c5103120100c020004540220303c1c25a0141c000c001c3c4960610b520590041066100140400c01030610000003204c4456a0100520481d4081004c050b190754544c061070113400b10440c10741d0b84501c442c84010355520000c8038407010a0b4280700180100245100303540041d5808001030000344100720800400c85083c0700201c80011502c0032a00e40c2d521580050109065240c80f100070102c00b000b86400268148100744c80c49000001040046540724070b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 585984973 1250 585983723 585983729
    0xe0f030a0206070f0b15030c0a03050316140304060c02010906260c09030604140106080c1503060a031202060a0c080403081f12080a0314040c03030e0f040510150c0c 72
    0x40c21583e9910349141002070b1100b0441c016000580c50310400c811102d0070320040451382d00c100c050381c25a5548504201b6498014000030303006d5030040c07040c0e00606241c9a20701090b58010b48003801204201070805255901a802420000c1e0100d03404108550b0400600f6000d0310860401e024401ca05030268444043c0651107000000070303c0b00890200100e0130212170b0710440c05070940d403891030316080556080d04080d050150395032030072000240c0710001148000d030b880001004c1e003686440c1d01c42c2007022030700060074059101c0d599140000006261505080c20f1a0b59600a8402c82c0307000502a411140181c610000b889002020040081c1d48511010ba1101285090742142ca124a114480300403458001c40d080c5002030070794034140a4820701034000003100f0b68092022000c1e012041c1800759080d42d006004648058040c00043c0c001e010f0285010005460040d0248804000030280c4170305032440d1403080343c001c4083c0255028100d402010501720b060095070f0040341d80d03c080358140720348 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 585986223 1250 585984973 585984979
    0x204171c030c051909030312140c0711090a0527032218060807300302031c05070908011a1504080d391118160e0f030a02 53
    0x20b10084140390103901590340b5080601c044000e555803404000d400200180016004605c50101031182e0040b28040c541c42c10303064400c01700103038031228480f0a1b01e800140c41203e89105a0210708075585495107460b08c22040c06901141c68201942030352000d819002c159031494a010941924051001044825503426081c0b409074484800911002d040116088844004424280340d10ba0b40c034940c01c010309880c0c40741c040c1e8020980c2c0d0b81110341c51141000d240d18600c0329600341520034801d4004c44200490203030041e00d1a12610140c80b000c054070401c1c400c1134240d994010f10031400d9000c041307070018100d44002002100c3c2d90405062020310341c2c000c881d100c1d80200c01c180001c00d05400564000700740d100e08454081d9112a009061303d1894983c00058040c00f244000216040000c40c03050400c4403000b40d614107209813940d00c180c1c1203501c4016089402203050300c03440402a20214410060003000d01424000603e0003002460b5855250f442441d162180f030416590114480b001c80f5412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 585987473 1250 585986223 585986231
    0x11040b010503010b1c051305010e07030c15050f04060c11090c040b0903010608030309010203011a0703120209031e160e040c1202150703031508060403080f0a060f090204171c03 77
    0x3030702d4401c81721150080c2e202c0d08070b041400f4051500408440c44080b140310340c00900141c42104034003982e40c1d0403440080d1107582c420804201d07070001078003131400b40d075081d10306549400c4c3c2c442094052a40150320070000107060001000c1806829000380741d0b0000e04a4180509042004494020340514080e0704454000010f1121140e50250b0000004105800c113681e22440c2103000ad9000303400c2485000e00c1024615005007001d00510b085071005070b4580c03554101600d4050b100b00094200300411078040c444d2004d0310341c005941912100c1035000301c200521a030400b00c0c829401c01e42c45035003c02441c2c01c03101305110001d00540c244c4002c1d112031b01c902185415a41c0000b5000c048c01c48a4983d80e070070000381202c01e0541c150040e81d82011283c140c2803009036100da520355501d5085401500003003085d07020a18401c0404172035070b0481070114001c64215155484041c410340281e100d0480030ba0f000030304000f00e210741c07094640b09071004005400e90100d00d000d4030303135940d60740c4d800c4400b01135071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 585988723 1250 585987473 585987487
    0x6030607140903100506150331150c030606090b07140c090109060e011413091b2303010204030b0f040204021903200301080c120a14070311040b010503010b 68
    0xd04019184a0790303008084501c0c41389002e01c201c0c010441034a8103070282d0f4680707800c03176119001181101e024800204400c02c014801e804004440c14850500d0380d15901c1c3c155070390f000304041c080e00c11b00d40b51840038000b60100b00f035100501203e0250f230054040c045e06800c2081020351b100140c4031142e0300110390b80351042006c2c5019081c050243d082a5000004038004a05692154008001c2e204011400303c01d503621180c1c06005d884141010030b6000c20025021003000c2c0703468100d95102440745c034840f095803100c45c041e01040a001e80180d03169505c8101c40320010043c00c2c03804118050150002c62a2a045440c0c00e0101d6500610742c00c11400b0300d1001c0740464a550341100d4802000100c0c11984910490740100581015442c1d046000c2c0504000421158201c003200d049800c080300410001003d1024004103800d0001d01007074601030352441c580401c6006140303695006011002e0300b00e40303066251036410000340100407370255180c41d0003c641d0b40d0f00b16003100d05446040009640304e02c0307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 585989973 1250 585988723 585988757
    0x6130c0c021e03010504050a0302012009040213150c0318080a0b090703020a090614010e210307020a0801050405160e01090902120a0830060105030c1201120311010506030607 76
    0x2c1c01c1410690558a00020407081c031001259414005200354020700a050a808100e421500c2001c9030255005003000200e840349015801423007803100b00f0100c080c440307640c4d80013a004082001c464101090f650380c0c9290805078440d100d41225180383c8400304009080850300c0f55510303070000000303001903014004116043c100304408002150300402c0d03010131946400356203016000038031400210912446c40401d00307600a4508001d102406001d801080c041000d090a01c0d401c0d00c0056a201d0004014000241e1503000380f00e805080c401002003104d0038689095864403042c404007031400b100b1003100303002550050f5240d80c11102d201d880401c482c00d090001400f6424003030300c145c80620401c4000400c021030000a00800c1840440b0007203032945862600503d032010040700441803904a0000b5520f42c0039502864101c5201d00105061405442da1101d4008003030f040a009851841984801c155200080c03085c42c10786040280403034140080801d41d00c00004d40741c0414050140004c0d05008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 585991223 1250 585989973 585990019
    0x305060315010b0a140c0d082703040e240906061b060f1522060f0602100b100806010804060f0c051c02071e0f02060a02010506130c0c02 60
    0x20354440400841c0e5944168580140d440780c000040801c65840c01403100c0c1040744281d448041001002d800c40300402d020440e503d035001400101c1740c0a026501800301480401b000c2c090a4042d40150750315420b101c080e484d2480001c2c03666084040a65484217a202d10782030304082208145c40031a070944404000600900901d110000d51410012181000280005809024900341c802c1807105c3e84800c08010410103100a40355000400d0010320100ca040c84e0a2030b03114a0b080141c0000c0c2143c84440c14818044594080340069016107991a0441140d01c0354407540803040703607450000a80c4143c080d0191038010005414420161b000a041c401d26401400e5a013600c50320402803aa07000b0006001604102c15a4040300c0075030f06c916010701203034401c89030302903000311044490445402d59030410b246c0c9d00c02c00311a43d008a464a03c0140c440740b014013440710064001080d5440c0100501903425001c80350040c141d800d0072200030205400c58088004103405941c041110310360305008810070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 585992473 1250 585991223 585991243
    0x40305040b031e09060907031b05060406020d0806040504110409032d11280302010225020913032f0601121505150d060e1204140105040b07020103050603 67
    0x451400400c00600600c25a0f1191014842002d03145a5844d10092950b88890445a072206076000440c01d001188888600f803102c4051001180c002ca500c0d14007040b005d070491342c0f040002d0303031040c203840f4251038002d0070341e40c0e001000784c0701000540303000d4507040c484805144039a401141d40381003c0003410310405003140143c260550907a110b003600d9111500e030070080b9508000080441c1c05a5008000100300c03880e04ca52911181d140c00c4144411061316002e521008506542d03007000104030600607910050790700400342480366040900342c010302500060040600070030094894400c000030790400101d07844c48100310174984030110710622407005010188803000a92055900000b519a100c2c868805250f224241c1d071303e55004201442000e50744c0c2902c0c0b200301c95211000398505418058107402010780101d4000c645012010120741c04c201072004191020503000a0500801036134441c0e1440c0c0007020710302540340901c0c04188201714040c03500c0c020704040e160300c0424110760b0104540822 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 585993723 1250 585992473 585992489
    0xe071d0a09021c1a1807080a020310112712030702010f0323010e060f1c0308040201031d0c100c0b0c0f0903031606060609180906020f16060b03010908040b0304030504 73
    0x4c5401c0c40f4400341502c0341107056020300351090b20781c08250040c0220703c4a4083d5406401402c4844040714600040e08a4400f076546941050000c0080151300d44d02110784078010b02041001c0300341030030a02c88041c40003528031708603520130400b6000507603220910181488480c0f800107880c0c0382c40c0ca1224500c2c1c03a14072052041c01c100d90000309861103201c00300c0f40240c40440b042a02114210140701c40e188080a402018240714900400031a0045115540c014070500d4001621000e01c810701c807100181d507020074941c1d40314110200301c42c01d202142941c411280d04100300b0303000c00ba544a241c1235034010690b42c030300b00002c2100c2a00750452400d1300c508000050982e9140d42030000190081501d49100340e0b841c900740703840080c0c1d081c060440d140a40b0401001e1003c0f0540302454000034100044044509507400c1201800503421940940b00038114085045111082400c181c0c0c15101d40d4403546212307914004080d80003400884c1218200c0f201030564a4813565641001d035200e0190750300400c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 585994973 1250 585993723 585993773
    0x14010c03030518011a1309080406080402031e0a030e01021b040905071a0d0b04020913020a0909050106090f0f0605032e0b03010e0f04030e12010e071d0a09021c 70
    0x913500c0700d050000520f511709840500c40c02c2005500f007000ea03070325540041c221500130030041c09618842c01c50b0541c0240040c08660b408074010506131098000500d41242c0b0340c0000042008150307000c180408080400d01c01071810954403103c00c01490700715441c0380d215590754a00038041240610080005064010241c030741c2c65140c5003002015845040189552480c2c03ea141d0b20528240c400e4503164100a02580f2444600e82d8ae40c000039800103da00c014041d541400046089890150718041d1415940d0084094035081c80c0a6061010790005268900b100d8024052294000181c95100168000d401d4640300c52301c203010303541c220340307150070010790f403009008031300340030308000450495602c0740c40c3e00d03600e5a500e01040c0e4200c0040c0d50090000c0c5104208082a20b0003961000395040f002d0f0000640000c0e58180d02c1c41c0c01c81607800700182410601c041a6103c14100c0119800b01c0315410070b212a0510394002120031007400e041c80201b091542d040700500081c0c60104003101d40c0b0200c810 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 585996223 1250 585994973 585994991
    0x301050906060901170a0602031509070e0102010c050408120f040b0d05270c040b04020408030d0c02010e070b090409080405030313030c060e0d0605061c03030e0714010c0303051801 79
    0x341c89881c22600c2d10f000e03001c3c200c000550b03240100b80c140c50302d0740740802401a614403540da20010b540041d00712554107c401d070800415645541640d805940310303488607140e021840d400642564101c60401c41480428030041055502c041101c65400217502020303680c880c4540d01850150056402c42650000007281001c21841c8503071080d40140b0340d08541030180702c141301e82c4030b1040304110b056804941296846d00c070282003070b400400c0018802403000d424541c841c04220300c1c5800c9454403448075901c4407020141c171030b020b104003802150498003510b00c10b420602c281800c1d03c502c040c42801580e440da4814144404141a5400f51070020705070396481c510400c1c050803d41c1d1a00041e155407032680b0740011898058400b00d10b01d400003505028400003540c6030900248001083e113500700818000c01d059203c00005a88921446034800084101000038050318103011a040b24508510115000880d81e810070009809682c0c1894045041d40c0c896003c8003d809203d22207404a600307100c43c007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 585997473 1250 585996223 585996241
    0x4050606150a0509010809010e0a080d0b0406061e050403020d030f0908010b22021210030c06021209120c0a1d0604020415110703170d050a052203020a02030105 70
    0x25004000c11200d541d444421003401d41898460030741c4540c0030540030092204130f54050108140d0185030340c000001c40c59a408892400d09990100807a24680002001c9014444912504043c001c0c1030b6030420035242446406010109000f400c40c15021010b901154802d209000322000344d5406400400c0c054000d150141032400c618100001141c40c070700b004100c41805200310044020700509282da0b030310602840050181020410b600c0d229000c01c20140c450464820103401007a400440b100340d203141d400d000055000c10f400c20011500130390a26613060110106031a22090100c1d298030300340980e43c040b549001034007044960050310079900002c0c1c410610008514003101130710a0b405542c0c811040208911440c0a0240d000148404503000e0074412030240515840701c10071121040e40384c3d15003800c410402c003103020840b900003560110444941c011035800c0b4051503005c2c00941401500720580e8540800344491003500052058103240c03007040310b0b06600341c029000704042d00308807104c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 585998723 1250 585997473 585997483
    0x221802010e0d0308061003020403081306140313020111100c05030601170c0409020309030f030901020a14070c1418040b011d0c070308071124280906140405 68
    0x109a010401c1005000344a040c50541025150791540e0381d01d040381c3d02c4030100000d02c41c031441e10030700f0035034280400300004807000014100841a078000040e6185010030081c60400c00500b13180030a86d0a106010b400701c40000441003d41d42404d0a41e040003081c00658684100d101102c0040c03402d0060601e003e40e000b00c021800f90308280e9402031401200340e40c0c82440a4261222080d8007800c00007000000e02c07079800b6540102140080e07034580b012070000400c160f001600c40d182a40d600054800300c1d90341150f02c0d419440700c40b80300541842465200e0362000c004501c242c054041114858080c00e5076a41581100400e003550105e42c941000e060be01c001800034060f03c5112441c41d0150300c3c40000d242080340c0310303020b2191007a241205966003101e120201402c01000e11034000400e440d0480144455000101e504c0060942c80301441404010b03083c000e0180043d40902501240c115204003031032080701e9aa85102080c18001840d10300000c140d1f0341c1c0900f141017122400e000400401240c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 585999973 1250 585998723 585998771
    0x70507090b190e191b1d0d08160816080d0c0801050321041e090b03071503090317010306050901050c0c030703051e0f0a02010b15040306050702100e070527010522 71
    0xb0030100c001b105006020710300c040c60f00040c0c012081400602510500361054219192062021504140d2012100312851800e17010032220460041150210724401c0d1003091401c40341d2b031610020039450400809d441d5228100400000368054050546110100084030028a20000007100744c20002c411403450b92103078003031403201d142480103100d900c0c580000c43c00c0c19141e0b0040c12844460300128168000e2420301011030601c084160903143c80d101c1202000e0095001e14000b00d0799213400100a42120802031407490f00b00c0d014800c80d0341c001000400c0d0703040b1990608040c1da0354140c91851a200314290050b201c04a80000740c00d0024030005005011500c030160001d111542d402c0313042054441c15800089110313042844104081042a0080c40e00079240d030055940340441030840d074040c0d41600040e002c1d1680302d540104813604007000111165070112000690300402c13041c5c00042d1120600c20ba0344611780079280607040c10011004c2d12a04020100100b003141c404201c2080c0c1041102 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 586001223 1250 585999973 586000007
    0x1090e01080c1801030b011e05060d0203190e0c120f030f091503041104090201030b030a030201020301051e03030d021b0304080d0806060c06060114070507090b190e191b 74
    0x1010f1000081c40c1c0075505880d0b000031a254a0b03070034140050304001810303c40901c80200720703000091944609000704030703a0003c8000980c0d28501420712400c0304444800c0301100b5490b04c1e0703030080040c0c004520009240c0040311415105551a0071759441c0400e01210f042c51400300107618802010540010300c00010242c5425069555000e50809a400101c801074403c001c055003003500c034603041d80b00a030480d205044c001000440000824600510030400300c0260790700000600080c40c01000c44603111006245485001420201180d1a400b51100da20410f54003c00c284180c0d02c55141503000c810003640440762599943c2c40c0c3c01c0d0b0f556540c00c007903001003890000416000d092120481c1d0102803190020503071904d404004503a01444007241c100c01000c14800a0009a01807001e0002847c0c0b10344041034803002c4c2002c00c00c60304510a00c040d02c2e12000202000891039142c509a80641e600d1040c04034882d200030000c001e407201c0f88a08010202c2192003092098216a0301c8040e10180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 586002473 1250 586001223 586001239
    0xe090322060f050310030f020103020724050606090112020c0a021203031021030f0203040911270d06110f04091d21030a1401030503070308061801060c0201090e01080c 73
    0x42c805942c2031206440354001001002c0c403c0c0086040003003000f40b820700c180b40040ca80012074555108202181c0103600d440704000000340c916509d9405a6034012800301c40c11860400303007000103003101c4035100310814416008903441e107801d41c00340141d1440603006408540d03415201081607031070394000c8944003c6901c09107400304042e040c00c080f144651030b400c0e40742c660100f0705403030650b0301100c80000710301144000c000100d043c4880b80501a1007540701c0070800e803560501030000b08856100c4000c2c4284000b80342110803940c0c0c80c96011741000740c00260004080c01186160042841801c0031006013070b4000500084803070f0240d101d00801c00c80c02002141c1e0100c032907406511400707030354001440340302d514440c04103806000d0000c680080003c2c40025807600403802c0611208070036401501c0c2a040400e15600340340d0000c00d141e0b0f0100086425038100d070101c203001c000c03407070060085500f00725004188004590040c2e04d003e015004440d94068a5a51054a10b6840300b2400c0e0450150b144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 586003723 1250 586002473 586002497
    0x10525030501030822080f0703050606030d05041806030b1003050f06100b0d0b041802030709060503030d0b010c020d210302030411060306130204030c14030c0102070e09032206 77
    0x1003840303050b060b43e81c410b0825140044082074280c82c1854803201854080d104c400000d103c603001c0141c000d400c0c01707a0300640095440e6040441c1001c10080c2003030701a4102c041140821544a0100c0c0d082d150310b034501020038641e05d03022600401d20798100600b03604180e810b01c450b0f034200e60082c00031a8412821518082000c010341a1222019503044e19590485807041c815011548003a0022322170700080000c0360703e060070000d001c0da440d002c80824560004410036056080510082000e0a5505014081c40b4034100c0404c4d0f49101d81a50f00760b0341580c0344c41c500c505038451401d034100250010444000d00c816810402c002030480d60310700c840040300300700c02031115010b030080c3da120315000108000783c000070f0b5081c80401c0d4002042103a012507426101c8c05045518030180000e14003c0c0081540c040c00d02c044c281d140c80d49114094880d0780314000b04070003070303900091401c2079030002940d1502c1910ac00e010f01d441c500840c80050000702c0d00410803203103203045051341030858041c1d585218403420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 586004973 1250 586003723 586003727
    0xf0c0a060923100203060f0a09140c03040816020d02130f0507030b09011e08030a121109060d0b0a080708010e0c010f1e140a0c020307090c0f110708010525 68
    0xb200b9584202c0070f030004000001e0320601a4051030b400340003d00714010460342200001c0b501c05c400e4010102d0715503160241250310b40114842a0300420300a08139180d420700361a072400c58001c0b0000070a0384107502c0f00c81d00c11512104030580300181d0207400341103902750756078655021b0b05007000c603070325243c3c40d0a0002d4841e41c800c0c05801010000500100c000c1d909003031104084081c090100301c00c24100000c0054103160410040100320381e90360300d417148940d413214010286c6441c204252040034007488440919921041290358103003986100162030040f40c0701080303607c05079504c480024041c074100000d4040040d00310480d05002001a6891509890010340d00c06210400c002e0010300d1603d10940e55400da0304207035203c0f8805081102d22100410050b1550ba03011030020000548031100810450404000d140c000e0200c640c003d100510015000418144040e00c030101000a00c000d1043d0105091224201500304c0c0300c0203010074581036050780e551030406040000d41e1041e000b0310701a00740c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 586006223 1250 586004973 586005023
    0x130207050616052d120108010e07150e0102010f180224040b0f071e150507080c0711041407200d03091b0618060203120601050f0c0a0609 60
    0x5001600c50b2402c05110503000041e1000210941491070415265030501d1808131001c1d028107001c001041d030f4103605181e892801d646640c0f607076500d02c1d030001105011450300c080104920074a9860009580070006004130b01500f8580c411044841c901001401c16014448580d1a840c0c005d44040d241c022200300141034501c0d11604212021005010a215005a1400810035050304001244c108101912031800c1310780b101310b01c1c06003110741550310010054016051601203045940c1041580f42900015205183c0240500b100e0f0400241c1d06040080000701c0c8042c02001400810060483c01c8030005071840c299a0040819030f0905010202a00e9400c00001401640003803c80c41c580c6a10039000781c8441d00341182c00c50009002e50007005921410940140352681d00c00c054a00103c800d803040070ba540c0c004800b15001001183c88103161035502503040300c02031801136a1151420b640306224080d03449a080035018851100081c003240350020300480e070240241418446d03101e00300030004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 586007473 1250 586006223 586006261
    0xa090b0f011a180108040c09050a05150f0a0303030b060d060f0f21061a030102070b0415061d07230c010c030509100905010e100e0c010c021f0e1302070506 68
    0x1d1143c00c0018200382d40309422064100d0301c107410300580c0d9900c0d41100400d4400840d0300c0a5019514003c11000d0008608070b6641e0b9102602c0c080c00042c02e82c2d0104802510500001d8149915650b41c03800d6600c414040300d0051840340000c100300d545441d8030403200c010620942500054008000c01c24101c8050700c42480405103003054200c0800b90364840181c080d00203150000c8100004c2d4a0190304c082c0000d0072014480c8110045510307081c50416508514040b00603403951520070f0501003c1c86561a001c9000707410710444d1032075511450100e62581c40720b00e45035007100c601006001d090340c141c006010349a030813100a00545c0100801102280c004803a024620b40c0800c015a042c18047e620090031f0b140640b00100b2940c918806051410368028601d8509540d41c954007982d11200740041d0380c00c0c907003d01e40500d0750322032a00040d500c4030448604141c2c1d44145510445410700503808102c280d280038080c1c82210341603102c040c1c002e401c007070310554290080c0c00000baa20301c1c1d0304609900f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 586008723 1250 586007473 586007497
    0x9080d09060b12072303122b0506150c010905030c1c0315170106170313090903080f09010b0d21020f0619150e010305070b0408150a090b0f011a 63
    0x21702c0d001c0108400004509020458141c00b40e400040700303840420000740141c0304074403084600d4100d030710482c545042c401103108d00305a2401040c01426a90b02d1200400703101178a24868403a140324004a0061841d803a000f4440e100c0010140714110000c00c544410307500d0902d440d01c1c00300f07513200241c0c00e40d88080d0700c41464504a6405105841c122030400551512041c0001010341d15911210a004104110013070554004101e000c854100c49803454050141140b00b40700001e15550042c25183e8003030000035034940f4400000b8030004007580800305080b0001c1c10b50000740c501c3d0511442c651480d1000891618010443e58002400043c000004074401002000d09660f113010180514119103100324800b40c81d131540040d180c08007554440603000c1c90660b142c055240d031030854a0700000782e000600390b41092004111041020820324520249103070140819601d0561030401410180001041100781e881800408164811100c0c180e503000c1c50020344408044009002d1801040d0200300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 586009973 1250 586008723 586008749
    0x1809100524090111030d0f0203060a1e0510051e090907110c09060103110408010c270b070f05010f05070e031506040c17010311010e0a140409080d09060b1207 69
    0x40b0b035100d403125804d0304524005607401c0c008000000025600c001c0158103140d034010091104616201001e540201180410807810585201a18151800500c0b803180f107030003030001440540303000c3c00458115500700c5485101b0440d12070fa4941c01900546070040c0500043e0002903901030003502c2417140d00c038988009240600303d581c10406141c0c0000c1c040d07810552220321694104a070803020300083c01d130510010400004000b8000d000e0700c610303070712001ca240145614102c105407002040c0217540710306808940d0350a05003001d00312900081c0d0001c05075031a0003610110084158411402010720340d4030080301c1060002016030714840b10034181c03001140000411040d02c1c0681c0003031050395040c1060f107500f52001e002d4040e03021003640152800d0b210b10b00c0c20b1501750307440065800c60a40484802e543c00e400c115000d211040c0310030081d8001c0790380d503000005001028064500e140b24a8130280502510b81c43d20102421401c1c4601c1d0040e00c400d0b1085501003070110300c900c00d403084507040c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 586011223 1250 586009973 586009987
    0x60207050d150e10020c07030213060b0f031b12040c050f0a0b090a1a07030201060801180213061e08010b0d1106030a0e03160b07090b0a051809100524 66
    0xf001503500c2d409581c42418250900c2440d40c0c00070702002071405018104c42450360040c030469085544844800a2801d1000c0c04190321580c00e540384030310203085190b2242d0360365142c90900c661f180c410f54005003003c03403d44a00c074211180345204900c1064095041030799002800441c0c01e2414200d035116800d10800d11034198050050b10392810b0040c40c07892076a994428600a44c0903000d81c0c0c00342a400000c10500303142e0240108001400c10400070008030003c69200201400032000091064030741b0000c14400303201b81e800000c0030b03200c8072102c00c0003002d0360701700855055010f12614203103500746106c151300c910706540c042000036004200c001700100900b0821146a100405150300700e961400094508035040001d40070300303001e1500d025048025070802c000c0350b600c001c0c030a908000d00d03c002800703508504e409460302100581001e5440d100d844404007004035800c9281600440071800700020f00102e2030000c0c0071160141c82c0b03101d040ca211480c0c1150707641154070440704031100304412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 586012473 1250 586011223 586011263
    0x1e0602100f06030b10030227010509071e0201241511150901140a0c0e01050307030b15040f120f02060a12050a0b010216030b04110f060c0601060207050d 67
    0x42900312a40c0303400924252290381300042004142d8a10641c0b01011070b0520460400c0454414219100003901c01d1045244032440d8540c0e0050242c1e6004444590104081a0007451070258010500b540c3e00985070344030318002d00a0042d6203803e0182d1000e2804d004030800501d4100c0c09941c1920040900300280c01015510070303518140710b18441c03141100644211000185003800746e180c500011030354020350030300615098009864110010315014281040e15000602c1e010b2950003824480d031030342d451000642c0104031700c1d80902d800050312220070b005651200c3c01072060300c159144482c40c66440b0a5218221100444003d00100d0700085075000b502d0580042d01401c6d40910b006040c400e001542c0344181c1c0c1e4140d5400c0369a0781c81c1e0506100c03668042c00f60070030b0600761510140c0245e00c1d5454524084402400141400c0c2c0042040b4019842c1e1401c8001240710142c00b6035611354520310038a54488091041e50014003030729001091605d40b41c00309046846e01300c0040001c4011007091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 586013723 1250 586012473 586012481
    0x1b12112e02060c0a050f1b1006050103140702060411040b03012301060e011d2709010606080613050402030f0304081b150a050931060909030206040f24061e060210 71
    0x4981f000a0101c801d44503826010400b12101c940c000c00c0c0410b0f05c074980720000d810b41e411000d403022403031850303020880202d500285140d032064002032000b060300405004030f0020441c1082c45600f40d400d0a0106003c0681c0c1030310b03070000500d206e000390700580c0e030394004031420345150b607031540090360401a100362040340c0c9030380d07a1881800501368000103519104c2a04031156645a035030282ea034000411142040030703c6000010702c02c034186403146150400010b0600303080b00008000c1c03c2d5480740480c00b035450411000320085006000c80b565079855807007140d074440901c58050450400e282d4180885c5c10a260440024524540e00314103148148405581d1600302003000341e040b10300402605620180c0e0748c0046041611a00120449440881c1c0017003a10303640c0e08001c481609005a030b50000b5070015a03264060380060205032010036a281442584d00041c822540c0035400c05c455000308295684401e0444090100890740e000e808220651401520720981e0302580100c032081458080303c4e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 586014973 1250 586013723 586013737
    0x60a030603081801140909041b180b0112050c1c06030b010b03060918062e23030a0c0306021c0203160e09390c07031b12112e02060c0a050f 61
    0x560140054840300750345401e500ad031410200706a100c03620b42e002541c00940d0f031081044100300c28081c1d8a85008100400d104911400c076100c20039210080100798103038080e0300a5540141c7c521a5940e440444200c0c07500309680700d0344201021030120f0703a08003480302c3d501a540e00d88409071200d03a0380e408005c000e000e405114030300c41c5020058220511802400741b40c02514000c00c17006442c441e4a0840314035158a0b10069010382c3c014024000410500c82c0d40c002200e81c012000740c0d03104494080e035481070783c0b02c41e00c0403182400481841070007903249c0702c52a0100c002e551341c02220f6541808002015101f034850303a00f4042088183c05098400e010450700440c1c02940e445101c1c00c241040605542c072841400c00650400d660030302c00c004c00302a200c0000005002280c1c565401d24080402e0821440002845585a1481c083c0c46464020f0b06110104a1104900c464140300c8010001803200e80b034148010b01134400054a40b00c10300083d1209080c05681d082d080c005102800380040d07011503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 586016223 1250 586014973 586015013
    0x80307060c18120b1e090604120207050d082101060804050105100605032a0a03091110090e1005040513060c11071a0702220c09060509060a03060308180114090904 71
    0x10304071505c084151352140112030940c0108024a03280c2003402c0307020100704c0c40404540105504000300c2d5240f0740c4142c01c2c0c58024401a5641001e055040c452400280b6501b51050600d4000142241c00c5400300703100d02d001d400240900c1d5507112810715120007900503200840c0c0140003082c0c2c1550312464801000041e81c0805842202125040015410420800001139103410b954000c025207915980d101650907101030220088018018003030300414040c03540340700f6012000418a2808a458000516010303200b00031505200030f0b07089842c46422001d036461400d0043d406607803886072001a40700c011510180c00c0103410014070002501350742075a03210f42e0300e00780312200150b40c42d01c1d0040c00d40001c951071003c0d07941c0301c00b485000303075100b801c1900148030701c001c07080106941200c112003040c20200c03100c07a6901c041000030390052586800182000e1808640410400482c135224980301e64262100c4020400c1030742c4100692040110860300106820042400501040180d00c030001d908 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 586017473 1250 586016223 586016251
    0xa05030406090b0a020901031a010503011e0e070309021c0803010b09010c08130303110304030c03030509190602211305040915050708040b1f0e10080307060c18120b 72
    0x264840c3c42c8010300503188000700c69030010b145d001e20741e050f10450540350f51483c50f28188440140c0040c016020500c1248206170010199030304042d4031440c1c1c4405400f088000c1d0255083c8014010004e00301d5007000c0307001e0f031000e1103040340d0900040405485150320021b06880c0d41c1c203056010710181c00543d4020305004215400313170000346240024000e0000b00070000d02e0344a20310b05006107440055601c101490300104414404943c240019400790b03a01403c0466803404003001092290328071018001e80d2000b4564041503050b03000c50240004031003c07c02c1c80c603a00c616a04002d46100d42442c0090200c04a81e0400413410150495200980a000202d90200f014400301090b18401c90740341c0000342c400c4081000f0441d80c5003823150028000700308010a000480c220211004290007500c501c40c0b0040c1c002902883c42c5680000a4034565003038a4035090a89460030280c4900301c480c402144541448802103180c0c108503c0480e043c402c9003c0c100c0c10a03899000400348040c003140c1e041a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 586018723 1250 586017473 586017491
    0x2090f012007030f35030714070501051602010608100906091e02030106090b0d0323070c05120d0f0309080d060b0304060b1c0201082e03260a05030406 66
    0x109000c4040114011505907165542d0f17468055801e01502110200040c8070030b00e1005044c0c0ba4418000340c4281c25400140d8035101d06031f045e03a4007100c20f00c00101015001030144100704041d0000b17401984003801c40e010102c000217050742614030600a0320866072200c0010313481514990080c00380760740104000160b555040d141e11208010070014010044600c00540c82182801d03ca200700030f01d03a151040080f8100400001d1403201005400f0301008004100c03e0285a030940105084108808206a030b03030b0100d1500806084440c420f03603114080c0070214404448001c039052141c0c604554829411baa5902070940c0140003140060314009000d0021042080c0c0a00c50200540304540b4490303200c0ca03041c40d10009880589011500406404c0401d146c03408890000c04000c1c0d81c2400c1414650b580c040b8964001c0e85138240c010800005079601212110700f000b880d20a50b0300528090039070348441390002420070706401491690040400c500e0121920072409190054840d140110b40070003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 586019973 1250 586018723 586018787
    0x91107021504150512010f0308070b0601090806190506090402010f081f090905250603021608070c0609080f0304090e100c030506040b09060306071b12020309090a02090f01 75
    0x30f4809100004a0400a0681e502c0c2c03241c00880785c01461042e04007800c4904598401035030740a00300000707000d03005aa021450980c040d0780204090f1040030201c40803860301d0390310912070103001c1480e200e950345402c01103002800e14210092140d83c040c0c4a03000e800c1c03a182000c40310701038014840c10b0340603005454032070f01410a4014000501c02194040781d0348100d4100b0b1810a03110840c050041000800c010b00081c001c4a050411103034503040058807520324040016080600381c00c000c19000d0005583c4040006000d0400291140c07551107030052034803124415600c40c03100440c4c011030f600c244010418808160001b00c00c0310706130740035548d00c4048101040c0039900f09101c040301098548080100074142889002400c00007183c2c11000c6040c0b00012039100c03c0064141c900f0440c4222501c410203009003400c118a40d44020300d0b0410196442d0000d4881d000402800d00c0741541601040d000407060081d0303807252030000c1010020060140054924042e10440d9040102c00c014412040c00c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 586021223 1250 586019973 586019999
    0x2d0a0b0a0c080f060d080c03040b0c031b241e1e0a0b130b0f0303030c0a12052502071a190c050a1e061107050106091107021504 56
    0x1820310105118031501005001004000c1c4500891074100c800c1000c150f4800c5919420540c01416059941034400c02c164150310079500080d540d0a00001c2030f08082c3c000000904d601400340000041481c1d0384100c0980310850004401c2482c6041c10b44103009520107008c41350000d101888040b08405e424001c5010001c040700c00030b804121030608040c0034001d1040065021500341c0040083d850710f4000200d0013080040c2c2114407541c1c3c1e8400c0503454944080381099044000c1c202c980b00d15140181054a07844040080c000408580000f8038000c0b0078050280108500072006010b0307480c800e983c03030300501e90718a143c4c21445003000003d10907024203a1145004000d6071005c0e03440c0c01602c12a00c1c860041c04040b020450b51030080c4000c1080442d10b9500203610019800070707500c0807405009813048281024118a01c2e000328a0b0600c4814401400c03114172030002880070325a90314610044911450304c0e413080b0038081204000502e0050310340000502010549401c040d150400070b0140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 586022473 1250 586021223 586021231
    0x902040621021b1615140904060911030a0b01180e070c150914060408030105060705071d1806090d030b01030f090803060111030c070501050d0f05190606022d0a0b 71
    0x1343c10981d41d60095074140b8407648003803c1201c2c1c560108140d03043e4001c01007212035a4040d500000817807041419034454100c04001d04481e8420301401070034510242a990056031501210b40c6045640c00031135008814072180702881c5600d00484624118050401c1200185040c0401083c18205d034009648801d61411804d8020000103c0300160700d09400c1c5202000c003100310780c1e030055041000140316101101d040d0744080d2440760311000d80e0314140e840d107445500001f140361240860641b110180001e26403041c1c088180342e20a020034100000d4803184160391040894004043c40840240039030070400003d1018500040c007540b07511190421200c2200e000c8070800c000005000e80f039a4000080001c40700785002940c0391440045490b583c40a8074800d040c10700102007502c14034960691300c158139500da40c810500003850b0131580b0120300500d60300d00700106850144040350b080d00c005030307030100b250b600354118810801400e541524500b289250b0080d510503141020f001480c418403550003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 586023723 1250 586022473 586022527
    0x8040206070b04081308031303030f09090f0c0807110a11011b14010c051206190e090606030d02010b0f0f0a031713050d020f01030f02160f020a090204062102 69
    0x2e400100c0b043d000005d00c5176000251039401480b00000078040159050200e0b541401d00304808003010000380d8900e41d00e61b021180c00c80c500300c102c036991a010f4000d81d00c83c2d10240e84446450356424401c4ea8140c3c208481c424031030340051708050000c1d110026016200c10141045c80e11400d0400b00c1008000044504a561503030315100107560000074052000d20720a14100ba90074201180102030300c00c40c00800c3c2c64403503241d8942c0000003030824000d0340d000e0700740104500e083e13151440d02a0350f141820341d2490301a200341c1c40c078040401d106102d06408041e0003096825030780d18000c00c01a0301440c0e01310407980b14008900000c005070000c4031840c6c021a01c81c0b04140c90341e1040d8881d0507030078603640c40603005824100c90800103940b20380d03400e4000b1900742000528001882414002406002d900c049801001c00515050040d515a281c0282e4800c550700104280c41c5c08040081e400386100724004105900c100610000c1e04500c8005a4000070780c00600b000c10384000711280c0d0058100c1029 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 586024973 1250 586023723 586023727
    0xa0e031c03060f050a030b240d031701060809100f0f230f0f01090c09080601120501230c0d0e01060603020c010f0605011421270d020d08040206070b0408 67
    0x41004048030300d02c004c000850b01000a146107440e07140711070300e000b455000f140091489015521040e841001c4841c1c10242142848054514001d4842044002039014a1183c00000030309648604800b502c204261409020001c026001c0e80c005814004007210b402038551110000c0000b0601c0790b05900c0d1020307010036240c0142844480c003035410103403010f0141001c0504203c0d442ca02e14402d80d0442e441e0f0300000440520400c0111014078040c0c01c039100c40e0003000000030303401e629200110035550103240208103500c15058940d001d590f01ca20000c203001c00f0071002503030a10340003024101d113a41710400803600700c09225080e0700b12039082d04210042980031603104007400091203105080d484040341003281e28100300000e8002f02503e140340050400004040c4039a91900d801c0d4407441c1c0f141d080c0169103060401841300c5100308881100c1c9100700b1160048900040010524080f40042e00901003c0c0000207080b69050b000500581e04114100010b10004092b03001c3d052180380202c040603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 586026223 1250 586024973 586024979
    0x403050607080f0106110318130507031e050f04030f112509051003110409021c021914010f092d060f12020702180a0b0411030c0a0e031c0306 62
    0x180084181c210f502000031540c00240c21b80000400c171840381c1c1144a04501c481e09060028031740005807001c881482e8240f500380b180300c50300341c2c200000c1c80c1442c8003013a0300b080c10450000c080b146c0031940080700100d080082804a4016003a088074a4407905c0c0006425010060a610b0601004800d8900d00c105034190789034141701010f8200649244001401582080400100410071034003000c0c043e181300201d01441580c865002000807a4040c2c440c1c001180240e8444800134049901a030141d040704c000c4a10303110400750500c1c25202101400c100406059004541c01d000040d01d07841440340b5000007040355110a24011001e101024003c0d44c21403403046250a0100c06074404014091090300c4a030000d50401c60362040d81d080c40b580141c03292120300001e26007050111060140c6560002407040603c00c7c1d40107402c0c0140161014400e5480c100e1090000340300488440200034001d1140d5401d49100301c007a49425240101169034510004030701e040c684040e0368000000c2903580d1010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 586027473 1250 586026223 586026241
    0x915020f2a0c0d1112011d01050f0f011503050415060b19020f12250f0b070804020603070e030109140d0909020c1e1603300e0114040305060708 63
    0x40c030750b066040d0b4507264030b8a403e0740c40040380254041501d1042c142c0c61581c0031002d80950100c2c1e080b00713045044050511700d00003400c0c0201000d0b035003240032001c1319000070a605c0e00d04410504813540c10310390b4050780c00c9401c021001000090310441e40b81004a0500d0508060350059001402c101e0540c1030307445d000241c80302450441d0501c19030564020110318205148003088264100011011369136441c01640369131500503502820f01c0003e044043c200005004e03d65044c2d03c8500c0c8180304080031911031060030354a10408036402503208404000007100306110391008440014040c001084c18001950b030709400701c0c001901d854495201d0301582140d40d511501c14002850070801c1180307071107046405035480d03008699404140d0b4240c08000e0305018810400e0080303030951064854030481e01c902d016200010702c1da0729612034a00d12110101d071090604c8072108560301c0c54941c2d1111594400040d40d00034452640c41483c05428400080070400600c41244280903036618048240380401c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 586028723 1250 586027473 586027483
    0xd020f0d0e0a0309051002031c09030908011803030f1d0102030a0f090206030a09051c051903051315020714010c030615140d0b0d0b0a0b040915020f2a 66
    0x100a039a503000da00b41c0c0021030341104100059400644e8200d07040301005500380d2852290130795041c5030803020584081800d4285d80a0403d580c803a5840c9403001e540c41a001d0f0a03134040c1c802c146484074001d81490000382c02a80078040d041441540484c0b44c11802c100c010b1441405000e0f00d505035000010049030080c148070b400203c0486000800200d4902d0300810344500004140d4806190344038191024408104016101070780c4415140c90917590440340107006410030358007402e10409042e00c0c100060701900441d8030403845000d00d801c00b020383c0d4903102007542c41c3d4900d81c4485603081019601240807803010815032158000040742880d00d50390f0080c2154403540c4640c0c2d0310910000c40b6643c442d40040100c1e0a020103000898445407540910310052409250850b070100a03881d4007c00c01154118151040c10081800c01600324090288815a00d85a0006100803040040c460b003c2c6083e60280c200f40201141103800c204520882946480c2c00000410040c031416030000022401086 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 586029973 1250 586028723 586028741
    0x206010e090d140f040e04030207030c09050601020616180b041d010b0a080603010b13050403020c030d02070504050c0d1e1b050a0f0210050106090608010902090906090406020d020f0d 80
    0x1000b80100441c40c500200300c0c1c3c0744011800051440010a1a281da100c1025500a040d120b8442d4526080c6844e02030359507405840101e0701311003503ca001902c1c1c90389102d207600c030300d0f07040e0050452a03891080440c5000304240c5001c0902c0382141514281e8840005075001429802c883d0590761f904100740101c0000110303070314540c00050800144000c281550550b0b2407100075040c62812030320b82c240040c1c09043c0b40080c007034001942540154441c10b643d00680d014600a40035149054006c03802e254a40d400f010021700980e0145c00108200d0400c5c0d03202960101c1c0304115942058170300f038107030401c2d500090200d400f1001074491b401603c401c140700c0c01c00729581510305d0420b6059181b001a06501034000c1c03a20500c92030307940e60f01d0524000d001a580070b0240c850104495070311003502901d54441402940700041c2008004221a0914400c8074048140104142d04039a03d0100f0403070115801801124161313024007075820700c0501070000e41080290036201c0ea80fa0b40d1412022011280740030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 586031223 1250 586029973 586029991
    0x120102130306110a0f142106100906020c060a030b0607050106061403010e0c030603030c0d11011112040809120129060909060105221211060c060c090d120206010e 71
    0x40a150840d411400103043c551050074030a10101c40c58041b071300280203003540c1549203004c3d240a0300702040e500400902c6000700300c1c1c88000c2c5090700a0112442c456038011400541c2c006901d564640c940f5101501c2280160700d000b0a01c0c40b2901c000c1201500110b4040b68141c4d1a07403814064990040e102e042d20400088940341150b03d0f019044a4880003d40301100c020400804a9085d46082c02214591031810703045803442300c48181700070722900c01103011042c0d9510300300c22084522001c104840c4810200600c001c1c091b01c940e12541c41076408111404e0b80240d0721003040444032400c1c020440200a44800c400b808290304030b02203601501c5000c200c0c03103284100320500003a640d550f000364022000703181882d00d88000c00003580750348000d038402d00c040b035031180300000705072004400c5110401c2c401c021400c0c1511a50042c05082e0281c84031404850308000001040304854001604080300c5c01049008140000d4a60850410080d0031000060f0000f130010300803116210b100580091581d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 586032473 1250 586031223 586031227
    0x40c0603052a1914090103090305071e14010608060a15050307080304081612030e0112090b04111c0f03020a0c0305010e0601150f120605060301080708060f0411010e12010213030611 79
    0x580900e444d0b0301c00c421032241030660b00e0b040403083c18465016101c2d8950700c40300380e00e0910280486501d40e0310480740110b44864811a0f0703210f034150180683c2048581c0310000301000e0300d031403284e08054a030b500b030f0810741d0545500e80000c0e00e0303500b041140c2c000c10004001e9580e41e4208503c190400080750455040c0c8400032404000c0343d050000000380858241c5820202a000ca50040340c0c00c0c00318003030130804a81000141c07010b01c02c20440c0140528171400d240c8044500c818180041001c02080da00d40020248480341c002c01d0280c440c034040369210b44140d800440e174544d183c0416516680003501d05a540e0072000428490400801d8098140c0383c80800c803108041e500101013204080f400420020040b02c08144c0c181150000005000b0061900c5c9d100c0d030f1503002e42a0b840c0324601c90210940b0848010400d80074100410034000c4d038001c0340380020141c11400645511503618103481d0006c582002900f01d1540a1029113444004003018595280c074604100c0150703030034815503952650702 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 586033723 1250 586032473 586032497
    0xc060f0c0e0402031801060b0408070e0f0c070c18140619062d0809190b07051b0109060c1103130504092301091703040c0603052a19 58
    0x1c03440084095070100c0b00540d0343d9841d14144894000121110703401503003410400f254942d4075001500540e1001000c40381c40070b42e9803800c52008601541c0d500c81004404001c246d074803900d03a0042c80c405014048426555550368030f00c040d41003004035169041c5650b4040081c03038801760040c2503041082110490315200340141a600843d541d440740310180011120141d01c1c99594142031241b542c50501405074a8074242000741c5126400c5542d01128080c190240003a50242d181c2603900c03a40007075004055942d25601a51194070101c034280a4106068140a03072071400d001e1050018440d11010516100c444806019900c0f4800b00f80650b42003440010458004403045078102e403030485010400642908240301c844d02c2807408140c142203040c072101c40e00c2c1015000001a00c0c480c100394044d00d4441201c2461500095038010042d20740d05a04106081c401e400c1079800168203412035801203062241850501030181c1d10800443e0085003000a0721015140010311001c1030a100b500c92078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 586034973 1250 586033723 586033727
    0x2030f180f0f030c090a0e0a0c140901030c1514181219200a0f061d0d060b010e060a0e03010b03190807240905120f04030f05100603030c060f0c 63
    0x102404204c3d0003841ca0900041007070070160806004134040105681c2c03600c000781840070b8805285c2c0114a0603000320b07119030b2040d00308080741e58102c0380c0060000500c2c9003048403040d4004030100300d800030810460850f0880301d62070001411815060364003600c0e00d80b40002846000c40c0a00d4007100590861965165050800041083d045034800d40302d200100c10708820072058230b508551140c02090182020444c683c0c011000400d1311295110041c0070b1000c14900b1451401e42c200036900b0520041c1080f00050658020f10030b070241c141040e4405048038404584190071103945030f00040c0c0c00071445c0946060a220385006401d090303000e0024040c00c001c0070b580c032410043d0b0007008900001298024448040d00051191241c0c602c0c6040c2c0d100100300341c4014200c0c40a007541d8901a01d010203030390904140c1200c0c80985620444e50900b85180c4800b000d10181610030740326030060082312500034501b845543c0103107110703807510b010a0045040810403100c103130405000b5646040c4040048603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 586036223 1250 586034973 586034983
    0x9021009141309140717060c0711040603080d0b1801080307120201110a17090714041d01050f041b030b180307020d03020715020303010506040b070302030f180f0f03 72
    0x1daa00c01142d00007042000d0040a0904010701303280d0380c02c0d288903c02c07800864104102c1d05420001e0000c05101c01c03060362503100c1526280361440003040540002380420101011000f00180300250082c1c1c1d0342c03a103200035840182ca1701500d558070804c0144924140d10310f00c1d617211030005003c0c3c03030b50b0510402c940c0e20300ca411301c00740c01c3c4009095000c845901c00d4002c1100c811044c90300c076891341600300c0081e114600c41d07100b00558025020015000d080001080be0489680b2061100c0328441c0c001440300801e00a46000c100d8403042812040305a02400740a0080c92401103940c0c00d440e146c03c1c01d904c2240d141c081e0356182c114440081002c01e04083c03100f0380200224208040e6008a010014035601c00d00600940100c00f0440000515401180c800112000500c5141000a42c0c45049849201c02d00603035900400a200c10301c840c0c0003040103003560310b109004032031802d43c04021702030710780e008605a070410015862031440a402c2a50502520440503920750701d0080d0f210001a07296 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 586037473 1250 586036223 586036259
    0x11a071505040206040f0e01030b060d030206010501030e030d090813051801031e02030f0c030c0105090a03080304050106080615130509150405010b13050f09070810090812010909021009 81
    0x9940761800309065560303650032500100005481085000d544050441c10b2200901c0140c4049001000144107030070f1640000841035803583c090600307a07003400c006500800703580344540d81074802402401860f2402e0301c40c2c440303110f02424a0325221000300306030906c989900d4200710b000b1031724240d840486141c03605119064940c41042150396a004d042020120700a400b80a54544180703680030964800c04500c2201d2140203505640001c1e04142c0152804c0c895161541d400400d00c080800202e01007802640e0002e2007103001141c03032562001010700c1d001c402d4425030040a41c030310404a1a00d0141d0034082000f800d014240034034a0084201a1240007103c1d0a00b2900041800101040303021b40c04100c1c0340c0710081c071040368504442684002003600b110041d00c80c4100c0c01c04a0342c40c940010f910402c0399880c20040c4400c17900812611701502c040300b0300720341e44403081c070582c190500c828060a01a080c0e83c0d00006e40d621440c0104200b105015031160300b44000c160301070180a904d01340384100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 586038723 1250 586037473 586037513
    0x120a020c0a0609120602030903070c03030f030f0e0a0f020301020c0328031a192102010305010b04030f030f05070209041410060b0406030902010219031107060305071b03170f011a07 79
    0x923a0341d940c130214118420118000c001541c4c0000200030103803c01020303112510203a800700510054011807a04980601ca2404a16448841340c1c1c00064500520b08020510140000d0309100410400c103165070808007481c409054030310350a8008200003a440c0c03203a094149401e00c00c078450b10406540c1014800303034403801484518940d81e40402174032410701c0103000d40384440c0b0360a041271110887ca150b006000b240040d06040c0006205800b44056605036a00441015035076802a5030541e0006c02d60050301c3c1c1401814400710b1301503a0391580461140d8000ca070700c14a1580c43c02c03081400d1807405568450607602c0c05400b03002c0008031205036000d030782d620306001500011500042c2d24281d50b0140c1019506080e020a1302019440300300c480c01520800120b1712100d0b02d540055068a0048421600103025020300c1150b15010a00401e02e540c001d041c0703200e030051080880c041c0010700311180011281400b00400c44039080118100031100081280b605000c4240e44080011810448000b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 586039973 1250 586038723 586038727
    0x20c06030f041b0f05100504030c06051c090b06040b040504110105160b13060c050c031e0702061605060105030d0801120302011e090203010c080f18120a020c0a0609120602 75
    0x2c00c10001031405009604002200d512203540e822026008401d2406070b80d0192914050320030035980600d080d5010341c1da0000004481c603080141c111142c2d007018840c0400d958070744107440c0030007502e80300b00008140a82c1101d0300c1444e280e818441900e484a4079180a1454078042101180d00c008bc2113100603400d2800d25581d01030031081c13800d1a04481d8000c0c00080001061010038101c603800401d24510455007404040c004000030744460260110104158004004500710780c4030115031180303401550400117080851680101c1e0044e000281e00701241044803480d0800d1150800485004240c00c400800421400c01307001083c0500c10301c40d061944c4401610442014000e41216803000b64030b0048040c1c280300c104184003d0595102c0583c003951a10061160342842100f50f50302c500d0b0008000d50141e2039440345402c1500c00b8814040080c081c2da02c40402c220850b200030300d041090f5600a00b52251000e04003c50307069680d00082c107100784540100910304260f00703000085500000c00503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 586041223 1250 586039973 586039981
    0x60d050309041a10020a08030726040501020909060a050a03030503090109210801150903030e040e010501061d060403020306060108091c0f0201050f040c1419150f020c06030f 76
    0x51450003074114007540941404403400c1d0a540400401c00e100d2001c80d031041301c00407101016a250811442e015065480030000125401d00131980c01c8000c000c103100c00740b00c6a010b05192541040c003a6011070309650002182c0744a403524030b80c15a0000d90807a0308a603501e241c400054a01c40c00e070701c40142840404400284211400e501442500d608a0448500752940c1c41c0589203a158504840020850392000800c1c0001c588215400c0100c44d074803070000d550300b075440580346541d006201c10f9000d91610b9036101400000c0c01a80c0c000d00c01512030240c10342410003214907403d03071012424000c1405100800159400140c00c07178100000303080006043c5c48140c0c001d400e0804d1134860904a0300786241030208158044420204203000c0c0d070082040c2d8a03600300514451906a501804140300c0500900c010000c0d4280d040d40200000c04922009805555032101040d15a00400001952103c01000d0076007040d80c0c01c2c1046003038409850098110400100e0781d000240000d800480844001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 586042473 1250 586041223 586041233
    0x110f1009020f061b060901060f0e0402040e0706030606020705031f11070c0b0d0e010903021c09090f0b010311070b01180e030d0509010e070501051902190b010501030b1206060d 77
    0x4040901d406820f1540e698150364210294203049080241d051040c000043c144170010300c5841c090f44c08070014a040146000624020003401070010780e841075a40050044000040004400038890f5840100d00342d1302e4194064123003c0540d0000340070b5040012111a403260078204030400c6d51000600060780401804040a14024904001c2c002e40b41c0010121f05581040c01802000c106002d06100300c0070b101c00d1003426034043c001c00501503800180c2090304809060140703440c07500c1e60311300618560b0755240d04000366000c0317406103140702d99501c0021010f96490700030220074040310b04034280b800740c9a0741c030001c41c01414410703002c60b82140c00d1850b501c03040380d4003c64082c0246400301c030b1b15594140c8440c03000b80303170503140300384250300c0d0600a20082c000490503408076001611002d0918000089040103566064150340440c02000b440701a8490012130041c0c184e40115091082176041100140842e414089001d00c91781c04025460110f040000301680e02460030f4800c82401d403034924003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 586043723 1250 586042473 586042489
    0x31704050c0a03050a150c0e0f01050904090b06120f030d020a120603032c010f05070c050a0f03061103160f030914010e060f070f080c041d07110f100902 67
    0x1001c1e07400101e4690001c1400342c00940760035041d0061034000c5480c1103903c0d00d40e08580807104002c000c030b5200721182d0001c3c602800d9500f500d20041c1025840d11503600c00240c111801c229045990010020a10007907007444601e851000c0304100c001c1555000c55035820303a590148400c244500c0350005050a03807180304806980c80c030100300d4001d000081c1c49180c054900381e07901c11024016000e01d04503035040c952604031003180c5101a1916150340140c0081154564041d031000d8609481981d000038841c1c44603000d140080c0003c96240549a045d8644001550501403038900c6111040c020b20407010f845452194200d000ca081c141004034080307205801404031404064a44491072030310140b101419003010810b110a80f040e107019680e986503a401403002550784070005030b8207016041e03c40b402114074a80002d000c548880c285680d90001c1010a00c0041c03083e801200d6180500114581080c490581164510080e10380003424005040c0e8076020b0b2040ca130302e0030392030308141c4080d0340b01c03540e07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 586044973 1250 586043723 586043743
    0x607060e070603022110140613060e1c020105122707060f140d02130e040c060e0306040b07050f04030203010f0b0f010c150506040b060304060615090303170405 70
    0x1090701e0711681e80e000050f0094028035016250003148210b8112444100444c1d81d100c0c6019a07503d0302041e04001005041141020744103800003000c008191003a100c20002a006208680e1895039005955051201c83da5102c686a42c0c2141c92041c2c0c80010b03070300a410707615220b00500820106a580300100385200890001625036003100020003582e6400200e0184191602d5840e20383e514404400200c803003611301b05901040980c240122007108106070024100c00002400100199440f403035a9211500c0c21780301200c20312040c0ca410030050380c0002c00140c00c800214050011031034103460308881d1840041110042010008403058441c070ba00c0c0a940165401800070420003207004002402002641c0c54944241e0b803400c00310341c0941c8103401d420405507200382c1a480703661000015101400c4090030041e40541c6420000c070a0b5115100a188141d01a2801099030b514000c60072420003408031406042240c204420b00120b500420a21030103110b01c00050b03203c0c3c0e07850404505000c8406 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 586046223 1250 586044973 586045001
    0x10909080409090b090708072405040f090b0f04020f0a0f020f0f0a110301090515100302090a0c0306060509060414030f010603050318010f17070309020a1715060f060706 74
    0x40c03443e00074042d018440c00c1c0320b81007100c11181110340381c88501d0355403000d1748540301c01c2c0000c45070780f140055103180c601c0c400d40c60309040c260306087e12078490345945640c581003844103580da40031060030307482c0c000e050108001090300c3c1146400380785000c0c6402071050040400c280074244801500303442c4208012001850b40005075242c18049280070f944404542c107082d60020043d03078107022103146c103101d461a2640c0c00030040c03c4100d11141a020080002440c417040c15028000010150300c030024542d108521079500000c0b90442c20102600301d42440c0c00400400100b441680810b85655084030180c82eaa42031911010b00c4d480e000901d4100780220812865081c0034000013002070020140c1840108035031007100344503401c0c1c01160440740444680c00000c1d1151600820300680882d00c41e0002c4061801260200c000d070045107401480f980170000d0f00800440350201407200340000c0408100240ba0b170000b030f080883c0007411017025040d00c00c5c41900c002a00c1010041e070741c0d1004c07070114140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 586047473 1250 586046223 586046231
    0x60a0b0a0f2312010b03150105010c0b1e0103392102030d0906020d051306120b030f100f02090918030c0712172701050f220b030f010909080409 63
    0x10183e03140603003003008810303000784500000030b8122410080c205041e91810303910326458143ca51620a02c2e1030016008402d91718511488000c0b800d07200c80342c07a019500a00040e514000d544005880840d0008140c49241c0b185048403109021018841002c40d903090460b10070b4400d81074030295500b0b50001000390b0512400358503071081780d0003a041e002281ca5a80a0380c000c0503616009031801c0c0301c0e8030b15a800403284000309000450103080c200e68002c1802e000003400009400c0841d203400e9124200e442d5684c888200720b0700d00000c50280c02d01100d00c060041d07040c800100040399041c0e030003508101d2920b507560002410f00604000b600c09203c5a41d04550f500c650b0350001c01002d240c0d081e02032b5002c0340c9182c00d85001014490840e65840900c0e85400030004040c0c032400c01102c0c8200f401810045c04000340b41c4d1703941c180310240c2028000036100801503451115412502e20301c56000081120041c81040140030040c82c40ba411208561404a020300852070308400398841e40e00000c89031460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 586048723 1250 586047473 586047499
    0xc1e040203180105090601030809040c300507030c05070b1e010b070312090f0f0c15031d010c050d0b0a090905030901020c12071202150a02060a0b0a0f23 67
    0x5071503164504108500007003040c5d0f2241d00034507840c0d40c0c0034040a04691010004401d807400c16a003c103240750b03064601700c3c64000036500780a41e5200e1070041100c8407841110b8507800140c151203130507003080450404110034007405501174414000c403040604041041e50004907001a800300e0601c001c42e42c8102c841e110740e1034041031880398000e800f05800041521084180d8010b091003082c0101d600481c0465020312180d03207204030705100d058200c0c2d142c0c141d40400104062200810a1200c0a546000c40c03061500b4400301f4104c1d145e50362003503280e81441d103841c00103078215044a43c403404d22000410010184404220644c1140d4003504c11075190500710001e102010002c0c02c075410090307003074038040212481008140364150310001e14980007660200910f04e920031180c0300707092000d001031005080e0360802d007040e90040c05401000d40c00100030441842043e05c2a40341c03600c4100e85c0103800070709019032025604510b020f0b2000b00d800300c8a002905070000d0141258140d0000c3c038003030807900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 586049973 1250 586048723 586048741
    0x303040602030a020708010506010c06090201090504020316030e160e1f0b0702090f0108031c09080706060f0b0a020309010e011211090f060f090906011b0309050a0b03090c1e040203 79
    0x40703d155108018010350101148880060281c1c0f800b890f07050b52050005401511030700e0051138104012418032055050019140e01c903400511300c181c1c011041d204076a00706400142c141da05002d64407038907401081c8151649000078a5400035548035024818180e90f131074091008420111103000043c001c0d0020004046070140d004001c003d1080c4c0f801c005a032202a00e00100d40300c2806400d0041d0020700080d200d480c18210004c1010741d017488041400308154540c07071041d5200001c265003160311a8800c0c014002045269070040040400340c91600042383c40007500c82c0030b00d0000504100a920714151315a1240808000f03271000403c0800000440801c007103c00d030b120b441c5c100c1c010714580118074500d16007002641e50b864003c00c01c4d20300d400c032120100007400b040100400d050142c0700f009c0001c1d0790002003102d08010310076198105803038184020032002038543d61240701c10800c10010041411000b051440581c80c05481d01c9251150205929009111490440350850f101008000d4041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 586051223 1250 586049973 586049977
    0xa05030d0204230d0201050a020703060e0601150503070e0f15030f07020d05040605040302040216230c0f030c121e071503050106020a031101060308030f06091501090320030304060203 80
    0x9103840074200b03100008035000f0644006451102584111019500d01c0503500071002488020f4003031060700d003100d031255500c00c103c031407400f0801d404e40d001d074006000c1d80c02e810740940c00103e041d040150071882c007080001c2c20030344900c04150090a2091100c091601c483d02d1a003070903a43c2e204c40d070b601d91608000700300140508803030150042c0704140389903032000d000d034003140c0541d6881d07907404c0d1901d800c54080c48065803044101403160480b000007040810003548140c101000d4148094900810340320030189042e002c50845482003c0b0742c081504c03240d5000900307000011003070b01d840820015204015003003015051001c20960f00300c02c0b23140f1070450081400d82c10b80324060782078441d000f4400f004604580c424000c03500983e200111035030109015191401e10f00796113900100b03940e61250b6450055400540b100c041e45000c01060291520b0010f0509500034005949030315210007110000707007580001d12002c0d000120590000f090080710100c229007480001c1c00f241d681b03980d1804002e55079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 586052473 1250 586051223 586051229
    0x1140304030f03271713060906140306090703090501110a020706021009030522090606030902010809060c090f030a0b040b010302100927090c0e0115080f0a0e0a05030d0204 75
    0x78070300805803030741c6681001e5000d2000c0b81844040030110301c0f035448603000320680d200032038172100c28401d8036001c0351004c1403c805000c81340d030350035072051402c14007925010950260001042d000c0c404c201460302c44c8040554006000d1030040b440c034100d400c0c01401401915003108180b400044c0c0c0300407a0760000381d07142c1114007a6007201c2c0319001c20b042e04002c4405095004000901c1044100540c142944450680c01083c108070b48009035126032080c122503156001d100402d4407032640c1e400b99a004902254405000c0c0f025182e1480e101d0181146449960545445030494110035001074a0400450b04540d5101040500b00e0406003001e0004000900c8100d104400d11950040c0300d52051050070229a004208243d028643c6040040c00f000c1064180805664035090300d004583c01007000381c0107000c0c10314000919410302951400320781b400e152900c140210790060002d29040c02910b0703a07005948a00008288048202c803e0920080d00310241c09840041041041c8540d590700034811 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 586053723 1250 586052473 586052477
    0x1f0516060626060601030c1101020a081909050a02091509091c1d01050d090b070c030908031201030b1f0914130308040609060204080115050901051c1101140304030f 72
    0x621070201101d01c02e26500d040026860b04620003084180d402600f04000e00d001d5030809400e00045281d400782260849802e1030002850f46040c81240d0951030607041e00240c0104040c0207984c1d0300e80300d09035226030700e60f0001d001d10726810000e131388070301c8035106110328400080100f04181070050001c0d41d20460301c030308640d401030410303504a050b500501c0c1401201641282507505100c1000c019155a0000603042182640b14601c10000030a003075030092007102c2c0350f00e600350013901030b040c004d180b010b103600051000c0c1d104100f907070310013084090081d04588d0700c0b09084401d95035141901103201c0d44210561240c034609000032031050401d0b00844040c00001d00030300c405507903080c1a8a03030b1030a00c070340140c007140340c500201b00802d040340c0000080078001e84002d440e041e070b035400c0c160840d0383d03810302c48006840200081c0114907110440c180189401ca926200740f4032500c0d076400a43c9043c5900418606c108001d01466902910b5a00c2c040321801d1131240e2240342504000d03020188054400300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 586054973 1250 586053723 586053749
    0xc0106030311240103080d090204020a0201200c0c04050408070c030c17030a201e030c010e0f060610110d050d0b090f0a0c021905030c060a06051f05160606 68
    0x800b803c1455400880c07051200d4082d02c0e42d03440d64030765144580c85110903491054031066818050b80700c40c00107114428055000240c0c5888102c254522030041700f020780c1c2128402c1110b40c1d403401000078034a0b540c40003100c0000d0303c0e8845107844c9a10307200320170004001043d4280700109220402100508603003481c3d044c0c00708100c0d021009030300c81c4903414000001c80c1845102c55444641404000b03440240c04e81107500c1c024403c1000c041324291410300c0760075a8030029000194460038000e80720440391000017020312620f41200640c030343c900207060390f02030900c500d0b0300701301d441c4110550320f00f40d041c070f205451001800340700043c03460380300b4460070300558113114004c4040c3c280704454500c00d0718030408204040d101c43d02c164002d802507002c45000c52069050080c04004800703d80c101e82c40c40380e40115951095280010300f09640240222401031602000301b0160321120000402e03200c2c8029402204500c0c0d501c1070fa0240181c20a4601c82d45154008904008460b409141039904c0c1201000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 586056223 1250 586054973 586054993
    0xa030c06021015090507030f060f150e10050304081e042408061e1809010e0f0d0315180b040506030706090b2808010e060d0201020d12020c0106030311 66
    0x8141c3e0614144042d100508220800c180f0405501894101c0010b20300403918a00484d42e4505446483d00301f104d440c0c0c0d904008101542d044030a40645a40c00d04280080444000004015035000003801c0240722000000a08211000702101e00c00070f038418690981420512107421560494018204404540c1c8080400e01c1c809034051040c1a240781d88600380b40d501d00081c01004a44148886001065001d08196941e40d510101c2e00c0358040006042680c60a088048e0035100104580b40750340e003045403401542400400c600100c0a42c0d030030040741003114409049140070a9a12009500c3e904d400d40a51412281d0014004640221400d00580d1203800402d034581d59584111404642c440c072003000061f050741e0290601c2c0c1d010400301500d50b004a030b040c074140041c0c0d00105c800500110014800311441c1c0b0011500244255000b0301b01040302c0d80084d40d90b4491601002c1808030400d0500900407150301110400f00070790009104070b60b1b0701e10f006085a014204001d070319009401d821 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 586057473 1250 586056223 586056253
    0x30506061915030b040f06140a090e060117030904050f04171602010c080f0a091508150904022803051513151410031a040b240a030c0602 60
    0x604252011442d1841c1024120a0250018068080025005511000e0842c4d40b0001803151100800901c0366454004131400100130764040203400c0818170a00c0e08101e180003090000c1c00c3d505480e1100325802e00203040e10103181c40d40c000d158070740d42c1c020305140411021036000e0348a5401a48503404410502d403410284d0002800b0300f107500460b07440701010b0076001d5031145129481450145062030b00d0001002c2e443c0b041980101d08000110310081400c1200e0035120084208034007a92410b810a81080800c0d0700291003900140c0e031007003203c5000700d0709560782c060b20108605a410300507161038400d07030384a800180b0306100507100382c007891524000700150b200880c0d101ba610000603020705c0d41144c0d10045130f0700703c1c1d4104411f0180d440301266850313410a03141134081d125580380e148040c1e24602d40003888441801140e541c00f2080400e1100056145e003155800031310300d41400003500b248000040d45d40c2480e03a03503c1c0d48001025000010b01400c0425601520000d900741c8101071031001d80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 586058723 1250 586057473 586057519
    0x11010c03020607180b0f07021207050105030f090f011a0f01032304080d09032118140a2a082a0406051315091a13090c03050606 56
    0xe00560020720016004030b20510a0b54140706515071a4485141c03a00c0010743c2d19000040701c0000001c2c0040e900c815032030003294035854800c6045c01001d11301d080100003842c2c3d0101074828445c1601c1040802c200d4002881001e1240a0b03880003003011058014800b251200200c402900800b0380944148107544640640d80a0003000c00266502141206803c1c002c080018000d07a0488018000029800c07d98000c00c91002c1c000e03074610700341c1103950780c014900c170110402a07940140361000c400b218a080313a00302240c1717542029a41c8000c800c5080c1544c101141c0c48401800303250600212010628078030403440701ca409581c1c0d881041074807001c0187d0748030305412044c401021400748119034200644100b166004001c1c00200701183c6e10300c0418106100001e0104082d510703203c0500c89110443d15210050110003002d000c449030f617034111101d40d0340c40c0d0710550040310308241c0150703001c500350002040280c0c0659880c0d031303403541da0802c540c0303032202501c3c0707940f01e2000070050741f051040d1000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 586059973 1250 586058723 586058747
    0x17012102060d09170d0c030c1b021f0314060321030615070b04060e1204170102090d08030403020f03030403051801090e0108030901031d030a1b0b0a091101 68
    0x2a090a86a1a000c008003604420200980107840b12140000161001902e80d003071024141c14944424840000c0c0d800e942c0192001300030189003050440350a035000c42000c2601450082c10800c10b4024004501c1403000d17281c140a20500c1d8a041d000c403903515901030100c100701890f240c2d48a413101c0080545409030010003c0c031310078002e840d9140c421000801540c004a00901c075456205003241a81265000f140050310b0044561007044148403007401600d141035048800b03405010b4028841c00c8140c015402055842103036200040c3c0d84a000758101d9400780300c0117080e05000780075494040038581c000c43d03044005000d100c814546014000058a010356810b8850703905022401c0e695040d11402c002111f41005005070000800240e80d0011502800c00303103014540c7c0724bc1c0140090207595240c99000421204481c0e00c0203e40004415640c402d4840d01d44142807030349030710701c42c912244c0214000d0800600321060000c09540d59003c180c05910607443c40e030007800550019110004031300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 586061223 1250 586059973 586060019
    0x130302190311061b010518010c0f05160303110c0309011205010b0714011e020c010c140403031b171e0304020f130905190b2a0a050903030a1701 63
    0x80b4500031549021006040498409410410f03c4a406580c032030130340c0c0055032120502420002180e2403c44280600c514201d174904050a8170354048200130028030032440704c2c1d400c400b00001d1031400c02d8480d40040556910b05104c00e45c41e50b003e4414291298800394402c0c0c04284501c20210a022890041c18102d8141c036210314142059a00c804042c2945040140202e543c2c0340310200a06155a252100240501c2c2c00141c940d41101003007801c40d42c140d10b003038041c4000b100c0c807500f480c000e440807a4152607040c507107031402c00c00d81110040021107940d00103115184080d440f1880c0030b1010058900c00c011204025000d26251440140d80d101c180d80203900709a0f80402000e16080100c0f243c1c070501010340000451086980394581080440020038554000c45003500d0705100c0b40d080c4031034000380c0d0b505200d2420f41d6000d43d104445160321000c0680b0001c0400d409480501034010f0b6120707150050103481c0e507000c00d90b00080041b6406c004844140030a0000801d84c2d19501c446010314800074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 586062473 1250 586061223 586061243
    0x7080f071d0d1a0a050c070506161119030e010c1203090507050d110a0e06060a110c060d0b03010c02120406120b040204080d030e0a0b0105091008031303021903 70
    0x11944503000d01c1005140300e50040e04803903081c000219101d6100f0b411480c001801801414030b001071a0a885d4050f00443d1000010b02c4440b001c20f002203411a0080303810a19142d421144036015070321080e0103191112540212072000c10074654200d07508010511175079407500c03240f886000540d40701040d440081c0c1540c0b0b5a032103490f83e150003548240402400703041120441c9650350006076100d94801001c540d600c03146070100b1101e041800d0b42d000900003600800c045031400d6008200e6034000e124404c4d0401c0050100140d90300d0040c06840300c0b603d4082c002c41c0d5100e41c08000007014040b4180d45d14007070361920100591581c804143d08149290514155150078942041240c4000041d80921031940e500e007481c02080e611840100010000880503103070030480c408000c0d003229001228006d140e0010000900013a001c102d425054030340450342c1d0304094964000a0001000d00c0c2c101311494840003d62403000b400006c50707203040304c2c03080b42c5141c81d006003500140010001c41c071006142c6010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 586063723 1250 586062473 586062497
    0xf080703030f2c01241a0307050f18040207060509060711100e12070b04030206010e06030613030c060501031b0506190e1318030e04090309060e0307030609050607080f07 74
    0x100311030741d04000c81c00350300200b2680d40c03168403513000320010352030085c0401030301200300049005005044801ca001c004454294900808040c00b944250005c410151a0004070b848000a40f0015803600c01707400351045403140c00914050300242401d8405602e0751185000213447d10b4810030a0b1007101600700040c000f441560010580078082011154445000e0f080803d0008410341028001d1140103051342407240c1802c2c20080c7c28440103802c15108446164100f04040e100001c9190704030b4900601602b140d1100c0c2400ca40700946148001e01e064200300c0000103011040304500016000700382c070428406c0c3d96000300035051140039a802140c10400c1d203488401030044005a020390401b078840c4126080c1c0202d001d089030413141c4400c0c00c0c40d1030450f0071800c1c10b600039005070400c142501d007003000c0c1440e03440142a904140c440e1104001c010090b5440988003405903100542c0e001e1b00c2030140009a03d07080b51522012901c1d81e00003505100002e00711200641014010621600d075110b140b0b903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 586064973 1250 586063723 586063781
    0x50a0501090218091003020d060911010207030302030406142503021e190212070803030a05060f03100c030615260610080402150a0509181605090301090f080703030f 72
    0x2800801c05d0590303c0c1c4004000000d6203801c20f01c800582d00c20500050b03041d01c5440c0040d030840d0b03680852070456010f0031050000a400000702e9094440d54141040285410b000c2c951081c0f01d80e00e4240c0d0419105204441c1024040b01e03240f660501c40c0e0255005403100609489000010406d075060319440b5140c0380034495075088645040c10f0000e844241c0064a82071110710f44607080d07001007600e510010800041d0f000521032260404822640200d4001d006030009503076100b01d82d600a08940e40308210340855001f6401714004040786c0f01c00c0004152040c0e00a440c0e44a1442820141c8030f43c01e4200b9101242c80c04070386d1207044010b1000b004490f8011084941c0e00e001031049800803019032048a60300c0c401c0c406402d007000b1a035209590f40d610324041c0000042d03220400e000d60305610081c82065044480045881383d45440c05a444202c03080000b8050100d8110203840b12100c0049034060145500082c407065020341c5003403010340c0c1d640e4500c0d01110103c1102c100540303982c1c0c5400c00418 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 586066223 1250 586064973 586064989
    0x90901230c1e0409050609060d061e11094f060e010302100c03050a21060b3a0203041a010b0415030608030406050a180603050a0501090218 61
    0xc20014411410220310200285207410b600c001e6520110b40410104800c0344140180c075401141030358090001e013040c00110300100b80030080244030f15168031030301c1405070511450020700e903a1003c00740a00b80001a0080c100d920000c00640110b40090070801810400c4154030519034111041640c00300300c01c10300081d10b483d040c5515565154104100c07a081045000f01d50142a04040c4504d455145104100c0d02c40401c0c0e03200020700007000d987d840400c0d0080d083c4d400d48040380c00c0c0350003004441c246050560300740100e4034103920f04c0e2190216540300c42c00060900d801128010720418403054512116044152004c2000a02a50207012111a06402858201d48284008049807007560aa400c080200743c2201e82d03510408a0200264803041013259502c0241d0b0070104149400d011003e0340f01d114a0149005211001806070310140c030800c4000d50341ca0940d10401b03e81032f12808002e01408080e5425658642440c0020a024803248210b8003202a5260601c546103018400d1124007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 586067473 1250 586066223 586066231
    0x1905060303040311011b05010b1e01020a031d060c010608011113030f06230403020d031a06072307030201020d0908100b120a08030402030124031713030302010b09090123 74
    0x480201800780350f01b942c0c5003140039040d00c6540045502c011520501041d0700701c66804100c0c403400d840f80184181d801042d61004550146050042840e01209050500445a0b101900a40c001440001002043d402001503d40c0c11300207120000122460f94420302131040c400d5000801003c00300300203900080000d80c818800d40022521404003007824860318104040c0d101503800000070030003015410300400d420840b075800d00708039011842c804001b04605040c2042d0150a0015500f000c4c800d4529041d43e0004078050440000742050070074035100d4403140300c100d01600c12905410600e0780030304c2810317007500ca0b0f0300020302621420f0120100a00310000701990002603250070214001c1081c040b854805002c0e070109640d900702407040c542141c1c5d9000c509140752904103003480c40d43c008190300400300c2c0e4100c0d070701d00000c5e0424282c28142d440390001481e0b01c80c00b101000800c040e0107400000010b08215107400c0c41d070740e448003601d082c3d610300a00d5801e10301c41c0c0c2540800040030141f80b2504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 586068723 1250 586067473 586067477
    0x5060307051e07051f020c0a170d0e0703030e0406060509010c2613090207080702060d060e13140c061b0312010f15050a02030a0e0d1208190506030304031101 69
    0x74801c0b98603404102e5500200301599160030860300700c410580549040d21581a01440462070300350300da0b00082d12500c03a20002000702d00c0410100b640034085200b500d0903003c000500700071708a01e503c45c00d40c0d91000ea1200b24045000301402d10601d10b49031003224112007513502d84505c3c00030724000460b00703181612800c458458a0481c6a451091b04190311448407044000003541e5a0092452085000740d0340d001010490040014000084000e000d0710441e80c0d0540342180c440071003400303010190070340d6001a40494201010001c18005021a905400d4080c90492021140c004820342c0c6030043c0782002d58008608000320740000716500d814107030104014064908003011448110920882070740500d40080d4484014401121007002049544029082c0f05107019640e0402a480c2d0080d02c0001c0c1c24001d450b94000e420b925440302a001903584400d0300300c881c88240001800e00c401c140d40100510140480c00c04142c00d041c070500b8002c450040045050a1030743d40c540c802110082c4401d81 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 586069973 1250 586068723 586068757
    0x915061701090c090e19150e2a0616030815010507120e0a090509030a03230619081c09050f03060a050702031201030311010f020405060706050414150f0906010506030705 74
    0x10f1541c6c0e81e40088105e851095103808030101e8140310340c60960308014100c41c400c0c1c010102e45044540000c00300c101075501c00c10b136100f01d20781d40400604d160180340c42103102c641c40440c034030080580c403401a0b88102203a003040d07200112890011240f5005d0010020b0104008001c1700d481c542c095540d40c1007046000f80308102480c1c030742602c2416904243e0b000201030380045040c042c10340d05130040c400500652401c580b02132401155552400c031000d080d050290b030812075054081c03081801e039400030707100000448110b90700030441002d440383c0001c0c2c2c160015200f90004a03036032510480110195030010003c000c103840c1ca00c6050002e007005002002980300410106c040f54034619100c5000314003e0300c0d61010482204035260035140e005040f030740700c41c1c4100014400c996591040e43c40c000e4000d1000102c50380c8514020000e0030300c141484049120300e0f440040d620303109644280c0700c3d0322044220340d01d5440e0b80d204255242002e000c0d540d8030072800e000144c0124450b901034071a183d40ca07000c43c0c0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 586071223 1250 586069973 586069993
    0x6070c1e03020604120519030c090e070f1d0a140f181009050f04060e1510080c0301060602151f03030503011e061d03010915061701090c090e 62
    0x1840e000e60001140581c200700d0800c0b051007904042124141003604009142c4120700010040d607041200410041c036660342d01010205128070a40c0b00944110426040181001800074090805955010002501031038111a01a0700141c009404a001420036501141442c80495001c03041088480e040810882c1202150f84d031018500a06420850340c9285814004500d4800c1d12281d04001039660810041c82456000030406036442600110001081c1885a115034240144034a0107102c142e5550244030014581d1604401110354031f4080b5001c6564050505090310400e200304270240e00002045481c0c0c0713644c40b101ca40d101d40e044104104410321055111507500c901d0700164001480030006200ca000b4000915030041955800504040e1400c9801080c11103441c520040d1060300d401600c410751401d40151803c56400141030102c0342c503a86403440100018416400c2d0350b001d520305040d0402044c81002d02064024002441c60f0307007400d8211000d08005400010a40300f1500c02e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 586072473 1250 586071223 586071263
    0xa09020d05101d06040f0312140c09040b0f030c060313060c08060a0611060610020c1f0206010b341416060516140c1801060206130506070c 61
    0x49030107500026000821140f4030220021054001000b4010f60384504180300200b01e0300f62031640201e40c1403404d0742d40c030803040c4051005490a108800340c0300c081070050110503000500680241c070000d03503003007143c814003808014000c945640d619405811040c034403803082c141344000710350100034079030660f03124000c035922031040f501280c5a000018450720140882c1e480c0c181c000710300400b080d10301100100c600b02411901c661014106d5480340d90050b1250481900900049400e404018541c40140521380001c1582419401d400c0c03005005c0c000c0081500c21507031003942d4100140c011030b00c5a40b10025103040c003070b200c8020341c1e5060070101003070840000e0607892038100104500d0080c100124901c0040e2072040110b03080340084c0042801800200c0460201e481c0d00b9580003c03155444031380d00c9e200b15007031031415441140c1200c424601c03040c41031641c0311894122000307582200c015507035a0b541c00e240075044030710040203034102d18040380c0d54522031790f00c60700c003d03000c1d00c641c038081e50300e04400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 586073723 1250 586072473 586072483
    0x1e040f020918010f09140f0403090f03230f060a090c030c18050603071d15150307080106030204180f110301080d0801150e09040507030204050403030e0105130b0a09020d05 75
    0x190411400c10b5001449401540071100d0014290a0424000b140d400031401c0c61580004169030002c1e8203031000501854860620080203040c45440190744640740d0a0802c03141e41518610783c3e051201c8218180001d8002904079410608603019002c0c1e07445040c3d1030310240107802410303260410301c91800f1000c0352003000d002004000100c1d90400b44800d0021034015903c000b4a5180309800a0a040200c0855880c1600700740b5071700c000070001030b40d501b40140086103070380b41e19076001640010075001c034000c02c6005602880c5191108241a030780c07404103d00f82d11541c003d142d1501030300300d00000d020703030140c200603204011a0004614076081010104068100340c6c000e0400364061a103441c02281c01210003405410301c3d030140c01d141003510308003818628000d0034980c042e22100000a050000a00c44a0051030b4010000e100301d08103401d00038003600300f0b0300e4841015440c2c81d000c034000c16100f160000d10554068011442590351079030b208020080d241003170340c000c101000c00700009402442 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 586074973 1250 586073723 586073749
    0xc03040b0610032c1c0e0f1c0803060108010e090319050d0c090f08010b1807020a142103041703090a0206120a050106090b0d02030c09030a03030b010206061e040f0209 73
    0x140c00380103c01c14040c1c2c02c0c90442c071802400e81200170b180c41c0c10750555122603480c08244c0c059560300888a01c50b00407403101071002150400e4130043e44001001c02049000950203001c003640c5050fa640d8a45014442e0454142c40c003100950080000155446901c1c01d500714041c258104035051512654209081c2c6003580207840004100007410701c00801040f004201070440d4030000c200d88240c0801041740050050507030381024000c00c00040d070061080201a000e290b10901c071981e03410404034195583d0a074504140440d80c0701001c806841c09508054030303c50758100da440802421680c507031004960016041e100940202e0174150003685507400100b0359001102a001c1d0b5a2400140315412960103030407420800005000070000e80d0085802c2e00c1c00440b040e000103070740340c031440c0c0495240e200344015290140034101e034140c14150558444c2a80d60310a80075619555507050030400d1070700d400d542d4148681c1d480d0f01c044405050640c031040d801030361030000520700320346600082d0542007405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 586076223 1250 586074973 586075031
    0x1116030e030607110c0d02030a021003050f0f0705070209090705060703021f0e0715030b0405091b03120d0e03040b07230328090308160b0c03040b061003 67
    0x10300310140307007020400c1c26480030403441c001d14220b401820f41c646a91403500c2c454030038490000e030b10081d50b13001e00c46450032a1b4010070055100780b40d4070015001d48070455044447d07101caa40001d44e88a40d4064080c0301d0b04941d41c034503240c40619401c101209034054000012481030250111b211303122500100f40a034000c0d001403c1e621300210100e1380000400c0b0072030054a040c40240610a00d00042c43d400f600c00064109489400070f400c110000c004812555034017904210500c05441c8000c9031050f580c8001190710103100140109059580c00700c2c0345050915402009503403d10b101e603a000806582d1424103403460a50358210060487c0c100030000c1d1180400c021307155070300c0b1550400070602001040041d509014036680d01e41da607042a4016400c0134003003041110315651285c1c907000042d661010702d05442d41000301c00c440b00408400c40441d0010b0321800410080761302c50094030b03c10350303001801039200d03503640c400d000841220340400010b05440f00440802060b0251004000b0340381e038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 586077473 1250 586076223 586076237
    0x41060a1d090109240e071d15090103150f0b0d06051509101806030c0c020a0605030910020405063405010b0906060c0601090c05160f0b06030f0a020103111603 69
    0xc0c02e00069140c0001c4042c14200d11403813400c1001009108115600c0881c03424036108105c4000c085a1a80d1000903d140d8895046941007440d159800081c2043d42000e076010800520f039024000344240d1b440c062740e01d002004184c10081400c1120082900701031102021550f29078810108804104078070360000300700400700e148112800c03d000644038040481c43e14081500c0340d0310f683c42411816000300030800d42c07511140048540204008040325034050200301440340d4501c00140940c106039075182c074900035070b000340320010107500a171819210000e15440c03602c0d4684d00c1c140c110300c00c400d81040606010106844841c02c1d40600d00c25924007450000c08c04101d00810001c0302a4020040c0d48034082c01e01c018160074030005003050650341e000d240003600e143d00b0a0700b51030b50b000d08000301d08140815104c580c200501400720340c407624801c0c440300c1543d032111020181c035071180d103d60440390b500850701d5070055886a04910300e00c50801d203002e0728200c60344101a100d2515914150082240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 586078723 1250 586077473 586077491
    0x120109060207020f1f0c030c05061f0f03022b1406060102060a09050d11030c01090303021c0c0503070e0607080403050a0506150d030509060441060a1d090109 69
    0x1100200302070f035840850303070b40300e00810785c3c00d808030f422520a81c108100050070f90400109805000b440901c990418121019440d080b2035000c151100040d8845103408541400160040000380711026203078001c29a16242c90946131041c2140104400c620650219801c1c580104a449900b070046644490140c1080d2400c0800a46081c0e005000d0040d070a181031350440100c0c01c082450305a940a500d40740b00300c0106041041e2642c040c1007520441940382400070010103405078010074042e05804140b0440c1c240840b9501c0490346d0020342714000c55010000a1040c42c89000d0794510703508002c2c9554203011144c0c5a0f4506900690012190344c0d000541440c2407140802503240e00203100c40c00d07544034a4440f03002c510094002e84009041c0705001c92000c03081e42e43d030b1003a1006015200d000014006080425003e0306401c84aa00e40c2900d00a08100c00c07044d070000d2554040c00060515032801d101c0300300440ea840114030b038640d46400d0098a01c2d8a50303407001000360081004102c04030740c030030b1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 586079973 1250 586078723 586078729
    0x151707031101090303080a090201140f07020a0b0307140a030905010204060806031e0309120c0402030403020a0b07050301030c18090501050925050901060f02030721140315060912010906020702 84
    0x8580781c026060085440040000a1b40040c82d10b40c05214003802041c03410851005940d020719103101e558080e134000c281441512140e201502d4407074009c0300c01540c00c03035a40311004050b02c015030340200091a545001003203481000c004011403005c4e460000340510440d01c80700d08a80080d081800080c6c081da0501c0554901041100300301c0d004d16840100c644810b52056541f84034880c141801150940000c5002442c00d00115500140c054001c0d503492805160003503c80c0d0803404111360400f10300b808104e4136842030f4262416aa40619131007881804c01259000223a94652600382d01521502c610000800a01904d802041440c3c02482400c1c401400c1505590100b13158003200b480d4200b0400c00f9546000c0302c60304495450800d50103840f10403c080f401c41c8242140030308005041108120418000100781868035190b42c1d46544d20360101d49050120b03c0181e5150b5400c030b00006c005e50061510380e00030442d00368001d00094002180c912200d0942d014640e00307544030b550101d8641c055003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 586081223 1250 586079973 586079993
    0x110d0b010b0415050a0e130f0608280f021e03031305010e060f09061e040305100c03060e27072c0c070303150e18010606030b1315170703 60
    0x43d240e410100d09000078070f0310040ca10504e4406003886460800c130f10383c002030207681c0034200c05140b04038103002981c2c440c160280d4030407107210014003001030f9122030f001482103170407003155041d0f004080c0340c038138007883d020080c40348500010075905082c100603254881d034042004004006040c2c2070724070003501d40b1001520380000407454a02a00042000740f5000c0e0342c0d041114210700e402c440c016203482c03901481d203080000d2011041c4c102d01e0005008003d0000029103000729151101040c4280056400c04070140d480b130344288a500c075400408a50001c008081822016400d020191001503585880302e242c070600d0b41c4912910076a00d5031034038801d1554034489070754079010f170070400340c0382829181d107841480392401c060b081503600d000038038021a040312094014032048040704602e0a180005054021080f281c1c83c02c0340d0321301071001940c140039003c0c0082c40d0748014a4100f030300018a0101d009019944c0300310411034826100401d00c2c2d00a01910101c0c81000b1008102090442c68000042e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 586082473 1250 586081223 586081259
    0x34116020f030c150a0608030c030d051e071b05250807080d142214030c06091e04050103120f1404060c03030b1e10030216110d0b010b04 60
    0x794200300460026010000b83c2d0404202c091142c080306543d8200881c002040030390084003480c00002201044035031700001410b011725803010100504e45130207400094550b21581c1300740c5c10204c002c0c006040e550042540740b003007200c650102131541199a5599060403620f0110780001010308240c0d02544040300740c000c0c0503104100087c0100c60034581d0080d524580007206c04100007166078114281c0309658207581111000280701c1858013901050001c1e004105c0c0030b2265143c0c1142c0361069149000140d44817402006042d0900e46a01e000a110095174000090703060b1060150341021103071100d128181c020b41c0282c448441250005500074469030181c000f42082000b100802c0884084800032034003181c2d03050901c038129803a03e1500360054010070249952003103041040b40b00e211540803401034580c408481c0410540c61541c23080d412805007403407468404800003a500002042c11041500110005158291001156846041003507090304000010b04002c5010272041c10740088980c58 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 586083723 1250 586082473 586082503
    0x30d0b03010e1c20010515030c0d060b0a2c071706010e150d0c02010606051e0306030c1309021807120f06080f0c030c0103411602 57
    0x110b0700030481003039598150700d07100c0c00c050360740c0c41508501140130342406041003000c1e0a10102a8401030310b8540203101c1156543c08003484180d00c008903282c0882d82c0c0d0703d400302c0280b8810720100c1d5a19050020802c90041941007859002d004c80ea01300262203d00c058240c0c0c5500650040305020040035002002c1c100030207110380360813541e00500c000044268454828a04030000d00d0f256000202c2001c52044d4020701c000e0005007c0f44241c1182d041011564901e800a1103e2981d03803108540740e200d0800c1c0b0b0f1500d641c14480128110840d10021508884020308680762030a07600001103030420688a51884150380700d54180850500700c071104007000c2c8180c088c1d40d80e4900000c01070b15041d000e100c10010035640c0d0b1281803020020794000000b40c90b0b008203c50803a070180d2041503640d0011028180710784120350030805207602c03034002d0710b4500019002c000300d0078004441c20100b500780b07040403041d0704401c2024420030000c01840c1d0ba2007070039000440c00403000b6411010341001109400c000c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 586084973 1250 586083723 586083731
    0xd060902030c04090b130204020d050f040308010b0307050406030906061e0e010506031017160b46020c060f030402120105160f020c090709061107050d03080405030d0e030d0b0301 78
    0xc283c5d541942940207014484401d8003181505c0010024410301c02e03a0003049150000340940c04050b2182640b04510030389403d8066600c80380c54078003500003210401c0000301c3c00c200c2800782c02c0c0700750030041404c0d01c90040440d40340d48588401c09031030602403140009411a40c001c0211046050415005200a580040c91410710203c83c1022203158002c60140c4808000d0394903001c074007041100906588950303e4842a40c4030640301c0c0c215800300d142c0500000c000d803901080e1000e64001c104803d240c503100d046080221828109845040440321402e41c06180038803047c03178035400005c00106800c00307207059403441c1510403c0b011000c03030300c1c00c0e4520341e140608000700c08491628621083d192070500605940403900100d19007240300d2402030704031702c0748818405c1244e080b070081c0040c0e81e09a1640c9401621003500703181c4c1c4040e603100f032980c00038003c6088000700340038118013900303e405482501d20b048010304020043d103404241c000001d50000070b40180e00f607507034400d464220350210004c0c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 586086223 1250 586084973 586084991
    0x303060a060c0b0106032a05030108010c0504081504020d05010e01061701020a0801290d090c120b010603150503030a0e100203070b0114030a05060c0d1b050a14090d060902030c04 78
    0x154441d4140035805c02c1c96610041d4001c0400070304952102c401c41c050851038551001c00e801841c40c0c0084c030540784598200340e02042d00320b0003001038905840b0503000a00c0ca0700041c1e50000c1c608040070700180d810940803028072001c2070b0203001c0c42c01d82020320000884d405150010424940100125a103040e900c14802c4240c1d06602c00180d0303044071024540c80d06100740f0015540e008000800b200c480000c80000c2403044021a504042071103070143c004210950703640c060002080170051740040c40442c614006200e1140260b00c94003400304102c88078012561100c0209166a00c48441040443c4100300401d4107407404284041500c0c40500c0a10304000041d0380392072040506014414410b1040f550f1051103403002c2041d00035107500305003150464200120021032652000081c40b00c07060818030420451b0b40e03e1182c0c01c0c911230440d5103161908040c000d0854400204000384c0100010410000c150740d5500a1803481086c0543d10010390b40e091881014a08030741440010700450801900e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 586087473 1250 586086223 586086233
    0x9060e13030e0f030102160b0411100210020c01060306051e010f0513020c0f0a0803010911030c07030f0221120f060303091311160203150c03010519080304080303060a060c 75
    0x48004251501c400350920f250019001e13000d40840c5c1c4541d070585520000910250088041c012405001c11040c0c07000920248064184554088805a4084040c0d02130340982c0e98020300310041008000180035440e6039825059460076640711a01040f141c4019000501c04480680100701e80b0080d18125481c000c00304440c08403000da0300e100e0769030110300205001000c0c0328051282c01c62000384d5110031940d25262240d50000e00511440902d8540c4a0394590b46603c2100d0160642c094000d0900400348e400b1900c2c403010306032031001c5000d2040d03081c07151025091001b40c00c01883c121140c076090030040100d5910802007808250486070b0050000d1906e01008680d1800410b840c109545d8510460480c00740010f402c0400280c5800078200b203881e443c80c0808114540708800b80c0d103882040460400711a2000d80742c04030b0703803141080100500d144c07843c94a007203c181358207243c01d0965910b0045045800c036500170801070300000100101490805403000c054840c500744910071880d1a115 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 586088723 1250 586087473 586087487
    0x80705030a2001050709170f061015030c1d1233010f050103090c0f08150c03060901170a151508071d0601030f0e15011a19170109060e1303 61
    0x80d00b04085201000c42c140140601c00300c2c1d4030311481030844001e4241044604568240d0380300309103c0c11f40c000522f0000078413034051046d07041c00c3c554402c0c0c400841103820225941040e0101340c0c0c00400d111042c90140000e0008110b00d51040290050b4000c0381003100c5d0801080441100664204d0f00050128941c1c4803481d806483c400c4c44c0020713520643e0306d491280c801c132503080136a0a112288001070484000105c680c1c3c401c01c803440c0c900b240c1d1291981c641140c00240d074202c0e40441903000510011007817401402c100503000c4100c42618826440712800919016a00034880e52154090002141d000d400f03000100002001089440d1034a0100001e480840503078602e2011118041485a032180d0031507100100004d508103c00300105900960740d0308054505000350400c0300001a5010391440c40d141a03c05050b440792821034202d82e000340c3c2c401618001e6040c400707882c41400000240c0400203001e8400001c000a00504152901480150080054100042501342c031400a0b038072500e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 586089973 1250 586088723 586088729
    0x1008011401030b10030c1502010f11030a0908040b12010504050c030610080a0b060c010f06060f0504050103020c030403140604050106052b02030c030d0e010806030a0c0e04080705030a2001050709 85
    0x100c0b010003601c9042c4c0890340400182e001511040d001e603000b1078244188030342464900160340080200c0050132407032000350b62031455a40340000041c0006842d83c00180c1104000074031078100e00349401c1c1c13100030304104c0ea04240c240d5880040a0340061017942000d10400d504205a0740d24181149018400594052600000e51003004000b07404110146525004030707164000007002292070340d01090b0141d0007030000c2c10350a2269070910b0800030700f1900801c0741d1210b5811507611146410b04090054000e54800c0940e1500c91000b00b2002022412280c00c2000440351308015060324101410000c2c25030700507421030351241d602002c404125003800d9680c408058601c0c00c201c033402c07c0c3c0b4000641401150068103805010b1001d041d813a1590242c401c94150100740c0b103d10940d2a0320b01890790750100f070800103144449051003070100c20350f0001900d50007845420114035004260355018115000f40c00000c011412001c56541c0d401c814032021440c0740300300002040f40f40361100000b410015144 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 586091223 1250 586089973 586089983
    0x2d060b030711030c0109120e010f080109090c090905011506020c0906040b13090503090120120306030a0c180605040513060e030c031801020708030301141009030f030305100801140103 80
    0x70402c20411003030068440c0c05481c00c1c0204180728082c03d14081c0405107504502c00507102c140c00320755540c010304015002078800d948401c0c0603800c0c1103c85008105000c1c0c2980c029444e4480061690b045009209829110303100114001d0110215101c1c80d40c0180c2240d415900110320b60f10560310780060955204034222004200039030703c0d030b0115a5410f80c030300d0628505401c20b8078540a0200002c01000c4111003030348c999813000c0040fa02d0050090b04043c403a4000c0d0070500c1d40442c034040a81c05560080c600400356115200039641da440700020a0f1b10240b4400164a008081c0382c1580c03240c00300801096805204924107070600341d440c2110080020049a41c1d60580d00c0d45407020030581d1b20702c0c0407440469903265002c2ea14400d9030b4032003802c55401840b0301030000c5100500030081d2030485000c1101000414481f00401800c0507840421004001007403400201140340c42e81304104503030098900007094245a038850380c041000d6084000c00c1da0600100300c0c5c034200c041c0b8449045035044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 586092473 1250 586091223 586091237
    0x30f0705010908370f0f0c060203040501081311060a08091504120f0302040f0b0403020306090a1a06240a020105060a060f0c060e0703140c04180308090f012d060b0307 73
    0x13500613048110048000542a14102014642041840400703035407440c0c05965190f46043c0c1e500340803a900d209900907140000c411401080c104140091214112032042c0700403501c900c1c01c41c0124246030480c185050000d4000c50601c41c20701c2d4117204c03072506024440744a20031890903490707194000000c0544070701040202510b401c5024400d6050f2000f500d07141490b031500964840a5202e00d8001c0d0000b42d10900408c1c01103051214001041aa4180c0c407030008044107095044109841100500c0e10350011071121501c0708030581c29180b11031010101e180c064031110409402401c4071401071401e070286800d480b06114158020b040c4904944075460103411001e03140c9489030150218209a04d0244107903600401003042c2601c0d04070240d80000101c6609508181c100001d488190b034039000020404540840880d00c54106180d101c50014212410a0980a01b45084030310f2288400085441441e003545041c85071000046e45003c0386100b84070441c1018000e100070311014140405100007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 586093723 1250 586092473 586092553
    0x614060306120715030c020105090a03080402060d0906112502010801091505030304030b010e070302120a0507051201090c1206030b07030903140c030403230d1d030f0705010908 77
    0x400800f0081d0024443c04401d41e90f2500d0094084c00c880c2c65010099400c01001840025000803c1400560590344550298803280c0078042107900c6a0440120140c03595807034404110580610075025600342c000c80e40d03d1080e19501d6101101080040786106284040b280160fa482900d40d030554442940009000c4c0d100500c0000b6a035069014035054040030500105010780c183d0324034105c5e041078244840a50740c42008404a200d01c207084a038194948000c01c000030040d03400568001e103e4144903140100c0c41d4548080c1c5030090b030103581034980319504040041e80c015410100c00025441c18000c1500350b035120041c2150042004081650b10741811003450321030441003003030207100718585d80d03152020100c003500c903809030100ba038038484282c80c90506c001e00c580100300d001d4600d20280c56281c05070901140ca142118000d80d07034900d041c3c440610f4540e03082c402601a886244001c0140da890140050002c142507405920903800030302e144c2074002200401c0840350381a02080d8071207451 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 586094973 1250 586093723 586093759
    0x6050702160305070306110f0f03070c1a04120302130e041b060e100c020f130e0723010201060e0106050903070902040902070213020a02070909050705030d050307030614060306 77
    0x200041454074000c140740000184000418800162401403809103c040300075030020740644608400d2210312001008040c501e044903c0107584c20038058030b000324624450b603c6042c0f0260282c2c4840341d52500c508284003c002030003900e00305070f44a505055081491400301b4a004c081c042c031994051a071744400190406c940440c0842200c0000120140340d9925803200070080c1801c014440c0c01401400e034000034650050498081b051b03401846010100784440602130003004141c1c4030706440d0703100d41d1900d100403400d110210281c082c1250030564400601da41043e900d00c174102050659141540030700160341c0e0480c610b030542d80c09080c038550320b84103e400b20b490058075a102e4003049101090201d2035080640007410610300031100c0306181c48889440100b00e02c214444900564440c8204101108140d0030041c0840d000d641074400c105d07514004242480810f468101c0087c10001c10003007080c0d014800d2074080d04918002e81c43c440d0480c4017007600c41c80054021403140421040e0100020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 586096223 1250 586094973 586094983
    0xc09140d0609120c060b0a050619021e01140f27120a0306050108061203041203090f030614090102040f03140f0a030207080f0615010e010210060f030b01120f06050702 73
    0x42d900405203d210b1562142c018040300d0f4420003141d4003400c0c414100e0b464603282400c8010345030000c07c0036103820051a2001c648103000c003100d00550256845c1c0c070300c0b1403c00e100d59421342c0e09280d0000c1026048418401c184e100e0003444024000a03000c03e208412118646080c01d101d1118031201c0140a00d421282ca0090780c0248916124400078941c00b80030b50603048141101d0003a252461184c444100b04000c2c0b50351419204e000e80d000340410081c4820301281d40c80881e000b4100310640980b1604c000040070540d41080d203000341c64942862410324a801915030000c1c22000071400c2c14101448822690981e20000d000f454103c0d5401c2904801400368503000c8155100711000d9102916010351600d103148201c40440c050a85413220f090b2000c00c41c0d52107006504100c07088443c04100645810a10b030f00418110303c103010322a0304480d41d031710171070010b050128a8208c2c10780ca1807600d150400e0058001e21005001c1894020010b4000c80c540b10099600c03850104503a83c903810200d00e05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 586097473 1250 586096223 586096241
    0x8040308040b1201080c012a0c08010c02120a02030d020d0b030d020609010b030114010b030a060e150f0a03020105030a0e010b27070309050319032d0c09140d06 70
    0xa80001400211030301010000c101e540c0c8032400f58450740ea652110717141c44041c40303054a804554030b40c02d080c5122140020090390512407440f180901d05c2141c0769039a0050b42078001900b560b654150f0b5a295580402c92400c00c0401d0754400d41c98641c11040082d120b0140d030815482d45500440c01001d144045d8000c00e03900135016045aa01d0b1500480003550b82e102520308504039442c200c1d00800d0f5007010b0003010714900d4801c400d1010350346449142d141c60b40c001032083c50f280e940d0b02d1011402c2078108040c0790141e510b464641c0d10765420305040100d00c50880314070320322800c81c607402000140d0300031042ea81d04c01a24180082c24403c40000c003405422001060350b8800007014180c48415031440f4400c145c1e013003520b0303d02c0729a560381e1010b4046039100213015040c0da200384025042c0000255180c6c050020600e00820082000041c400f030142ca1000d650007003c500c00d914050811441c0f00300e00c0328104500d0710183c614680740100e1a40c08802046501500641111a09200454100c461a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 586098723 1250 586097473 586097483
    0x1d010201110c011e02041505030417130f06080106080f0612010f0f0b06120f092803020607020106050a090c021609020309070f0503030d020d1e1a0105070809060304080403 75
    0x40d0390ba01110042c02040005280c007a55040713082d80c404000158030a45040e0b40c0240d4840301c105030380c00da068445810050044500f0104100c03040c041201d418041c2242030701048484184904281c1c401d4038488581e0480400c02410900400c0825408040c09400c232900d500e50501d140c440c600410580c400005044030990f003002c1000c081040c0b5a8049040079070f44007010400200c0e0141000788a104849000c034004d078071f187c08941d02c5c00c071040d107c82e040344c003101c00c4603009495a40281010031028070501f281082141c0c0c5403041c99011300c011940904148020003205040134002540311000d402178038840e6540c0c1001d82013240c000c1140d04084001d8030303007400c0c00b1941c0e42c591201a41c03046078900d5440c040c000001500120005d4204240c0c3c0c0c00074003031030401e88600f084c81e0081d000800d9001d1043e88071101c414031601c181e000041011059080803900c61b490194014800c0b44114000b0b0400008010b00710214440d4425507441400849655540e5101c070305026089000799040500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 586099973 1250 586098723 586098727
    0x406030b0f1009090b0111062d040602030115030905120d0f0218100f02100b0a2105061311060a030e030424050723072120011d01020111 60
    0x1d5070542003c510001c490711000b0901203080e0b80e50045518001c45802180c42e82c0c424000f10307a10703141e030151080718286501c80c02c030800075203884c4a080c865403e480a03108198000010300040d4403001c054110b031401802d0500040d8483d070742d000d50718610341c0b81c811444e60000c10601c20007441e54221220040221909544907403034001c0c82d0f0004070f680403410303100e038615018002280380507980c00d034002e0b10941c01505c4140f1900100034098034000305426030298940c80c0c081100780103400d4200c04018502300303000d40700b90549031030341c0f4060010f41480110102c401c102c0d0300060f00a80d0b01c2105980075200d01e80c545002c5a42903018000c0c02012030401d01010074045910301c00c0146620403070314a4810707200004204002541c61f0b2090000c00b903d030015401600d000b81e4105032244c030451b14180c080b5140d59654140000c45449a412010154802802c1040070b00c06da04040d81c000624001c2d404140c120080e0020b8801c8081800d20203428082c09030f0011240c2c001e500000c4004c0003807503515 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 586101223 1250 586099973 586099999
    0x60329060d02041e050406030b01090c02030d0c050d14061c0f02211501050d1b1a0903010e0106050102061816030c06031b0e060c0c0a380406030b0f 65
    0xa007207071484d1075140a1a5034850f0740002d9900d040d00801c02241d1700b00550001d180d080540400103080401f02e91400d41c441000068109202c5c1e07c100c40c0c07205d03410340d0791903250305409144805940c03000c01401039095500003032049d55500d211001040780001e0013540000c01092a24250512100398003a41c01070205200c5645101308410300304017103e01c03900f904c94060980e078141000f044207000781ca82150b50058044002448813406145911440380007503d5241d94240d0300d140b45c0d010081110070b401022640150900b070901440d60040d20190003806030780d06140000756140d00003021381c03003126071103108000e012509200d100c600e25094070064541d9500e80c280240c000c8054400c03580002c0c5000c0e038500c0c1100080310304580640c20f50344c42d1144008c0c0d0504000701500915010781d064081c02d001c0b843c503503a0740d200c80c03c001d00c0a80d00541010b14001d001c0c05105100d803001d10300c0040075144515501c500c0808440503503205050008c0d0f072604070300229179103148244115401075019100740f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 586102473 1250 586101223 586101239
    0xb0a090c030f0c0804170c0c060313060c0f0306090501030210050702061905031005030a05060c0a051b0f0c19290a03090210020c0109030b0a0207150204050307060329060d0204 77
    0x700380300714001ca100510528441c440d00c0d46c0d5110341a080700150300030b894140341707518100f4021078100000015030b030030012103611482d080380c4030050160041902200c800e0021a0940103480040c428000d04000b103602d1a00401c00c0901c03000f40d401c0401c01c00049040440d591141503410303010f003030708800c02034006c800d4014051b90b00c282c5401520605031003000856250015124040d00c3c1e0000103030901d912541e41c02003440d0450a803600c00d1000a0000401107041644041d0001485c03000800c4850908403450342000c01e48410b0328000d01c2000f0240a910042d040c50b182102c00f12101060741540182611070051081014204e90b92000a4450f0180e6855007022041a00858511094204158040e40e9403061311941c03e01151640d05c1c1000883d20321003601e90301c1442804054a4010259909a81c4140403040310f50761136030118041c130903414200002000341c4524102084021200030182c0801f4019071404c2d03e0541804400c00032544602c01524410b5081020a6454684904030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 586103723 1250 586102473 586102487
    0x1050103110901060c020f01021e03070b0c030c07031b0b04060e060c03090c0904021c080a0806061e030a061809061a100c050f0a0804090b040b0a090c030f0c 69
    0x2a10441101c110344109032900d1401c0a040301d070a85c607100000c1d03036640c1c2070150b246220707200107042d4054038424081c10541e00c02900010f9007000c1c081c640e14807203441e020f40342e50400b501c8218404014020082c2d1510b60b030701201d004370b030036041080041d190301c0b21491400701c48030382c01070070003160805002c104141e41d0440540030255000303444003980ca01a030718042d030104a070000e156074040660b00f50305d418440760050304140050410803400303060003182c81208021074811103904500144541070164000c0d0100d4002c0c00071924145080c0058620701402c03001012040341850000012541460060303210300f000704908040d00550070310401480c8001c00e2205000e550080c00e00c0300c00d07090a404901c5405604034001c004900405100504035009680c080007181e091107105480c82e814142045040101d91261803042d640c0d6041103000c4040d0b801d5101c0e0140524100701542040744d56256005050b600c517403200060100c00c44000301c1c003410204000c3c02c0c5051030301980e45111544049 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 586104973 1250 586103723 586103729
    0x11b11010f14071b0809010e03010e0a0b04050607180317131509090b061602180c210f0c0f040506070c15080103110405150405070f1808060f0606040e09010501 70
    0x3078418604c00c1c3da00c07903012800e15001008140d0390701009180c1d601d40c02a1140b0304042030260001075802d03105412b0b280381801c140303001e44408000c07a00b040100300040201e030741e00200a15103c46000c403590f2072034400c1d0085000040450300c400304a25001412501503d00c0720f07103140c410b40c248a40d1140310740612140c0741d20002c00154510000305850340c041c0511000600007400051404000e01000e16001801c000100d0f8803c020144025192610703030300c054005c0312031054032aa5141c0300b010840d80c40025074501d03a900d42101e0b00b0030040349600c4030b240354070083c04a4100e40d2186e0082c510b0000c3e100e903030001caa1100340429080b00744509021250140c0d942640f4032108800031800c00c0d901043c0921009014a00b4195030180500305074100d039400c03d0301c290361111035003900000035003a01d0003200c0ca400091001503400700180e9006014070281b0056240001c0803d0401d540f00b40c4590004203651011b05d400000318605455010440f00104181416420316040c2010f140b8082c0000784 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 586106223 1250 586104973 586104977
    0x40f09030f11030903120c0718051006080f04062d0e12090d1b051507210e0915030109030207180c0e010e0a0308130314011b11010f1407 60
    0x301030802c611000401c849441c03200a00030710300e141d10004851010341c0b00071168101801071210000e0703200c0e4064400b0452112801e030200300e80c5494121060105404e51011082103101c4080c4a20025100d40043d04503420400114640005815901c07540000b240e400c446c840b884910705034050460342c412a03603e0030880645011072010302060320640a41c04a181d4058070088040c000521040f14210060401c0203d0310200d81d40e520019121341c05100701503608290026001d02001b00c41c400300031400240b08125850001c90f540e008010500d004422400b9042ca580440d855012035200c010034600014028040b814803417800a464030751a200c1d9001c0112502c10010a1891a02030032401b8101c0e641d034600010000e000464040350a902402c0e00034840c2d03400400402e500c00c0041c0000d8030783c0c41d441c0e82002d1840c03400e0050018040c04031180d90345003036031b1500142c0100316040c444d04081d24100360800c52040c80c050040042d070f04030144240c54100c160000c20811400790740704205e15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 586107473 1250 586106223 586106237
    0x3030903090a09061d1e0a0902040c020a030509060d0905030a022b080a18050d080118020c07060c141b130c02060106080907031a0a0513030c11040f09030f 68
    0x4084035800c0d203e0a005a10150702ca80c8030780c3c0a400c10040c505da03031102a403400070840700800420b0705403000c0c065070911403e5440f62440c00030750900b4001c401e035020300c1d803005040324600c544004009000e2502c803c0c1c4503500014540084100541003d80300907004801e8a54401201c0d0010395900c0c00302d032000c04200d82c0c10a0504400301225100c1c007418200d0348602c0e0081d59804a910b0080680c4045109400702c4c103d6203d0105004202d0b034100c8580c1da4640740003e5043c542404205e000c401105840e1500402030501034600100710300044517042e041c050055240380c17410001c28150820380c90050700c43d5205200f12495107030744c03089c07280c0c2c01503d80c0c5503171310791445007901034444143c845800360344207100421031188607159083e80041020141e0309070380d44a03038450b2010541c5001446540841e8800d000034180d00b0720030f01d03401c41880700041c511392459176805011402c0c0d100c00a01421000651898183c8450b08150001c800f890300400076140d081c42c0280130408040f8223440040c0c01c0e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 586108723 1250 586107473 586107479
    0xd020909060a0e071b080703020d09050a03050304211407050a060f08061005040b1219020705190f0c0902180423040204060314030a030b040903090519050303030903090a 74
    0x300c900918140c810b00140ba040139540c180c4151210701c00200b90283d08944052a0008204250040c110307284c841d60207001018680000104140c0d41a041103228141c00790b800c10018200000703e808a8600302074000c0e080003050740021004802d0340f8080d1045c400c0340c50746050300724007040c4407060340e00489602c15001d484030030840303241a0080000b40890aa10003181c0540360110448900003041d2622601d02030b110305284009421040c40340741c1500c100c600b84900c0030340e2140f43c0410b216503004118201002c035128039a403042403501d195245801a0b09480c1030054982031010415008000f02420968a07122240254400f9030301000b40102401101158500350141c0228010070075810b618691004001c00e0020700041c204030ba100c0d40c0c40c00000001015810403403541c00c5054007035921004604130280a851410020911481c60090000f0000c0e0300401c6050988405131505901a4147c01260341c901e801c6030410740e072503c000f10400c024a0f80001c002e1043c1c40040d5a84404196 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 586109973 1250 586108723 586108729
    0x6121203061401050d0203180d0903020306010e090a14161211010e10200105041a090a0b131e060209040b04090803070e011704050307033e10020d02090906 68
    0x14492405400030720100b00da40f0ba5006146c0180d50071900e94214207062884541e00c170b5242001c1001e0902c00300398050010010341c0350612860f1300400c1003115200141c80e10284490711502c00b0000140305406c0100b14803100704041058400300604540d200c2c450700d485000107034a0311403550003240e12461712a00c1c640654803401c0c00103044d0b607000d8910203035661840801c0c0e80c0b40030340c110700c6d2a0158841d162520310702c00901038035002e540034210b00440e035480c9000360484103e0042c015100d560040d0500800034014a074a00c0d4010221003507440ca0070324a03d000009803002d03904613030100281c206401d0622500380d004014040c001c50f0104030107032128003444243e905800d009410400e050002498450041442005150051403d4844c1210080128200b00700a49081d1541e40c00030620b0410107400150a1542c041049400704050049246070f0041408040d201c0c040048d040c101011b10240c104841040d2130703d519010340d120162444c03c08000e4120040301071081c155080403c4040c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 586111223 1250 586109973 586109999
    0x30c110f030c150d140702150906040b0408070506090706090609230d0206030c041a03040f030c170c0a0507060c0209130c09022206030b220612120306 66
    0x2020150240c2071008582e8200705000550f280700180110007002501142c014074850b00b4078401d5440c441d84001e0500d550002e10304040404e000c07240030483e00c20311199010008016038005d9001a81e450181e442c0d240090180c0120f5000608034450181409a10780c0e011981a040d10120f030b45214015540341400c540c002112310030080381d8440384090304558101403841402ea1240501001340500c2035601064044e44100c50041d0901e102103020300c4108000301d901030070504100442c42c1036041076161040584a81d5500a0034026203502c00400c000b2002d04468010403184410f58403400751544950302c400b1844030031110381c05010f00c01b103803143c001c200049007140c0103080c0c03241c0c039624540103049000d401581643c1c0f6030305a501c0007032a5806400141203240501d4030a52140c82c03030251035540081660030213400e044c240b0341002c8441d2a00400881079011219040031480351403482c6200814454206807001304d0064900c0d424003c406443c0314514005d6501001b486540d41c405010007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 586112473 1250 586111223 586111249
    0x8161a09030f04031719050d0506040204030c060f020a0b07021b03150c07060b0907091404060302030c06070602071a07081b030408220612060803070f0204020307110a030c11 76
    0x8405003c11300110707401d40a600740880045400501e448881d1000082d0604075030700da50005040050300c9885840240035603a000703041524154107003400c56861a0382207007180104010801e8040312160b110780300700048004180c0048809500d402c0c00d000003502c501180e4080c00c01442d100c100c100300e5040004a5940b4007a0904d40801c043c0c8840110103080d0f400494251032154403200000d1031135469000403400b40056440d8500301a1410085150091014042c00c3c455440d001c81000035071400309401000342000c6501035950320180c03400328000d001d50500030b04201207001e0792004010041104600072881030b182c62440d1342da407201940911800514000000f10709101040c0040e01010141c02014134210310728080c2c0000720f0014602000c00d50006002401e10b070381d4581500e0403441060b001d000340a002c1d602e031990707a0315004403100c3c190074000c3c0545d41c004001590244210301a0030121882003d60b04190030301d0400900b0301d030040f401134814544200030341c011490401c05000740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 586113723 1250 586112473 586112497
    0xe121038011106090c010f03090308040b0606070606031a0f01060c0b0a020408062a0c0c06181507030206150f01121503051f0c05040308030408161a0903 67
    0x594048000c0308140c0144005803181403015020144401c0c1c0c02c2070010b1449003a4140040103540340f410001485080c0e004640b50a1503e4012888040b90780801c071030350b000340c03c814031842c00e0310351f4008107800340324001d0b000d49120b242c00030200401c01000c0d1a24502034210011094540740c2601e07041e0064030038816000854480b0700303280b00040080b8840d9900010031840103040503501c02220782403290481c0c03946126a0304003a4070001d620241c030801902030007403039290309064a00380c01c03950354034030881180c3c446c0202044c1480a031542e00d244080744c41340074056000c50b008030900c004030798100400c100d0241c060500080c0200600c40744500c80b5100c024660b81211004d4001542e0381195141c001c121140c40d010080074042c60b18105100943c0300ea0014490340d40c0d007095420102110310b0720b49001504004030790340103590084c140d509a035003001b640f40d036139161450094207a1050b12103250b03000050440380e000303012014000300d0710a03c07141100492544c42c101d805480c0e2007100c44440c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 586114973 1250 586113723 586113791
    0x40803030103060908070c06020c01110607050f0334120902090c09010210051f1a07020613031205031801050f180120070c08030301030210030902010e1210 68
    0x30101d000c0e80c12000405000305d240c240b519a407519004207040007074002801503804440401c80559100d81080070010840340a4070860402860040c15845044024640e0400200200d159005840c8100107042a040001c4c150650b161245501c0070b401c0c0d0b009000070491401080c60564180e000d03d10303030175500038446607140d61451030b8000c1c03a8005c100c80604605c2400003c0345001c0041c8600d502400e01040c600c3c411001c0e10207000004680f94100803c08001010154035085104d01968045075040fa0056110070440007503240b0040c16510140550308900c203144441a00316000303502a02030514100b01c030441d03101000307082c4d030010354103000d0080219000031b056225070010f503d035440801d400401e0149d4140120f01915450f40481000e04500185d80000c001099182d0001802c11401550841d0b25540024170590001600e20303040c1602c8080442c11684600d800c40c070800802032410505e00300d040d044640d80d10b240700c100c40480d4a00420002d088981030000080560007d00ca0750b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 586116223 1250 586114973 586114979
    0x13050f100f03020423091b030a1e050a150902041b080402041e1b09150804080304061107060b03010f060b041a04050d0b1b040815070e040603060905120408030301 71
    0x280802e6512594105c40d015080070102c0b06032403070500a441100051100603040d00181c04104501d07100540f1942c803405042c0c000500c242c0c2c20315084144c81d0340b0188242c1c9203080150601d000400000c1c03525100d8400201d8a05140d1b01c2085003a000395070400c09040c0061400d15030640c030200c0800854640700c0002c5c0107140542180d41e1058252100540321905030740400d054400c040b1410214080325120740700810352040d82c0c00c004103d2200c10300b1000342c454502074400703800904043e0400d030002000034240003943d007048890352882121582d86954034100300e0001e04010342d1441c442d508004682d20760402e1809803400399082d800c1103a18041c9003a44840007510411209246007105100004880d621130045001c4607000b5090702c1c03017600c3c141c2c60340841160b44005d803265010082c0414003429000140080c0b40304450401108151240c050560b5049074140405900c036091000220070000241c000060885c403543c121444d048205803a4105030141c1d0040c00c070154020b01c010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 586117473 1250 586116223 586116229
    0x8010515030f0705090604060e04051b0d0b01051b0a02010210110405011803021021061a030703060b040902041d090d1d090c040501020f0d0801170c13050f100f0302 72
    0x5103030040b0f52030915600d03241107400400c0300354010307521000200d10035410b001d01034209030240d6503100c1244900070309018400c0021440500450b408629a280d56000c0182107900034000c07524069292181c1420300315040001c650303284441d010880c0140214648030989540750b00a003160982c0d0000e2043c1000c1c281001103079120780100c0100c0b04840408800805a250070700114a55501a919030a942922000030117440c2003040c000c11000c0e1030114200301c50b05a00f80c500c0a0011010b1502da540d40300e030701007240070b400c01e034110303194a500020300056102140e03801081226524210100001030182c103214001784102d6146148d0b40103802d080c07845e540310b0b4400120481f0009024030038404107001203108514120b904020f600b00c0000c003400150f0f010005210359442400c000d06114142c094000d00c0d0100620034503500c103100c8960600390140c03e020380c068810018041c0a09482c00d9140500605800d0300c8111540d510078001c81c80c030038180740d0840166000500122034051039a428 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 586118723 1250 586117473 586117501
    0xb061905010e1314090102090a0b040b030105041805011d0c09090709090309080109050d11031e0a120f1401050102032701050d140103030206060d05100c020f0307030f0801051503 78
    0x162100d9030340313800000c1c0081a20351140c3c0aa01850001070300c80704000240540b440307264000305130381d0354103010400c81804044126419104c0554021801581e88000540f0000026100034841d5003490103d081c83c6262550f02045148840105d421405400c000c0c803000b0fa009a07030ba90880c6d0011141800000c5940e0042d0f000e95229160481c07903079669038030003030840304080022182a08860004401190f110ba02801d030980054069881c281800000064441c1c4150307600e0f14442c0c0100380701701000d024a20145c4400341c0701405004000042640d10028104012201c0d100d800320340021949502c000181d910781c05420404540301e00c01c00400118004141c0c203940d0402104000f05040d00e42d00d0300404c0d803045070504980b001541940390181c109070300145641d029090303030f46a0501080300066441c46600e5440c0b0005412003c03200f089040c40d00b0129464102c1c88006441c0080551090307000440c0c461036510900d90342d0301c450402c502e1500d0481400c55041c010720105642085000c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 586119973 1250 586118723 586118749
    0x150e09030c070b120a0c02030a0c022b050d020604030c1e080a080f060103020f040306020c10021b0c01020c0a0302040e1006170105130c060503150d0b061905010e 71
    0x2044034245060004242d1a0000079000300415001c0807441840348211841c0703ea40086900006214818007108020765074014000a0070422540040390401e54480201c40c90a070582c144850103104c1c8404882d20032000c4000c0102c456215501140b55411310100304940500c0e03060f81e0b100c02248403a21400c421449080b212919602d4400f82c40d4001071060000304411107083c1c03a132100625007140081c2c0c90340d03001400c1d94107150040120385003491180007150b0907281d004070016140c50600000324582030010814a082c50310018181252041e0032002d847c404104104643c400748241d0012602c4e049103640007034002c07112900620040c6413541010403608485021a9603014400000d9015580700c0d601203003e20109600c0c2c1d2100d4035082c02196803108040410740c1011016586840e8050801c4c4200c00400c0004000b00790300440c2d0f441c605583c40e0000f454403a4140207424284030680098034920b01c12015001c4100030f18030611180710417114141c507000c0003180f4640c14031401044e030309 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 586121223 1250 586119973 586119991
    0x1b120909040804090f0905160b030c0a180602010e0706090b030114060c0604110f0603063d120501140a150e090405060105010801050904150f0b031902010909150e 71
    0x212021868140d144511800413841c40004210b2404074180700e4144101c00400184108650074180174035109400ac407900038018a64150741d40c2c0b01c0200844803d5484078800700b064143d09800540d0950541044010040d40f80a03100e0703941d81c03003800b0b95204000780b081c0c00280206000422003010f03105d81c1d01c140040080d000520300b1307000100d40703401c00d13808540c1100d6814281120281ea420144005410f07184107079803584c13541c01c10350001000802084040d242880c030302c102ca00e203515003d8418601c003031404032003d03000340744c64a8050300c00c50800440c3c8410602d00000080c00700511600401c0c00c5034080c6c00014500d091a203000d401c5060300391503906010540103484c1e0b0075110b0b084200d101e80c3c000d80107880194101400141401e5040c1c1c0712504c1035120506000100f609101000c03c0241010800116211903040003005805010541c50b80b500031200b035400500b0003525100c0e4054401d90365140b00c5a16501200111480c0e4000305061040c003010600000000c80070785a0441d00c0d00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 586122473 1250 586121223 586121227
    0x24060103021608120a0507020102040b090613030f20100c020f01180f1502030f030133080a0b04060b0f09040b1903030e030109170d201b1209090408 65
    0x42d210002c00b5070001e5800b44140300b513841004104403071031103120b800000a20007075141a1401e00f1412030342c0100321005100c1c100001d10121810920419540110392002100585240d6800e10b241850861000d000003180020344500d15880c20303041000313485646495036880c078012a000d101ea50754020603118103100c00d071055520b07194a10907095001300744014128034114100f040d01c80c112980c442c540c02c20b65000340003821044259a042c1da0644401c6840d000d03555031407450690440a5080c101c42014000503203850615900903001032049264060510480d0203070014003003110260310031880d4040c404e0040313101c05000100140381d00c000c004c001140105000c2c000038125603441c00c0180414031602000c20400d50030110000e24400101c0080203652100e489030120440060150414007038006103140300305030664010141c000001d949000629102854040030341d004038004900325034108809505d128001640ea0208000a90b40c00d040494075010700c0508000500200c8120b101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 586123723 1250 586122473 586122517
    0xa1a010f030903020c040e03040f0801090b0f0c091503040203010c0906020d110a02131b08060609010305270708161404051003060207060920150309011d06092406010302 74
    0x11b00d010740418140640007941d07490341340580c1401c1e4042c650740002c041d079041048a6002c15145c22040d9802078000307514a1683d0b803120800d0703815200701c0107503035480b40a480d44c0e810350003240c001941c49144203800070088420a04002c0d070702400d00d44039000041c0c2c8115a145c01682c41002c42c00102d0084a0441e01c140120b5400502d401200e541c035418180c0d80e0b4403000e0441503511194507881009410080000d0426002040c8207220b0407080398140342d00c50000c80e0421481404132509400c402030803049075030040b80c40c40d80f50400740c45003200a101d10200d061200c0031402d20310302110018000c00e040c0803d84424032024001c018000c21403288295000404a416400100341040c030238240000c0f08202d41c80c080506000d1401c190400e130700300d043c0000803a214140340b249145a103540d242e07200d42d58001202c4c00740c0500b0080310170b0030008400e00001840b000554900404184082e54003c1003480d24400310002c0e020590750015245002003281c650096009001c0c004101d401d5002c1c10311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 586124973 1250 586123723 586123729
    0x50610051e09030c030f0d025104060912020f0604020904020f060301150f2105040212070906030215030402012a0804062609070311270a1a010f030903020c 68
    0x40e03940640798203400c0301c01d030f003018280c1c1407201c1640030700d59070080f2492958468009103c40004005403c0100c429070360811641c2710b404601d0541c0c00c102d00b42d40581d03d00780c54400050982400304403107507070400340343c03a19203400801d801c00000c0d0f01c0c4004140701e0341c0c0c580130020fa102c80900160303000503500500b01010345500000f903010b1f00789000f10844004c41d4400081c41074074031000941c02c1001d45003500c1c460607a00010140014407100012074591681c2c000130b032448036041c45c801c102d8400c1d6600041c41c0940f50300700b401120700880e81255941c13266104003000b4402124024000381250041d01070050404402a050703410030f040703850106500c1e80c0e4003142179010f40c2181010405e80101100c02c048407200d1100c100d107800b84c80c0c882d00d05242448a59800c0d5a02000b400d580c4045010540b0740c4420189042c519132251440207000f01c2121081607008098407020714142c1022450406407004990361810204181d44141c006054201c08500038414031000b201103002d9481440c42d19a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 586126223 1250 586124973 586124983
    0x1513020310080a0c0e0105011803030e01110715030f1103040b09100c1d0a060206060402072f0a1a030109110c160617130321020d050610051e09030c03 66
    0x2500c141c2003104c249007401c0d402102c41c1816840340313041100000d0074207041481494150b0850784c0c1401d015000e10440070040c2c56114081219840c0d51207a82e0001406041c040b9000446a402e034604108080c80d890302d08050319040206110310100800c0880c0000c1c55000100b64004206029203010401d11100041518000e0080b10b0008421642e04248240f0000c044070a444040350004c4040740f41003806510b0f0040205414480d03a8041000018004140b0342c0007007110f4a28400f003007031500921101d40790b45107030607030780e008400781c5101081c0c0d41044404150301042c1c803d00d040c02c41e071811000002500c02c1584600f1006018030070ba1003c0c44e8100000751a00444d03043e9011600e040c554000c00703480d40c286511401c2456801071015403400740c3c000403210f541500c3c01210301c50101c0701215820b48842c2c580c4480601c002581307400c85d80c040d449280a400100c628020b0304082e400f0444040c0680c04035010901e480300840041050204000e1406c4400503096811080c04c41e80002e00305 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 586127473 1250 586126223 586126243
    0x30709090e06061f02070302010e06130305060901050603030f0315060405060a090e0c1608090d0b090307030e0402030610120b10030509010f0e1507020106090e15151302031008 77
    0x354014414007100b450b204065011195604c8640c002d42c20ba01c0b04003e69800035444082c1c10b100d000502d03216030392900c0d0102d6003211101c2068001c1c00e90740c2d1801c11390b41e4030704035240401946010003141e101e180c0441100d096510014a150031600d90301c856503031148030f51480551000003044005010380300c20021304440506902d40e15480c0e8940341010004000007481060107070781c00c0240145404041403804001504138405548610011003c10700342000004007500380028402001445840080149a094482e541303040e032690f40c040a000c243d020a8511503402001e1b90300514001d84525001d0540114410b40814004002d00215a0071094040b1103030000c1d40342c4042102d411400d00400c6103a240c8007038100303c05c002e05032507551103072440716141000490040114442178400d400403c09041015400c01c00c0261300003445555242c40f00e041c0c40d50981420001d9000456004220011a000b804507051414812424002980020405c154154404d4008658180100581446 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 586128723 1250 586127473 586127501
    0x18061817090406090f050708010f0506070f0203030f04080a110a060f0c05011103070c02010801050a0f0b0a051201240809060a09020117010617160e0d11130f06060504030507050603070909 82
    0xd87d05222000420b120816002540700290020f001c00040e119401184c103415000702d440724800f012440000d0031842260015900f40c0b80c04100459032902c0400e00040302c612880c2403440d454099418019074590600c207000100e90482c01c074010982c06540c500b50005c0c403031000020040840001494140c0058545d40c8c0000ca440401c5021940c1040d241809010215503055009180c108803100200d100e0240030610310010170007aa8150046050343c156600715a010b4032290307160008203482e00c01c1c0713004140b010100ba01d81d95440901a10307400b800760342927030050266913440080e044040c00105034201d0404c00500703230941e000041c02002034045d200c00e43d10240b061803142d01c071040900014028100c44001c81b4030b440c00c420340002c4207a4001d8030a50b6492030b01d10050404001141415140726080038a051441050740007076404815110440402000030503200c0008072460f0280f400010301c0c542c4102018010b82c50580040c590000851410a0300f0702e842c1e095031420349540201c4c07900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 586129973 1250 586128723 586128731
    0x120b0105042301230f0604030f02010c0602030f1e0702060402060c1e301c09060507080a150303020303040204051b0f0715090b0604091518061817090406090f 69
    0x2136485000d0307420680070f00c021102d00c01c0000b10800040c0561080c0e00c801480c0050001809085900031062000c4003500410119144d141440000040600484015480c400dc0700300b131241c9284401d88142c0281400c0d030040100ba503076036091120581c40214151010305c600c81d0003030507c0f4511800044401540000b4028500324103e1300c080c006102d8819140068038140102d800c8030801d0b069070a2001c0003070400301c0f02080c4111000c0101151180602414248030801c50711541015200740a2203100c0340130040420f4080c00302450190b2408001c0041e0010008500545056046180c1100d205490100c21303803580102d04601d64048002041ca014010a42c901070200425a08100c81480c940c188144c1c107a03541c59611050005100c05d00c581d07035402e80001480b0700c9100b0031113484a028000c2040342d000e21001101d5416011044880340e007000000c0340d0041c222540c45e00c150746c0c8421204854a003c4c01500c00c150490400e040d0495540d00001540d01202d0003000710210810500007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 586131223 1250 586129973 586130009
    0x1a0907050f070c2630030c2a150619060206042f06070c03080d02090423070f1e050403060e0604020618060702060c010204050307120b0105042301 64
    0x1200f40c2840034866100e5019025454145012070a140e0600040c4650301c0c0100d1121081d490030840005c601100100200410021007003603401000c1c4256421141d00301a40d8140014540304008611940780da00b10000d9103401c4004a1001a00410024090660000303c50310b40010780d91a90301103001a489002884144502e0549843d408249403072001ca0201d400c0f2070040550450400071030060f080000d040c024040c0c090038000113154024405a80c40d507502c41288082d40000c41000d20842c03031b01c80140041414200510654003100854800c0d41c1c1e42d5180548010030160401d005100c203c0803881684468902e044203842c500b615100d80303175820342c20080300300c40300c60404003640d900c00c8061002603039034102591500ca00d04410306071404241c501150036805030200003900244003241500c0c515106401800a2310b0085c0d040340c004070358561064010344200503015090200600050142e41010b410140342e00d41030b01c0584030300321000d180081c070b0108240e1080840341c141d403142c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 586132473 1250 586131223 586131239
    0x1d030405130e1f0f0e07050f04140126030f07060b040b0a05240c070e060901030b0f060609130c020c1503011707031e151a0907050f070c 60
    0x800a02501c20a0800101c0719420703280b41d541240740c81c05070b0390030a5405a0a800001604000c2c2e440c050303510284a05564404041c1d0303074010a0150b203200e49010194510076040c54450080d04891030004103400387d281c00030707070700900d08140c1c4580f03446503401c411042d0b6140204000c148550329641d605540e40100d08040d0122140040c40d18800e03030500c188598640d64440c44e08040c1c640498185600c0195840c03840200c2e00100c215010540010a0040e05030802050350400c07101c202d03403210490303a02d00040012240090000400070036850021422080320440d14a0f80031601411051411160f200020040411112000302e807907140c0d290180040e5041c0704a8214103401d4440440ea00e203406005413040c00140103861131030210034408a00702034100f08041c011508a4121201011240b0b0501051042c0000a42d504100d4007000d000110039445403044900721030130260000402c07481085490940034206904011092000d5011480054010034200d072044d18080d24140c942106 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 586133723 1250 586132473 586132489
    0x60306050604080c0f0604080109050a120305100b09040b420a030b21030a030e070b0414031f20130e1b070c06110a080a121d030405 58
    0x180d0300550041c003040008640c00205013a072800103ea2034110241810003154580c007403903011000540c2070604440a11802041a0401d20b004050350700007440701140680585405481b01080303074050785000c01c1280152000b4180d503810042011401c03654680000314465403843c5042c40403414081281080160445010ba4820500c122080481031301c034100b25090240c1c2c0c101b00d00f85512480d04070070315034408401c07000250a41842100110a0300304580e5a07422010b200c5004c01e1524581c070741c029200091170000c07180821301042c64039080c44c001d680340d081c0842542c0c4e014460b800301140c040000380407004603580312000014503150105107007940c1841c000450041d00c03c2c00c1041075000c0b14480c0c00082981e03940500c3c000c0da41c40d80361100300c0c100c002005810003890007017461420062500c0320b22044482e42e58a00d000340383c5602c000c548461501800606229041109183d142d0054120360703000301030048009a4008410040d0000001c0410783e03000341c1d000050300b07024034a05600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 586134973 1250 586133723 586133729
    0xc0806161b0b0a1d030d02070515100611010e0a1101020d09030b0f13050d020703060b032407030b040f06080613050d031e0c0305010e1f14210304060306 67
    0x41d1240308568552100400c051018202d42140c0e44c03581c1404040300120507880301072110a40403a0380d079130000d4290310025040340104442c0c5000b40c4000c2d0550700f402c0110280a036441e181000c007654501901a40c24103090000e055195480c0c03526940c95060a100040640d40218107800000141100080c203126966032400240003c0d06e170180b01081a4a550560200b10394102107000d4913040030742903500c807101c0d50041c0b45205000480f0b1a455010442008407403040c0c500344400d4881d2010180c84000d10340b142642200c166030301207100341031002851f4100c1c5c85801e000945801240200702510080c1c2d100364812a00c2c1c00e020403119000b0004c903a44000814462130011486070340340340d103803c9045100c02c03c064603074803903145541062880c0380400e40d90b403008112000d0680009009071070240300b194407001e001000646c9281510740710000031131711030308004541814036028002e50f100e2a298250080454000032030044002407514204205400065443e240740c0580107041d40c103e03070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 586136223 1250 586134973 586135007
    0xf140c0406080304140d0302011b0e0a0b032202190b1b010e0d030b0105092d1507031b020301020310170109081911030a171e040f0c080616 61
    0x801c04000000034800300e45d4801c4450501d06590740c102240589220742c0701405402c1400400b003002d58003e6450501072030155501142503a4480d0318100c14001111215008015001d00300200380c108043c80003c2ca01c02010b680115400c01c0914180e13990300d41004004081c000f86d078960700302040c4441c4855501120080c00b02c509000002c585940c41f40c611541030503111074049100d68020019620a400003400145000c1e04070750a045987d00295142c58211707582c0c4441c100d103424001d44512010a20541162034043c9033703079048a51800390009141040a00b5500000594081c0000c6009900c588440d2080a04110b144070002c500e00740c202440b41c2c508042240003412150554185c0f54000d0640d030f00c951045a0150b0b14960a1342d4903109034000025200e00c0030b50000c8541c404002804900748042d0784015490003500016441500d1000d210f000041c0007d480c820300001d042c0c820142c49900607560f108151801c0303000d40b010165001c1e10009c0d2810981d10035002c4800310150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 586137473 1250 586136223 586136227
    0x1150305160203070b0a0b10050d05092a0301090605090a020a0f271508030d1802090103082125020d080105060315060301030812161b0f140c04060803 66
    0x30710300603560348241c0c40014009080e10703000400ea034076540e01081400708040c2c2808010301030007400402680c860030381900305501d0700700442c0c84450001804000c40290790417015030394211a15603041c2a2500c40314590540d00c0f03903420380009845020f06400b0b4103031031000f801c0c4060f5510400c02d40c0311180c0c000085980703480d0b004000704030030340d10300c100040114445960112003001c800000b421180000920103c0d602100190660002001701801e1010000070000c60942e6400c6961002c1102d40c040d5005070301f0801031020030b5092009202d03009008842c5c2001e0341d2511002901c011003184c030340c0058448840c11011030002c1000000440340b613403000c0e01d54402c2d00c40005c0d0506006004560040102000050034100e48120b50b070040c42008000c0740d125a900d00d44203c0c59800342c3c8002202520304c0c404100d215036003801403405542c8688513114602c0040007102c81c20840f0a0081d0b4180f031080c00c4d400c020903095202e9a115910203405407400a00200030701c0151612584000125801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 586138723 1250 586137473 586137511
    0x7080d0503070f0c1a0708130c0915030b0c04030b0a020a020a0b0414032a07080a03030b061905071703010f060c050a1a04050c03060f181501150305 65
    0x4480201d81e4820440e040c0074040081e800740c203c1e00407181c0d203c0144809401c60001c8a4048031020040c0b044c1d0180d80e5454081d42c8000416040e4042020020202c2c0820f0505200c5080b0340c2e0405a8031300c6206d28280d0744075550391a50003040300c00707039141d0740d600d03070005828014066100000c56100e1504d400942c58400e1505001b0740d52032501401803e62006107005c101003103042c11402c8075207040441140c0d00d64440e0340c44503e0043c00c1022201543c115288502c010300404200c1c40d046500040150200c0b8215450580241c0601062641d122808005c2c098640c40c0783d0a120701c88501960301c0d03d0700c88519103080f4480101d9411201d62808040c00100300344541c40582c401a0343d01440e048100040e0740c0340103841c0081a510050807083c0c0d001c44001a01d070340c070360040d200b18060401c480302c191840c418941c40760800d884580c50040c1001c001941c07000c500c200c035258401c4110031120f4003603901890302e00e211402e80080c0b803e10041c08528540c60781c1800380503004189004181b41e2184 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 586139973 1250 586138723 586138727
    0x3190305070e0f04090611180a12021f0201200304020301050a0504050616030915051009050103120e010e310501080a031107122303030609010308090d2307080d 70
    0x2405043c094416611014004200065a04061030382100000c01c0f82c0c07034918129100a891000c3c18905024080d03841000440259074140410402e402600900c001d408075140c1400948800300d080096648500b007550401c400c102803021039090602c0a9901d030b06282c410107095a001400d0012614201000d01002c030b000803400640000d032070010074552618a29058014025600e4058404d144502c0c1c0800c1118050b00294400c0000c0710172180700301c2d15403003a2001c0f80c1080c00090124200b8525080c03455000d50708810003040305042c5848055645c00000c0c8002003501741c1d2441d01c1503145526419100101010200f000c100036042c01302c0d42c101420269a03180b20b140c058104a1180ca01c1c03d2016400d20090001d410307039150000208410381081c040210140382e15074540401031070105c14040c0040140ca010b84401411414580d1a6460315101d51f00046401a0f00030f446034107840c00603900301c80549010a07622600d40036907601c8c46681d030411190354840e00e9240c1050300c0d101c207095 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 586141223 1250 586139973 586139989
    0xa170709140120010b0108090d080106180e09010b0f0f0d08161209031506120f050708030c011b0903031713080403050610170c012003190305070e 64
    0x1604a4500821001c84800121411040010103601900000743c64903c01d44040d045404120307000e0321500c1054036005c0c1e83c517a80c0c1e40c0e6400e810000603070003801481080d1040b88041607042c0c030704444400c0380d40c541005011200c8140c8210400c0d0b9590b43c00c4d203c090500c569042c41d140710446150440080f54070221b009010f416100600100000642c0000070200b108074000458000c10000c000325004180070380744071041d0000356145e00100007036000810860081c04280d031290010f8402e5881556149083e401000004030341c2c42c02101c42c0840c0c0c0381c2080000d4101d080d0080004102c2000c203406442d08890340265100403c00d02000c1840465084403400d401160000c40f140780303564400041c4046403440910040600c0c40c000380c000f06002000507060300038160241c0e4800c0c41540d40c0700748841c400c40e0100c051181d0704440801304c101c0d8020040c00c5260048142806400c0c00729403041801c1d5808008104408100302d11800c208907030610803a503110140b410000040c00040000401c10303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 586142473 1250 586141223 586141229
    0x1060509060706020903120c0a200a0905091e0c09011e050112060e0708010311030606010906050a090509040c0e090d02060a0e030d0c030608010b030a0809010c1e05030a170709 77
    0x3d1500040c10004d251004c001030405841006566600c071514045d5940e01c4200c2c0c17079801c1e00e2800c0143d100401c0d80c1c0384d822001c184164001d2144450f0351034000d030000a0003005104100364014a80040b240200c841c100768280d003218406408540400401c000d500101070300029024444e528003e002c00d03d584000030b09440d801d0030000074045042c0d0b403402c0980302c20f4001000c8100680f0030300400715084a601c905880c800c0d10000404c42e00d04092541d200c0302211a1800143d600004001250144000703145030300d01490103000c81600d60010454003401510f003103410401e0324900700715607854001c0998110707100c4400313401d051160440003555118007a0904045070707a80d20b24405507403000c10459000209d01042402071017648900900103040e148071b039401550030040240010300d0041403210221b9400034010342008548401110141640501114112050b042c1c0c0780040314260ba0034501207118400443e52110b2800004004038070703007030545004510a005000906400c5000d110503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 586143723 1250 586142473 586142483
    0x90c03060406301b0308030703050c0a1403070e030303100311062803091406011401020c130b06090a081c080106020322181a03060c0d0b0102010b1c02030105010605090607 75
    0x4410f001d41801c4040d0003141031803400c4031005001c00804c01225038051803007084540c40800c06607032544801101c0d0710440b0041c40c002424180400e10030f0800d4400341d40c00000d0fa107084410401c40b4070100e45954019a02c0d050182c50380c120420410070102401c0003855015a0140d0515031120031040a0103100200000b29098920070004024807981c0540240f07074122604000010301c400480340c84030340a001e10010a0306000b5044e425500014800d803030503501030444101c10225407038480052081c6e1a60b141d011004001c14205035a41c601542d018040440140c00ca104a000004407504d40081c0084c081c000400010815241c000c0180d030011640d00704420709040201802040720b04140c0c001d4021426002003103000f4180381d074040550118006281c4184030050380030555242d808442d19040403900700107500c401c40c0190001240c689d01070001151000201d00050811840c1c10504188214129054801d5260901559004040605046103002d82400101c2d015104264024003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 586144973 1250 586143723 586143809
    0x409230c0a0905060a0602030406090b0c150127090b0a0504230d030609111b102a090308030a09050f070603090b0106051309051302090c03060406 64
    0x680404180080300051000400503800e041d1501c8011000380015100d003030003110a2200420386500001c1290155120741e241c5401561801d9a044100e0740b1202208410f401010740d150b4180e4030700e0540302d01924450220703030b0320711495122450b00b1005c2e40202044140c00c014074100450144410035400c6000e08001060b1555036062000088500ca8602da1920041444a0b201000d010400c180b01070420350f014802c40303581b4a0350405646a8204c500f080340f03403c100e0240b84118003880c0010200c0f088081d00c110003200e00d20f02c0201c0b120001520102d0480c0d560b80c2028405141a1900d64001424a07100b0182103803248603403408014004d10b5480d070b0315411002401070400c03200599144601c21540c0c065100c43c0000d020703246c110800c40c0c00d01120000030400e28058419208041504170880e8a080e1809050340c015003409000c44522482070401040581c45040c4d503140301e00900240141e490030501c0a02040310003660101c49041509522802c40b40c912001581074180e1b07460f4100b07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 586146223 1250 586144973 586145033
    0x10151a21060d021906030e0102041d0624090112020a0c110d05060103140721030f0e1009080c0303090105161e0506060405070e031c0509150702040b0409 67
    0x600310030b04140042c4d40f1840901c240105550048083ca0540d446503800b030080d650326543d80c80c240e001d14001e240e0040c0d284518107501e0403030302c0e96180e4421001843d030005072035035070407180010149030002c009008001a0660340c0d960845916030283d444c0340400c514044c400040201800c40500c001440005400c4c045103c80c1e680300203070680180c02400b42d41c41c0303594a140890104622040140035809500000101d900005002c0301c1c1c1c512112a1041081c44140e070216621010101444140443c1c141e607080c59807603d204440c81d682c003a0b01c402d00100e0402442620346210f604d1658481d601c10400761861344da00200703413102503c83c0001035803000741602e01041a1410154201082d210022038802803110004010f40608010b841c1000540c44003003040f14542d1300f428000c0c1c1c240c0d21240042c000140c1c2d0700b003101c0004c000c80c5403803410f14440300c0c00600080b02e0381540701c403220301c049110000e40c505031052020095003124100454031440c0d4803900301d045d0000040f516040441084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 586147473 1250 586146223 586146229
    0x4030e0111070b0f121308222301020f0705130b15070c0f08070506030c03040f0c1203021204050315090a1a0a18050714010210151a2106 60
    0x1d0090101c40304001e0b141c1401c181c050716980c0091107003040100e689004180c4030f2121a51803501c9503004140c01c0d1805a03000540c09550401c0340d1140540f181b040c10004000059801e4010f1270500c2881140360000c00d600028a000c1c088002c19007280c01030326040145580e4488800720201d0103aa0200d2829542c00001c1c10114990345135202400001030800d0410000032030401c00c1e500049034240d40180c50751b102c0f170b030303130700410f00400c4c2d0020010008a25040000005580d00520882d608907004a282c1d4a807001103602da8003121044034160340e220100340c0c050008501c071248a88045041500e42800a40d88500c41c103120b000c83c245c1c04002c07a01e0000309114030f460442c0c100e8405080d031002e11070a2040200b0884174410307840d20f070500c43c034040303060442c80a00140e045001000018180f41005c0000701c049150b650640c4141d000c841c0da130750480c2c000c080c1e020f41c0135039a032110a0b00c2d1a1220b0042c001c080100c10b001d040800500000300d03000c1c0010000c01007041c20041c4075541d40404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 586148723 1250 586147473 586147483
    0x140610050a06110a080a0c020a0e1b0d180302010b01020c010315061110050c0a1202070c0b0d1e0e070501140a050f07052e0b03120a1403040308040c0e04030e0111 71
    0x90450400006d9034103269400043d00300b4018404d0360002003481e940d200d0140f04c00e00c00d80e0141420301132440c101082c40c1246010307040c1c0901124001a02d22020b030b40e40351455100364421409030351038460006081d078050001c240408001e0905111110b90014404803c5020b40640b10900031118003441149004001c0c0601c05458400c0030010b9041401d066655030b04071a01d243d0000340c50400c5210225420300030f075086107a000c611200300c2030a000503451603400031441c480c01655140400307801f10080b007500b8000c88a000c140050603034241010181403035210741042e4184070484060b94003103030785002141c1a4a18502d092920380c030504684c0c88480c130030008041d0a40c82441002e007d42c0c0c1740780143c0744169080c020052000382c003141c40d00080d15039010038107901da0001c862040c4840403020050040450b903140500c20036890bd0304d00c0d000340e0020359042c1e001410350f1040100304500303034104901410392200701c03180c035140964004150380c20084046041000d1000c0440d10103a04100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 586149973 1250 586148723 586148743
    0x406121b08060f0109150506070f02012a050708060c0708070201020c06030103060c02010e240c12011203030e120901030b180115090504020910050315030109140610050a0611 76
    0xc0d40c04505050f09a0340c070058003030045501451418002a035200360f1184038070103c401c041c00f09810720340c890b1142007419184000590520110608525115800e0020300c84043c1045540da0700740b1038241001840e220301c503005180030703030300c03c00603c829000b141003540c0c1c1895028850b607699280c28070040341401505d062154000c44040008420800c080d0000030040203582c1c020403038001255240ca640d000c4402100302d000386c000d00d588420303400145240da441075408817241e00c1d04440c81c10645048200343e1049880104140055080550500620401c0c50507203008101c02408014229418851101010b06159880b413000f40c00d03840341446208042d55002110541d03680d2014280e12540d42882c550000404548001c9510b04d418400e4865041000c0c246884003445044240c5190740090590901d0140c0d01844400c5580c00340580d81c0031038411030002540d080d031444001c0c503151010744020482598000d0602c09502d42001060440e03115107408d60701807201400d128201410340c0c2d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 586151079 1106 586149973 586149989
    0x1409100b0a0612060806070908190c0b070f12050c0111030108030421172505210c0f0f19050c09041401090605150406121b 54
    0xe0201c1c0c3d88a42030240004029840d40095464401c0c04c55100000032040c4901340140c01c420f00800c410003907180c425581e1150503544100542185000f003020410002c101c400a00c0304550703820403403030341140303101d01140089a4000c0559100c6858006658245002c55140039000000ca07412540150040c5091500f0002c800b0fa410f0302d41c2c13441188640ca085d5031030001c00c070741003400010394601d40c81da55928843d040d01e240078290b11740c00410300c903a280e001200120b60040380d1000002900c1c51282c1d290016900c5420701805081c002c4040e43c456001600b00064000401c01800740010045841d0740300e41c4004603941e2107030203500410300e40064122400c1420411000b03031b0007030700c01ca0365403103410340c01180310b42110001034007560b03050b844005106040034124200850800c060718188280e1b4201030035001c4500c0c0441000307003510b00340185034804140c00000704029084603 = true := by decide +kernel

theorem cover : BRFrame.Cov 585971223 586151079 := by
  have h0 := BRFrame.cov_init 585971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 585971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 585971223 ≤ n) (h2 : n < 586151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
